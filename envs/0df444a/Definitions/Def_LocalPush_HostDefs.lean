-- Prove2me | Definitions.Def_LocalPush_HostDefs
-- name    : LocalPush_HostDefs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:41:21.545454+00:00
-- url     : https://prove2.me/theorems/e8db8a75-ec69-4fa6-aa6a-e598f0bf7df9
-- title:
--   Host program for ActiveSetPush: relocation, data layout and loop invariant
-- statement:
--   Definitions used to state the iteration theorem of a concrete *host program* for the machine `LocalPush.Machine`. The host runs Algorithm 3 (ActiveSetPush) of Cui–Wei–Yang with $\lambda=\eta=\varepsilon/2$ and $\kappa=\varepsilon^2\alpha/10$, and solves the restricted system of each iteration by calling a *guest* program $Q$ (an SDD solver as in Theorem 4.1).
--
--   1. **Relocation.** `RP` records the relocation parameters (code base, register offset $R$, scratch and log pointers, return address). `trI p Q` translates one guest instruction: guest register $r$ becomes host register $R+r$, guest memory cell $z$ becomes host cell $2z+1$ (odd cells), every guest store is additionally *logged* at a decreasing even negative address, oracle queries return $-1$, and `halt` becomes a jump to the return address. `reloc p Q` concatenates the translations, `sz` gives the number of host instructions per guest instruction, and `lay p Q i` is the host address of guest instruction $i$.
--   2. **Register bound.** `wreg` bounds the register indices written by one instruction and `regBound Q` $=\sum$ `wreg` bounds those written by $Q$. `post p B` zeroes the guest registers $R,\dots,R+B-1$ and jumps into the guest code; `rp` and `postAddr Q` fix the layout used by the host.
--   3. **Guest input.** For a node list $L=(v_0,\dots,v_{N-1})$, `edgesOf` lists the pairs $(v,w)$ with $w$ a neighbour of $v\in L$, `intern` the pairs with both ends in $L$, `entPairs` the index pairs $(i,i)$ and $(\mathrm{idx}(u),\mathrm{idx}(w))$ of the nonzero entries of $L_{\alpha,S}$ in list order, and `intsT`, `realsT` (with `bList`) the integer and real input tapes of the guest: $N$, the number of entries and the entry positions; $\mu$, $\delta'$, the entry values $d(v)$ and $-(1-\alpha)$, and the right-hand side $\alpha(e_s-\lambda d)$. `guestInit L h` is the resulting initial guest state, with the constants read from the host registers of $h$.
--   4. **Host state.** `degSum L` $=\sum_{v\in L}d(v)$; `DInv` describes the cached node positions, edge list and degrees in the integer memory; `RegC` fixes the real constants held in registers ($\alpha,\varepsilon,\delta,\mu,\delta',1-\alpha,\dots$); `LoopInv lst TL h` is the invariant of the main loop at program counter $68$, where `lst` lists the nodes already added and `TL` the nodes still to be added to the active set $S=\mathrm{lst}\cup\mathrm{TL}$; and `xtOf L y` is the vector on nodes that takes the value $y_i$ at the $i$-th node of $L$ and $0$ elsewhere.
--
--   These definitions are reusable for any proof that runs a guest program inside a host program on `LocalPush.Machine`.
--
--   **Formalization Note.** All objects live in the namespace `LocalPush.M`. The guest's memory layout is that of `sddInput` (Theorem 4.1); `guestInit` coincides with `sddInput` for the list order of the active set.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and Effective Resistance, STOC 2027 submission (manuscript sha256 4c36279a…), Algorithm 3 (GeneralActiveSetPush), p.18; Theorem 1.2, p.5; Theorem 4.1, p.15. Formalization infrastructure: a host program for the machine LocalPush.Machine that runs Algorithm 3 with λ = η = ε/2, κ = ε²α/10, calling a guest SDD solver through a relocating compiler.

import Mathlib
import Definitions.Def_LocalPush_Machine
import Definitions.Def_LocalPush_Layout

/-!
# Host program of the ActiveSetPush reduction: shared definitions

Definitions used to state the iteration theorem of the host machine program that runs Algorithm 3
(ActiveSetPush) of Cui–Wei–Yang on the machine `LocalPush.Machine`, calling a guest SDD solver
(Theorem 4.1) through a relocating compiler.
-/

namespace LocalPush.M
open LocalPush SmaleNinth

/-- Parameters of the relocation of a guest program into a host program. -/
structure RP where
  base : ℕ
  R : ℕ
  t : ℕ
  lp : ℕ
  X : ℕ

/-- Number of host instructions per guest instruction. -/
def sz : Instr → ℕ
  | .core (.load _ _) => 3
  | .core (.store _ _) => 6
  | .integerLoad _ _ => 3
  | .integerStore _ _ => 6
  | _ => 1

/-- Host address of guest instruction `i`. -/
def lay (p : RP) (Q : Program) (i : ℕ) : ℕ :=
  p.base + ((Q.take i).map sz).sum

/-- Translation of one guest instruction. Guest memory cell `z` lives at host cell `2z+1`; guest
register `r` at host register `R + r`; real and integer stores are logged at `p[lp]` (decreasing by 2). -/
def trI (p : RP) (Q : Program) : Instr → List Instr
  | .core (.const d c) => [.core (.const (p.R + d) c)]
  | .core (.add d a b) => [.core (.add (p.R + d) (p.R + a) (p.R + b))]
  | .core (.sub d a b) => [.core (.sub (p.R + d) (p.R + a) (p.R + b))]
  | .core (.mul d a b) => [.core (.mul (p.R + d) (p.R + a) (p.R + b))]
  | .core (.div d a b) => [.core (.div (p.R + d) (p.R + a) (p.R + b))]
  | .core (.load d q) => [.pointerAdd p.t (p.R + q) (p.R + q), .core (.pinc p.t),
      .core (.load (p.R + d) p.t)]
  | .core (.store q a) => [.pointerAdd p.t (p.R + q) (p.R + q), .core (.pinc p.t),
      .core (.store p.t (p.R + a)), .integerStore p.lp p.t, .core (.pdec p.lp), .core (.pdec p.lp)]
  | .core (.pset q c) => [.core (.pset (p.R + q) c)]
  | .core (.pcopy q q') => [.core (.pcopy (p.R + q) (p.R + q'))]
  | .core (.pinc q) => [.core (.pinc (p.R + q))]
  | .core (.pdec q) => [.core (.pdec (p.R + q))]
  | .core (.jle a tg) => [.core (.jle (p.R + a) (lay p Q tg))]
  | .core (.pjle q q' tg) => [.core (.pjle (p.R + q) (p.R + q') (lay p Q tg))]
  | .core .accept => [.halt]
  | .core .reject => [.halt]
  | .pointerAdd d a b => [.pointerAdd (p.R + d) (p.R + a) (p.R + b)]
  | .pointerSub d a b => [.pointerSub (p.R + d) (p.R + a) (p.R + b)]
  | .integerLoad d a => [.pointerAdd p.t (p.R + a) (p.R + a), .core (.pinc p.t),
      .integerLoad (p.R + d) p.t]
  | .integerStore a b => [.pointerAdd p.t (p.R + a) (p.R + a), .core (.pinc p.t),
      .integerStore p.t (p.R + b), .integerStore p.lp p.t, .core (.pdec p.lp), .core (.pdec p.lp)]
  | .pointerReal d a => [.pointerReal (p.R + d) (p.R + a)]
  | .coin d => [.coin (p.R + d)]
  | .deg d _ => [.core (.pset (p.R + d) (-1))]
  | .nbr d _ _ => [.core (.pset (p.R + d) (-1))]
  | .halt => [.core (.pjle p.t p.t p.X)]

/-- The relocated code. -/
def reloc (p : RP) (Q : Program) : List Instr := (Q.map (trI p Q)).flatten

/-- An upper bound on the register indices written by an instruction. -/
def wreg : Instr → ℕ
  | .core (.const d _) => d + 1
  | .core (.add d _ _) => d + 1
  | .core (.sub d _ _) => d + 1
  | .core (.mul d _ _) => d + 1
  | .core (.div d _ _) => d + 1
  | .core (.load d _) => d + 1
  | .core (.pset q _) => q + 1
  | .core (.pcopy q _) => q + 1
  | .core (.pinc q) => q + 1
  | .core (.pdec q) => q + 1
  | .pointerAdd d _ _ => d + 1
  | .pointerSub d _ _ => d + 1
  | .integerLoad d _ => d + 1
  | .pointerReal d _ => d + 1
  | .coin d => d + 1
  | .deg d _ => d + 1
  | .nbr d _ _ => d + 1
  | _ => 0

/-- Registers at index `≥ regBound Q` are never written by `Q`. -/
def regBound (Q : Program) : ℕ := (Q.map wreg).sum

/-- Zero the guest registers `R + r`, `r < B`, then jump to the guest code. -/
def post (p : RP) (B : ℕ) : List Instr :=
  (List.range B).flatMap (fun r => [Instr.core (.const (p.R + r) 0), Instr.core (.pset (p.R + r) 0)]) ++
    [Instr.core (.pjle p.t p.t p.base)]

/-- The cached edge list of a node list: `(v, w)` for `v` in order and `w` in `nbrs v` order. -/
def edgesOf {n : ℕ} (nbrs : Fin n → List (Fin n)) (l : List (Fin n)) : List (Fin n × Fin n) :=
  l.flatMap fun v => (nbrs v).map fun w => (v, w)

section
variable {n : ℕ} (nbrs : Fin n → List (Fin n)) (lst : List (Fin n))
/-- Internal edges (both ends in the list), in cached-edge order. -/
def intern : List (Fin n × Fin n) := (edgesOf nbrs lst).filter fun e => decide (e.2 ∈ lst)

def entPairs : List (ℕ × ℕ) :=
  (List.range lst.length).map (fun i => (i, i)) ++
    (intern nbrs lst).map fun e => (lst.idxOf e.1, lst.idxOf e.2)

def intsT : List ℤ :=
  [(lst.length : ℤ), ((entPairs nbrs lst).length : ℤ)] ++
    (entPairs nbrs lst).flatMap fun p => [(p.1 : ℤ), (p.2 : ℤ)]

def bList (r0 r10 r17 : ℝ) : List ℝ :=
  lst.mapIdx fun i v => (r10 - r17 * ((nbrs v).length : ℝ)) + (if (i : ℤ) ≤ 0 then r0 else 0)

def realsT (μ δ' r9 r0 r10 r17 : ℝ) : List ℝ :=
  [μ, δ'] ++ (lst.map fun v => ((nbrs v).length : ℝ)) ++ (intern nbrs lst).map (fun _ => r9) ++
    bList nbrs lst r0 r10 r17

end

def degSum {n : ℕ} (nbrs : Fin n → List (Fin n)) (l : List (Fin n)) : ℕ :=
  (l.map fun v => (nbrs v).length).sum

/-- Data invariant of the host memory for the node list `l` (positions), with the degree cache
valid on `D`. -/
structure DInv {n : ℕ} (nbrs : Fin n → List (Fin n)) (M : ℤ → ℤ) (l : List (Fin n))
    (D : Fin n → Prop) : Prop where
  lst : ∀ i (hi : i < l.length), M (16 * (i : ℤ) + 6) = ((l[i] : ℕ) : ℤ)
  pos : ∀ i (hi : i < l.length), M (16 * ((l[i] : ℕ) : ℤ) + 2) = i
  eu : ∀ e (he : e < (edgesOf nbrs l).length),
    M (16 * (e : ℤ) + 10) = (((edgesOf nbrs l)[e]).1 : ℕ)
  ew : ∀ e (he : e < (edgesOf nbrs l).length),
    M (16 * (e : ℤ) + 12) = (((edgesOf nbrs l)[e]).2 : ℕ)
  deg : ∀ w, (D w ∨ ∃ u ∈ l, w ∈ nbrs u) → M (16 * ((w : ℕ) : ℤ) + 4) = (nbrs w).length

def rp : RP := ⟨511, 64, 60, 61, 289⟩

noncomputable def postAddr (Q : Program) : ℕ := 511 + (reloc rp Q).length

/-- The real constants held in registers during the main loop. -/
structure RegC (h : State) (α ε δ : ℝ) : Prop where
  r0 : h.core.regs 0 = α
  r1 : h.core.regs 1 = ε
  r2 : h.core.regs 2 = δ
  r6 : h.core.regs 6 = α * (1 / 100) * (ε * ε * α * (1 / 10))
  r7 : h.core.regs 7 = ε * (1 / 2) * δ
  r8 : h.core.regs 8 = 1 - α
  r9 : h.core.regs 9 = 0 - (1 - α)
  r10 : h.core.regs 10 = 0
  r17 : h.core.regs 17 = α * (ε * (1 / 2))
  r21 : h.core.regs 21 = α * ε
  r22 : h.core.regs 22 = α * (ε * (1 / 2) + ε * ε * α * (1 / 10))

/-- Main-loop invariant at pc 68. -/
structure LoopInv {n : ℕ} (nbrs : Fin n → List (Fin n)) (s : Fin n) (α ε δ : ℝ) (B : ℕ)
    (lst TL : List (Fin n)) (h : State) : Prop where
  pc : h.core.pc = 68
  hh : h.halted = false
  p10 : h.core.ptrs 10 = 0
  p9 : h.core.ptrs 9 = TL.length
  p1 : h.core.ptrs 1 = lst.length
  p2 : h.core.ptrs 2 = (edgesOf nbrs lst).length
  p0 : h.core.ptrs 0 = (s : ℕ)
  p61 : h.core.ptrs 61 = -2
  regs : RegC h α ε δ
  nd : (lst ++ TL).Nodup
  head : lst[0]? = some s ∨ (lst = [] ∧ TL = [s])
  dinv : DInv nbrs h.integerMemory lst (fun v => v ∈ lst ∨ v ∈ TL)
  ins : ∀ v : Fin n, h.integerMemory (16 * ((v : ℕ) : ℤ)) = if v ∈ lst ∨ v ∈ TL then 1 else 0
  tl : ∀ t (ht : t < TL.length), h.integerMemory (16 * (t : ℤ) + 8) = ((TL[t] : ℕ) : ℤ)
  oddz : ∀ z : ℤ, h.integerMemory (2 * z + 1) = 0 ∧ h.core.mem (2 * z + 1) = 0
  accz : ∀ v : Fin n, h.core.mem (16 * ((v : ℕ) : ℤ) + 2) = 0
  negz : ∀ a : ℤ, a < 0 → h.core.mem a = 0
  high : ∀ r, 64 + B ≤ r → h.core.regs r = 0 ∧ h.core.ptrs r = 0
  queries : h.queries = 1 + 2 * degSum nbrs lst

section
variable {n : ℕ}
/-- The solver output extended by zero, as a vector on nodes. -/
noncomputable def xtOf (lst : List (Fin n)) (y : ℕ → ℝ) : Fin n → ℝ :=
  fun v => if v ∈ lst then y (lst.idxOf v) else 0

end

/-- The guest input of an iteration, as a list pair, from the registers of the loop-head state. -/
noncomputable def guestInit {n : ℕ} (nbrs : Fin n → List (Fin n)) (lst : List (Fin n)) (h : State) : State :=
  initState (intsT nbrs lst) (realsT nbrs lst (h.core.regs 6) (h.core.regs 7) (h.core.regs 9)
    (h.core.regs 0) (h.core.regs 10) (h.core.regs 17))


end LocalPush.M


