-- Prove2me | Definitions.Def_ParallelLpSCO_EpochDA_Machine
-- name    : ParallelLpSCO_EpochDA_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:04:31.73149+00:00
-- url     : https://prove2.me/theorems/4f12540b-876b-4d58-aef8-014ff7e68abf
-- title:
--   Parallel stochastic first-order algorithms: the machine, its run on random tapes, and its four costs (query depth, total queries, computational depth, work)
-- statement:
--   The paper measures an algorithm by its **query depth** (number of parallel rounds of oracle queries), **total queries**, and the **computational depth** and **work** of everything else, "assuming that each oracle query has $O(1)$ depth" (§1.2, p. 4), with each update and vector operation of constant depth (p. 64) and work multiplied by $d$ (Theorem 14). It does not formalize its machine; this definition pins one.
--
--   A **program** is a finite list of instructions acting on real scalar registers $s_0,s_1,\dots$ and vector registers $v_0,v_1,\dots\in\mathbb R^d$. The input $(d,L,R,\varepsilon)$ is in $s_0,\dots,s_3$, everything else is $0$, and the output is $v_0$ at halting. Addresses are expressions in the registers ($\lfloor s_k\rfloor$) and the lane index, so batches can have data-dependent sizes.
--
--   - `par n op` — one parallel computation step: the primitive `op` runs in $n$ lanes reading the memory before the step. It adds $1$ to the computational depth and $n\cdot\mathrm{cost}(op)$ to the work, with cost $d$ for vector primitives and $1$ for scalar ones.
--   - `jumpPos c t` — conditional jump (depth $1$, work $1$).
--   - `query n pt dst` — one **oracle round**: lane $i<n$ queries the oracle at $v_{pt(i)}$ with a fresh independent draw and stores the answer. It adds $1$ to the query depth and $n$ to the total queries.
--   - `halt`.
--
--   The **primitives** use only numbers in memory and fresh random draws:
--   - real arithmetic, comparison, $\exp$, $\log$, $\lfloor\cdot\rfloor$, $|\cdot|$, real powers;
--   - uniform draws and $GG_p(0,\sigma^2)$ vector draws;
--   - vector addition and scaling, $\|\cdot\|_p$, dot products, $J_p$;
--   - the positive root $a$ of $(A+a)^{p-1}=c\,a^p$;
--   - the ℓp proximal map $\operatorname{argmin}_{x\in K}\{\langle w,x\rangle+\frac ap\|x-u\|_p^p+\frac bp\|x-z\|_p^p\}$ with $K=B_p(c,\rho)$ or $\mathbb R^d$. This is the "Bregman proximal update" of Algorithm 9 line 11 and the mirror step of Algorithm 6.
--
--   No primitive can read $f$, its values, its subgradients or the oracle's law. A **run** is driven by three tapes: uniform draws, standard $GG_p(0,1)$ vectors, and the uniform draws fed to the oracle. `run p A g tp L R ε n` is the state after $n$ steps; `output` is $v_0$ at the first halting step. `IsTapeLaw p P T` says the tape cells $(u_n,z_n,e_n)$ are independent across $n$ with law $\mathrm{Unif}[0,1]\otimes GG_p(0,1)\otimes\mathrm{Unif}[0,1]$.
--
--   **Formalization Note.** The counters `rounds`, `queries`, `depth`, `work` are natural numbers that stop changing once the run halts. A program counter outside the program halts. `log 0 = 0` and division by $0$ is $0$ (Lean conventions of the primitives). The proximal map and the root are Hilbert-ε choices of a minimizer / positive root, unique whenever the paper uses them. Real literals are allowed.
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), p. 4 (§1.2), p. 47 (§4.1), p. 61 (Algorithm 9), p. 64 (proof of Proposition 13), p. 65 (Theorem 14)

import Mathlib
import Definitions.Def_ParallelLpSCO_EpochDA_Basics

open MeasureTheory

/-!
# Parallel stochastic first-order algorithms and their four costs

Nie, Shyam, Bullins, *Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in
ℓp Geometries*, STOC 2027 submission (manuscript, sha256 fe68639b…), §1.2 p. 4, §4.1 p. 47,
proof of Proposition 13 p. 64.

"We assume a setting where multiple queries can be submitted simultaneously. Along with the query
depth, we also compute the computational depth and total number of queries … the computational
depth measures the parallel depth of the algorithm, assuming that each oracle query has O(1)
depth, and the total number of queries refers to the total number of queries made to the
stochastic gradient oracle over all rounds." The paper does not formalize its machine; this file
pins one.

A program (fixed in advance, for a fixed exponent `p`) is a finite list of instructions run on a
memory of real scalar registers `s : ℕ → ℝ` and vector registers `v : ℕ → ℝ^d`. The input
`(d, L, R, ε)` is placed in `s 0, s 1, s 2, s 3`; all other registers are `0`. The output is
`v 0` when the program halts. Instructions:

* `par n op`: one parallel computation step; the primitive `op` is executed in `n` lanes
  `i = 0, …, n − 1` (`n` is computed from the registers), every lane reading the memory as it was
  before the step, writes applied in lane order. Counts `1` toward the computational depth and
  `n · cost(op)` toward the work, where `cost` is `d` for a vector primitive and `1` for a
  scalar one.
* `jumpPos c t`: go to instruction `t` if `s[c] > 0`, else to the next one (depth `1`, work `1`).
* `query n pt dst`: one oracle round: lane `i < n` queries the oracle at `v[pt(i)]` with a fresh
  independent draw and stores the answer in `v[dst(i)]`. Counts `1` toward the query depth and
  `n` toward the total queries.
* `halt`.

The primitives involve nothing but numbers already in memory and fresh random draws (uniform
on `[0, 1]`, and `GG_p(0, σ²)` vectors): real arithmetic, comparison, `exp`, `log`, `⌊·⌋`,
`|·|`, real powers, vector addition and scaling, `‖·‖_p`, dot products, `J_p`, the positive root
`a` of `(A + a)^{p−1} = c a^p` (Algorithm 6 line 4), and the ℓp proximal map
`argmin_{x ∈ K} {⟨w, x⟩ + (a/p)‖x − u‖_p^p + (b/p)‖x − z‖_p^p}` with `K = B_p(c, ρ)` or `ℝ^d`
(the "Bregman proximal update" of Algorithm 9 line 11 and the mirror update of Algorithm 6
line 9). None of them can read `f` or the oracle.

A run is driven by three tapes: uniform draws, standard `GG_p(0, 1)` vectors (a `GG_p(0, σ²)`
vector is `σ` times one), and the uniform draws feeding the oracle. A pc outside the program
halts.
-/

namespace ParallelLpSCO.EpochDA

/-- Address expressions, evaluated from the scalar registers and the lane index `i`. -/
inductive AddrExp where
  /-- A literal address. -/
  | lit (n : ℕ)
  /-- `⌊s[k]⌋₊`. -/
  | reg (k : ℕ)
  /-- The lane index `i`. -/
  | idx
  | add (a b : AddrExp)
  | mul (a b : AddrExp)
  | div (a b : AddrExp)
  | mod (a b : AddrExp)

/-- Value of an address expression. -/
noncomputable def AddrExp.eval (s : ℕ → ℝ) (i : ℕ) : AddrExp → ℕ
  | .lit n => n
  | .reg k => ⌊s k⌋₊
  | .idx => i
  | .add a b => a.eval s i + b.eval s i
  | .mul a b => a.eval s i * b.eval s i
  | .div a b => a.eval s i / b.eval s i
  | .mod a b => a.eval s i % b.eval s i

/-- Binary scalar operations; `lt` gives `1` if `a < b` and `0` otherwise. -/
inductive SBin where
  | add | sub | mul | div | rpow | max | min | lt

/-- Unary scalar operations. -/
inductive SUn where
  | neg | exp | log | floor | abs

/-- Primitive operations (one per lane). Destinations and operands are address expressions. -/
inductive Op where
  /-- `s[dst] := c`. -/
  | sconst (dst : AddrExp) (c : ℝ)
  /-- `s[dst] := i` (the lane index). -/
  | sindex (dst : AddrExp)
  | sbin (o : SBin) (dst a b : AddrExp)
  | sun (o : SUn) (dst a : AddrExp)
  /-- `s[dst] :=` a positive root `a` of `(s[A] + a)^{p−1} = s[c] · a^p`. -/
  | sroot (dst A c : AddrExp)
  /-- `s[dst] :=` the next uniform draw. -/
  | sunif (dst : AddrExp)
  | vzero (dst : AddrExp)
  | vcopy (dst a : AddrExp)
  | vadd (dst a b : AddrExp)
  | vsub (dst a b : AddrExp)
  /-- `v[dst] := s[c] · v[a]`. -/
  | vsmul (dst c a : AddrExp)
  /-- `s[dst] := ‖v[a]‖_p`. -/
  | vnorm (dst a : AddrExp)
  /-- `s[dst] := ⟨v[a], v[b]⟩`. -/
  | vdot (dst a b : AddrExp)
  /-- `v[dst] := J_p(v[a])`. -/
  | vJp (dst a : AddrExp)
  /-- `v[dst] := s[σ] ·` the next standard `GG_p(0, 1)` vector, i.e. a `GG_p(0, s[σ]²)` draw. -/
  | vgg (dst σ : AddrExp)
  /-- `v[dst] :=` the ℓp proximal map with linear term `v[w]`, weights `s[a]`, `s[b]`, centres
  `v[u]`, `v[z]`, over `B_p(v[c], s[ρ])` if `ball` and over `ℝ^d` otherwise. -/
  | vprox (dst w u z c a b ρ : AddrExp) (ball : Bool)

/-- Whether a primitive acts on vectors (cost `d`) or scalars (cost `1`). -/
def Op.isVector : Op → Bool
  | .vzero .. | .vcopy .. | .vadd .. | .vsub .. | .vsmul .. | .vnorm .. | .vdot .. | .vJp ..
  | .vgg .. | .vprox .. => true
  | _ => false

/-- Instructions. -/
inductive Instr where
  | par (count : AddrExp) (op : Op)
  | jumpPos (cond : AddrExp) (target : ℕ)
  | query (count pt dst : AddrExp)
  | halt

/-- A program. -/
abbrev Program := List Instr

/-- The random tapes of a run: uniform draws, standard `GG_p(0, 1)` vectors, and the uniform
draws that feed the oracle (one per query). -/
structure Tapes (d : ℕ) where
  u : ℕ → unitInterval
  z : ℕ → Vec d
  e : ℕ → unitInterval

/-- Machine state: program counter, memory, tape cursors, halted flag and the four counters. -/
structure State (d : ℕ) where
  pc : ℕ
  s : ℕ → ℝ
  v : ℕ → Vec d
  uCur : ℕ
  zCur : ℕ
  eCur : ℕ
  halted : Bool
  rounds : ℕ
  queries : ℕ
  depth : ℕ
  work : ℕ

/-- The initial state on input `(d, L, R, ε)`. -/
def initState (d : ℕ) (L R ε : ℝ) : State d where
  pc := 0
  s := fun k => if k = 0 then (d : ℝ) else if k = 1 then L else if k = 2 then R
    else if k = 3 then ε else 0
  v := fun _ => 0
  uCur := 0
  zCur := 0
  eCur := 0
  halted := false
  rounds := 0
  queries := 0
  depth := 0
  work := 0

/-- The objective of the proximal primitive: `⟨w, x⟩ + (a/p)‖x − u‖_p^p + (b/p)‖x − z‖_p^p`. -/
noncomputable def proxObjective {d : ℕ} (p : ℝ) (w u z : Vec d) (a b : ℝ) (x : Vec d) : ℝ :=
  ∑ i, w i * x i + a / p * lpNorm p (x - u) ^ p + b / p * lpNorm p (x - z) ^ p

/-- The proximal primitive: a minimizer of `proxObjective` over `B_p(c, ρ)` (if `ball`) or over
`ℝ^d` (it is unique when `a + b > 0`; an arbitrary point when no minimizer exists). -/
noncomputable def proxMap {d : ℕ} (p : ℝ) (w u z c : Vec d) (a b ρ : ℝ) (ball : Bool) : Vec d :=
  Classical.epsilon fun x =>
    (ball = true → x ∈ lpBall p c ρ) ∧
      ∀ y, (ball = true → y ∈ lpBall p c ρ) →
        proxObjective p w u z a b x ≤ proxObjective p w u z a b y

/-- A positive root `a` of `(A + a)^{p−1} = c a^p` (an arbitrary real when there is none). -/
noncomputable def posRoot (p A c : ℝ) : ℝ :=
  Classical.epsilon fun a : ℝ => 0 < a ∧ (A + a) ^ (p - 1) = c * a ^ p

/-- A write produced by one lane. -/
inductive Write (d : ℕ) where
  | sc (a : ℕ) (x : ℝ)
  | vc (a : ℕ) (x : Vec d)

/-- Apply a write to the memory of a state. -/
def Write.apply {d : ℕ} (st : State d) : Write d → State d
  | .sc a x => { st with s := Function.update st.s a x }
  | .vc a x => { st with v := Function.update st.v a x }

/-- Binary scalar operation. -/
noncomputable def SBin.eval : SBin → ℝ → ℝ → ℝ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y
  | .rpow, x, y => x ^ y
  | .max, x, y => Max.max x y
  | .min, x, y => Min.min x y
  | .lt, x, y => if x < y then 1 else 0

/-- Unary scalar operation. -/
noncomputable def SUn.eval : SUn → ℝ → ℝ
  | .neg, x => -x
  | .exp, x => Real.exp x
  | .log, x => Real.log x
  | .floor, x => (⌊x⌋ : ℝ)
  | .abs, x => |x|

/-- The write of lane `i` of a primitive, reading the pre-step state `st`. -/
noncomputable def Op.lane {d : ℕ} (p : ℝ) (tp : Tapes d) (st : State d) (i : ℕ) :
    Op → Write d
  | .sconst dst c => .sc (dst.eval st.s i) c
  | .sindex dst => .sc (dst.eval st.s i) (i : ℝ)
  | .sbin o dst a b => .sc (dst.eval st.s i) (o.eval (st.s (a.eval st.s i)) (st.s (b.eval st.s i)))
  | .sun o dst a => .sc (dst.eval st.s i) (o.eval (st.s (a.eval st.s i)))
  | .sroot dst A c => .sc (dst.eval st.s i) (posRoot p (st.s (A.eval st.s i)) (st.s (c.eval st.s i)))
  | .sunif dst => .sc (dst.eval st.s i) ((tp.u (st.uCur + i) : ℝ))
  | .vzero dst => .vc (dst.eval st.s i) 0
  | .vcopy dst a => .vc (dst.eval st.s i) (st.v (a.eval st.s i))
  | .vadd dst a b => .vc (dst.eval st.s i) (st.v (a.eval st.s i) + st.v (b.eval st.s i))
  | .vsub dst a b => .vc (dst.eval st.s i) (st.v (a.eval st.s i) - st.v (b.eval st.s i))
  | .vsmul dst c a => .vc (dst.eval st.s i) (st.s (c.eval st.s i) • st.v (a.eval st.s i))
  | .vnorm dst a => .sc (dst.eval st.s i) (lpNorm p (st.v (a.eval st.s i)))
  | .vdot dst a b => .sc (dst.eval st.s i) (∑ j, st.v (a.eval st.s i) j * st.v (b.eval st.s i) j)
  | .vJp dst a => .vc (dst.eval st.s i) (Jp p (st.v (a.eval st.s i)))
  | .vgg dst σ => .vc (dst.eval st.s i) (st.s (σ.eval st.s i) • tp.z (st.zCur + i))
  | .vprox dst w u z c a b ρ ball =>
      .vc (dst.eval st.s i)
        (proxMap p (st.v (w.eval st.s i)) (st.v (u.eval st.s i)) (st.v (z.eval st.s i))
          (st.v (c.eval st.s i)) (st.s (a.eval st.s i)) (st.s (b.eval st.s i))
          (st.s (ρ.eval st.s i)) ball)

/-- Whether a primitive consumes uniform draws / `GG_p` draws (one per lane). -/
def Op.drawsU : Op → Bool
  | .sunif _ => true
  | _ => false

/-- See `Op.drawsU`. -/
def Op.drawsZ : Op → Bool
  | .vgg .. => true
  | _ => false

/-- One step of program `A` against oracle `g`, with tapes `tp` (exponent `p`). -/
noncomputable def step {d : ℕ} (p : ℝ) (A : Program) (g : Oracle d) (tp : Tapes d)
    (st : State d) : State d :=
  if st.halted then st else
  match A[st.pc]? with
  | none => { st with halted := true }
  | some .halt => { st with halted := true }
  | some (.jumpPos c t) =>
      { st with pc := if 0 < st.s (c.eval st.s 0) then t else st.pc + 1,
                depth := st.depth + 1, work := st.work + 1 }
  | some (.par count op) =>
      let n := count.eval st.s 0
      let st' := (List.range n).foldl (fun acc i => (op.lane p tp st i).apply acc) st
      { st' with pc := st.pc + 1,
                 uCur := if op.drawsU then st.uCur + n else st.uCur,
                 zCur := if op.drawsZ then st.zCur + n else st.zCur,
                 depth := st.depth + 1,
                 work := st.work + n * (if op.isVector then d else 1) }
  | some (.query count pt dst) =>
      let n := count.eval st.s 0
      let st' := (List.range n).foldl
        (fun acc i => (Write.vc (dst.eval st.s i)
          (g (st.v (pt.eval st.s i)) (tp.e (st.eCur + i)))).apply acc) st
      { st' with pc := st.pc + 1, eCur := st.eCur + n,
                 rounds := st.rounds + 1, queries := st.queries + n }

/-- The state after `n` steps of the run on input `(d, L, R, ε)`. -/
noncomputable def run {d : ℕ} (p : ℝ) (A : Program) (g : Oracle d) (tp : Tapes d)
    (L R ε : ℝ) (n : ℕ) : State d :=
  (step p A g tp)^[n] (initState d L R ε)

open Classical in
/-- The output `v 0` of a halting run (`0` if the run never halts). -/
noncomputable def output {d : ℕ} (p : ℝ) (A : Program) (g : Oracle d) (tp : Tapes d)
    (L R ε : ℝ) : Vec d :=
  if h : ∃ n, (run p A g tp L R ε n).halted = true then
    (run p A g tp L R ε (Nat.find h)).v 0
  else 0

/-- One cell of the tapes. -/
def Tapes.cell {d : ℕ} (tp : Tapes d) (n : ℕ) : unitInterval × Vec d × unitInterval :=
  (tp.u n, tp.z n, tp.e n)

/-- The law of the random tapes `T : Ω → Tapes d` on `(Ω, P)`: the cells
`(u_n, z_n, e_n)` are measurable, independent across `n`, and each has law
`Unif[0, 1] ⊗ GG_p(0, 1) ⊗ Unif[0, 1]`. -/
def IsTapeLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (p : ℝ) (P : Measure Ω)
    (T : Ω → Tapes d) : Prop :=
  (∀ n, Measurable fun ω => (T ω).cell n) ∧
    ProbabilityTheory.iIndepFun (fun n ω => (T ω).cell n) P ∧
    ∀ n, P.map (fun ω => (T ω).cell n) =
      (volume : Measure unitInterval).prod ((ggLaw d p 1).prod (volume : Measure unitInterval))

end ParallelLpSCO.EpochDA


