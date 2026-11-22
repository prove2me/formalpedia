-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_GDesc
-- name    : QuantumKtSoI_Supplement_GDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:37:18.365547+00:00
-- url     : https://prove2.me/theorems/f4a58628-3106-45ec-b58a-8bf2f7da3d0e
-- title:
--   $\mathcal G'$-descriptions, their machines $M'(e')$, and the measure $\mathrm{qKt}_{\mathcal G'}$ (Definition 9.3)
-- statement:
--   Given a finite gate set $\mathcal G'$ and an encoding $\ulcorner\cdot\urcorner'$ of the $\mathcal G'$-machines, the set $\mathcal E'$ of **$\mathcal G'$-descriptions** is defined by Definition 3.6 with $\mathrm{BASE}'(A)=000\,\overline{\ulcorner A\urcorner'}$ for every $\mathcal G'$-machine $A$ in place of $\mathrm{BASE}(A)$. The $\mathcal G'$-machine $M'(e')$ is defined by the clauses after Lemma 3.7 with $M'(\mathrm{BASE}'(A))=A$, and $P'_{e'}=P_{M'(e')}$. For strings $x,y$,
--   $$\mathrm{qKt}_{\mathcal G'}(y|x)=\min_{e',t}\{|e'|+\lceil\log t\rceil : e'\in\mathcal E',\ t\ge1,\ P'_{e'}(x;t,y)\ge 2/3\},$$
--   and $\mathrm{qKt}_{\mathcal G'}(y)=\mathrm{qKt}_{\mathcal G'}(y|\epsilon)$. The constructors add only classical steps, and $\mathrm{LIT}(y)$, which has no gate states, makes the minimum finite.
--
--   This is the measure compared with $\mathrm{qKt}$ in Theorems 9.6, D.45, D.47 and D.55.
--
--   **Formalization Note** The machines of $\mathrm{LIT}$, $\mathrm{SEQ}_g$ and $\mathrm{AMP}$ are the published constructions of the base mission applied to $\mathcal G'$-machines, with the same glue routines and the same pinned loading, comparison and copy routines. The minimum is an infimum of a nonempty set of natural numbers and $\lceil\log t\rceil$ is `Nat.clog 2 t`.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 9.3, p.118; Definition 3.6, p.24; constructors, pp.25–26

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_GlueRoutines
import Definitions.Def_QuantumKtSoI_Desc
import Definitions.Def_QuantumKtSoI_Supplement_GCodedMachine

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-- **`G′`-descriptions** (Definition 9.3, p.118 of Myrisiotis, *Failure of Symmetry of Information
for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…): the set `E′`
defined by Definition 3.6 (p.24) with `BASE′(A)` for every `G′`-machine `A` (a valid coded
`G′`-machine) in place of `BASE(A)`; `LIT(d)`, `SEQ_g(e₁, e₂)` and `AMP(r, e)` are unchanged. -/
inductive GDesc (L : GateLib)
  | base (A : {A : GCodedMachine L // A.Valid})
  | lit (d : List Bool)
  | seq (g : Glue) (e₁ e₂ : GDesc L)
  | amp (r : ℕ+) (e : GDesc L)

/-- The binary string of a `G′`-description for the encoding `enc = ⌜·⌝′` (Definition 9.3, p.118;
Definition 3.6, p.24): `BASE′(A) = 000⌜A⌝′‾` (the self-delimiting code of `⌜A⌝′`),
`LIT(d) = 001 d̄`, `SEQ_g(e₁,e₂) = t_g e₁ e₂` with `t_feed = 010`, `t_cat = 011`, `t_pair = 100`,
and `AMP(r,e) = 101 r̄ e`. -/
def GDesc.bits {L : GateLib} (enc : {A : GCodedMachine L // A.Valid} → List Bool) : GDesc L → List Bool
  | .base A => [false, false, false] ++ sd (enc A)
  | .lit d => [false, false, true] ++ sd d
  | .seq .feed e₁ e₂ => [false, true, false] ++ e₁.bits enc ++ e₂.bits enc
  | .seq .cat e₁ e₂ => [false, true, true] ++ e₁.bits enc ++ e₂.bits enc
  | .seq .pair e₁ e₂ => [true, false, false] ++ e₁.bits enc ++ e₂.bits enc
  | .amp r e => [true, false, true] ++ sdNat r ++ e.bits enc

/-! ### `M(LIT(d))` -/

/-- The `G′`-machine `M′(LIT(d))` (p.25; Definition 9.3, p.118), the published `litMachine` as a
`G′`-machine without gate states: only its input tape (`false`) and output tape (`true`);
classical states `q₀, …, q_{|d|}` (`some i`) and one final state `q_fin` (`none`); the only active
tape is the output tape. In `q₀` it writes back the scanned symbol, moves the output head right,
and enters `q₁`, or `q_fin` if `d = ε`; in `qᵢ`, `1 ≤ i ≤ |d|`, it writes `dᵢ` if the scanned
symbol is not `⊢` and writes back `⊢` otherwise, moves right, and enters `q_{i+1}`, or `q_fin` if
`i = |d|`. -/
def gLitMachine (L : GateLib) (d : List Bool) : GMachine L where
  Q := Option (Fin (d.length + 1))
  T := Bool
  kind := fun _ => TapeKind.classical
  alph := fun _ => ioAlph
  inT := false
  outT := true
  companion := id
  init := some 0
  isFinal := fun q => q.isNone
  act := fun _ => {true}
  δ := fun q σ =>
    match q with
    | none => (none, σ, fun _ => Move.N)
    | some i =>
        let nxt : Option (Fin (d.length + 1)) :=
          if h : i.val + 1 ≤ d.length then some ⟨i.val + 1, by omega⟩ else none
        let w : Sym :=
          if i.val = 0 then σ true
          else if σ true = Sym.mark then Sym.mark else Sym.ofBit (d.getD (i.val - 1) false)
        (nxt, fun t => if t then w else σ t, fun t => if t then Move.R else Move.N)
  gdata := fun _ => none
  gnext := id
  gmove := fun _ _ => Move.N

/-! ### `M(SEQ_g(e₁, e₂))` -/

section Seq

variable {L : GateLib} (M₁ M₂ : GMachine L) (α : Routine 2) (β : Routine 3)

/-- Tapes of the composite: its own input and output tapes, a private copy of every tape of `M₁`
except its input tape, a private copy of every tape of `M₂`, and the work tapes of the two glue
routines (p.25). -/
abbrev GSeqT : Type :=
  Unit ⊕ Unit ⊕ {t : M₁.T // t ≠ M₁.inT} ⊕ M₂.T ⊕ Fin α.nWork ⊕ Fin β.nWork

/-- States of the composite: the nonfinal states of `M₁` (phase 1), the states of the `α`
routine (phase 2), the nonfinal states of `M₂` (phase 3), the states of the `β` routine
(phase 4), and the final state. -/
abbrev GSeqQ : Type :=
  {q : M₁.Q // M₁.isFinal q = false} ⊕ α.R ⊕ {q : M₂.Q // M₂.isFinal q = false} ⊕ β.R ⊕ Unit

variable {M₁ M₂ α β}

/-- The composite's own input tape (also the input tape of `M₁`). -/
def GSeqT.inp : GSeqT M₁ M₂ α β := Sum.inl ()
/-- The composite's own output tape. -/
def GSeqT.out : GSeqT M₁ M₂ α β := Sum.inr (Sum.inl ())

variable (M₁ M₂ α β)

/-- The tape of the composite standing for a tape of `M₁`. -/
def gSeqE₁ (t : M₁.T) : GSeqT M₁ M₂ α β :=
  if h : t = M₁.inT then GSeqT.inp else Sum.inr (Sum.inr (Sum.inl ⟨t, h⟩))

/-- The tape of the composite standing for a tape of `M₂`. -/
def gSeqE₂ (t : M₂.T) : GSeqT M₁ M₂ α β := Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))

/-- The tape of `M₁` a tape of the composite stands for, if any. -/
def gSeqP₁ : GSeqT M₁ M₂ α β → Option M₁.T
  | Sum.inl _ => some M₁.inT
  | Sum.inr (Sum.inr (Sum.inl t)) => some t.1
  | _ => none

/-- The tape of `M₂` a tape of the composite stands for, if any. -/
def gSeqP₂ : GSeqT M₁ M₂ α β → Option M₂.T
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => some t
  | _ => none

/-- The tapes of the `α` routine: sources `x` (input tape) and `u` (copy of `M₁`'s output tape),
target the copy of `M₂`'s input tape, and its own work tapes. -/
def gSeqEα : RTape 2 α.nWork → GSeqT M₁ M₂ α β
  | .src i => ![GSeqT.inp, gSeqE₁ M₁ M₂ α β M₁.outT] i
  | .tgt => gSeqE₂ M₁ M₂ α β M₂.inT
  | .wk i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))

/-- The tapes of the `β` routine: sources `x`, `u` and `v` (copy of `M₂`'s output tape), target
the composite's output tape, and its own work tapes. -/
def gSeqEβ : RTape 3 β.nWork → GSeqT M₁ M₂ α β
  | .src i => ![GSeqT.inp, gSeqE₁ M₁ M₂ α β M₁.outT, gSeqE₂ M₁ M₂ α β M₂.outT] i
  | .tgt => GSeqT.out
  | .wk i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))

/-- Kinds of the composite's tapes. -/
def gSeqKind : GSeqT M₁ M₂ α β → TapeKind
  | Sum.inr (Sum.inr (Sum.inl t)) => M₁.kind t.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => M₂.kind t
  | _ => TapeKind.classical

/-- Companions of the composite's tapes: the copy of a qubit tape's companion (p.26). -/
def gSeqCompanion : GSeqT M₁ M₂ α β → GSeqT M₁ M₂ α β
  | Sum.inr (Sum.inr (Sum.inl t)) => gSeqE₁ M₁ M₂ α β (M₁.companion t.1)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => gSeqE₂ M₁ M₂ α β (M₂.companion t)
  | t => t

/-- The state entered when `M₁` would enter `q`: `q` itself if nonfinal, else the start of
phase 2. -/
def gSeqν₁ (q : M₁.Q) : GSeqQ M₁ M₂ α β :=
  if h : M₁.isFinal q = false then Sum.inl ⟨q, h⟩ else Sum.inr (Sum.inl α.start)

/-- The state entered when `M₂` would enter `q`: `q` itself if nonfinal, else the start of
phase 4. -/
def gSeqν₂ (q : M₂.Q) : GSeqQ M₁ M₂ α β :=
  if h : M₂.isFinal q = false then Sum.inr (Sum.inr (Sum.inl ⟨q, h⟩))
  else Sum.inr (Sum.inr (Sum.inr (Sum.inl β.start)))

/-- A step of a component inside a larger machine: the component's transition on the copies of
its tapes (through the embedding `e` with inverse `pre`); other tapes keep their symbols and do
not move; the next state is relabelled by `ν`. -/
def gCompδ {L : GateLib} {T Q : Type} (M : GMachine L) (e : M.T → T) (pre : T → Option M.T) (ν : M.Q → Q)
    (q : M.Q) (σ : T → Sym) : Q × (T → Sym) × (T → Move) :=
  let out := M.δ q (M.mask q (σ ∘ e))
  (ν out.1, fun t => match pre t with | some s => out.2.1 s | none => σ t,
    fun t => match pre t with | some s => out.2.2 s | none => Move.N)

/-- The `G′`-machine `M′(SEQ_g(e₁, e₂))` (p.25; Definition 9.3, p.118), the published `seqMachine`
construction applied to `G′`-machines for components `M₁ = M(e₁)`, `M₂ = M(e₂)` and the glue
routines `α = α_g`, `β = β_g`. Phase 1 runs `M₁` on its copies (sharing the input tape); when
`M₁` would enter a final state, phase 2 runs `α`, which writes `α_g(x,u)` on the copy of `M₂`'s
input tape and returns its heads to cell `0`; then phase 3 runs `M₂` from its initial state;
when `M₂` would enter a final state, phase 4 runs `β`, which writes `β_g(x,u,v)` on the output
tape, and the machine enters its final state. An initially final component takes no steps. -/
def gSeqMachine : GMachine L where
  Q := GSeqQ M₁ M₂ α β
  T := GSeqT M₁ M₂ α β
  kind := gSeqKind M₁ M₂ α β
  alph := fun t =>
    match t with
    | Sum.inr (Sum.inr (Sum.inl t)) => M₁.alph t.1
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl t))) => M₂.alph t
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) => α.walph i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))) => β.walph i
    | _ => ioAlph
  inT := GSeqT.inp
  outT := GSeqT.out
  companion := gSeqCompanion M₁ M₂ α β
  init := gSeqν₁ M₁ M₂ α β M₁.init
  isFinal := fun q => match q with | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => true | _ => false
  act := fun q =>
    match q with
    | Sum.inl q => (M₁.act q.1).image (gSeqE₁ M₁ M₂ α β)
    | Sum.inr (Sum.inl r) => (α.act r).image (gSeqEα M₁ M₂ α β)
    | Sum.inr (Sum.inr (Sum.inl q)) => (M₂.act q.1).image (gSeqE₂ M₁ M₂ α β)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl r))) => (β.act r).image (gSeqEβ M₁ M₂ α β)
    | _ => ∅
  δ := fun q σ =>
    match q with
    | Sum.inl q =>
        gCompδ M₁ (gSeqE₁ M₁ M₂ α β) (gSeqP₁ M₁ M₂ α β) (gSeqν₁ M₁ M₂ α β) q.1 σ
    | Sum.inr (Sum.inl r) =>
        routineδ α (gSeqEα M₁ M₂ α β) (preOf (gSeqEα M₁ M₂ α β))
          (fun t => decide (gSeqKind M₁ M₂ α β t = TapeKind.qubit)) (gSeqCompanion M₁ M₂ α β)
          (fun r' => Sum.inr (Sum.inl r')) (gSeqν₂ M₁ M₂ α β M₂.init) r σ
    | Sum.inr (Sum.inr (Sum.inl q)) =>
        gCompδ M₂ (gSeqE₂ M₁ M₂ α β) (gSeqP₂ M₁ M₂ α β) (gSeqν₂ M₁ M₂ α β) q.1 σ
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl r))) =>
        routineδ β (gSeqEβ M₁ M₂ α β) (preOf (gSeqEβ M₁ M₂ α β))
          (fun t => decide (gSeqKind M₁ M₂ α β t = TapeKind.qubit)) (gSeqCompanion M₁ M₂ α β)
          (fun r' => Sum.inr (Sum.inr (Sum.inr (Sum.inl r'))))
          (Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))) r σ
    | q => (q, σ, fun _ => Move.N)
  gdata := fun q =>
    match q with
    | Sum.inl q => (M₁.gdata q.1).map fun d => ⟨d.1, gSeqE₁ M₁ M₂ α β ∘ d.2⟩
    | Sum.inr (Sum.inr (Sum.inl q)) => (M₂.gdata q.1).map fun d => ⟨d.1, gSeqE₂ M₁ M₂ α β ∘ d.2⟩
    | _ => none
  gnext := fun q =>
    match q with
    | Sum.inl q => gSeqν₁ M₁ M₂ α β (M₁.gnext q.1)
    | Sum.inr (Sum.inr (Sum.inl q)) => gSeqν₂ M₁ M₂ α β (M₂.gnext q.1)
    | q => q
  gmove := fun q t =>
    match q with
    | Sum.inl q => (match gSeqP₁ M₁ M₂ α β t with | some s => M₁.gmove q.1 s | none => Move.N)
    | Sum.inr (Sum.inr (Sum.inl q)) =>
        (match gSeqP₂ M₁ M₂ α β t with | some s => M₂.gmove q.1 s | none => Move.N)
    | _ => Move.N

end Seq

/-! ### `M(AMP(r, e))` -/

/-- The machine with one state, which is initial and final (p.25: "If the initial state of
`M(e)` is final, the initial state of `M(AMP(r,e))` is final"); it halts at deadline `0` with
empty output. -/
def gHaltMachine (L : GateLib) : GMachine L where
  Q := Unit
  T := Bool
  kind := fun _ => TapeKind.classical
  alph := fun _ => ioAlph
  inT := false
  outT := true
  companion := id
  init := ()
  isFinal := fun _ => true
  act := fun _ => ∅
  δ := fun q σ => (q, σ, fun _ => Move.N)
  gdata := fun _ => none
  gnext := id
  gmove := fun _ _ => Move.N

section Amp

variable {L : GateLib} (M : GMachine L) (r : ℕ+)

/-- Tapes of `M(AMP(r, e))`: its own input and output tapes and `r` private copies of all tapes
of `M`, each copy with its own input tape (p.25). -/
abbrev GAmpT : Type := Unit ⊕ Unit ⊕ (Fin r × M.T)

/-- States of `M(AMP(r, e))`:
* `Sum.inl k`, `k ∈ {0, 1, 2}`: the three states of the loading sweep;
* `run (i, cs, H)`: pointer `i`, current states `cs` of the copies, halted set `H`;
* `cmp (i, cs, H, j, count, agree, phase)`: comparison of the output of the halted copy `i` with
  that of copy `j`, phases `0` (return), `1` (scan), `2` (return);
* `copy (i, scanning)`: copying the output of copy `i` to the output tape;
* the final state. -/
abbrev GAmpQ : Type :=
  Fin 3 ⊕ (Fin r × (Fin r → M.Q) × Finset (Fin r)) ⊕
    (Fin r × (Fin r → M.Q) × Finset (Fin r) × Fin r × Fin (r + 1) × Bool × Fin 3) ⊕
    (Fin r × Bool) ⊕ Unit

variable {M r}

/-- The state `run (i, cs, H)`. -/
def gAmpRun (i : Fin r) (cs : Fin r → M.Q) (H : Finset (Fin r)) : GAmpQ M r :=
  Sum.inr (Sum.inl (i, cs, H))

/-- The state `cmp (i, cs, H, j, count, agree, phase)`. -/
def gAmpCmp (i : Fin r) (cs : Fin r → M.Q) (H : Finset (Fin r)) (j : Fin r) (cnt : ℕ)
    (agree : Bool) (ph : Fin 3) : GAmpQ M r :=
  Sum.inr (Sum.inr (Sum.inl (i, cs, H, j, ⟨min cnt r, by omega⟩, agree, ph)))

/-- The state `copy (i, scanning)`. -/
def gAmpCopy (i : Fin r) (scanning : Bool) : GAmpQ M r := Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, scanning))))

/-- The final state. -/
def gAmpFin : GAmpQ M r := Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))

/-- The decision after the comparisons of the newly halted copy `i` (count `cnt` of halted copies
with the output of copy `i`, copy `i` included): copy that output if `cnt > r/2`; otherwise enter
the final state with empty output if every copy has halted; otherwise move the pointer. -/
def gAmpDecide (i : Fin r) (cs : Fin r → M.Q) (H : Finset (Fin r)) (cnt : ℕ) : GAmpQ M r :=
  if (r : ℕ) < 2 * cnt then gAmpCopy i false
  else if H = Finset.univ then gAmpFin
  else gAmpRun (nextPtr i H) cs H

/-- The comparison stage entered for copy `i` with halted set `H`, from the copy `j₀` on: the next
comparison partner in `H \ {i}` at least `j₀` in increasing order, or the decision. -/
def gAmpNextCmp (i : Fin r) (cs : Fin r → M.Q) (H : Finset (Fin r)) (lo : Option (Fin r))
    (cnt : ℕ) : GAmpQ M r :=
  let rest := (H.erase i).filter fun j => match lo with | none => True | some j₀ => j₀ < j
  if h : rest.Nonempty then gAmpCmp i cs H (rest.min' h) cnt true 0
  else gAmpDecide i cs H cnt

/-- The state entered after copy `i` takes a step into the state `q'` (p.25): if `q'` is nonfinal,
the pointer moves to the next running copy; otherwise `i` is added to the halted set and the
comparison routine starts with count `1`. -/
def gAmpAfter (i : Fin r) (cs : Fin r → M.Q) (H : Finset (Fin r)) (q' : M.Q) : GAmpQ M r :=
  let cs' := Function.update cs i q'
  if M.isFinal q' = false then gAmpRun (nextPtr i H) cs' H
  else gAmpNextCmp i cs' (insert i H) none 1

variable (M r)

/-- The copy tapes. -/
def gAmpCp (i : Fin r) (t : M.T) : GAmpT M r := Sum.inr (Sum.inr (i, t))

/-- The tape of a copy a tape stands for. -/
def gAmpPre : GAmpT M r → Option (Fin r × M.T)
  | Sum.inr (Sum.inr p) => some p
  | _ => none

/-- A routine move `d` given to the classical tapes selected by `sel`, extended to every qubit copy
tape whose companion (in its copy) is selected (p.25: "Whenever the loading or comparison routine
moves a classical head, it gives the same move to every qubit head having that tape as its
companion"). -/
def gAmpMoves (d : GAmpT M r → Move) : GAmpT M r → Move
  | Sum.inr (Sum.inr (i, t)) =>
      if M.kind t = TapeKind.qubit then d (gAmpCp M r i (M.companion t)) else d (gAmpCp M r i t)
  | t => d t

/-- The input tape. -/
def gAmpIn : GAmpT M r := Sum.inl ()
/-- The output tape. -/
def gAmpOut : GAmpT M r := Sum.inr (Sum.inl ())

/-- The transition of a classical state of `M(AMP(r,e))` that is not a copy step. -/
def gAmpRoutineδ (q : GAmpQ M r) (σ : GAmpT M r → Sym) :
    GAmpQ M r × (GAmpT M r → Sym) × (GAmpT M r → Move) :=
  let isLoad : GAmpT M r → Prop := fun t =>
    t = gAmpIn M r ∨ ∃ i, t = gAmpCp M r i M.inT
  let allMove : Move → GAmpT M r → Move := fun d t => if isLoad t then d else Move.N
  match q with
  | Sum.inl k =>
      if k = 0 then (Sum.inl 1, σ, gAmpMoves M r (allMove Move.R))
      else if k = 1 then
        (if Sym.isBit (σ (gAmpIn M r)) then
          (Sum.inl 1, fun t => if t = gAmpIn M r then σ t else σ (gAmpIn M r),
            gAmpMoves M r (allMove Move.R))
        else (Sum.inl 2, σ, gAmpMoves M r (allMove Move.L)))
      else
        (if σ (gAmpIn M r) = Sym.mark then (gAmpRun ⟨0, r.pos⟩ (fun _ => M.init) ∅, σ, fun _ => Move.N)
        else (Sum.inl 2, σ, gAmpMoves M r (allMove Move.L)))
  | Sum.inr (Sum.inr (Sum.inl (i, cs, H, j, cnt, agree, ph))) =>
      let ti := gAmpCp M r i M.outT
      let tj := gAmpCp M r j M.outT
      let a := σ ti
      let b := σ tj
      let back : GAmpT M r → Move := fun t =>
        if (t = ti ∧ a ≠ Sym.mark) ∨ (t = tj ∧ b ≠ Sym.mark) then Move.L else Move.N
      let both : Move → GAmpT M r → Move := fun d t => if t = ti ∨ t = tj then d else Move.N
      if ph = 0 then
        (if a = Sym.mark ∧ b = Sym.mark then
          (gAmpCmp i cs H j cnt true 1, σ, gAmpMoves M r (both Move.R))
        else (gAmpCmp i cs H j cnt agree 0, σ, gAmpMoves M r back))
      else if ph = 1 then
        (if Sym.isBit a ∧ Sym.isBit b then
          (gAmpCmp i cs H j cnt (agree && decide (a = b)) 1, σ, gAmpMoves M r (both Move.R))
        else
          (gAmpCmp i cs H j (cnt + if agree ∧ ¬ Sym.isBit a ∧ ¬ Sym.isBit b then 1 else 0) agree 2,
            σ, gAmpMoves M r (both Move.L)))
      else
        (if a = Sym.mark ∧ b = Sym.mark then (gAmpNextCmp i cs H (some j) cnt, σ, fun _ => Move.N)
        else (gAmpCmp i cs H j cnt agree 2, σ, gAmpMoves M r back))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, scanning)))) =>
      let ti := gAmpCp M r i M.outT
      let a := σ ti
      if scanning = false then
        (if a = Sym.mark then
          (gAmpCopy i true, σ,
            gAmpMoves M r fun t => if t = ti ∨ t = gAmpOut M r then Move.R else Move.N)
        else (gAmpCopy i false, σ, gAmpMoves M r fun t => if t = ti then Move.L else Move.N))
      else
        (if Sym.isBit a then
          (gAmpCopy i true, fun t => if t = gAmpOut M r then a else σ t,
            gAmpMoves M r fun t => if t = ti ∨ t = gAmpOut M r then Move.R else Move.N)
        else (gAmpFin, σ, fun _ => Move.N))
  | q => (q, σ, fun _ => Move.N)

/-- The `G′`-machine `M′(AMP(r, e))` for `M = M′(e)` with nonfinal initial state (pp.25–26, p.29;
Definition 9.3, p.118), the published `ampCore` construction applied to a `G′`-machine.

* **Loading** (`2|x| + 3` steps, p.29): at cell `0` write back and move the input head and the `r`
  copy input heads right; while the input tape scans a bit `s`, write `s` on every copy input tape
  and move all right; at the first non-bit move all left; move all left until the input tape
  scans `⊢`, then enter `run (1, init, ∅)` without moving.
* **Round robin**: in `run (i, cs, H)` the machine performs one step of copy `i` (its kind, gate
  and active tapes are those of `cs i` on copy `i`'s tapes); if copy `i` enters a nonfinal state
  the pointer moves to the next index after `i`, cyclically, not in `H`.
* **Comparison** (pp.25–26): when copy `i` halts, `i` is added to `H`, the count is set to `1`,
  and for each `j ∈ H \ {i}` in increasing order the two output heads return to cell `0`, move
  right together until one of them scans, from cell `1` on, a symbol outside `{0,1}` (adding `1`
  to the count if both do so at the same cell and all earlier scanned pairs agreed), and return to
  cell `0`. If the count exceeds `r/2` the machine copies the output of copy `i` to its own output
  tape and enters its final state; otherwise, if `H = [r]` it enters its final state with empty
  output; otherwise the pointer moves to the next index not in `H`. Pointer moves and decisions are
  made by the transition that ends the step of copy `i` or the comparison.

Every routine move of a copy's classical head is given to the qubit heads having that tape as
their companion.

**Formalization Note** The paper fixes the loading, comparison and copy routines only by this
behaviour ("We fix these routines once and for all", p.26); the formalization pins them as above:
the two comparison heads return simultaneously, and the copy routine returns copy `i`'s output
head and then copies in one sweep. The copies are indexed `0, …, r−1` and the pointer starts at
`0`. The counts live in the finite control, so there are no work tapes. -/
def gAmpCore : GMachine L where
  Q := GAmpQ M r
  T := GAmpT M r
  kind := fun t => match t with | Sum.inr (Sum.inr (_, t)) => M.kind t | _ => TapeKind.classical
  alph := fun t => match t with | Sum.inr (Sum.inr (_, t)) => M.alph t | _ => ioAlph
  inT := gAmpIn M r
  outT := gAmpOut M r
  companion := fun t =>
    match t with | Sum.inr (Sum.inr (i, t)) => gAmpCp M r i (M.companion t) | t => t
  init := Sum.inl 0
  isFinal := fun q => match q with | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => true | _ => false
  act := fun q =>
    match q with
    | Sum.inl _ => insert (gAmpIn M r) (Finset.univ.image fun i => gAmpCp M r i M.inT)
    | Sum.inr (Sum.inl (i, cs, _)) =>
        if M.isFinal (cs i) then ∅ else (M.act (cs i)).image (gAmpCp M r i)
    | Sum.inr (Sum.inr (Sum.inl (i, _, _, j, _, _, _))) => {gAmpCp M r i M.outT, gAmpCp M r j M.outT}
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, _)))) => {gAmpCp M r i M.outT, gAmpOut M r}
    | _ => ∅
  δ := fun q σ =>
    match q with
    | Sum.inr (Sum.inl (i, cs, H)) =>
        if M.isFinal (cs i) then (gAmpFin, σ, fun _ => Move.N)
        else gCompδ M (gAmpCp M r i)
          (fun t => match gAmpPre M r t with | some (j, s) => if j = i then some s else none | none => none)
          (gAmpAfter i cs H) (cs i) σ
    | q => gAmpRoutineδ M r q σ
  gdata := fun q =>
    match q with
    | Sum.inr (Sum.inl (i, cs, _)) =>
        if M.isFinal (cs i) then none
        else (M.gdata (cs i)).map fun d => ⟨d.1, gAmpCp M r i ∘ d.2⟩
    | _ => none
  gnext := fun q =>
    match q with
    | Sum.inr (Sum.inl (i, cs, H)) => gAmpAfter i cs H (M.gnext (cs i))
    | q => q
  gmove := fun q t =>
    match q with
    | Sum.inr (Sum.inl (i, cs, _)) =>
        (match gAmpPre M r t with
          | some (j, s) => if j = i then M.gmove (cs i) s else Move.N
          | none => Move.N)
    | _ => Move.N

/-- The machine `M(AMP(r, e))` for `M = M(e)`: the one-state halting machine when the initial state
of `M` is final, and `gAmpCore M r` otherwise (p.25). -/
def gAmpMachine : GMachine L :=
  if M.isFinal M.init then gHaltMachine L else gAmpCore M r

end Amp

/-- The `G′`-machine `M′(e′)` of a `G′`-description (Definition 9.3, p.118), for the glue routines
`G`: `M′(BASE′(A)) = A`, and the clauses after Lemma 3.7 (p.25) for `LIT`, `SEQ` and `AMP`. -/
def GDesc.machine {L : GateLib} (G : GlueRoutines) : GDesc L → GMachine L
  | .base A => A.1.toMachine
  | .lit d => gLitMachine L d
  | .seq g e₁ e₂ => gSeqMachine (e₁.machine G) (e₂.machine G) (G.α g) (G.β g)
  | .amp r e => gAmpMachine (e.machine G) r

/-- `P′_{e′}(x; t, w) = P_{M′(e′)}(x; t, w)` (Definition 9.3, p.118). -/
def GDesc.prob {L : GateLib} (G : GlueRoutines) (e : GDesc L) (x : List Bool) (t : ℕ) (w : List Bool) : ℝ :=
  (e.machine G).outputProb x t w

/-- **Definition 9.3** (p.118), the measure over another gate set:
`qKt_{G′}(y | x) = min_{e′,t} { |e′| + ⌈log t⌉ : e′ ∈ E′, t ≥ 1, P′_{e′}(x; t, y) ≥ 2/3 }`, for the gate
set `L`, the encoding `enc` of the `G′`-machines and the glue routines `G`;
`qKt_{G′}(y) = qKt_{G′}(y | ε)` is `qKtG L enc G y []`.

**Formalization Note** As for the published `qKt`: the minimum is the `sInf` of a set of natural
numbers that is nonempty because `LIT(y)`, which has no gate states, is feasible (p.118);
`⌈log t⌉` is `Nat.clog 2 t`; descriptions are charged `|bits|`. -/
def qKtG (L : GateLib) (enc : {A : GCodedMachine L // A.Valid} → List Bool) (G : GlueRoutines)
    (y x : List Bool) : ℕ :=
  sInf {n : ℕ | ∃ e : GDesc L, ∃ t : ℕ, 1 ≤ t ∧ (2 / 3 : ℝ) ≤ e.prob G x t y ∧
    n = (e.bits enc).length + Nat.clog 2 t}

end QuantumKtSoI.Supplement


