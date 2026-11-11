-- Prove2me | Definitions.Def_DistLTLSynth_Char_CounterFormula
-- name    : DistLTLSynth_Char_CounterFormula
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:16:45.787235+00:00
-- url     : https://prove2.me/theorems/455d6b29-dc8f-40e6-a7a8-038963b6cea4
-- title:
--   The 1-counter encoding: output tuples (q, zero, plan, carry, pos) and the safety formula ϕ(M_counter) of Eq. (31)
-- statement:
--   For a 1-counter machine with finite state set $Q$, inputs are singletons and both processes output tuples $(q,\mathit{zero},\mathit{plan},\mathit{carry},\mathit{pos})$ with $q\in Q$, $\mathit{zero}\in\{\top,\bot\}$, $\mathit{plan}=(w,a_0,a_1,a_2)\in\{0,1\}^4$, $\mathit{carry}\in\{0,\dots,8\}$, $\mathit{pos}\in\mathbb Z_3$. Finite-valued arithmetic constraints on outputs are finite disjunctions of conjunctions of atoms (p. 21–22). The formula is
--   $$\varphi(M_{\mathrm{counter}}) := \mathrm{PosOrd}\wedge\mathrm{PathAgr}\wedge\mathrm{LocalSum}\wedge\mathrm{ZeroCheck}\wedge\mathrm{InitCheck}\wedge\mathrm{PropTrans}\wedge G\Big(\bigwedge_{q\in F} q_1\neq q\Big)$$
--   with $\mathrm{ChildPos}_g$ (Eq. 2), $\varphi(u,v,g)$ and PosOrd (Eqs. 3–4), OneIsLeft (p. 10), PathAgr (p. 21), $m(q,z)\in\{1,3,9\}$ for increment / decrement at zero / decrement at nonzero (table p. 21), $\psi_p$ and LocalSum (Eqs. 20–21), ZeroInd, LeftMost, RightMost, ZeroCheck (Eqs. 22–25), InitCheck (Eq. 26), $D(\ell_1,g)$ (Eq. 27), StateTrans, WeightTrans, PropTrans (Eqs. 28–30), each transcribed term by term; $\mathrm{next}(q,z)$ is the $\Delta$-successor of $q$ given the zero status $z$.
--
--   **Formalization Note.** $\top$ is `true`. $m(q,z)$ and $\mathrm{next}(q,z)$ are undefined in the paper for $q\in F$; here they are read off the (unused) instruction stored at $q$, a fixed convention that a realizer never meets because no halting state is ever output. Big conjunctions/disjunctions over finite sets use an (irrelevant) enumeration order.
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), pp. 9–11 (PDF 10–12), §3.2; pp. 20–24 (PDF 21–25), Eqs. (2)–(31)

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_CounterMachine

namespace DistLTLSynth.Char

open Classical

noncomputable section

/-- The output set of the 1-counter encoding (§3.2, p. 9): tuples
`(q, zero, plan, carry, pos)` with `q ∈ Q`, `zero ∈ {⊤, ⊥}` (`true` is `⊤`),
`plan = (w, a₀, a₁, a₂) ∈ {0,1}⁴`, `carry ∈ {0, …, 8}`, `pos ∈ Z₃ = {0, 1, 2}`. -/
abbrev CtrOut (Q : Type) : Type := Q × Bool × (Fin 2 × Fin 2 × Fin 2 × Fin 2) × Fin 9 × Fin 3

/-- Formulas of the reduction: singleton inputs, outputs `CtrOut Q` for both processes. -/
abbrev CtrFormula (Q : Type) : Type := Formula Unit Unit (CtrOut Q) (CtrOut Q)

namespace Ctr

variable {Q : Type} [Fintype Q]

/-- Component projections of an output tuple. -/
def oq (y : CtrOut Q) : Q := y.1
def ozero (y : CtrOut Q) : Bool := y.2.1
def ow (y : CtrOut Q) : Fin 2 := y.2.2.1.1
def oa (k : Fin 3) (y : CtrOut Q) : Fin 2 :=
  match k with
  | 0 => y.2.2.1.2.1
  | 1 => y.2.2.1.2.2.1
  | 2 => y.2.2.1.2.2.2
def ocarry (y : CtrOut Q) : Fin 9 := y.2.2.2.1
def opos (y : CtrOut Q) : Fin 3 := y.2.2.2.2

/-- A finite-valued constraint on process 1's output, as the disjunction of the atoms
`(out₁ = y)` over the outputs `y` satisfying it (p. 21–22). -/
def atom1 (P : CtrOut Q → Prop) : CtrFormula Q :=
  Formula.bigOr ((Finset.univ.filter P).toList.map Formula.out1)

/-- A constraint on process 2's output. -/
def atom2 (P : CtrOut Q → Prop) : CtrFormula Q :=
  Formula.bigOr ((Finset.univ.filter P).toList.map Formula.out2)

/-- A constraint relating both outputs: the disjunction over the pairs `(y₁, y₂)` satisfying
it of `(out₁ = y₁) ∧ (out₂ = y₂)`. -/
def atom12 (R : CtrOut Q → CtrOut Q → Prop) : CtrFormula Q :=
  Formula.bigOr
    (((Finset.univ : Finset (CtrOut Q × CtrOut Q)).filter (fun p => R p.1 p.2)).toList.map
      fun p => Formula.and (Formula.out1 p.1) (Formula.out2 p.2))

/-- The three graphs. -/
def graphs : List CommGraph := [CommGraph.oneToTwo, CommGraph.both, CommGraph.twoToOne]

/-- `a mod 3 ∈ Z₃`. -/
def mod3 (a : ℕ) : Fin 3 := ⟨a % 3, Nat.mod_lt _ (by norm_num)⟩

/-- `ChildPos_g : Z₃² → Z₃²` (Eq. (2), p. 10). -/
def childPos (g : CommGraph) (u v : Fin 3) : Fin 3 × Fin 3 :=
  match g with
  | CommGraph.oneToTwo => (mod3 (3 * u.val), mod3 (2 * u.val + v.val))
  | CommGraph.both => (mod3 (u.val + 2 * v.val), mod3 (2 * u.val + v.val))
  | CommGraph.twoToOne => (mod3 (u.val + 2 * v.val), mod3 (3 * v.val))

/-- `(pos₁, pos₂) = (u, v)`. -/
def posEq (uv : Fin 3 × Fin 3) : CtrFormula Q :=
  atom12 (fun y1 y2 => opos y1 = uv.1 ∧ opos y2 = uv.2)

/-- `ϕ(u, v, g) := (pos₁, pos₂) = (u, v) → X [graph = g → (pos₁, pos₂) = ChildPos_g(u, v)]`
(Eq. (3)). -/
def phiPos (u v : Fin 3) (g : CommGraph) : CtrFormula Q :=
  .imp (posEq (u, v)) (.next (.imp (.graph g) (posEq (childPos g u v))))

/-- `PosOrd` (Eq. (4)). -/
def posOrd : CtrFormula Q :=
  .and (Formula.bigAnd (graphs.map fun g => .imp (.graph g) (posEq (childPos g 0 1))))
    (.always (Formula.bigAnd ((List.finRange 3).flatMap fun u => (List.finRange 3).flatMap
      fun v => graphs.map fun g => phiPos u v g)))

/-- `OneIsLeft := ⋁_{(p, q) ∈ Z₃², q ≡ p + 1 mod 3} (pos₁ = p ∧ pos₂ = q)` (p. 10). -/
def oneIsLeft : CtrFormula Q :=
  atom12 (fun y1 y2 => (opos y2).val = ((opos y1).val + 1) % 3)

/-- `PathAgr := G((q₁ = q₂) ∧ (zero₁ = zero₂))` (p. 21). -/
def pathAgr : CtrFormula Q :=
  .always (.and (atom12 (fun y1 y2 => oq y1 = oq y2)) (atom12 (fun y1 y2 => ozero y1 = ozero y2)))

/-- The multiplying factor `m(q, z)` (table p. 21): `1` for an increment (`c ↦ c + 1`),
`3` for a decrement test at zero (`c ↦ c`), `9` for a decrement at nonzero (`c ↦ c - 1`).
On halting states the (unused) instruction stored at `q` is read. -/
def mult (M : CounterMachine Q 1) (q : Q) (z : Bool) : ℕ :=
  match M.instr q with
  | .inc _ _ => 1
  | .dec _ _ _ => if z then 3 else 9

/-- `next(q, z)`: the `Δ`-successor of `q` given the zero status `z` of the counter. -/
def nextState (M : CounterMachine Q 1) (q : Q) (z : Bool) : Q :=
  match M.instr q with
  | .inc _ q' => q'
  | .dec _ q' q'' => if z then q' else q''

/-- `Σ_k plan.a_k`. -/
def planSum (y : CtrOut Q) : ℕ := (oa 0 y).val + (oa 1 y).val + (oa 2 y).val

/-- `ψ₁(q, z)` (Eq. (20), `p = 1`). -/
def psi1 (M : CounterMachine Q 1) (q : Q) (z : Bool) : CtrFormula Q :=
  .imp (.and (atom1 (fun y => oq y = q)) (atom1 (fun y => ozero y = z)))
    (atom12 (fun y1 y2 => planSum y1 + (ocarry y1).val = mult M q z * (ow y1).val + (ocarry y2).val))

/-- `ψ₂(q, z)` (Eq. (20), `p = 2`). -/
def psi2 (M : CounterMachine Q 1) (q : Q) (z : Bool) : CtrFormula Q :=
  .imp (.and (atom2 (fun y => oq y = q)) (atom2 (fun y => ozero y = z)))
    (atom12 (fun y1 y2 => planSum y2 + (ocarry y2).val = mult M q z * (ow y2).val + (ocarry y1).val))

/-- All states, and both zero statuses. -/
def states : List Q := (Finset.univ : Finset Q).toList
def bools : List Bool := [true, false]

/-- `LocalSum` (Eq. (21)). -/
def localSum (M : CounterMachine Q 1) : CtrFormula Q :=
  .always (Formula.bigAnd (states.flatMap fun q => bools.map fun z =>
    .and (.imp oneIsLeft (psi1 M q z)) (.imp (.neg oneIsLeft) (psi2 M q z))))

/-- `ZeroInd` (Eq. (22)). -/
def zeroInd : CtrFormula Q :=
  .always (.or
    (.and oneIsLeft (.imp (atom1 (fun y => ozero y = true)) (atom1 (fun y => ow y = 1))))
    (.and (.neg oneIsLeft) (.imp (atom2 (fun y => ozero y = true)) (atom2 (fun y => ow y = 1)))))

/-- `LeftMost := [carry₁ = 0 ∧ (zero₁ = ⊥ → plan₁.w = 0)] W (graph ≠ (1 → 2))` (Eq. (23)). -/
def leftMost : CtrFormula Q :=
  .weakUntil
    (.and (atom1 (fun y => ocarry y = 0)) (.imp (atom1 (fun y => ozero y = false)) (atom1 (fun y => ow y = 0))))
    (.neg (.graph CommGraph.oneToTwo))

/-- `RightMost := (carry₂ = 0) W [graph ≠ (1 ← 2)]` (Eq. (24)). -/
def rightMost : CtrFormula Q :=
  .weakUntil (atom2 (fun y => ocarry y = 0)) (.neg (.graph CommGraph.twoToOne))

/-- `ZeroCheck := ZeroInd ∧ LeftMost ∧ RightMost` (Eq. (25)). -/
def zeroCheck : CtrFormula Q := .and zeroInd (.and leftMost rightMost)

/-- `InitCheck := (q₁ = q_init) ∧ (zero₁ = ⊤)` (Eq. (26)). -/
def initCheck (M : CounterMachine Q 1) : CtrFormula Q :=
  .and (atom1 (fun y => oq y = M.init)) (atom1 (fun y => ozero y = true))

/-- `D(ℓ₁, g)` (Eq. (27)): `0, 1, 2` for `(1 → 2), (1 ↔ 2), (1 ← 2)` if `ℓ₁ = ⊤`, and
`2, 1, 0` if `ℓ₁ = ⊥`. -/
def dVal (l1 : Bool) (g : CommGraph) : ℕ := if l1 then delta g else 2 - delta g

/-- `D_k(ℓ₁, g)`: true iff `D(ℓ₁, g) = k`. -/
def dConst (k : Fin 3) (l1 : Bool) (g : CommGraph) : CtrFormula Q :=
  if dVal l1 g = k.val then Formula.tt else Formula.ff

/-- `D_k(g) := (OneIsLeft ∧ D_k(⊤, g)) ∨ (¬OneIsLeft ∧ D_k(⊥, g))`. -/
def dK (k : Fin 3) (g : CommGraph) : CtrFormula Q :=
  .or (.and oneIsLeft (dConst k true g)) (.and (.neg oneIsLeft) (dConst k false g))

/-- `plan_ℓ.x(v) := (OneIsLeft ∧ plan₁.x = v) ∨ (¬OneIsLeft ∧ plan₂.x = v)`. -/
def planL (sel : CtrOut Q → Fin 2) (b : Fin 2) : CtrFormula Q :=
  .or (.and oneIsLeft (atom1 (fun y => sel y = b))) (.and (.neg oneIsLeft) (atom2 (fun y => sel y = b)))

/-- `StateTrans` (Eq. (28)). -/
def stateTrans (M : CounterMachine Q 1) : CtrFormula Q :=
  Formula.bigAnd (states.flatMap fun q => bools.map fun z =>
    .imp (.and (atom1 (fun y => oq y = q)) (atom1 (fun y => ozero y = z)))
      (.next (atom1 (fun y => oq y = nextState M q z))))

/-- `WeightTrans` (Eq. (29)). -/
def weightTrans : CtrFormula Q :=
  Formula.bigAnd ((List.finRange 3).flatMap fun k => (List.finRange 2).flatMap fun b =>
    graphs.map fun g =>
      .imp (.and (.next (.graph g)) (.and (dK k g) (planL (oa k) b))) (.next (planL ow b)))

/-- `PropTrans := G(StateTrans ∧ WeightTrans)` (Eq. (30)). -/
def propTrans (M : CounterMachine Q 1) : CtrFormula Q := .always (.and (stateTrans M) weightTrans)

/-- `G(⋀_{q ∈ F} q₁ ≠ q)`. -/
def noHalt (M : CounterMachine Q 1) : CtrFormula Q :=
  .always (Formula.bigAnd ((Finset.univ.filter (fun q => q ∈ M.halting)).toList.map
    fun q => .neg (atom1 (fun y => oq y = q))))

end Ctr

/-- `ϕ(M_counter) := PosOrd ∧ PathAgr ∧ LocalSum ∧ ZeroCheck ∧ InitCheck ∧ PropTrans ∧
G(⋀_{q ∈ F} q₁ ≠ q)` (Eq. (31), p. 24) for a 1-counter machine with finite state set `Q`. -/
def counterFormula {Q : Type} [Fintype Q] (M : CounterMachine Q 1) : CtrFormula Q :=
  .and Ctr.posOrd (.and Ctr.pathAgr (.and (Ctr.localSum M) (.and Ctr.zeroCheck
    (.and (Ctr.initCheck M) (.and (Ctr.propTrans M) (Ctr.noHalt M))))))

end

end DistLTLSynth.Char


