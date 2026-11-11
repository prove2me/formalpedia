-- Prove2me | Definitions.Def_JainCRERepetition_Cubic_repeated
-- name    : JainCRERepetition_Cubic_repeated
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:31.293184+00:00
-- url     : https://prove2.me/theorems/73758c85-71f5-4d53-8b3f-15ef4ffa1c23
-- title:
--   Definitions 3.1–3.4 — actual conditioned strategy and coordinate construction
-- statement:
--   Fix an actual finite-dimensional strategy for $G^{\otimes n}$. A coherent representation consists only of a unit shared resource and local isometries whose measured question/answer probabilities reproduce that strategy. Its preselection vector is constructed with amplitudes $\sqrt{\mu^{\otimes n}(x,y)}$, matching question copies and coherent answer copies. The postselection vector is obtained by the diagonal checked-win projector and normalization by $\sqrt{p_C}$.
--
--   For a proper checked set $C$ with $p_C>0$, put $J=[n]\setminus C$, $m=|J|$, $Q=P(\cdot\mid W_C)$ and
--
--   $$B_C=|C|L+\log_2(1/p_C),\qquad t=B_C/m,\qquad A_C=m^{-1}\sum_{i\in J}Q(\neg W_i).$$
--
--   The register partition is Definition 3.4's exact protected-reference/history/core-workspace partition. Unchecked answer copies are retained as part of the allowed local environment. Coordinate conditional vectors and answer readers are computed from the postselection vector. Comparisons use target history weights but normalized preselection blocks conditioned only on the history with checked answers removed. Charges and question divergences are then computed; no consistency, finite-divergence or budget conclusion is a data field. Coherent representations exist for every strategy by Fact 2.11 and the application in Definition 3.2.
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), pp. 22–24, Definitions 3.1–3.4, Eqs. (23)–(29); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Definitions.Def_JainCRERepetition_Cubic_registers
import Definitions.Def_JainCRERepetition_Cubic_copied

open scoped BigOperators Kronecker
open Matrix
noncomputable section

namespace JainCRERepetition.Cubic
attribute [local instance] Classical.propDecidable

inductive RepeatReg (n : ℕ)
  | xh : Fin n → RepeatReg n
  | x : Fin n → RepeatReg n
  | yh : Fin n → RepeatReg n
  | y : Fin n → RepeatReg n
  | a : Fin n → RepeatReg n
  | ac : Fin n → RepeatReg n
  | b : Fin n → RepeatReg n
  | bc : Fin n → RepeatReg n
  | ea : RepeatReg n
  | eb : RepeatReg n
  deriving DecidableEq, Fintype

section Repeated
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
variable [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
variable {n : ℕ} {G : QuantumParallelRepetition.Game X Y A B}

/-- Operational purification/dilation data of the fixed actual strategy. No budget or preparation
conclusion is a field. All local outputs, including coherent answer copies, are retained. -/
structure CoherentStrategy (S : QuantumParallelRepetition.Strategy (G.repeat n)) where
  I : Type
  J : Type
  EA : Type
  EB : Type
  [fi : Fintype I] [fj : Fintype J] [fea : Fintype EA] [feb : Fintype EB]
  [di : DecidableEq I] [dj : DecidableEq J] [dea : DecidableEq EA] [deb : DecidableEq EB]
  [ni : Nonempty I] [nj : Nonempty J] [nea : Nonempty EA] [neb : Nonempty EB]
  eta : I × J → ℂ
  eta_unit : IsUnit eta
  U : (Fin n → X) → Matrix ((Fin n → A) × EA) I ℂ
  V : (Fin n → Y) → Matrix ((Fin n → B) × EB) J ℂ
  U_iso : ∀ xs, (U xs)ᴴ * U xs = 1
  V_iso : ∀ ys, (V ys)ᴴ * V ys = 1
  reproduces : ∀ xs ys as bs,
    (∑ e : EA, ∑ f : EB,
      Complex.normSq (((U xs ⊗ₖ V ys) *ᵥ eta) ((as,e),(bs,f)))) =
      S.outcomeProbability xs ys as bs

attribute [instance] CoherentStrategy.fi CoherentStrategy.fj CoherentStrategy.fea CoherentStrategy.feb
attribute [instance] CoherentStrategy.di CoherentStrategy.dj CoherentStrategy.dea CoherentStrategy.deb
attribute [instance] CoherentStrategy.ni CoherentStrategy.nj CoherentStrategy.nea CoherentStrategy.neb

variable {S : QuantumParallelRepetition.Strategy (G.repeat n)} (T : CoherentStrategy S)

def regType : RepeatReg n → Type
  | .xh _ | .x _ => X
  | .yh _ | .y _ => Y
  | .a _ | .ac _ => A
  | .b _ | .bc _ => B
  | .ea => T.EA
  | .eb => T.EB

instance regFintype (r : RepeatReg n) : Fintype (regType T r) := by cases r <;> simp only [regType] <;> infer_instance
instance regDecidable (r : RepeatReg n) : DecidableEq (regType T r) := by cases r <;> simp only [regType] <;> infer_instance
instance regNonempty (r : RepeatReg n) : Nonempty (regType T r) := by cases r <;> simp only [regType] <;> infer_instance

def answerLength : ℝ := max 1 (Real.logb 2 ((Fintype.card A : ℝ) * Fintype.card B))

def priorLaw (G : QuantumParallelRepetition.Game X Y A B) : Law (X × Y) where
  p z := G.questionWeight z.1 z.2
  p_nonneg z := G.weight_nonneg _ _
  p_sum := by simpa only [Fintype.sum_prod_type] using G.weight_normalized

def checkedWin (C : Finset (Fin n)) (xs : Fin n → X) (ys : Fin n → Y)
    (as : Fin n → A) (bs : Fin n → B) : Prop :=
  ∀ i ∈ C, G.predicate (xs i) (ys i) (as i) (bs i) = true

def transcriptWeight (S : QuantumParallelRepetition.Strategy (G.repeat n))
    (z : ((Fin n → X) × (Fin n → Y)) × ((Fin n → A) × (Fin n → B))) : ℝ :=
  (G.repeat n).questionWeight z.1.1 z.1.2 * S.outcomeProbability z.1.1 z.1.2 z.2.1 z.2.2

def checkedProbability (S : QuantumParallelRepetition.Strategy (G.repeat n)) (C : Finset (Fin n)) : ℝ :=
  ∑ z, if checkedWin (G := G) C z.1.1 z.1.2 z.2.1 z.2.2 then transcriptWeight S z else 0

def posteriorWeight (S : QuantumParallelRepetition.Strategy (G.repeat n)) (C : Finset (Fin n))
    (z : ((Fin n → X) × (Fin n → Y)) × ((Fin n → A) × (Fin n → B))) : ℝ :=
  if checkedWin (G := G) C z.1.1 z.1.2 z.2.1 z.2.2 then
    transcriptWeight S z / checkedProbability S C else 0

def coordinateLaw (S : QuantumParallelRepetition.Strategy (G.repeat n)) (C : Finset (Fin n))
    (i : Fin n) (xy : X × Y) : ℝ :=
  ∑ z, if z.1.1 i = xy.1 ∧ z.1.2 i = xy.2 then posteriorWeight S C z else 0

def unchecked (C : Finset (Fin n)) : Finset (Fin n) := Finset.univ \ C

def budgetRatio (S : QuantumParallelRepetition.Strategy (G.repeat n)) (C : Finset (Fin n)) : ℝ :=
  ((C.card : ℝ) * (answerLength (A := A) (B := B)) +
    Real.logb 2 (1 / checkedProbability S C)) / (unchecked C).card

def meanRejection (S : QuantumParallelRepetition.Strategy (G.repeat n)) (C : Finset (Fin n)) : ℝ :=
  (∑ i ∈ unchecked C, ∑ z,
    if G.predicate (z.1.1 i) (z.1.2 i) (z.2.1 i) (z.2.2 i) = false then
      posteriorWeight S C z else 0) / (unchecked C).card

/-- The actual preselection ket (23). Every answer is copied coherently; unchecked copies are
part of EA/EB, an allowed choice of retained measurement environment. -/
def preselection : Config (regType T) Finset.univ → ℂ := fun z =>
  let xs := fun i => readReg (regType T) z (.x i)
  let ys := fun i => readReg (regType T) z (.y i)
  let as := fun i => readReg (regType T) z (.a i)
  let bs := fun i => readReg (regType T) z (.b i)
  if (∀ i, readReg (regType T) z (.xh i) = xs i ∧ readReg (regType T) z (.yh i) = ys i ∧
    readReg (regType T) z (.ac i) = as i ∧ readReg (regType T) z (.bc i) = bs i) then
    (Real.sqrt ((G.repeat n).questionWeight xs ys) : ℂ) *
      ((T.U xs ⊗ₖ T.V ys) *ᵥ T.eta)
        ((as,readReg (regType T) z .ea),(bs,readReg (regType T) z .eb)) else 0

def postselection (C : Finset (Fin n)) : Config (regType T) Finset.univ → ℂ := fun z =>
  if checkedWin (G := G) C (fun i => readReg (regType T) z (.x i))
    (fun i => readReg (regType T) z (.y i)) (fun i => readReg (regType T) z (.a i))
    (fun i => readReg (regType T) z (.b i)) then
    preselection T z / (Real.sqrt (checkedProbability S C) : ℂ) else 0

def refSet (i : Fin n) : Finset (RepeatReg n) := {.xh i,.yh i}

def historyA (C : Finset (Fin n)) (i : Fin n) : Finset (RepeatReg n) :=
  (C.image RepeatReg.x) ∪ (C.image RepeatReg.yh) ∪ (C.image RepeatReg.a) ∪
  (C.image RepeatReg.bc) ∪ (((unchecked C).filter (· < i)).image RepeatReg.yh) ∪
  (((unchecked C).filter (i < ·)).image RepeatReg.x)

def historyB (C : Finset (Fin n)) (i : Fin n) : Finset (RepeatReg n) :=
  (C.image RepeatReg.xh) ∪ (C.image RepeatReg.y) ∪ (C.image RepeatReg.ac) ∪
  (C.image RepeatReg.b) ∪ (((unchecked C).filter (· < i)).image RepeatReg.y) ∪
  (((unchecked C).filter (i < ·)).image RepeatReg.xh)

def coreA (C : Finset (Fin n)) (i : Fin n) : Finset (RepeatReg n) :=
  (((unchecked C).filter (· < i)).image RepeatReg.xh) ∪
  (((unchecked C).filter (· < i)).image RepeatReg.x) ∪
  ((unchecked C).image RepeatReg.a) ∪ ((unchecked C).image RepeatReg.ac) ∪ {.ea}

def coreB (C : Finset (Fin n)) (i : Fin n) : Finset (RepeatReg n) :=
  (((unchecked C).filter (i < ·)).image RepeatReg.yh) ∪
  (((unchecked C).filter (i < ·)).image RepeatReg.y) ∪
  ((unchecked C).image RepeatReg.b) ∪ ((unchecked C).image RepeatReg.bc) ∪ {.eb}

def workspaceA (C : Finset (Fin n)) (i : Fin n) := historyA C i ∪ coreA C i

def workspaceB (C : Finset (Fin n)) (i : Fin n) := historyB C i ∪ coreB C i

def viewSet (C : Finset (Fin n)) (i : Fin n) (alice : Bool) : Finset (RepeatReg n) :=
  refSet i ∪ if alice then {.x i} ∪ workspaceA C i else {.y i} ∪ workspaceB C i

def coordinateVector (C : Finset (Fin n)) (i : Fin n) (x : X) (y : Y) :
    Config (regType T) (workspaceA C i) × Config (regType T) (workspaceB C i) → ℂ := fun ab =>
  let q := coordinateLaw S C i (x,y)
  if 0 < q then
    (∑ z : Config (regType T) Finset.univ,
      if readReg (regType T) z (.x i) = x ∧ readReg (regType T) z (.y i) = y ∧
        restrictReg (regType T) z (workspaceA C i) = ab.1 ∧
        restrictReg (regType T) z (workspaceB C i) = ab.2 then postselection T C z else 0) /
      (Real.sqrt q : ℂ)
  else if ab = Classical.choice (inferInstance : Nonempty
    (Config (regType T) (workspaceA C i) × Config (regType T) (workspaceB C i))) then 1 else 0

/-- (29): target history weights; separately normalized preselection blocks omit checked answers. -/
def coordinateComparison (C : Finset (Fin n)) (i : Fin n) (alice : Bool) :
    Op (Config (regType T) (viewSet C i alice)) :=
  let H := if alice then historyA C i else historyB C i
  let Z := if alice then C.image RepeatReg.a ∪ C.image RepeatReg.bc
    else C.image RepeatReg.ac ∪ C.image RepeatReg.b
  let Hbar := H \ Z
  let K := viewSet C i alice \ H
  let φ := ket (postselection T C)
  let ψ := ket (preselection T)
  fun a b =>
    let h := restrictReg (regType T) a H
    if h = restrictReg (regType T) b H then
      (recordProb (regType T) φ H h : ℂ) *
        conditioned (regType T) ψ Hbar (restrictReg (regType T) h Hbar) K
          (restrictReg (regType T) a K) (restrictReg (regType T) b K) else 0

def coordinateTarget (C : Finset (Fin n)) (i : Fin n) (alice : Bool) :=
  reduced (regType T) (ket (postselection T C)) (viewSet C i alice)

def coordinateCharge (C : Finset (Fin n)) (i : Fin n) (alice : Bool) : ℝ :=
  let ρ := coordinateTarget T C i alice
  let ν := coordinateComparison T C i alice
  let K := viewSet C i alice \ refSet i
  d ρ ν - d (reduced (regType T) ρ K) (reduced (regType T) ν K)

def coordinateS (C : Finset (Fin n)) (i : Fin n) : ℝ :=
  coordinateCharge T C i true + coordinateCharge T C i false

/-- Consistency is equality to the actual conditional measured question/answer law. -/
def coordinateConsistent (C : Finset (Fin n)) (i : Fin n) : Prop :=
  (∀ x y, IsUnit (coordinateVector T C i x y)) ∧
  ∀ x y a b,
    coordinateLaw S C i (x,y) *
      (∑ ab, if readReg (regType T) ab.1 (.a i) = a ∧ readReg (regType T) ab.2 (.b i) = b
        then Complex.normSq (coordinateVector T C i x y ab) else 0) =
    ∑ z, if z.1.1 i = x ∧ z.1.2 i = y ∧ z.2.1 i = a ∧ z.2.2 i = b
      then posteriorWeight S C z else 0

/-- The actual copied-input expansion (25), before any protected reference is discarded. -/
def coordinateExpansion (C : Finset (Fin n)) (i : Fin n) : Prop :=
  ∀ z : Config (regType T) Finset.univ,
    let x := readReg (regType T) z (.x i)
    let y := readReg (regType T) z (.y i)
    postselection T C z =
      if readReg (regType T) z (.xh i) = x ∧ readReg (regType T) z (.yh i) = y then
        (Real.sqrt (coordinateLaw S C i (x,y)) : ℂ) * coordinateVector T C i x y
          (restrictReg (regType T) z (workspaceA C i),restrictReg (regType T) z (workspaceB C i))
      else 0

end Repeated
end JainCRERepetition.Cubic


