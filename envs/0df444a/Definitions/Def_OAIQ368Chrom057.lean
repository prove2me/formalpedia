-- Prove2me | Definitions.Def_OAIQ368Chrom057
-- name    : OAIQ368Chrom057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:22:50.876294+00:00
-- url     : https://prove2.me/theorems/a43826f4-57d4-4ba5-9033-595bd0cb4049
-- title:
--   Definitions bundle OAIQ368Chrom057 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 144 declarations of OpenAI's Lean: 64 definitions, 2 inductive types or structures, 7 instances and 71 theorems. The definitions and types are `OAI.ElementaryPositivity.ForwardChain.gaps`, `OAI.ElementaryPositivity.ForwardChain.positiveMutate`, `OAI.ElementaryPositivity.LatticeRealization.cast`, `OAI.ElementaryPositivity.QuantumTorus.Compatible`, `OAI.ElementaryPositivity.QuantumTorus.CutSupported`, `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr`, `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr.eval`, `OAI.ElementaryPositivity.QuantumTorus.IsIndependent`, `OAI.ElementaryPositivity.QuantumTorus.centeredCrossing`, `OAI.ElementaryPositivity.QuantumTorus.embeddingSumCompl`, `OAI.ElementaryPositivity.QuantumTorus.homogeneousElementaryExpressionsAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.homogeneousElementaryExpressionsRing`, `OAI.ElementaryPositivity.QuantumTorus.independentElement`, `OAI.ElementaryPositivity.QuantumTorus.independentTerm`, `OAI.ElementaryPositivity.QuantumTorus.instRingTorusLaurentSeriesRatVUnit_15`, `OAI.ElementaryPositivity.QuantumTorus.nearCutMutationRing`, `OAI.ElementaryPositivity.QuantumTorus.pivotMap`, `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming`, `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionOrderBound`, `OAI.ElementaryPositivity.QuantumTorus.rootMutation`, `OAI.ElementaryPositivity.QuantumTorus.setMonomial`, `OAI.ElementaryPositivity.TriangularDynamics.Cell`, `OAI.ElementaryPositivity.TriangularDynamics.FreeChart`, `OAI.ElementaryPositivity.TriangularDynamics.FreeChart.mutate`, `OAI.ElementaryPositivity.TriangularDynamics.GapIndex`, `OAI.ElementaryPositivity.TriangularDynamics.Lattice`, `OAI.ElementaryPositivity.TriangularDynamics.Vertex`, `OAI.ElementaryPositivity.TriangularDynamics.afterGap`, `OAI.ElementaryPositivity.TriangularDynamics.anchor`, `OAI.ElementaryPositivity.TriangularDynamics.bridge`, `OAI.ElementaryPositivity.TriangularDynamics.bridgePositive`, `OAI.ElementaryPositivity.TriangularDynamics.cellLevel`, `OAI.ElementaryPositivity.TriangularDynamics.cellRow`, `OAI.ElementaryPositivity.TriangularDynamics.chartMatrix`, `OAI.ElementaryPositivity.TriangularDynamics.chartPairing`, `OAI.ElementaryPositivity.TriangularDynamics.cutContains`, `OAI.ElementaryPositivity.TriangularDynamics.cutDeficit`, `OAI.ElementaryPositivity.TriangularDynamics.cutPrefix`, `OAI.ElementaryPositivity.TriangularDynamics.delta`, `OAI.ElementaryPositivity.TriangularDynamics.eventRoot` and 26 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_HomogeneousElementaryExpressions`, `Chromatic_GradedAlgebra_MutationRootMap`, `Chromatic_GradedAlgebra_RootMutationInventory`, `Chromatic_QuantumTorus_IndependentElementReindex`, `Chromatic_QuantumTorus_IndependentSetElements`, `Chromatic_QuantumTorus_NearCutMutation`, `Chromatic_QuantumTorus_RationalFiberTorus`, `Chromatic_Walls_FiniteLatticePairing`, `Chromatic_Walls_ForwardChartMutation`, `Chromatic_Walls_ForwardInventoryRotation`, `Chromatic_Walls_ForwardPolynomialMutation`, `Chromatic_Walls_PathRoot`, `Chromatic_Walls_PolynomialIncomingPerturbation`, `Chromatic_Walls_RationalCutIdentity`, `Chromatic_Walls_RealLatticeRealization`, `Chromatic_Walls_StationaryIntegerSequences`, `Chromatic_Walls_TriangularGapOrthogonality`, `Chromatic_Walls_TriangularLateStationarity`, `Chromatic_Walls_TriangularLevelQueues`, `Chromatic_Walls_TriangularScheduledRoots`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom012` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom058` and `OAIQ368Chrom074`; the statements `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation` and `OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit`; the proofs of `OAI.ElementaryPositivity.QuantumTorus.polynomialSectionIncoming_mutation` and `OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom012

section
-- module Solutions.OAIQ368_CHROM.Compat
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_RationalFiberTorus
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
namespace FiberTorus
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
instance instAddCommGroup : AddCommGroup (FiberTorus v Ω α) := inferInstanceAs (AddCommGroup (M →₀ RatFunc K))
end FiberTorus
end
end ElementaryPositivity.RationalFiber

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RationalCutIdentity
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WallUnits
open Polynomial
noncomputable section
variable {K : Type*} [Field K]
def centeredExponent (t : ℕ) (i : Fin t) : ℤ := 2*(i:ℕ)+1-(t:ℤ)
def centeredPolynomial (v : Kˣ) (t : ℕ) : K[X] :=
  ∏i : Fin t,(1+C (↑(v^centeredExponent t i):K)*X)
end
end ElementaryPositivity.WallUnits

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_MutationRootMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open WallUnits
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
def centeredCrossing (p m : M) (t : ℕ) : Torus v Ω :=
  ∑j : Fin (t+1),Torus.monomial v Ω (m+(j:ℕ) • p) ((centeredPolynomial v t).coeff j)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_IndependentSetElements
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M V W : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

def IsIndependent (u : V → M) (s : Finset V) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, Ω (u x) (u y)=0

def setMonomial (u : V → M) (s : Finset V) : Torus v Ω :=
  Torus.X v Ω (∑ x ∈ s,u x)

def independentTerm [DecidableEq V] (u : V → M) (k : ℕ) (s : Finset V) : Torus v Ω :=
  if IsIndependent Ω u s ∧ s.card=k then setMonomial v Ω u s else 0

def independentElement [Fintype V] [DecidableEq V] (u : V → M) (k : ℕ) : Torus v Ω :=
  ∑ s : Finset V, independentTerm v Ω u k s

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open scoped BigOperators
open Classical
noncomputable section
variable {K M W : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

abbrev Compatible (a : M) (w : W → M) (t : Finset W) : Prop :=
  ∀ y∈t,Ω a (w y)=0

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_IndependentElementReindex
attribute [-simp] _root_.OAI.ElementaryPositivity.WallUnits.rescale_C
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
open scoped BigOperators
noncomputable section
variable {K M V W : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)

def embeddingSumCompl (e : V ↪ W) : V ⊕ {w : W // w∉Set.range e} ≃ W :=
  ((Equiv.ofInjective e e.injective).sumCongr (Equiv.refl _)).trans
    (Equiv.sumCompl (fun w=>w∈Set.range e))
@[simp] lemma embeddingSumCompl_inl (e : V ↪ W) (x : V) :
    embeddingSumCompl e (.inl x)=e x := rfl
@[simp] lemma embeddingSumCompl_inr (e : V ↪ W) (x : {w : W // w∉Set.range e}) :
    embeddingSumCompl e (.inr x)=x.val := rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HomogeneousElementaryExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
noncomputable section

inductive ElementaryExpr : ℕ → Type
  | zero (k:ℕ) : ElementaryExpr k
  | one : ElementaryExpr 0
  | atom (k:ℕ) : ElementaryExpr k
  | add {k:ℕ} : ElementaryExpr k → ElementaryExpr k → ElementaryExpr k
  | neg {k:ℕ} : ElementaryExpr k → ElementaryExpr k
  | mul {k l:ℕ} : ElementaryExpr k → ElementaryExpr l → ElementaryExpr (k+l)

variable {M V:Type*} [AddCommGroup M] [Fintype V] [DecidableEq V]
variable (v:(LaurentSeries ℚ)ˣ) (Ω:M →+ M →+ ℤ)
local instance homogeneousElementaryExpressionsRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance homogeneousElementaryExpressionsAddCommMonoid_r16ce0b_1 : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance homogeneousElementaryExpressionsAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def ElementaryExpr.eval (w:V → M) : {k:ℕ} → ElementaryExpr k → Torus v Ω
  | _,.zero _ => 0
  | _,.one => 1
  | _,.atom k => independentElement v Ω w k
  | _,.add f g => eval w f+eval w g
  | _,.neg f => -eval w f
  | _,.mul f g => eval w f*eval w g

def CutSupported (ell:M →+ ℤ) (N:ℤ) (F:Torus v Ω) : Prop :=
  ∀m∈F.support,ell m≤N

open RationalFiber
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_StationaryIntegerSequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
abbrev Vertex (n : ℕ) (B : Type*) := Sum (Fin (n+1)) B
abbrev Lattice (n : ℕ) (B : Type*) := Vertex n B → ℤ

def anchor (i : Fin (n+1)) : Lattice n B := Pi.single (Sum.inl i) 1
def bridge (b : B) : Lattice n B := Pi.single (Sum.inr b) 1

def delta (level : B → Fin n) (b : B) : Lattice n B :=
  anchor (level b).succ - anchor (level b).castSucc

def eventRoot (level : B → Fin n) (L : ℕ) (b : B) : Lattice n B :=
  bridge b - anchor (level b).castSucc + (L:ℤ) • delta level b

def levelTotal (level : B → Fin n) (i : Fin n) : Lattice n B →+ ℤ where
  toFun m := ∑ b, if level b = i then m (Sum.inr b) else 0
  map_zero' := by simp
  map_add' m m' := by
    change (∑ b, if level b = i then m (Sum.inr b)+m' (Sum.inr b) else 0) = _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp

def cutContains (level : B → Fin n) (i : Fin n) : Vertex n B → Prop
  | Sum.inl a => a.val ≤ i.val
  | Sum.inr b => (level b).val ≤ i.val

instance cutContains_decidable (level : B → Fin n) (i : Fin n) :
    DecidablePred (cutContains level i) := fun a => by
  cases a <;> unfold cutContains <;> infer_instance

def cutPrefix (level : B → Fin n) (i : Fin n) : Lattice n B →+ ℤ where
  toFun m := ∑ a, if cutContains level i a then m a else 0
  map_zero' := by simp
  map_add' m m' := by
    change (∑ a, if cutContains level i a then m a+m' a else 0) = _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp

@[simp] lemma cutPrefix_single (level : B → Fin n) (i : Fin n) (a : Vertex n B) (z : ℤ) :
    cutPrefix level i (Pi.single a z) = if cutContains level i a then z else 0 := by
  classical
  change (∑ v, if cutContains level i v then Pi.single a z v else 0) = _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

@[simp] lemma levelTotal_anchor (level : B → Fin n) (i : Fin n) (a : Fin (n+1)) :
    levelTotal level i (anchor a) = 0 := by
  simp [levelTotal,anchor]
@[simp] lemma levelTotal_bridge (level : B → Fin n) (i : Fin n) (b : B) :
    levelTotal level i (bridge b) = if level b = i then 1 else 0 := by
  change (∑ c, if level c = i then bridge b (Sum.inr c) else 0) = _
  rw [Finset.sum_eq_single b]
  · simp [bridge]
  · intro c _ hc
    simp [bridge,hc]
  · simp

omit [Fintype B] in
@[simp] lemma eventRoot_bridge (level : B → Fin n) (L : ℕ) (b c : B) :
    eventRoot level L b (Sum.inr c) = if c = b then 1 else 0 := by
  simp [eventRoot,bridge,anchor,delta,Pi.single_apply]

@[simp] lemma cutPrefix_eventRoot (level : B → Fin n) (i : Fin n) (L : ℕ) (b : B) :
    cutPrefix level i (eventRoot level L b) = if level b = i then -(L:ℤ) else 0 := by
  simp only [eventRoot,delta,map_add,map_sub,map_zsmul,anchor,bridge,cutPrefix_single,
    cutContains,Fin.val_succ,Fin.val_castSucc,smul_eq_mul]
  by_cases h : level b = i
  · simp [h]
  · have hne : (level b).val ≠ i.val := fun hh => h (Fin.ext hh)
    split_ifs <;> simp_all <;> omega

@[simp] lemma levelTotal_eventRoot (level : B → Fin n) (i : Fin n) (L : ℕ) (b : B) :
    levelTotal level i (eventRoot level L b) = if level b = i then 1 else 0 := by
  simp only [eventRoot,delta,map_add,map_sub,map_zsmul,levelTotal_bridge,levelTotal_anchor,
    sub_self,smul_zero,add_zero,sub_zero]

def periodFunctional (level : B → Fin n) (i : Fin n) (L : ℕ) : Lattice n B →+ ℤ :=
  cutPrefix level i + (L:ℤ) • levelTotal level i

@[simp] lemma periodFunctional_eventRoot (level : B → Fin n) (i : Fin n) (L : ℕ) (b : B) :
    periodFunctional level i L (eventRoot level L b) = 0 := by
  simp only [periodFunctional,AddMonoidHom.add_apply,AddMonoidHom.zsmul_apply,
    cutPrefix_eventRoot,levelTotal_eventRoot,smul_eq_mul]
  split_ifs <;> ring

variable (Ω : Lattice n B →+ Lattice n B →+ ℤ)

def rotate (level : B → Fin n) (L : ℕ) (m : Lattice n B) (b : B) : Lattice n B :=
  mutationIncomingLabel Ω (eventRoot level L b) m

def period (level : B → Fin n) (cycle : List B) (L : ℕ) (m : Lattice n B) : Lattice n B :=
  cycle.foldl (rotate Ω level L) m

def history (level : B → Fin n) (cycle : List B) (m : Lattice n B) : ℕ → Lattice n B
  | 0 => m
  | L+1 => period Ω level cycle L (history level cycle m L)

def cutDeficit (level : B → Fin n) (i : Fin n) (N L : ℕ) (m : Lattice n B) : ℤ :=
  (N:ℤ)-periodFunctional level i L m

end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLateStationarity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open ElementaryPositivity.QuantumTorus
variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

def extendedTotal (level : B → Fin n) (m : Lattice n B) (k : ℕ) : ℤ :=
  if h : 0 < k ∧ k ≤ n then levelTotal level ⟨k-1,by omega⟩ m else 0

omit [DecidableEq B] in
@[simp] lemma extendedTotal_zero (level : B → Fin n) (m : Lattice n B) :
    extendedTotal level m 0 = 0 := by simp [extendedTotal]
omit [DecidableEq B] in
@[simp] lemma extendedTotal_last (level : B → Fin n) (m : Lattice n B) :
    extendedTotal level m (n+1) = 0 := by simp [extendedTotal]
omit [DecidableEq B] in
@[simp] lemma extendedTotal_succ (level : B → Fin n) (m : Lattice n B) (i : Fin n) :
    extendedTotal level m (i.val+1) = levelTotal level i m := by
  unfold extendedTotal
  rw [dite_eq_left (by constructor <;> omega)]
  congr 2

end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_FiniteLatticePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def matrixPairing (K : Matrix V V ℤ) : (V → ℤ) →+ (V → ℤ) →+ ℤ where
  toFun x := (Matrix.toBilin' K x).toAddMonoidHom
  map_zero' := by ext y; simp
  map_add' x y := by ext z; simp

@[simp] lemma matrixPairing_single (K : Matrix V V ℤ) (a b : V) :
    matrixPairing K (Pi.single a 1) (Pi.single b 1) = K a b :=
  Matrix.toBilin'_single ..

variable {n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

def chartMatrix (level : B → Fin n) (bb : B → B → ℤ) : Matrix (Vertex n B) (Vertex n B) ℤ
  | .inl _, .inl _ => 0
  | .inl a, .inr b => (if a = (level b).succ then 1 else 0) -
      (if a = (level b).castSucc then 1 else 0)
  | .inr b, .inl a => (if a = (level b).castSucc then 1 else 0) -
      (if a = (level b).succ then 1 else 0)
  | .inr b, .inr c => bb b c

noncomputable def chartPairing (level : B → Fin n) (bb : B → B → ℤ) :=
  matrixPairing (chartMatrix level bb)

end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

abbrev Cell (n : ℕ) := (i : Fin n) × Fin (i.val+1)
def cellLevel {n : ℕ} (b : Cell n) : Fin n := b.1
def cellRow {n : ℕ} (b : Cell n) : ℕ := b.2.val

def phaseEarlier {n : ℕ} (b c : Cell n) : Prop :=
  cellRow c < cellRow b ∨ (cellRow b = cellRow c ∧ b.1 < c.1)
instance instDecidablePhaseEarlier {n : ℕ} (b c : Cell n) : Decidable (phaseEarlier b c) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

lemma cell_ext {n : ℕ} {b c : Cell n} (hl : b.1=c.1) (hr : cellRow b=cellRow c) : b=c := by
  cases b with | mk i r =>
    cases c with | mk j s =>
      dsimp only at hl
      subst j
      have HH:r=s:=Fin.ext hr
      subst s
      rfl

lemma phaseEarlier_trichotomy {n : ℕ} (b c : Cell n) :
    phaseEarlier b c ∨ b=c ∨ phaseEarlier c b := by
  by_cases hr : cellRow b=cellRow c
  · rcases lt_trichotomy b.1 c.1 with h|h|h
    · exact Or.inl (Or.inr ⟨hr,h⟩)
    · exact Or.inr (Or.inl (cell_ext h hr))
    · exact Or.inr (Or.inr (Or.inr ⟨hr.symm,h⟩))
  · rcases lt_or_gt_of_ne hr with h|h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl (Or.inl h)

@[simp] lemma phaseEarlier_irrefl {n : ℕ} (b : Cell n) : ¬phaseEarlier b b := by
  simp [phaseEarlier]
lemma phaseEarlier_asymm {n : ℕ} {b c : Cell n} (h : phaseEarlier b c) :
    ¬phaseEarlier c b := by
  unfold phaseEarlier at *
  rcases h with h|⟨h,h'⟩ <;> intro H
  · rcases H with H|⟨H,_⟩ <;> omega
  · rcases H with H|⟨_,H⟩
    · omega
    · exact lt_asymm h' H

def bridgePositive {n : ℕ} (b c : Cell n) : ℤ :=
  if b.1=c.1 ∧ phaseEarlier c b then 1
  else if c.1.val+1=b.1.val ∧ phaseEarlier b c then 1 else 0

def triangularBB {n : ℕ} (b c : Cell n) : ℤ := bridgePositive b c-bridgePositive c b

noncomputable def triangularOmega (n : ℕ) := chartPairing (@cellLevel n) (@triangularBB n)

lemma eventRoot_anchor {n : ℕ} (b : Cell n) (a : Fin (n+1)) :
    triangularOmega n (eventRoot cellLevel 0 b) (anchor a) =
      (if a=b.1.castSucc then 1 else 0)-(if a=b.1.succ then 1 else 0) := by
  simp only [eventRoot,Nat.cast_zero,zero_smul,add_zero,map_sub,AddMonoidHom.sub_apply]
  change matrixPairing (chartMatrix cellLevel triangularBB) (bridge b) (anchor a)-
    matrixPairing (chartMatrix cellLevel triangularBB) (anchor b.1.castSucc) (anchor a)=_
  simp only [bridge,anchor,matrixPairing_single,chartMatrix,cellLevel,sub_zero]
  rfl

lemma eventRoot_bridge_value {n : ℕ} (b c : Cell n) :
    triangularOmega n (eventRoot cellLevel 0 b) (bridge c) =
      if c.1=b.1 then
        (if phaseEarlier c b then 2 else if c=b then 1 else 0)
      else if c.1.val+1=b.1.val ∨ b.1.val+1=c.1.val then
        (if phaseEarlier c b then -1 else 0)
      else 0 := by
  simp only [eventRoot,Nat.cast_zero,zero_smul,add_zero,map_sub,AddMonoidHom.sub_apply]
  change matrixPairing (chartMatrix cellLevel triangularBB) (bridge b) (bridge c)-
    matrixPairing (chartMatrix cellLevel triangularBB) (anchor b.1.castSucc) (bridge c)=_
  simp only [bridge,anchor,matrixPairing_single]
  change triangularBB b c - ((if b.1.castSucc=c.1.succ then 1 else 0)-
    (if b.1.castSucc=c.1.castSucc then 1 else 0)) =
      (if c.1=b.1 then (if phaseEarlier c b then 2 else if c=b then 1 else 0)
      else if c.1.val+1=b.1.val ∨ b.1.val+1=c.1.val then
        (if phaseEarlier c b then -1 else 0) else 0)
  have h1 : b.1.castSucc=c.1.succ ↔ b.1.val=c.1.val+1 := by rw [Fin.ext_iff]; rfl
  have h2 : b.1.castSucc=c.1.castSucc ↔ b.1=c.1 := Fin.castSucc_inj
  simp only [triangularBB,bridgePositive,h1,h2]
  rcases phaseEarlier_trichotomy b c with H|H|H
  · have H' := phaseEarlier_asymm H
    have Hne : c≠b := by intro h; subst c; exact phaseEarlier_irrefl b H
    simp only [H,H',Hne,ite_false, if_false,and_false,and_true]
    by_cases hl : b.1=c.1
    · have hv := congrArg Fin.val hl
      simp only [hl,ite_true, if_true]
      split_ifs <;> omega
    · have hl' := Ne.symm hl
      simp only [hl,hl',ite_false, if_false]
      split_ifs <;> omega
  · subst c
    simp
  · have H' := phaseEarlier_asymm H
    simp only [H,H',ite_false, if_false,ite_true, if_true,and_false,and_true]
    by_cases hl : b.1=c.1
    · have hv := congrArg Fin.val hl
      simp only [hl,ite_true, if_true]
      split_ifs <;> omega
    · have hl' := Ne.symm hl
      simp only [hl,hl',ite_false, if_false]
      split_ifs <;> omega

end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularScheduledRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators

variable {n : ℕ}

@[simp] lemma omega_anchors (i j : Fin (n+1)) :
    triangularOmega n (anchor i) (anchor j)=0 := by
  change matrixPairing (chartMatrix (@cellLevel n) (@triangularBB n))
    (Pi.single (.inl i) 1) (Pi.single (.inl j) 1)=0
  exact matrixPairing_single (chartMatrix cellLevel triangularBB) (.inl i) (.inl j)

@[simp] lemma omega_delta_anchor (b : Cell n) (i : Fin (n+1)) :
    triangularOmega n (delta cellLevel b) (anchor i)=0 := by
  simp only [delta,map_sub,AddMonoidHom.sub_apply,omega_anchors,sub_self]

@[simp] lemma omega_anchor_delta (i : Fin (n+1)) (b : Cell n) :
    triangularOmega n (anchor i) (delta cellLevel b)=0 := by
  simp only [delta,map_sub,omega_anchors,sub_self]

@[simp] lemma omega_delta_delta (b c : Cell n) :
    triangularOmega n (delta cellLevel b) (delta cellLevel c)=0 := by
  simp only [delta,map_sub,AddMonoidHom.sub_apply,omega_anchors,sub_self]

def levelCartan (i j : Fin n) : ℤ :=
  if i=j then 2 else if i.val+1=j.val ∨ j.val+1=i.val then -1 else 0

def scheduledBridge (L : ℕ) (b c : Cell n) : Lattice n (Cell n) :=
  bridge c + ((L:ℤ)+(if phaseEarlier c b then 1 else 0)) • delta cellLevel c

@[simp] lemma scheduledBridge_self (L : ℕ) (b : Cell n) :
    scheduledBridge L b b=bridge b+(L:ℤ) • delta cellLevel b := by
  simp [scheduledBridge]

end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PathRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open scoped BigOperators
open Classical
noncomputable section
variable {n : ℕ}
abbrev GapIndex (n : ℕ) := (i : Fin n) × Fin (i.val+2)

def levelNode (i : Fin n) (j : Fin (i.val+3)) : Vertex n (Cell n) :=
  if h0 : j.val=0 then .inl i.castSucc
  else if he : j.val=i.val+2 then .inl i.succ
  else .inr ⟨i,⟨i.val+1-j.val,by omega⟩⟩

def afterGap (g : GapIndex n) : Vertex n (Cell n) → Prop
  | .inl a => g.1.val < a.val
  | .inr b => g.1.val < b.1.val ∨
      (g.1=b.1 ∧ b.2.val+g.2.val < g.1.val+1)

lemma afterGap_node (g : GapIndex n) (i : Fin n) (j : Fin (i.val+3)) :
    afterGap g (levelNode i j) ↔ g.1.val < i.val ∨ (g.1=i ∧ g.2.val < j.val) := by
  unfold levelNode
  split_ifs with h0 he
  · simp only [afterGap,Fin.val_castSucc,h0,not_lt_zero,and_false,or_false]
  · simp only [afterGap,Fin.val_succ,he,Fin.ext_iff]
    have hg:=g.2.isLt
    omega
  · simp only [afterGap,Fin.ext_iff]
    have hj:=j.isLt
    omega

variable {R : Type*} [CommRing R]
def forwardGap (g : GapIndex n) : Vertex n (Cell n) → R :=
  Pi.single (levelNode g.1 g.2.succ) 1-Pi.single (levelNode g.1 g.2.castSucc) 1

def forwardCoord : (Vertex n (Cell n) → R) →ₗ[R] (GapIndex n → R) :=
  LinearMap.pi fun g => ∑ a : Vertex n (Cell n), if afterGap g a then LinearMap.proj a else 0

lemma forwardCoord_apply (m : Vertex n (Cell n) → R) (g : GapIndex n) :
    forwardCoord m g=∑a,if afterGap g a then m a else 0 := by
  simp only [forwardCoord,LinearMap.pi_apply,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> rfl

lemma forwardCoord_single (a : Vertex n (Cell n)) (r : R) (g : GapIndex n) :
    forwardCoord (Pi.single a r) g=if afterGap g a then r else 0 := by
  rw [forwardCoord_apply,Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

lemma forwardCoord_gap (g : GapIndex n) :
    forwardCoord (forwardGap (R:=R) g)=Pi.single g 1 := by
  ext f
  rw [forwardGap,map_sub,Pi.sub_apply,forwardCoord_single,forwardCoord_single]
  simp only [afterGap_node,Fin.val_succ,Fin.val_castSucc,Pi.single_apply]
  by_cases hlev : f.1=g.1
  · simp only [lt_self_iff_false,false_or,hlev,true_and]
    have heq : f=g ↔ f.2.val=g.2.val := by
      constructor
      · intro h; subst f; rfl
      · intro h
        cases f with | mk i fi =>
          cases g with | mk j gj =>
            dsimp only at hlev
            subst j
            have hh:fi=gj:=Fin.ext h
            subst gj
            rfl
    simp only [heq]
    split_ifs <;> simp_all <;> omega
  · have heq : f≠g := by intro h; exact hlev (congrArg Sigma.fst h)
    simp only [hlev,false_and,or_false,ite_eq_right heq,sub_self]

def forwardRoots : (GapIndex n → R) →ₗ[R] (Vertex n (Cell n) → R) :=
  ∑ g, (LinearMap.proj g).smulRight (forwardGap g)
lemma forwardRoots_apply (c : GapIndex n → R) :
    forwardRoots c=∑g,c g • forwardGap g := by
  simp [forwardRoots,LinearMap.sum_apply,LinearMap.smulRight_apply]

@[simp] lemma forwardCoord_roots (c : GapIndex n → R) : forwardCoord (forwardRoots c)=c := by
  rw [forwardRoots_apply,map_sum]
  simp only [map_smul,forwardCoord_gap]
  ext g
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  rw [Finset.sum_eq_single g]
  · simp
  · intro f _ hf
    simp [Ne.symm hf]
  · simp

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularGapOrthogonality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ}

lemma phaseEarlier_trans {a b c : Cell n} (hab : phaseEarlier a b) (hbc : phaseEarlier b c) :
    phaseEarlier a c := by
  unfold phaseEarlier at *
  rcases hab with hab|⟨hab,hab'⟩ <;> rcases hbc with hbc|⟨hbc,hbc'⟩
  · left; omega
  · left; omega
  · left; omega
  · right; exact ⟨hab.trans hbc,lt_trans hab' hbc'⟩

def phaseLE (a b : Cell n) : Prop := phaseEarlier a b ∨ a=b
instance instDecidableRelCellPhaseLE : DecidableRel (@phaseLE n) := fun _ _=>inferInstanceAs (Decidable (_ ∨ _))
instance instIsTransCellPhaseLE : IsTrans (Cell n) phaseLE where
  trans a b c hab hbc := by
    rcases hab with hab|rfl
    · rcases hbc with hbc|rfl
      · exact Or.inl (phaseEarlier_trans hab hbc)
      · exact Or.inl hab
    · exact hbc
instance instAntisymmCellPhaseLE : Std.Antisymm (@phaseLE n) where
  antisymm a b hab hba := by
    rcases hab with hab|h
    · rcases hba with hba|h
      · exact (phaseEarlier_asymm hab hba).elim
      · exact h.symm
    · exact h
instance instTotalCellPhaseLE : Std.Total (@phaseLE n) where
  total a b := by
    rcases phaseEarlier_trichotomy a b with h|h|h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)

def phaseCycle (n : ℕ) : List (Cell n) := Finset.univ.sort phaseLE
@[simp] lemma mem_phaseCycle (b : Cell n) : b∈phaseCycle n := by simp [phaseCycle]
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_TriangularLevelQueues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ}

def levelQueue (q : List (Cell n)) (i : Fin n) : List (Cell n) := q.filter (fun b=>decide (b.1=i))

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.ForwardChain
open ElementaryPositivity.QuantumTorus
variable {M : Type*} [AddCommGroup M]

def gaps (a : M) : List M → M → List M
  | [],c => [c-a]
  | b::bs,c => (b-a)::gaps b bs c

variable (Ω : M →+ M →+ ℤ) (p : M)
def positiveMutate (r : M) : M := r + max (-Ω p r) 0 • p

end ElementaryPositivity.ForwardChain

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_RootMutationInventory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)

def rootMutation (p r : M) : M :=
  if r=p then -p else ForwardChain.positiveMutate Ω p r

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_QuantumTorus_NearCutMutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k:Module.Dual ℝ E) (H:∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance nearCutMutationRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ForwardInventoryRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus
open Classical
noncomputable section
variable {n : ℕ} {M : Type*} [AddCommGroup M]

def levelGaps (d : Fin (n+1) → M) (w : Cell n → M) (q : List (Cell n)) (i : Fin n) : List M :=
  ForwardChain.gaps (d i.castSucc) ((levelQueue q i).map w) (d i.succ)
def forwardInventory (d : Fin (n+1) → M) (w : Cell n → M) (q : List (Cell n)) : List M :=
  (List.finRange n).flatMap (levelGaps d w q)

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.QuantumTorus
open Classical
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]

def pivotMap (pc:I) (a:I → ℝ) : (I → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun d i:=if i=pc then -d pc+∑j∈Finset.univ.erase pc,a j*d j else d i
  map_add' x y:=by
    ext i
    by_cases hi:i=pc
    · subst i; simp only [ite_true, if_true,Pi.add_apply,neg_add,mul_add,Finset.sum_add_distrib] <;> ring
    · simp [hi]
  map_smul' r x:=by
    ext i
    by_cases hi:i=pc
    · subst i
      simp only [ite_true, if_true,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,mul_add,mul_neg,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    · simp [hi]

lemma pivot_involutive (pc:I) (a:I → ℝ) : Function.Involutive (pivotMap pc a) := by
  intro d
  ext i
  by_cases hi:i=pc
  · subst i
    simp only [pivotMap,LinearMap.coe_mk,AddHom.coe_mk,ite_true, if_true]
    have hh:(∑j∈Finset.univ.erase pc,a j*(if j=pc then -d pc+∑k∈Finset.univ.erase pc,a k*d k else d j))=
        ∑j∈Finset.univ.erase pc,a j*d j:=by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_right (Finset.mem_erase.mp hj).1]
    rw [hh]; ring
  · simp [pivotMap,hi]

lemma pivot_single (pc i:I) (a:I → ℝ) :
    pivotMap pc a (Pi.single i 1)=if i=pc then -Pi.single pc 1 else Pi.single i 1+a i • Pi.single pc 1 := by
  ext j
  by_cases hip:i=pc
  · subst i
    simp only [pivotMap,LinearMap.coe_mk,AddHom.coe_mk,ite_true, if_true]
    have hs:(∑k∈Finset.univ.erase pc,a k*(Pi.single pc 1:I → ℝ) k)=0:=by
      apply Finset.sum_eq_zero
      intro k hk
      simp [Ne.symm (Finset.mem_erase.mp hk).1]
    rw [hs]
    by_cases hj:j=pc
    · subst j; simp
    · simp [hj]
  · simp only [pivotMap,LinearMap.coe_mk,AddHom.coe_mk,ite_eq_right hip]
    have hs:(∑k∈Finset.univ.erase pc,a k*(Pi.single i 1:I → ℝ) k)=a i:=by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk; simp [Ne.symm hk]
      · simp [hip]
    rw [hs]
    by_cases hj:j=pc
    · subst j; simp [Ne.symm hip]
    · simp [hj,Pi.single_apply]

variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)
lemma mutatedRoots_realIndependent (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) :
    LinearIndependent ℝ (fun i=>e (simpleRoot (mutatedRoots Ω C pc) i)) := by
  obtain ⟨D,hD⟩:=realRootCoordinates_exists C e hC
  let a:I → ℝ:=fun i=>(max 0 (-mutationPairing Ω C pc i):ℤ)
  have hmap (i:I) : D (e (simpleRoot (mutatedRoots Ω C pc) i))=
      pivotMap pc a (Pi.single i 1) := by
    rw [pivot_single]
    by_cases hi:i=pc
    · subst i
      rw [ite_eq_left rfl,mutatedRoot_p,map_neg,map_neg,real_coordinate_simple C e D hD]
    · rw [ite_eq_right hi,mutatedRoot_off Ω C pc i hi,map_add,map_zsmul,map_add,map_zsmul,
        real_coordinate_simple C e D hD,real_coordinate_simple C e D hD]
      simp only [a,Int.cast_smul_eq_zsmul]
  have hind:LinearIndependent ℝ (fun i=>pivotMap pc a (Pi.single i 1)):=
    (Pi.linearIndependent_single_one I ℝ).map' (pivotMap pc a)
      (LinearMap.ker_eq_bot.mpr (pivot_involutive pc a).injective)
  have hd:LinearIndependent ℝ (fun i=>D (e (simpleRoot (mutatedRoots Ω C pc) i))):=by
    simpa only [hmap] using hind
  exact hd.of_comp D

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ForwardChartMutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus
open Classical
noncomputable section
variable {n:ℕ} {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]

structure FreeChart (e:M →+ E) where
  roots : (I → ℤ) →+ M
  coord : M →+ (I → ℤ)
  retract : ∀d,coord (roots d)=d
  independent : LinearIndependent ℝ (fun i=>e (simpleRoot roots i))

def FreeChart.mutate (Ω:M →+ M →+ ℤ) {e:M →+ E} (ch:FreeChart (I:=I) e) (pc:I) : FreeChart (I:=I) e where
  roots := mutatedRoots Ω ch.roots pc
  coord := mutatedCoordinates Ω ch.roots ch.coord pc
  retract := mutatedCoordinates_retraction Ω ch.roots ch.coord ch.retract pc
  independent := mutatedRoots_realIndependent Ω ch.roots pc e ch.independent

end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n : ℕ} {R : Type*} [CommRing R]

@[simp] lemma levelNode_zero (i:Fin n) : levelNode i 0=.inl i.castSucc := by
  simp [levelNode]
@[simp] lemma levelNode_last (i:Fin n) : levelNode i (Fin.last (i.val+2))=.inl i.succ := by
  simp [levelNode]
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialIncomingPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits PowerSeriesSplit
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ))
local instance instRingTorusLaurentSeriesRatVUnit_15 : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω

local instance instAddCommMonoidTorusLaurentSeriesRatVUnit_18_r16ce0b_1 : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance instAddGroupTorusLaurentSeriesRatVUnit_18_r16ce0b_1 : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
def polynomialSectionOrderBound (F:Torus LaurentRay.vUnit Ω) (r:M) : ℕ :=
  F.support.sup (fun b=>(rootOrder coord (r-b)).toNat)

def polynomialSectionIncoming (F:Torus LaurentRay.vUnit Ω) (r:M) : LaurentSeries ℚ :=
  polynomialSectionCoefficient Ω C coord (incomingCovector Ω r) F r

end
end ElementaryPositivity.QuantumTorus

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_ForwardPolynomialMutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits
open Classical
noncomputable section
variable {n:ℕ} {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (hnd:∀r≠0,∃m,Ω r m≠0)

def vertexDisplay (d:Fin (n+1) → M) (w:Cell n → M) : Vertex n (Cell n) → M := Sum.elim d w
end
end ElementaryPositivity.TriangularDynamics

end
section
namespace ElementaryPositivity.TriangularDynamics
open Classical
noncomputable section
variable {n:ℕ}

def periodBridge (L:ℕ) (c:Cell n) : Lattice n (Cell n) :=
  bridge c+(L:ℤ) • delta cellLevel c

def partialBridge (L:ℕ) (pre:List (Cell n)) (c:Cell n) : Lattice n (Cell n) :=
  bridge c+((L:ℤ)+(if c∈pre then 1 else 0)) • delta cellLevel c
@[simp] lemma partialBridge_nil (L:ℕ) : partialBridge (n:=n) L []=periodBridge L := by
  funext c
  simp [partialBridge,periodBridge]
@[simp] lemma partialBridge_cycle (L:ℕ) : partialBridge (n:=n) L (phaseCycle n)=periodBridge (L+1) := by
  funext c
  simp [partialBridge,periodBridge,Nat.cast_add]

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_RealLatticeRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.LatticeRealization
open scoped BigOperators
open TriangularDynamics
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def cast : (V → ℤ) →+ (V → ℝ) where
  toFun x i := x i
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

omit [Fintype V] [DecidableEq V] in
@[simp] lemma cast_apply (x : V → ℤ) (i : V) : cast x i=(x i:ℝ) := rfl

end ElementaryPositivity.LatticeRealization

end

end OAI
end


