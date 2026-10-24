-- Prove2me | Definitions.Def_OAIQWPB000
-- name    : OAIQWPB000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T19:54:37.336192+00:00
-- url     : https://prove2.me/theorems/b8e36408-f6fa-4548-ade2-e3d585c4fe6c
-- title:
--   OpenAI permanent border complexity split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that the border (and exact) determinantal complexity of the $m \times m$ permanent is at least $m^3/(5529600e)$ for $m \ge 1408$ (`OAI.PermanentBorder.permanent_cubic_lower_bounds`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Algebra/Determinantal` (OpenAI, *A cubic lower bound for border determinantal complexity of the permanent*, OpenAI Math Release, September 24, 2026, result family 108, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the selected coefficient polynomial (`Selector.diagonalCoefficient`, `coefficientPolynomial`, `selectorIndex`, `sectionSize`), the spectral pencil and its normalization defect (`pencilBase`, `pencilMatrix`, `normalizationDefect`, `curveCoefficientField`), and the square forms of characteristic two (`squareForm`, `halfIdeal`, `singularIdeal`). The bundle also contains the lemmas those definitions use in their bodies.
--
--   The definitions of the published statement (`permanentPolynomial`, `HasBorderDeterminant`, `HasExactDeterminant` and the rest) are not repeated: the bundle imports them from the published bundle `Def_PermanentCubic`. It imports no other bundle of this split..
--
--   Modules (some only in part): `AdjugateNormalForm`, `AffineSelectors`, `BilinearCounts`, `BorderPolars`, `BranchConductor`, `Centralizers`, `ConditionalBound`, `ConductorBounds`, `ConductorDimension`, `ConductorDuality`, `ConductorLocalization`, `CoordinateFields`, `CurveParameters`, `DegreeBounds`, `FiberDimension`, `FilteredPlane`, `GateCoefficients`, `Gates`, `GenericPolars`, `Gradients`, `HalfPolynomials`, `HomogeneousPadding`, `KernelCharts`, `LinearForms`, `Main`, `Model`, `Monogenic`, `Multigraded`, `Nilpotents`, `Normalization`, `PencilSeparability`, `PlaneHilbert`, `PointBounds`, `ProjectiveCounts`, `PunctualCharts`, `QuotientFields`, `RankTransfer`, `RegularSections`, `RowIdeals`, `SchurDifferentials`, `SchurLifts`, `Selector`, `SingularValues`, `SliceCertificates`, `SmoothSlices`, `Transcendence`, `WildParameters`.
--
--   The theorems of the development that the definitions do not need are proved in the eight solutions of this split. Seven prove the published intermediate statements: the two components `OAI.PermanentBorder.permanent_border_cubic_lower_bound` and `OAI.PermanentBorder.permanent_exact_cubic_lower_bound`, and the five results behind the border bound (`OAI.PermanentBorder.Polar.HasBorderDeterminant.smooth_lower_bound`, `OAI.PermanentBorder.HasBorderDeterminant.coefficientPolynomial`, `OAI.PermanentBorder.exists_effective_critical_bound`, `OAI.PermanentBorder.SpectralDimension.spectral_effective_bound`, `OAI.PermanentBorder.CurveFamily.half_curve_parameter_bound`). The eighth proves `OAI.PermanentBorder.permanent_cubic_lower_bounds` from the two components. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A cubic lower bound for border determinantal complexity of the permanent, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 108; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026/A-cubic-lower-bound-for-border-determinantal-complexity-of-the-permanent-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra/Determinantal at commit adc7f12

import Mathlib
import Definitions.Def_PermanentCubic

section
-- module Solutions.OAIQW_PermanentBorder.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Multigraded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

abbrev Piece (d : G) := weightedHomogeneousSubmodule K w d

abbrev componentQuotient (I : Ideal (MvPolynomial σ K)) (d : G) :=
  Piece (K := K) w d ⧸
    (I.restrictScalars K).comap (Piece (K := K) w d).subtype

def ComponentClosed (I : Ideal (MvPolynomial σ K)) : Prop :=
  ∀ p ∈ I, ∀ d, weightedHomogeneousComponent w d p ∈ I

noncomputable def componentMap {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) (d : G) :
    componentQuotient w I d →ₗ[K] componentQuotient w J d :=
  Submodule.mapQ _ _ LinearMap.id (fun _ hx => h hx)

@[simp] lemma componentMap_mk {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J)
    (d : G) (p : Piece (K := K) w d) :
    componentMap w h d (Submodule.Quotient.mk p) = Submodule.Quotient.mk p := rfl

noncomputable def mulPiece {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (d : G) :
    Piece (K := K) w (d-e) →ₗ[K] Piece (K := K) w d :=
  ((LinearMap.mulLeft K a).comp (Piece (K := K) w (d-e)).subtype).codRestrict _
    (fun p => by
      change IsWeightedHomogeneous w (a * p.val) d
      simpa only [add_sub_cancel] using ha.mul p.property)

@[simp] lemma mulPiece_val {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (d : G) (p : Piece (K := K) w (d-e)) :
    (mulPiece w ha d p).val = a*p.val := rfl

noncomputable def componentMul {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (I J : Ideal (MvPolynomial σ K))
    (h : ∀ p ∈ I, a*p ∈ J) (d : G) :
    componentQuotient w I (d-e) →ₗ[K] componentQuotient w J d :=
  Submodule.mapQ _ _ (mulPiece w ha d) (fun p hp => h p.val hp)

@[simp] lemma componentMul_mk {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (I J : Ideal (MvPolynomial σ K))
    (h : ∀ p ∈ I, a*p ∈ J) (d : G) (p : Piece (K := K) w (d-e)) :
    componentMul w ha I J h d (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (mulPiece w ha d p) := rfl

structure FactorPair where
  left : MvPolynomial σ K
  right : MvPolynomial σ K
  leftDegree : G
  rightDegree : G
  left_homogeneous : left.IsWeightedHomogeneous w leftDegree
  right_homogeneous : right.IsWeightedHomogeneous w rightDegree

noncomputable def productIdeal : List (FactorPair (K := K) w) → Ideal (MvPolynomial σ K)
  | [] => ⊥
  | q :: qs => Ideal.span {q.left*q.right} ⊔ productIdeal qs

noncomputable def splitBound (I : Ideal (MvPolynomial σ K)) (d : G) :
    List (FactorPair (K := K) w) → ℕ
  | [] => Module.finrank K (componentQuotient w I d)
  | q :: qs => splitBound (I ⊔ Ideal.span {q.left}) d qs +
      splitBound (I ⊔ Ideal.span {q.right}) (d-q.leftDegree) qs

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section Blocks
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

noncomputable def blockWeight (group : σ → ι) (v : σ) : ι → ℤ :=
  Pi.single (group v) 1

end Blocks
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearLeaves
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

noncomputable def blockExponent (group : σ → ι) (m : σ →₀ ℕ) (j : ι) : ℕ :=
  ∑ v ∈ Finset.univ.filter (group · = j), m v

noncomputable def componentEmbed (group : σ → ι) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℤ) : componentQuotient (blockWeight group) I d →ₗ[K]
      (MvPolynomial σ K ⧸ I) :=
  Submodule.liftQ _ ((Ideal.Quotient.mkₐ K I).toLinearMap.comp
    (Piece (K := K) (blockWeight group) d).subtype) (by
      intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hp)

end LinearLeaves
end PermanentBorder.Multigraded

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.LinearForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearCoefficients
variable {K σ τ : Type*} [Field K] [Fintype τ]

noncomputable def linearFormMap (v : τ → σ) : (τ → K) →ₗ[K] MvPolynomial σ K :=
  ∑ t, (LinearMap.proj t).smulRight (X (v t))

lemma linearFormMap_apply (v : τ → σ) (c : τ → K) :
    linearFormMap v c = ∑ t, C (c t) * X (v t) := by
  simp [linearFormMap, smul_eq_C_mul]

noncomputable def linearCoefficientSubspace (v : τ → σ) (I : Ideal (MvPolynomial σ K)) :
    Submodule K (τ → K) := (I.restrictScalars K).comap (linearFormMap v)

end LinearCoefficients

end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section VandermondeLeaves
variable {K ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype L]

abbrev BlockVariables (a : ι → ℕ) := (j : ι) × Fin (a j + 1)

def blockVar (a : ι → ℕ) (j : ι) (h : Fin (a j+1)) : BlockVariables a := ⟨j,h⟩

noncomputable def blockLinearForm (a : ι → ℕ) (j : ι) (t : K) :
    MvPolynomial (BlockVariables a) K :=
  linearFormMap (blockVar a j) (fun h : Fin (a j+1) => t ^ h.val)

omit [Fintype ι] in
lemma blockLinearForm_homogeneous (a : ι → ℕ) (j : ι) (t : K) :
    (blockLinearForm a j t).IsWeightedHomogeneous (blockWeight (fun v : BlockVariables a => v.1))
      (Pi.single j 1) := by
  classical
  rw [blockLinearForm,linearFormMap_apply]
  apply IsWeightedHomogeneous.sum
  intro h _
  exact (isWeightedHomogeneous_X K (blockWeight (fun v : BlockVariables a => v.1)) (blockVar a j h)).C_mul _

end VandermondeLeaves
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BinaryChoices
variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

noncomputable def pieceDim (I : Ideal (MvPolynomial σ K)) (d : G) : ℕ :=
  Module.finrank K (componentQuotient w I d)

noncomputable def choiceIdeal : (qs : List (FactorPair (K := K) w)) →
    (Fin qs.length → Bool) → Ideal (MvPolynomial σ K)
  | [], _ => ⊥
  | q::qs, c => Ideal.span {if c 0 then q.right else q.left} ⊔
      choiceIdeal qs (fun i => c i.succ)

noncomputable def choiceShift : (qs : List (FactorPair (K := K) w)) →
    (Fin qs.length → Bool) → G
  | [], _ => 0
  | q::qs, c => (if c 0 then q.leftDegree else 0) + choiceShift qs (fun i => c i.succ)

end BinaryChoices
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section MixedCoefficient
variable {ι E : Type*} [Fintype E] [DecidableEq ι]

noncomputable def choiceCount (g : E → ι) : ι →₀ ℕ := ∑ e, Finsupp.single (g e) 1

noncomputable def mixedPolynomial (u v : E → ι) : MvPolynomial ι ℕ :=
  ∏ e, (X (u e) + X (v e))

end MixedCoefficient
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section HomogeneousIdealMap
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]
variable (w : σ → G) (e : E → G) (F : E → MvPolynomial σ K)
  (hF : ∀ i, (F i).IsWeightedHomogeneous w (e i))

noncomputable def homogeneousIdealMap (d : G) :
    (∀ i : E, Piece (K := K) w (d-e i)) →ₗ[K] Piece (K := K) w d :=
  ∑ i, (mulPiece w (hF i) d).comp (LinearMap.proj i)

lemma isWeightedHomogeneous_smul {p : MvPolynomial σ K} {a : G}
    (hp : p.IsWeightedHomogeneous w a) (c : K) :
    (c • p).IsWeightedHomogeneous w a := by
  simpa only [Algebra.smul_def, MvPolynomial.algebraMap_eq] using hp.C_mul c

end HomogeneousIdealMap

end PermanentBorder.Multigraded

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.PointBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Persistence
variable {C V : Type*}
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

def SimpleAt (F : C × V → V) (c : C) (x : V) : Prop :=
  (fderiv ℂ F (c,x) ∘L ContinuousLinearMap.inr ℂ C V).IsInvertible

end Persistence
end PermanentBorder.PolarAnalysis

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ProjectiveCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section BilinearPointCount
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

noncomputable def vandermondePairs (a : ι →₀ ℕ) {M : ℕ}
    (u v : Fin M → ι) (t : (Fin M × Bool) → ℂ) :
    Fin M → FactorPair (K := ℂ) (blockWeight (fun v : BlockVariables a => v.1)) :=
  fun i => { left := blockLinearForm a (u i) (t (i,false))
             right := blockLinearForm a (v i) (t (i,true))
             leftDegree := Pi.single (u i) 1
             rightDegree := Pi.single (v i) 1
             left_homogeneous := blockLinearForm_homogeneous a (u i) (t (i,false))
             right_homogeneous := blockLinearForm_homogeneous a (v i) (t (i,true)) }

end BilinearPointCount
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section ProjectiveInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]

def BlockSeparated (group : σ → ι) (x y : σ → K) : Prop :=
  ∃ v w, group v = group w ∧ x v * y w ≠ x w * y v

end ProjectiveInterpolation
end PermanentBorder.Multigraded

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.KernelCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical

abbrev Groups := Option Bool
abbrev Var (κ : Type) (n : ℕ) : Groups → Type _ :=
  Option.elim' (Option (Option κ)) (fun _ => Fin (n+1))
instance varFintype (κ : Type) [Fintype κ] (n : ℕ) : (j : Groups) → Fintype (Var κ n j)
  | none => inferInstanceAs (Fintype (Option (Option κ)))
  | some _ => inferInstanceAs (Fintype (Fin (n+1)))
abbrev Variables (κ : Type) (n : ℕ) := Σ j : Groups, Var κ n j
abbrev Equations (κ : Type) (n : ℕ) := Fin (n+1) ⊕ (Fin n ⊕ κ)

variable {κ : Type} [Fintype κ] {n : ℕ}

noncomputable def dimensions (κ : Type) [Fintype κ] (n : ℕ) : Groups →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Option.elim' (Fintype.card κ+1) (fun _ => n))

@[simp] lemma dimensions_none : dimensions κ n none = Fintype.card κ+1 := rfl
@[simp] lemma dimensions_some (b : Bool) : dimensions κ n (some b) = n := rfl

lemma var_card (j : Groups) : Fintype.card (Var κ n j) = dimensions κ n j + 1 := by
  cases j with
  | none =>
    change Fintype.card (Option (Option κ)) = Fintype.card κ + 1 + 1
    exact Fintype.card_option.trans (congrArg (fun k => k+1) Fintype.card_option)
  | some b =>
    change Fintype.card (Fin (n+1)) = n+1
    exact Fintype.card_fin _

noncomputable def variablesEquiv : Variables κ n ≃
    Multigraded.BlockVariables (dimensions κ n) :=
  Equiv.sigmaCongrRight (fun j => (Fintype.equivFin (Var κ n j)).trans
    (finCongr (var_card j)))

@[simp] lemma variablesEquiv_group (s : Variables κ n) :
    (variablesEquiv s).1 = s.1 := rfl

noncomputable def linearMatrix (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (i j : Fin (n+1)) : MvPolynomial (Variables κ n) ℂ :=
  C (A₀ i j) * X ⟨none,none⟩ + ∑ k, C (A k i j) * X ⟨none,some k⟩

noncomputable def rightEquation (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (i : Fin (n+1)) : MvPolynomial (Variables κ n) ℂ :=
  ∑ j, linearMatrix A₀ A i j * X ⟨some false,j⟩

noncomputable def leftEquation (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (j : Fin (n+1)) : MvPolynomial (Variables κ n) ℂ :=
  ∑ i, linearMatrix A₀ A i j * X ⟨some true,i⟩

noncomputable def polarEquation (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    MvPolynomial (Variables κ n) ℂ :=
  ∑ i, ∑ j, C (B i j) * X ⟨some false,j⟩ * X ⟨some true,i⟩

noncomputable def system (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (pivot : Fin (n+1)) :
    Equations κ n → MvPolynomial (Variables κ n) ℂ :=
  Sum.elim (rightEquation A₀ A)
    (Sum.elim (fun j => leftEquation A₀ A (pivot.succAbove j)) (fun k => polarEquation (B k)))

def firstGroup : Equations κ n → Groups :=
  Sum.elim (fun _ => none) (Sum.elim (fun _ => none) (fun _ => some false))
def secondGroup : Equations κ n → Groups :=
  Sum.elim (fun _ => some false) (Sum.elim (fun _ => some true) (fun _ => some true))

noncomputable def coordinates (z : Option κ → ℂ)
    (u v : Fin (n+1) → ℂ) : Variables κ n → ℂ :=
  fun s => match s with
    | ⟨none,t⟩ => t.elim 1 z
    | ⟨some false,i⟩ => u i
    | ⟨some true,i⟩ => v i

@[simp] lemma eval_linearMatrix (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) (i j : Fin (n+1)) :
    eval (coordinates z u v) (linearMatrix A₀ A i j) = A₀ i j + ∑ k, A k i j * z k := by
  simp [linearMatrix, coordinates]

@[simp] lemma eval_right (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) (i : Fin (n+1)) :
    eval (coordinates z u v) (rightEquation A₀ A i) =
      ∑ j, (A₀ i j + ∑ k, A k i j * z k) * u j := by
  simp [rightEquation, coordinates]

@[simp] lemma eval_left (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) (j : Fin (n+1)) :
    eval (coordinates z u v) (leftEquation A₀ A j) =
      ∑ i, (A₀ i j + ∑ k, A k i j * z k) * v i := by
  simp [leftEquation, coordinates]

omit [Fintype κ] in
@[simp] lemma eval_polar (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (z : Option κ → ℂ) (u v : Fin (n+1) → ℂ) :
    eval (coordinates z u v) (polarEquation B) = ∑ i, ∑ j, B i j * u j * v i := by
  simp [polarEquation, coordinates]

end PermanentBorder.KernelBilinear

namespace PermanentBorder.Multigraded
open MvPolynomial
open scoped Classical
variable {σ : Type*} [DecidableEq σ]
noncomputable def collapse (i : σ) : MvPolynomial σ ℕ →+* Polynomial ℕ :=
  eval₂Hom Polynomial.C (fun j => if j = i then Polynomial.X else 1)

end PermanentBorder.Multigraded

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def block (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  fromBlocks (Matrix.of fun _ _ => a) (Matrix.of fun _ j => β j) (Matrix.of fun i _ => γ i) E
noncomputable def right (γ : ι → ℂ) (E : Matrix ι ι ℂ) : ι → ℂ := -(E⁻¹ *ᵥ γ)
noncomputable def left (β : ι → ℂ) (E : Matrix ι ι ℂ) : ι → ℂ := -(β ᵥ* E⁻¹)
noncomputable def scalar (a : ℂ) (β γ : ι → ℂ) (E : Matrix ι ι ℂ) : ℂ :=
  a - β ⬝ᵥ (E⁻¹ *ᵥ γ)
noncomputable def normalized (u : ι → ℂ) : Unit ⊕ ι → ℂ := Sum.elim (fun _ => 1) u

end PermanentBorder.PolarAnalysis.Schur

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SchurDifferentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def auxiliaryLinear (E : Matrix ι ι ℂ) :
    ((ι → ℂ) × (ι → ℂ)) →L[ℂ] ((ι → ℂ) × (ι → ℂ)) :=
  ((E.mulVecLin.toContinuousLinearMap).comp (ContinuousLinearMap.fst ℂ _ _)).prod
    ((E.vecMulLinear.toContinuousLinearMap).comp (ContinuousLinearMap.snd ℂ _ _))

omit [DecidableEq ι] in
@[simp] theorem auxiliaryLinear_apply (E : Matrix ι ι ℂ) (w : (ι → ℂ) × (ι → ℂ)) :
    auxiliaryLinear E w = (E *ᵥ w.1, w.2 ᵥ* E) := rfl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def auxiliary (β γ : V → ι → ℂ) (E : V → Matrix ι ι ℂ)
    (z : V × ((ι → ℂ) × (ι → ℂ))) : ((ι → ℂ) × (ι → ℂ)) :=
  (γ z.1 + E z.1 *ᵥ z.2.1, β z.1 + z.2.2 ᵥ* E z.1)

noncomputable def graphKernels (β γ : V → ι → ℂ) (E : V → Matrix ι ι ℂ)
    (x : V) : ((ι → ℂ) × (ι → ℂ)) :=
  (right (γ x) (E x), left (β x) (E x))

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
section Multiplier
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

noncomputable def triangularMultiplier (c : ℂ) (d : F) : (ℂ × F) →L[ℂ] (ℂ × F) :=
  c • ContinuousLinearMap.id ℂ (ℂ × F) +
    (ContinuousLinearMap.inr ℂ ℂ F).comp ((ContinuousLinearMap.fst ℂ ℂ F).smulRight d)

@[simp] theorem triangularMultiplier_apply (c : ℂ) (d : F) (z : ℂ × F) :
    triangularMultiplier c d z = (c * z.1, c • z.2 + z.1 • d) := by
  apply Prod.ext <;> simp [triangularMultiplier]

end Multiplier
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology
variable {T V : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {κ : Type*} [Fintype κ]

noncomputable def polarPair (F : T → ℂ) (ψ : V → T) (h : κ → T) (x : V) : ℂ × (κ → ℂ) :=
  (F (ψ x), fun i => fderiv ℂ F (ψ x) (h i))

end PermanentBorder.PolarAnalysis

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SchurLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix Filter
open scoped Matrix Topology
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

noncomputable def dirMatrix (A : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ) (x h : T) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ :=
  Matrix.of fun i j => fderiv ℂ (fun y => A y i j) x h

noncomputable def kernelRemaining
    (a : T → ℂ) (β γ : T → ι → ℂ) (E : T → Matrix ι ι ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (z : (ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) : ℂ × (κ → ℂ) :=
  (a (ψ z.1) + β (ψ z.1) ⬝ᵥ z.2.1,
    fun i => normalized z.2.2 ⬝ᵥ
      (dirMatrix (fun y => block (a y) (β y) (γ y) (E y)) (ψ z.1) (h i)
        *ᵥ normalized z.2.1))

end PermanentBorder.PolarAnalysis.Schur

namespace PermanentBorder.PolarAnalysis
open Matrix
variable {I J : Type*} [Fintype I] [DecidableEq I] [Finite J]

noncomputable def dotLinear (v : I → ℂ) : (I → ℂ) →ₗ[ℂ] ℂ where
  toFun f := f ⬝ᵥ v
  map_add' := by intros; apply add_dotProduct
  map_smul' := by intros; simp [smul_dotProduct]

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def determinantMultilinear :
    ContinuousMultilinearMap ℂ (fun _ : I => I → ℂ) ℂ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open Matrix

 def unitSumOptionEquiv (α : Type*) : Unit ⊕ α ≃ Option α where
  toFun := Sum.elim (fun _ => none) some
  invFun := fun o => o.elim (Sum.inl ()) Sum.inr
  left_inv := by
    rintro (u|a)
    · cases u; rfl
    · rfl
  right_inv := by rintro (_|a) <;> rfl

noncomputable def pivotEquiv {n : ℕ} (i : Fin (n+1)) : Unit ⊕ Fin n ≃ Fin (n+1) :=
  (unitSumOptionEquiv (Fin n)).trans (finSuccEquiv' i).symm

@[simp] theorem pivotEquiv_inl {n : ℕ} (i : Fin (n+1)) :
    pivotEquiv i (Sum.inl ()) = i := rfl
@[simp] theorem pivotEquiv_inr {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    pivotEquiv i (Sum.inr j) = i.succAbove j := rfl

end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis.Schur
open Matrix
open scoped Matrix
variable {ι κ T : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [NormedAddCommGroup T] [NormedSpace ℂ T]

noncomputable def matrixKernelSystem
    (F : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (z : (ℂ × (κ → ℂ)) × ((ι → ℂ) × (ι → ℂ))) :=
  (kernelRemaining (fun y => F y (.inl ()) (.inl ()))
      (fun y j => F y (.inl ()) (.inr j)) (fun y i => F y (.inr i) (.inl ()))
      (fun y => (F y).submatrix Sum.inr Sum.inr) ψ h z,
    auxiliary (fun y j => F (ψ y) (.inl ()) (.inr j))
      (fun y i => F (ψ y) (.inr i) (.inl ()))
      (fun y => (F (ψ y)).submatrix Sum.inr Sum.inr) z)

noncomputable def matrixKernelPoint
    (F : T → Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (x : ℂ × (κ → ℂ)) :=
  (x, graphKernels (fun y j => F (ψ y) (.inl ()) (.inr j))
      (fun y i => F (ψ y) (.inr i) (.inl ()))
      (fun y => (F (ψ y)).submatrix Sum.inr Sum.inr) x)

end PermanentBorder.PolarAnalysis.Schur

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.BilinearCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.KernelBilinear
open MvPolynomial PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
abbrev ChartSpace (κ : Type) (n : ℕ) := (ℂ × (κ → ℂ)) × ((Fin n → ℂ) × (Fin n → ℂ))
noncomputable def optionProduct : (Option κ → ℂ) ≃L[ℂ] (ℂ × (κ → ℂ)) :=
  (LinearEquiv.piOptionEquivProd ℂ).toContinuousLinearEquiv
@[simp] lemma optionProduct_apply (z : Option κ → ℂ) : optionProduct z = (z none,fun i => z (some i)) := rfl
@[simp] lemma optionProduct_symm_apply (z : ℂ × (κ → ℂ)) (i : Option κ) :
    optionProduct.symm z i = i.elim z.1 z.2 := by cases i <;> rfl

@[simp] lemma pivot_symm (i : Fin (n+1)) : (pivotEquiv i).symm i = .inl () :=
  (pivotEquiv i).symm_apply_apply (.inl ())
@[simp] lemma pivot_symm_succAbove (i : Fin (n+1)) (j : Fin n) :
    (pivotEquiv i).symm (i.succAbove j) = .inr j :=
  (pivotEquiv i).symm_apply_apply (.inr j)

noncomputable def norm (i : Fin (n+1)) (z : Fin n → ℂ) : Fin (n+1) → ℂ :=
  normalized z ∘ (pivotEquiv i).symm
@[simp] lemma norm_pivot (i : Fin (n+1)) (z : Fin n → ℂ) : norm i z i = 1 := by
  change normalized z ((pivotEquiv i).symm (pivotEquiv i (.inl ()))) = 1
  simp [normalized]
@[simp] lemma norm_succAbove (i : Fin (n+1)) (z : Fin n → ℂ) (j : Fin n) :
    norm i z (i.succAbove j) = z j := by
  change normalized z ((pivotEquiv i).symm (pivotEquiv i (.inr j))) = z j
  simp [normalized]

noncomputable def chart (i r : Fin (n+1)) (z : ChartSpace κ n) : Variables κ n → ℂ :=
  coordinates (optionProduct.symm z.1) (norm i z.2.1) (norm r z.2.2)
noncomputable def base (i r : Fin (n+1)) : Groups → Variables κ n
  | none => ⟨none,none⟩
  | some false => ⟨some false,i⟩
  | some true => ⟨some true,r⟩

noncomputable def outputLinear (r : Fin (n+1)) : (Equations κ n → ℂ) ≃ₗ[ℂ] ChartSpace κ n where
  toFun y := ((y (.inl r), fun k => y (.inr (.inr k))),
    (fun j => y (.inl (r.succAbove j)), fun j => y (.inr (.inl j))))
  invFun z := Sum.elim
    (fun i => ((pivotEquiv r).symm i).elim (fun _ => z.1.1) z.2.1)
    (Sum.elim z.2.2 z.1.2)
  left_inv y := by
    funext i
    rcases i with i | j | k
    · obtain ⟨a,rfl⟩ := (pivotEquiv r).surjective i
      rcases a with u | a
      · cases u; simp
      · simp
    · rfl
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · change ((pivotEquiv r).symm (pivotEquiv r (.inl ()))).elim _ _ = _
        simp
      · rfl
    · apply Prod.ext
      · funext j
        change ((pivotEquiv r).symm (pivotEquiv r (.inr j))).elim _ _ = _
        simp
      · rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def output (r : Fin (n+1)) : (Equations κ n → ℂ) ≃L[ℂ] ChartSpace κ n :=
  (outputLinear r).toContinuousLinearEquiv

end PermanentBorder.KernelBilinear

namespace PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {σ κ J : Type} [Fintype σ] [Fintype κ] [Fintype J] {n : ℕ}

noncomputable def affine (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y : σ → ℂ) :=
  A₀ + ∑ v, y v • A v

end PermanentBorder.KernelBilinear

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.RegularSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
section Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι]

noncomputable def linear (l : Option ι → R) : MvPolynomial (Option ι) R :=
  ∑ j, C (l j) * X j

noncomputable def normalized (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    Option ι → MvPolynomial (Option ι) R := Option.elim' (linear l - 1) H

noncomputable def square (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    Matrix (Option ι) (Option ι) (MvPolynomial (Option ι) R) :=
  fun i j => match i with | none => C (l j) | some k => pderiv j (H k)

noncomputable def bad (H : ι → MvPolynomial (Option ι) R) (l : Option ι → R) :
    Option ι → MvPolynomial (Option ι) R := Option.elim' (linear l * (square H l).det) H

def degrees (e : ι → ℕ) : Option ι → ℕ := Option.elim' (1 + ∑ i, (e i - 1)) e

lemma eval_linear (l y : Option ι → R) : eval y (linear l) = ∑ j, l j * y j := by
  simp [linear]

end Algebra
section Good
variable {K ι : Type*} [Field K] [Fintype ι]

def Good (H : ι → MvPolynomial (Option ι) K) (l : Option ι → K) : Prop :=
  ∀ y : Option ι → K, y ≠ 0 → (∀ i, eval y (H i) = 0) →
    eval y (linear l) ≠ 0 ∧ (square H l |>.map (eval y)).det ≠ 0

end Good
end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

noncomputable def powers (e : ι → ℕ) : ι → MvPolynomial (Option ι) ℂ :=
  fun i => X (some i) ^ e i - X none ^ e i
noncomputable def coordinate : Option ι → ℂ := Pi.single none 1

lemma eval_coordinate (y : Option ι → ℂ) : eval y (linear (coordinate (ι := ι))) = y none := by
  simp [linear, coordinate, Pi.single_apply]

def Roots (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ) :=
  {y : Option ι → ℂ // (∀ i, eval y (H i) = 0) ∧ eval y (linear l) = 1}

noncomputable def powersRootsEquiv (e : ι → ℕ) :
    Roots (powers e) coordinate ≃ (∀ i, {z : ℂ // z ^ e i = 1}) where
  toFun y i := ⟨y.val (some i), by
    have h0 : y.val none = 1 := by simpa only [eval_coordinate] using y.property.2
    simpa [powers, h0, sub_eq_zero] using y.property.1 i⟩
  invFun z := ⟨Option.elim' 1 (fun i => (z i).val), by
    constructor
    · intro i
      simp [powers, (z i).property]
    · simp only [eval_coordinate, Option.elim'_none]⟩
  left_inv y := by
    apply Subtype.ext
    funext j
    cases j with
    | none =>
      have h0 : y.val none = 1 := by simpa only [eval_coordinate] using y.property.2
      exact h0.symm
    | some i => rfl
  right_inv z := by funext i; rfl

end PermanentBorder.CI

namespace PermanentBorder.CI
open MvPolynomial
section
variable {σ : Type*} [Fintype σ]

noncomputable def polynomialDerivative (p : MvPolynomial σ ℂ) (x : σ → ℂ) :
    (σ → ℂ) →L[ℂ] ℂ :=
  ∑ i, MvPolynomial.eval x (pderiv i p) • ContinuousLinearMap.proj i

@[simp] lemma polynomialDerivative_apply (p : MvPolynomial σ ℂ) (x v : σ → ℂ) :
    polynomialDerivative p x v = ∑ i, MvPolynomial.eval x (pderiv i p) * v i := by
  classical
  simp [polynomialDerivative]

noncomputable def jacobian (P : σ → MvPolynomial σ ℂ) (x : σ → ℂ) : Matrix σ σ ℂ :=
  fun i j => eval x (pderiv j (P i))

end
end PermanentBorder.CI

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SmoothSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

noncomputable def linearEval (l : Option ι → ℂ) : (Option ι → ℂ) →ₗ[ℂ] ℂ :=
  { toFun := fun y => eval y (linear l)
    map_add' := by intro x y; simp [eval_linear, mul_add, Finset.sum_add_distrib]
    map_smul' := by intro c y; simp [eval_linear, Finset.mul_sum, mul_left_comm, mul_add] }

@[simp] lemma linearEval_apply (l y : Option ι → ℂ) :
    linearEval l y = eval y (linear l) := by
  rfl

abbrev FamilyRoots (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (s : Set ℂ) :=
  {z : s × (Option ι → ℂ) // (∀ i, eval z.2 (H z.1.val i) = 0) ∧
    eval z.2 (linear (l z.1.val)) = 1}

def familyProjection (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (s : Set ℂ) : FamilyRoots H l s → s := fun z => z.val.1

noncomputable def familyFiberEquiv (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (s : Set ℂ) (t : s) :
    (familyProjection H l s ⁻¹' {t}) ≃ Roots (H t.val) (l t.val) where
  toFun z := ⟨z.val.val.2, by
    have ht : z.val.val.1 = t := z.property
    simpa only [← ht] using z.val.property⟩
  invFun y := ⟨⟨(t,y.val),y.property⟩,rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext z.property.symm rfl
  right_inv _ := rfl

end PermanentBorder.CI

namespace PermanentBorder.SliceParameters
open MvPolynomial

abbrev DegreeIndex (σ : Type*) (d : ℤ) := {s : σ →₀ ℕ // (s.degree : ℤ) = d}

instance degreeIndex_finite {σ : Type*} [Finite σ] (d : ℤ) : Finite (DegreeIndex σ d) := by
  apply Set.Finite.to_subtype
  apply (Finsupp.finite_of_degree_le d.toNat).subset
  intro s hs
  change s.degree ≤ d.toNat
  rw [← hs]
  simp

noncomputable instance degreeIndex_fintype {σ : Type*} [Finite σ] (d : ℤ) :
    Fintype (DegreeIndex σ d) := Fintype.ofFinite _

lemma intWeight_degree {σ : Type*} (s : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) s = (s.degree : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]

lemma homogeneous_intWeight {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) :
    f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d := by
  intro s hs
  rw [intWeight_degree]
  have h : s.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf hs
  rw [h]

lemma homogeneous_sum_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    {f : MvPolynomial σ K} {d : ℤ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d) :
    f = ∑ s : DegreeIndex σ d, monomial s.val (f.coeff s.val) := by
  classical
  ext t
  rw [coeff_sum]
  by_cases ht : (t.degree : ℤ) = d
  · rw [Finset.sum_eq_single (⟨t,ht⟩ : DegreeIndex σ d)]
    · simp
    · intro s _ hs
      have he : s.val ≠ t := fun h => hs (Subtype.ext h)
      simp [coeff_monomial, he]
    · simp
  · have hz : f.coeff t = 0 := by
      by_contra hn
      exact ht (intWeight_degree t ▸ hf hn)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro s _
    have he : s.val ≠ t := fun h => ht (h ▸ s.property)
    simp [coeff_monomial, he]

lemma coeff_sum_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    (d : ℤ) (b : DegreeIndex σ d → K) (s : DegreeIndex σ d) :
    (∑ t : DegreeIndex σ d, monomial t.val (b t)).coeff s.val = b s := by
  classical
  rw [coeff_sum, Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    have he : t.val ≠ s.val := fun h => ht (Subtype.ext h)
    simp [coeff_monomial, he]
  · simp

lemma sum_degree_homogeneous {K σ : Type*} [CommSemiring K] [Finite σ]
    (d : ℤ) (b : DegreeIndex σ d → K) :
    (∑ t : DegreeIndex σ d, monomial t.val (b t)).IsWeightedHomogeneous
      (fun _ : σ => (1 : ℤ)) d := by
  apply IsWeightedHomogeneous.sum
  intro t _
  exact isWeightedHomogeneous_monomial _ _ _ ((intWeight_degree t.val).trans t.property)

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

noncomputable def macaulayMatrix (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ) :
    Matrix (DegreeIndex σ D) (Σ i : ι, DegreeIndex σ (D-e i)) K :=
  fun s t => (F t.1 * monomial t.2.val 1).coeff s.val

noncomputable def macaulayCombination (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) : MvPolynomial σ K :=
  ∑ t, b t • (F t.1 * monomial t.2.val 1)

end Matrix

end PermanentBorder.SliceParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SliceCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CI
open MvPolynomial PermanentBorder.SliceParameters
open scoped Classical
variable {ι : Type*} [Fintype ι]

noncomputable def Hline (H0 H1 : ι → MvPolynomial (Option ι) ℂ) :
    ι → MvPolynomial (Option ι) (Polynomial ℂ) := fun i =>
  map Polynomial.C (H0 i) + C Polynomial.X * (map Polynomial.C (H1 i) - map Polynomial.C (H0 i))
noncomputable def lline (l0 l1 : Option ι → ℂ) : Option ι → Polynomial ℂ := fun j =>
  Polynomial.C (l0 j) + Polynomial.X * (Polynomial.C (l1 j) - Polynomial.C (l0 j))
noncomputable def Htime (H0 H1 : ι → MvPolynomial (Option ι) ℂ) (t : ℂ) :
    ι → MvPolynomial (Option ι) ℂ := fun i => H0 i + C t * (H1 i - H0 i)
noncomputable def ltime (l0 l1 : Option ι → ℂ) (t : ℂ) : Option ι → ℂ := fun j =>
  l0 j + t * (l1 j - l0 j)

omit [Fintype ι] in
@[simp] lemma Htime_zero (H0 H1 : ι → MvPolynomial (Option ι) ℂ) : Htime H0 H1 0 = H0 := by
  funext i; simp [Htime]
omit [Fintype ι] in
@[simp] lemma Htime_one (H0 H1 : ι → MvPolynomial (Option ι) ℂ) : Htime H0 H1 1 = H1 := by
  funext i; simp [Htime]
omit [Fintype ι] in
@[simp] lemma ltime_zero (l0 l1 : Option ι → ℂ) : ltime l0 l1 0 = l0 := by
  funext i; simp [ltime]
omit [Fintype ι] in
@[simp] lemma ltime_one (l0 l1 : Option ι → ℂ) : ltime l0 l1 1 = l1 := by
  funext i; simp [ltime]

end PermanentBorder.CI

namespace PermanentBorder.Polar
open MvPolynomial
open scoped TensorProduct

variable {K R L : Type*} [CommRing K] [CommRing R] [CommRing L]
  [Algebra K R] [Algebra K L] [Algebra R L] [IsScalarTower K R L]

noncomputable def extendDerivation [Algebra.FormallyEtale R L]
    (D : Derivation K R L) : Derivation K L L :=
  ((D.liftKaehlerDifferential.liftBaseChange L).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K R L).symm.toLinearMap).compDer
      (KaehlerDifferential.D K L)

section Generic
universe u v
variable (K : Type u) [Field K] [CharZero K] (ι : Type v)

abbrev GenericField := AlgebraicClosure (FractionRing (MvPolynomial ι K))

noncomputable def genericParameter (i : ι) : GenericField K ι :=
  algebraMap (MvPolynomial ι K) (GenericField K ι) (X i)

lemma generic_formallyEtale :
    Algebra.FormallyEtale (MvPolynomial ι K) (GenericField K ι) := by
  let R := MvPolynomial ι K
  let Q := FractionRing R
  have : Algebra.FormallyEtale R Q :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have : Algebra.FormallyEtale Q (GenericField K ι) :=
    Algebra.FormallyEtale.of_isSeparable Q (GenericField K ι)
  exact Algebra.FormallyEtale.comp R Q (GenericField K ι)

noncomputable def parameterDerivation (i : ι) :
    Derivation K (GenericField K ι) (GenericField K ι) := by
  classical
  letI := generic_formallyEtale K ι
  exact extendDerivation (MvPolynomial.mkDerivation K (Pi.single i 1))

end Generic

end PermanentBorder.Polar

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.GenericPolars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.Polar
open MvPolynomial

section Parametric
variable {K L σ τ : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype σ] [Fintype τ]

noncomputable def polarValue (w : τ → σ → L) (f : MvPolynomial σ K)
    (y : σ → L) (i : τ) : L := ∑ j, w i j * aeval y (pderiv j f)

noncomputable def polarGradient (w : τ → σ → L) (f : MvPolynomial σ K)
    (y : σ → L) (i : τ) (j : σ) : L :=
  ∑ k, w i k * aeval y (pderiv j (pderiv k f))

end Parametric
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Square
variable {K L τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype τ]
abbrev PolarVars (τ : Type*) := Option (Option τ)

noncomputable def squareJacobian (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    (f : MvPolynomial (PolarVars τ) K) (y : PolarVars τ → L) :
    Matrix (PolarVars τ) (PolarVars τ) L := fun i j => match i with
  | none => aeval y (pderiv j f)
  | some none => l j
  | some (some i) => polarGradient w f y i j

end Square

section GenericSquare
variable {K τ : Type*} [Field K] [CharZero K] [Fintype τ] [DecidableEq τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

noncomputable def genericDirections : τ → PolarVars τ → E :=
  fun i j => genericParameter K P (some i,j)
noncomputable def genericLinear : PolarVars τ → E :=
  fun j => genericParameter K P (none,j)

end GenericSquare
end PermanentBorder.Polar
namespace PermanentBorder.Polar
open MvPolynomial Matrix

section Polynomials
variable {R σ τ : Type*} [CommRing R] [Fintype σ] [Fintype τ]

noncomputable def polarPolynomial (w : τ → σ → R) (f : MvPolynomial σ R) (i : τ) :
    MvPolynomial σ R := ∑ j, C (w i j) * pderiv j f

noncomputable def linearPolynomial (l : σ → R) : MvPolynomial σ R :=
  ∑ j, C (l j) * X j

noncomputable def squarePolynomial (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    (f : MvPolynomial (PolarVars τ) R) :
    Matrix (PolarVars τ) (PolarVars τ) (MvPolynomial (PolarVars τ) R) :=
  fun i j => match i with
    | none => pderiv j f
    | some none => C (l j)
    | some (some i) => pderiv j (polarPolynomial w f i)

def squareDegrees (τ : Type*) (r : ℕ) : PolarVars τ → ℕ := fun i => match i with
  | none => r-1
  | some none => 0
  | some (some _) => r-1-1

noncomputable def badPolarSystem (w : τ → PolarVars τ → R) (l : PolarVars τ → R)
    (f : MvPolynomial (PolarVars τ) R) : PolarVars τ → MvPolynomial (PolarVars τ) R := by
  classical
  exact fun i => match i with
    | none => f
    | some none => linearPolynomial l * (squarePolynomial w l f).det
    | some (some i) => polarPolynomial w f i

def badPolarDegrees (τ : Type*) [Fintype τ] (r : ℕ) : PolarVars τ → ℕ :=
  fun i => match i with
    | none => r
    | some none => 1 + ∑ i, squareDegrees τ r i
    | some (some _) => r-1

end Polynomials

end PermanentBorder.Polar

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.RankTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters

section Generic
variable {K τ : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Fintype τ]
local notation "P" => (Option τ × PolarVars τ)

noncomputable def universalBadPolar (f : MvPolynomial (PolarVars τ) K) :
    PolarVars τ → MvPolynomial (PolarVars τ) (MvPolynomial P K) :=
  badPolarSystem (fun i j => X (some i,j)) (fun j => X (none,j)) (map C f)

end Generic
end PermanentBorder.Polar

namespace PermanentBorder.Polar
open MvPolynomial Matrix PermanentBorder.SliceParameters
open scoped Classical
variable {τ : Type*} [Fintype τ]

noncomputable def hypersurfacePolars (w : τ → PolarVars τ → ℂ)
    (f : MvPolynomial (PolarVars τ) ℂ) : Option τ → MvPolynomial (PolarVars τ) ℂ :=
  Option.elim' f (polarPolynomial w f)

def hypersurfaceDegrees (r : ℕ) : Option τ → ℕ := Option.elim' r (fun _ => r-1)

def swapFirstRows : Equiv.Perm (PolarVars τ) where
  toFun := Option.elim' (some none) (Option.elim' none (fun i => some (some i)))
  invFun := Option.elim' (some none) (Option.elim' none (fun i => some (some i)))
  left_inv := by rintro (_ | (_ | i)) <;> rfl
  right_inv := by rintro (_ | (_ | i)) <;> rfl

end PermanentBorder.Polar

namespace PermanentBorder.Polar
open scoped Classical
variable {ι : Type*} [Fintype ι]

noncomputable def coordinateSplit (l : Option ι → ℂ) (h : l none ≠ 0) :
    (Option ι → ℂ) ≃ₗ[ℂ] (Option ι → ℂ) where
  toFun y := Option.elim' (∑ j, l j * y j) (fun i => y (some i))
  invFun z := Option.elim' ((z none - ∑ i, l (some i) * z (some i)) / l none)
    (fun i => z (some i))
  left_inv y := by
    funext i
    cases i with
    | none => simp only [Option.elim'_none, Option.elim'_some, Fintype.sum_option]
              field_simp
              ring
    | some i => rfl
  right_inv z := by
    funext i
    cases i with
    | none => simp only [Option.elim'_none, Option.elim'_some, Fintype.sum_option]
              field_simp
              ring
    | some i => rfl
  map_add' y z := by
    funext i
    cases i <;> simp [mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    funext i
    cases i with
    | none =>
      change (∑ j, l j * (c * y j)) = c * ∑ j, l j * y j
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    | some i => rfl

noncomputable def optionInsert : (ι → ℂ) →L[ℂ] (Option ι → ℂ) :=
  ContinuousLinearMap.pi (fun i => match i with
    | none => 0
    | some j => ContinuousLinearMap.proj j)

omit [Fintype ι] in
@[simp] lemma optionInsert_none (v : ι → ℂ) : optionInsert v none = 0 := rfl
omit [Fintype ι] in
@[simp] lemma optionInsert_some (v : ι → ℂ) (i : ι) : optionInsert v (some i) = v i := rfl

noncomputable def affineNormChart
    (e : (Option ι → ℂ) ≃L[ℂ] (Option ι → ℂ)) (z : ι → ℂ) : Option ι → ℂ :=
  e.symm (Option.elim' 1 z)

end PermanentBorder.Polar

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder
open MvPolynomial Filter
open scoped Topology

section FixedCoefficientSpace
variable {σ τ : Type*} [Fintype σ]

noncomputable def exponentCube (n : ℕ) : Finset (σ →₀ ℕ) :=
  by
    classical
    exact Finset.Iic (Finsupp.equivFunOnFinite.symm (fun _ : σ => n))

@[simp] theorem mem_exponentCube (n : ℕ) (d : σ →₀ ℕ) :
    d ∈ exponentCube (σ := σ) n ↔ ∀ i, d i ≤ n := by
  classical
  simp only [exponentCube, Finset.mem_Iic, Finsupp.le_def]
  rfl

end FixedCoefficientSpace

section AffineSubstitution
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def affineSubstitution (b : σ → ℂ) (B : σ → τ → ℂ) :
    Poly σ →ₐ[ℂ] Poly τ :=
  MvPolynomial.aeval (fun v => C (b v) + ∑ w : τ, C (B v w) * X w)

end AffineSubstitution
end PermanentBorder

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.BorderPolars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PolarAnalysis
open MvPolynomial Filter
open scoped Topology

section PolynomialSystem
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def polynomialSystem (L : τ → Poly σ →ₗ[ℂ] Poly τ)
    (P : Poly σ) (x : τ → ℂ) : τ → ℂ := fun i => MvPolynomial.eval x (L i P)

noncomputable def coefficientSystem (n : ℕ) (L : τ → Poly σ →ₗ[ℂ] Poly τ)
    (u : ((exponentCube (σ := σ) n) → ℂ) × (τ → ℂ)) : τ → ℂ :=
  fun i => ∑ d : exponentCube (σ := σ) n,
    u.1 d * MvPolynomial.eval u.2 (L i (monomial d.val 1))

def SimplePolynomialZero (L : τ → Poly σ →ₗ[ℂ] Poly τ) (P : Poly σ) (x : τ → ℂ) :=
  polynomialSystem L P x = 0 ∧ (fderiv ℂ (polynomialSystem L P) x).IsInvertible

end PolynomialSystem
end PermanentBorder.PolarAnalysis
namespace PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

noncomputable def affineChartSubstitution
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) :
    Poly (PolarVars τ) →ₐ[ℂ] Poly (Option τ) :=
  affineSubstitution (fun j => e.symm (Pi.single none 1) j)
    (fun j i => e.symm (Pi.single (some i) 1) j)

noncomputable def polarOperator (w : τ → PolarVars τ → ℂ) (i : τ) :
    Poly (PolarVars τ) →ₗ[ℂ] Poly (PolarVars τ) :=
  ∑ j, w i j • (pderiv j).toLinearMap

noncomputable def affinePolarOperators (w : τ → PolarVars τ → ℂ)
    (e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ)) :
    Option τ → Poly (PolarVars τ) →ₗ[ℂ] Poly (Option τ) :=
  Option.elim' (affineChartSubstitution e).toLinearMap
    (fun i => (affineChartSubstitution e).toLinearMap.comp (polarOperator w i))

end PermanentBorder.Polar

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Selector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]

noncomputable def allOnes (V : Type*) [Fintype V] : V →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

@[simp] theorem allOnes_apply {V : Type*} [Fintype V] (i : V) : allOnes V i = 1 := rfl

noncomputable def edgeExponent (e : n × n) : (n ⊕ n) →₀ ℕ :=
  Finsupp.single (.inl e.1) 1 + Finsupp.single (.inr e.2) 1

noncomputable def occupancy (S : Finset (n × n)) : (n ⊕ n) →₀ ℕ :=
  ∑ e ∈ S, edgeExponent e

noncomputable def permGraph (σ : Equiv.Perm n) : Finset (n × n) :=
  Finset.univ.image (fun j => (σ j,j))

@[simp] theorem mem_permGraph (σ : Equiv.Perm n) (i j : n) :
    (i,j) ∈ permGraph σ ↔ σ j = i := by
  simp [permGraph, eq_comm]

noncomputable def edgeProduct (M : Matrix n n R) : MvPolynomial (n ⊕ n) R :=
  ∏ e : n × n, (1 + monomial (edgeExponent e) (M e.1 e.2))

end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I E R : Type*} [Fintype I] [Fintype E] [DecidableEq I] [CommSemiring R]
noncomputable def graphMatrix (src dst : E → I) (w : E → R) : Matrix I I R :=
  fun i j => ∑ e, if src e = i ∧ dst e = j then w e else 0

end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {R : Type*} [CommRing R]

noncomputable def threeOnes : Fin 3 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1
noncomputable def gadgetAfterRows (a b c d : R) : MvPolynomial (Fin 3) R :=
  (1 + C a * X 0) * (1 + C b * X 1) *
    (-X 0 - X 1 + X 2 + C c) * (-X 0 - X 1 + X 2 + C d) *
    (X 0 + X 1 + X 2)

end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {R : Type*} [CommRing R]

noncomputable def gadgetH : Matrix (Fin 3) (Fin 3) R := !![-1,-1,1; -1,-1,1; 1,1,1]

noncomputable def gadgetRowEntries (c d : R) : Fin 3 → Option (Fin 3) → MvPolynomial (Fin 3) R :=
  fun i j => match j with
  | none => C (![c,d,0] i)
  | some j => C (gadgetH i j) * X j

noncomputable def gadgetNested (a b c d : R) : MvPolynomial (Fin 3) (MvPolynomial (Fin 3) R) :=
  C ((1 + C a * X 0)*(1 + C b * X 1)) *
    ∏ i, ∏ j, (1 + C (gadgetRowEntries c d i j) * X i)

noncomputable def gadgetEdges (a b c d : R) : MvPolynomial (Fin 3 ⊕ Fin 3) R :=
  (1 + C a * X (.inr 0)) * (1 + C b * X (.inr 1)) *
    ∏ i, ((1 + C (![c,d,0] i) * X (.inl i)) *
      ∏ j, (1 + C (gadgetH i j) * X (.inr j) * X (.inl i)))

end PermanentBorder.Selector

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Gates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {I J R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

noncomputable def blockExponent (d : I → J →₀ ℕ) : I × J →₀ ℕ :=
  ∑ i, (d i).mapDomain (fun j => (i,j))

end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I G E R : Type*} [Fintype E] [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] [CommRing R]

abbrev ExpandedVertex (I G : Type*) := I ⊕ (G × Fin 3)
abbrev InternalVertex (G : Type*) := G × (Fin 3 ⊕ Fin 3)
abbrev GadgetLabels := Fin 2 ⊕ (Fin 3 ⊕ (Fin 3 × Fin 3))
abbrev ExpandedLabels (E G : Type*) := E ⊕ (G × GadgetLabels)

noncomputable def baseEdges (src dst : E → I) (ω : E → R) : MvPolynomial (I ⊕ I) R :=
  ∏ e, (1 + monomial (edgeExponent (src e,dst e)) (ω e))

def vertexSplit : (ExpandedVertex I G ⊕ ExpandedVertex I G) ≃
    (InternalVertex G ⊕ (I ⊕ I)) where
  toFun
  | .inl (.inl i) => .inr (.inl i)
  | .inr (.inl i) => .inr (.inr i)
  | .inl (.inr (g,r)) => .inl (g,.inl r)
  | .inr (.inr (g,c)) => .inl (g,.inr c)
  invFun
  | .inr (.inl i) => .inl (.inl i)
  | .inr (.inr i) => .inr (.inl i)
  | .inl (g,.inl r) => .inl (.inr (g,r))
  | .inl (g,.inr c) => .inr (.inr (g,c))
  left_inv x := by rcases x with (i|⟨g,r⟩)|(i|⟨g,c⟩) <;> rfl
  right_inv x := by rcases x with ⟨g,r|c⟩|(i|j) <;> rfl

noncomputable def expandedSrc (src : E → I) (u₁ u₂ : G → I) : ExpandedLabels E G → ExpandedVertex I G
  | .inl e => .inl (src e)
  | .inr (g,.inl b) => .inl (if b=0 then u₁ g else u₂ g)
  | .inr (g,.inr (.inl r)) => .inr (g,r)
  | .inr (g,.inr (.inr (r,_))) => .inr (g,r)
noncomputable def expandedDst (dst : E → I) (v₁ v₂ : G → I) : ExpandedLabels E G → ExpandedVertex I G
  | .inl e => .inl (dst e)
  | .inr (g,.inl b) => .inr (g,b.castLE (by decide))
  | .inr (g,.inr (.inl r)) => .inl (if r=0 then v₁ g else v₂ g)
  | .inr (g,.inr (.inr (_,c))) => .inr (g,c)
noncomputable def expandedWeight (ω : E → R) (w : G → R) : ExpandedLabels E G → R
  | .inl e => ω e
  | .inr (g,.inl b) => if b=0 then -2*w g else 1
  | .inr (_,.inr (.inl r)) => if r=2 then 0 else 1
  | .inr (_,.inr (.inr (r,c))) => gadgetH r c

noncomputable def expandedMatrix (src dst : E → I) (ω : E → R) (w : G → R)
    (u₁ u₂ v₁ v₂ : G → I) : Matrix (ExpandedVertex I G) (ExpandedVertex I G) R :=
  graphMatrix (expandedSrc src u₁ u₂) (expandedDst dst v₁ v₂) (expandedWeight ω w)

noncomputable def splitPolynomial : MvPolynomial (ExpandedVertex I G ⊕ ExpandedVertex I G) R →+*
    MvPolynomial (InternalVertex G) (MvPolynomial (I ⊕ I) R) :=
  (sumRingEquiv R _ _).toRingHom.comp ((rename vertexSplit).toRingHom)

omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 @[simp] theorem splitPolynomial_C (a : R) :
    splitPolynomial (I := I) (G := G) (C a) = C (C a) := by
  simp [splitPolynomial]
omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 @[simp] theorem splitPolynomial_outer_left (i : I) :
    splitPolynomial (G := G) (X (.inl (.inl i)) : MvPolynomial _ R) = C (X (.inl i)) := by
  simp [splitPolynomial, vertexSplit]
omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 @[simp] theorem splitPolynomial_outer_right (i : I) :
    splitPolynomial (G := G) (X (.inr (.inl i)) : MvPolynomial _ R) = C (X (.inr i)) := by
  simp [splitPolynomial, vertexSplit]
omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 @[simp] theorem splitPolynomial_inner_left (g : G) (r : Fin 3) :
    splitPolynomial (I := I) (X (.inl (.inr (g,r))) : MvPolynomial _ R) = X (g,.inl r) := by
  simp [splitPolynomial, vertexSplit]
omit [Fintype I] [Fintype G] [DecidableEq I] [DecidableEq G] in
 @[simp] theorem splitPolynomial_inner_right (g : G) (c : Fin 3) :
    splitPolynomial (I := I) (X (.inr (.inr (g,c))) : MvPolynomial _ R) = X (g,.inr c) := by
  simp [splitPolynomial, vertexSplit]

end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
noncomputable def countIndex (q : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => q)
noncomputable def elementaryBoundary (a : I → R) (q : ℕ) : R :=
  (∏ i, (1 + Polynomial.C (a i)*Polynomial.X)).coeff q
noncomputable def diagonalCoefficient (M : Matrix I I R) (θ : I → R) (q : ℕ) : R :=
  ((Matrix.of fun i j => C (M i j) : Matrix I I (MvPolynomial (Fin 2) R)) +
    (Matrix.diagonal (fun i => X (0 : Fin 2) + C (θ i)*X 1) : Matrix I I (MvPolynomial (Fin 2) R))).permanent.coeff
    (countIndex q)

end PermanentBorder.Selector

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]

noncomputable def subsetExponent (s : Finset I) : I →₀ ℕ :=
  Finsupp.indicator s (fun _ _ => 1)

omit [Fintype I] in
@[simp] theorem subsetExponent_apply (s : Finset I) (i : I) :
    subsetExponent s i = if i ∈ s then 1 else 0 := by
  classical
  by_cases h : i ∈ s <;> simp [subsetExponent, h]

omit [Fintype I] in
@[simp] theorem subsetExponent_support (s : Finset I) : (subsetExponent s).support = s := by
  ext i; simp [Finsupp.mem_support_iff]

omit [Fintype I] in
@[simp] theorem subsetExponent_degree (s : Finset I) :
    (subsetExponent s).sum (fun _ m => m) = s.card := by
  simp [Finsupp.sum, subsetExponent_apply]

omit [Fintype I] in
@[simp] theorem subsetExponent_multinomial (s : Finset I) :
    (subsetExponent s).multinomial = s.card.factorial := by
  simp only [Finsupp.multinomial, Finsupp.sum, Finsupp.prod, subsetExponent_support,
    subsetExponent_apply]
  have hsum : (∑ x ∈ s, (if x ∈ s then 1 else 0)) = s.card := by simp
  have hprod : (∏ x ∈ s, (if x ∈ s then 1 else 0).factorial) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    rw [ite_eq_left hx]; rfl
  simp only [id_eq, hsum, hprod, Nat.div_one]

end PermanentBorder.Selector.Gates

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.GateCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
noncomputable def gateOuter (h : ℕ) : MvPolynomial (I ⊕ I) R :=
  rename Sum.inl ((∑ i, X i)^h) * rename Sum.inr ((∑ i, X i)^h)

noncomputable def gateCrossEntries (h : ℕ) :
    (Fin h ⊕ Fin h) → I → MvPolynomial (I ⊕ I) R :=
  fun v i => match v with
  | .inl _ => X (.inr i)
  | .inr _ => X (.inl i)

noncomputable def gateCrossEdges (h : ℕ) :
    MvPolynomial (Fin h ⊕ Fin h) (MvPolynomial (I ⊕ I) R) :=
  ∏ v, ∏ i, (1 + C (gateCrossEntries h v i) * X v)

end PermanentBorder.Selector.Gates
namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
noncomputable def pairedExponent (i : I) : I ⊕ I →₀ ℕ :=
  (Finsupp.single i 1).sumElim (Finsupp.single i 1)
end PermanentBorder.Selector.Gates

namespace PermanentBorder.Selector.Gates
open MvPolynomial
variable {A B I R : Type*} [Fintype I] [DecidableEq I] [CommSemiring R]
noncomputable def allOnes (A : Type*) [Fintype A] : A →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

def sumSquareSplit : ((A ⊕ B) ⊕ (A ⊕ B)) ≃ ((B ⊕ B) ⊕ (A ⊕ A)) where
  toFun
  | .inl (.inl i) => .inr (.inl i)
  | .inr (.inl i) => .inr (.inr i)
  | .inl (.inr j) => .inl (.inl j)
  | .inr (.inr j) => .inl (.inr j)
  invFun
  | .inr (.inl i) => .inl (.inl i)
  | .inr (.inr i) => .inr (.inl i)
  | .inl (.inl j) => .inl (.inr j)
  | .inl (.inr j) => .inr (.inr j)
  left_inv x := by rcases x with (i|j)|(i|j) <;> rfl
  right_inv x := by rcases x with (i|j)|(i|j) <;> rfl

noncomputable def fullGateEdges (a : I → R) (h : ℕ) :
    MvPolynomial ((I ⊕ Fin h) ⊕ (I ⊕ Fin h)) R :=
  (∏ i, ∏ j, (1 + X (.inl (.inl i))*X (.inr (.inr j)))) *
  (∏ j, ∏ i, (1 + X (.inl (.inr j))*X (.inr (.inl i)))) *
  ∏ i, (1 + C (a i)*X (.inl (.inl i))*X (.inr (.inl i)))

end PermanentBorder.Selector.Gates

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.AffineSelectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
abbrev SelectorOuter (I : Type*) (h : ℕ) := I ⊕ (Fin 2 × (I ⊕ Fin h))
abbrev SelectorLabels (I : Type*) (h : ℕ) := (I × I) ⊕
  (Fin 2 × ((I × Fin h) ⊕ (Fin h × I)))
abbrev SelectorGateVars (I : Type*) (h : ℕ) := Fin 2 × ((I ⊕ Fin h) ⊕ (I ⊕ Fin h))

noncomputable def selectorSrc (h : ℕ) : SelectorLabels I h → SelectorOuter I h
  | .inl (i,_) => .inl i
  | .inr (c,.inl (i,_)) => .inr (c,.inl i)
  | .inr (c,.inr (j,_)) => .inr (c,.inr j)
noncomputable def selectorDst (h : ℕ) : SelectorLabels I h → SelectorOuter I h
  | .inl (_,i) => .inl i
  | .inr (c,.inl (_,j)) => .inr (c,.inr j)
  | .inr (c,.inr (_,i)) => .inr (c,.inl i)
noncomputable def selectorBaseWeight (M : Matrix I I R) (h : ℕ) : SelectorLabels I h → R
  | .inl (i,j) => M i j
  | .inr _ => 1
noncomputable def selectorWeight (θ : I → R) (g : Fin 2 × I) : R :=
  if g.1=0 then 1 else θ g.2
noncomputable def selectorMain (h : ℕ) (g : Fin 2 × I) : SelectorOuter I h := .inl g.2
noncomputable def selectorGate (h : ℕ) (g : Fin 2 × I) : SelectorOuter I h := .inr (g.1,.inl g.2)

noncomputable def selectorMatrix (M : Matrix I I R) (θ : I → R) (h : ℕ) :=
  expandedMatrix (selectorSrc h) (selectorDst h) (selectorBaseWeight M h)
    (selectorWeight θ) (selectorMain h) (selectorGate h) (selectorMain h) (selectorGate h)

noncomputable def selectorBoundary (M : Matrix I I R) (θ : I → R) (h : ℕ) :
    MvPolynomial (SelectorOuter I h ⊕ SelectorOuter I h) R :=
  baseEdges (selectorSrc h) (selectorDst h) (selectorBaseWeight M h) *
  ∏ g : Fin 2 × I, (1 + C (selectorWeight θ g) *
    X (.inl (selectorMain h g))*X (.inl (selectorGate h g))*
    X (.inr (selectorMain h g))*X (.inr (selectorGate h g)))

def selectorSplitEquiv (h : ℕ) : (SelectorOuter I h ⊕ SelectorOuter I h) ≃
    (SelectorGateVars I h ⊕ (I ⊕ I)) where
  toFun
  | .inl (.inl i) => .inr (.inl i)
  | .inr (.inl i) => .inr (.inr i)
  | .inl (.inr (c,v)) => .inl (c,.inl v)
  | .inr (.inr (c,v)) => .inl (c,.inr v)
  invFun
  | .inr (.inl i) => .inl (.inl i)
  | .inr (.inr i) => .inr (.inl i)
  | .inl (c,.inl v) => .inl (.inr (c,v))
  | .inl (c,.inr v) => .inr (.inr (c,v))
  left_inv x := by rcases x with (i|⟨c,v⟩)|(i|⟨c,v⟩) <;> rfl
  right_inv x := by rcases x with ⟨c,v|v⟩|(i|i) <;> rfl

noncomputable def selectorSplit (h : ℕ) : MvPolynomial (SelectorOuter I h ⊕ SelectorOuter I h) R →+*
    MvPolynomial (SelectorGateVars I h) (MvPolynomial (I ⊕ I) R) :=
  (sumRingEquiv R _ _).toRingHom.comp ((rename (selectorSplitEquiv h)).toRingHom)
omit [Fintype I] [DecidableEq I] in
@[simp] theorem selectorSplit_C (h : ℕ) (r : R) : selectorSplit (I := I) h (C r) = C (C r) := by
  simp [selectorSplit]
omit [Fintype I] [DecidableEq I] in
@[simp] theorem selectorSplit_main_left (h : ℕ) (i : I) :
    selectorSplit h (X (.inl (.inl i)) : MvPolynomial _ R) = C (X (.inl i)) := by
  simp [selectorSplit, selectorSplitEquiv]
omit [Fintype I] [DecidableEq I] in
@[simp] theorem selectorSplit_main_right (h : ℕ) (i : I) :
    selectorSplit h (X (.inr (.inl i)) : MvPolynomial _ R) = C (X (.inr i)) := by
  simp [selectorSplit, selectorSplitEquiv]
omit [Fintype I] [DecidableEq I] in
@[simp] theorem selectorSplit_gate_left (h : ℕ) (c : Fin 2) (v : I ⊕ Fin h) :
    selectorSplit h (X (.inl (.inr (c,v))) : MvPolynomial _ R) = X (c,.inl v) := by
  simp [selectorSplit, selectorSplitEquiv]
omit [Fintype I] [DecidableEq I] in
@[simp] theorem selectorSplit_gate_right (h : ℕ) (c : Fin 2) (v : I ⊕ Fin h) :
    selectorSplit h (X (.inr (.inr (c,v))) : MvPolynomial _ R) = X (c,.inr v) := by
  simp [selectorSplit, selectorSplitEquiv]

noncomputable def selectorBoundaryWeight (θ : I → R) (c : Fin 2) (i : I) : MvPolynomial (I ⊕ I) R :=
  C (selectorWeight θ (c,i))*X (.inl i)*X (.inr i)

end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial
variable {I R : Type*} [Fintype I] [DecidableEq I] [CommRing R]
abbrev SelectorVertex (I : Type*) (h : ℕ) := ExpandedVertex (SelectorOuter I h) (Fin 2 × I)
noncomputable def selectorLinearEntries (M : Matrix I I R) (h : ℕ) :
    Matrix (SelectorVertex I h) (SelectorVertex I h) R
  | .inl (.inl i), .inl (.inl j) => M i j
  | _, _ => 0

end PermanentBorder.Selector
namespace PermanentBorder.Selector
open MvPolynomial
variable {I R S : Type*} [Fintype I] [DecidableEq I] [CommRing R] [CommRing S]

noncomputable def selectorCoefficientMatrix (h : ℕ) (ij : I × I) :
    Matrix (SelectorVertex I h) (SelectorVertex I h) R :=
  fun r c => if r = .inl (.inl ij.1) ∧ c = .inl (.inl ij.2) then 1 else 0

end PermanentBorder.Selector

namespace PermanentBorder
open MvPolynomial

noncomputable def coefficientPolynomial (k q : ℕ) (θ : Fin k → ℂ) : Poly (Variables k) :=
  Selector.diagonalCoefficient (Matrix.of fun i j => X (i,j)) (fun i => C (θ i)) q

noncomputable def selectorScalar (k q : ℕ) : ℂ :=
  (-2)^(2*k) * ((k-q).factorial : ℂ)^4

end PermanentBorder

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.HomogeneousPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial
variable {A B R : Type*} [Fintype A] [Fintype B] [CommSemiring R]

variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable def universalHomogeneousPencil (θ : I → R) :
    Matrix I I (MvPolynomial (Fin 2 ⊕ (I × I)) R) :=
  Matrix.of fun i j => X (.inr (i,j)) +
    if i=j then X (.inl 0) + C (θ i)*X (.inl 1) else 0

end PermanentBorder.Selector

namespace PermanentBorder.Selector
open MvPolynomial

noncomputable def integralCoefficientFamily (k q : ℕ) :
    MvPolynomial (Variables k) (MvPolynomial (Fin k) ℤ) :=
  diagonalCoefficient (Matrix.of fun i j => X (i,j)) (fun i => C (X i)) q

end PermanentBorder.Selector

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Transcendence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial
variable {K α β : Type*} [CommRing K] [Fintype β]

noncomputable def sectionForm (H : α × β → K) (i : α) : MvPolynomial β K :=
  ∑ c, C (H (i,c)) * X c

noncomputable def linearSection (H : α × β → K) :
    MvPolynomial α K →ₐ[K] MvPolynomial β K := aeval (sectionForm H)

@[simp] lemma eval_sectionForm (H : α × β → K) (y : β → K) (i : α) :
    eval y (sectionForm H i) = ∑ c, y c * H (i,c) := by
  simp [sectionForm, mul_comm]

@[simp] lemma eval_linearSection (H : α × β → K) (y : β → K) (f : MvPolynomial α K) :
    eval y (linearSection H f) = eval (fun i => ∑ c, y c * H (i,c)) f := by
  have h : (eval y).comp (linearSection H).toRingHom =
      eval (fun i => ∑ c, y c * H (i,c)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [linearSection]
    · intro i
      simp [linearSection]
  exact DFunLike.congr_fun h f

@[simp] lemma pderiv_sectionForm (H : α × β → K) (i : α) (c : β) :
    pderiv c (sectionForm H i) = C (H (i,c)) := by
  classical
  simp [sectionForm, pderiv_X, Pi.single_apply]

@[simp] lemma linearSection_X (H : α × β → K) (i : α) :
    linearSection H (X i) = sectionForm H i := aeval_X _ _

@[simp] lemma linearSection_C (H : α × β → K) (a : K) :
    linearSection H (C a) = C a := aeval_C _ _

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

noncomputable def singularSystem {R β : Type*} [CommRing R] (f : MvPolynomial β R) :
    Option β → MvPolynomial β R := fun j => match j with
    | none => f
    | some i => pderiv i f

def singularDegrees {β : Type*} (r : ℕ) : Option β → ℤ :=
  fun j => match j with
    | none => r
    | some _ => (r-1 : ℕ)

end PermanentBorder.SliceParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ConditionalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SliceParameters
open MvPolynomial

noncomputable def universalSection {σ α β : Type*} [Fintype β]
    (F : MvPolynomial α (MvPolynomial σ ℤ)) :
    MvPolynomial β (MvPolynomial (σ ⊕ (α × β)) ℤ) :=
  linearSection (fun i => X (Sum.inr i)) (map (rename (R := ℤ) (fun i : σ => (Sum.inl i : σ ⊕ (α × β)))).toRingHom F)

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial
universe u v
variable (K : Type u) [Field K] (ι : Type v)

abbrev GenericClosed := AlgebraicClosure (FractionRing (MvPolynomial ι K))

noncomputable def independentParameters : ι → GenericClosed K ι := fun i =>
  algebraMap (FractionRing (MvPolynomial ι K)) (GenericClosed K ι)
    (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (X i))

end PermanentBorder.SliceParameters

namespace PermanentBorder.Parameters

abbrev auxiliarySize (m : ℕ) := m / 11
abbrev selectorIndex (k : ℕ) := (k-1) / 3
abbrev selectorDegree (k : ℕ) := k - 2 * selectorIndex k

end PermanentBorder.Parameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ConductorDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Conductor
open Module

section Conductor
variable (B A : Type*) [CommRing B] [CommRing A] [Algebra B A]

def algebraConductor : Ideal B where
  carrier := {a | ∀ x : A, ∃ b : B, algebraMap B A b = algebraMap B A a * x}
  zero_mem' := by intro x; exact ⟨0, by simp⟩
  add_mem' := by
    intro a b ha hb x
    obtain ⟨c, hc⟩ := ha x
    obtain ⟨d, hd⟩ := hb x
    exact ⟨c+d, by simp only [map_add, hc, hd, add_mul]⟩
  smul_mem' := by
    intro a b hb x
    obtain ⟨c, hc⟩ := hb x
    exact ⟨a*c, by simp only [smul_eq_mul, map_mul, hc, mul_assoc]⟩

@[simp] theorem mem_algebraConductor (a : B) :
    a ∈ algebraConductor B A ↔
      ∀ x : A, ∃ b : B, algebraMap B A b = algebraMap B A a * x := Iff.rfl
end Conductor

section Multiplication
variable {S B A : Type*} [CommRing S] [CommRing B] [CommRing A]
  [Algebra S B] [Algebra S A] [Algebra B A] [IsScalarTower S B A]
variable (hi : Function.Injective (algebraMap B A))

noncomputable def conductorMultiplication (a : B) (ha : a ∈ algebraConductor B A) :
    A →ₗ[S] B where
  toFun x := Classical.choose (ha x)
  map_add' x y := by
    apply hi
    rw [Classical.choose_spec (ha (x+y)), map_add,
      Classical.choose_spec (ha x), Classical.choose_spec (ha y), mul_add]
  map_smul' s x := by
    apply hi
    rw [Classical.choose_spec (ha (s • x))]
    change algebraMap B A a * (s • x) =
      (IsScalarTower.toAlgHom S B A) (s • Classical.choose (ha x))
    rw [map_smul]
    change algebraMap B A a * (s • x) = s • algebraMap B A (Classical.choose (ha x))
    rw [Classical.choose_spec (ha x), mul_smul_comm]

@[simp] theorem conductorMultiplication_spec (a : B) (ha : a ∈ algebraConductor B A) (x : A) :
    algebraMap B A (conductorMultiplication (S := S) hi a ha x) = algebraMap B A a * x :=
  Classical.choose_spec (ha x)

@[simp] theorem conductorMultiplication_algebraMap (a : B)
    (ha : a ∈ algebraConductor B A) (b : B) :
    conductorMultiplication (S := S) hi a ha (algebraMap B A b) = a*b := by
  apply hi
  simp
end Multiplication

end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Module Matrix

section MonicPairing
variable {R : Type*} [CommRing R] [Nontrivial R]
variable {f : R[X]} (hf : f.Monic)

noncomputable def topRemainderCoefficient : AdjoinRoot f →ₗ[R] R :=
  (Polynomial.lcoeff R (f.natDegree-1)).comp (AdjoinRoot.modByMonicHom hf)

noncomputable def coefficientPairing : AdjoinRoot f →ₗ[R] Module.Dual R (AdjoinRoot f) :=
  (Algebra.lmul R (AdjoinRoot f)).toLinearMap.compr₂ (topRemainderCoefficient hf)

omit [Nontrivial R] in
@[simp] theorem coefficientPairing_apply (a b : AdjoinRoot f) :
    coefficientPairing hf a b = topRemainderCoefficient hf (a*b) := rfl

theorem topRemainderCoefficient_pow {l : ℕ} (hl : l < f.natDegree) :
    topRemainderCoefficient hf (AdjoinRoot.root f ^ l) =
      if f.natDegree-1 = l then 1 else 0 := by
  change (AdjoinRoot.modByMonicHom hf (AdjoinRoot.root f ^ l)).coeff _ = _
  rw [show AdjoinRoot.root f ^ l = AdjoinRoot.mk f (X ^ l) by simp]
  rw [AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hf).mpr]
  · simp [coeff_X_pow]
  · simpa only [degree_X_pow, degree_eq_natDegree hf.ne_zero, Nat.cast_lt] using hl

noncomputable def pairingMatrix : Matrix (Fin f.natDegree) (Fin f.natDegree) R :=
  LinearMap.toMatrix (AdjoinRoot.powerBasisAux' hf)
    (AdjoinRoot.powerBasisAux' hf).dualBasis (coefficientPairing hf)

omit [Nontrivial R] in
theorem pairingMatrix_apply (i j : Fin f.natDegree) :
    pairingMatrix hf i j =
      topRemainderCoefficient hf (AdjoinRoot.root f ^ ((i : ℕ) + j)) := by
  rw [pairingMatrix, LinearMap.toMatrix_apply, Basis.dualBasis_repr,
    coefficientPairing_apply]
  have hb (l : Fin f.natDegree) :
      AdjoinRoot.powerBasisAux' hf l = AdjoinRoot.root f ^ (l : ℕ) :=
    (AdjoinRoot.powerBasis' hf).basis_eq_pow l
  rw [hb, hb, ← pow_add, add_comm]

theorem pairingMatrix_reverse_det :
    ((pairingMatrix hf).submatrix id Fin.revPerm).det = 1 := by
  let A := (pairingMatrix hf).submatrix id Fin.revPerm
  have ha (i j : Fin f.natDegree) :
      A i j = topRemainderCoefficient hf
        (AdjoinRoot.root f ^ ((i : ℕ) + (f.natDegree-1-j))) := by
    simp only [A, submatrix_apply, id_eq, pairingMatrix_apply, Fin.revPerm_apply, Fin.val_rev]
    congr 2; omega
  have htri : A.IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    rw [ha, topRemainderCoefficient_pow hf (by omega)]
    rw [ite_eq_right (by omega)]
  rw [Matrix.det_of_isLowerTriangular A htri]
  have hdiag (i : Fin f.natDegree) : A i i = 1 := by
    rw [ha, topRemainderCoefficient_pow hf (by omega)]
    rw [ite_eq_left (by omega)]
  simp only [hdiag, Finset.prod_const_one]

theorem pairingMatrix_det_isUnit : IsUnit (pairingMatrix hf).det := by
  have h : IsUnit (((pairingMatrix hf).submatrix id Fin.revPerm).det) := by
    rw [pairingMatrix_reverse_det hf]
    exact isUnit_one
  rw [Matrix.det_permute'] at h
  exact isUnit_of_mul_isUnit_right h

noncomputable def coefficientPairingEquiv :
    AdjoinRoot f ≃ₗ[R] Module.Dual R (AdjoinRoot f) :=
  Matrix.toLinOfInv (AdjoinRoot.powerBasisAux' hf)
    (AdjoinRoot.powerBasisAux' hf).dualBasis
    (Matrix.mul_nonsing_inv _ (pairingMatrix_det_isUnit hf))
    (Matrix.nonsing_inv_mul _ (pairingMatrix_det_isUnit hf))

@[simp] theorem coefficientPairingEquiv_apply (a b : AdjoinRoot f) :
    coefficientPairingEquiv hf a b = topRemainderCoefficient hf (a*b) := by
  change (Matrix.toLin (AdjoinRoot.powerBasisAux' hf)
    (AdjoinRoot.powerBasisAux' hf).dualBasis (pairingMatrix hf)) a b = _
  rw [pairingMatrix, Matrix.toLin_toMatrix]
  rfl
end MonicPairing
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Module

section RootEmbedding
variable {Q L : Type*} [Field Q] [Field L] [Algebra Q L]
variable {f : Q[X]} (hf : f.Monic)

noncomputable def rootEvaluation : AdjoinRoot f →ₐ[Q] ((f.rootSet L) → L) :=
  AlgHom.pi fun x => AdjoinRoot.liftAlgHom f (Algebra.ofId Q L) x.val (aeval_eq_zero_of_mem_rootSet x.property)

@[simp] theorem rootEvaluation_mk (p : Q[X]) (x : f.rootSet L) :
    rootEvaluation (f := f) (AdjoinRoot.mk f p) x = aeval x.val p := by
  rfl

end RootEmbedding

end PermanentBorder.Conductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Conductor
open Polynomial Module
section GenericLattice
variable {S Q : Type*} [CommRing S] [IsDomain S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
variable (f : S[X])

noncomputable def genericBaseChange :
    AdjoinRoot f →ₐ[S] AdjoinRoot (f.map (algebraMap S Q)) :=
  AdjoinRoot.mapAlgHom (Algebra.ofId S Q) f (f.map (algebraMap S Q)) (dvd_refl _)

omit [IsDomain S] [IsFractionRing S Q] in
@[simp] theorem genericBaseChange_mk (g : S[X]) :
    genericBaseChange (Q := Q) f (AdjoinRoot.mk f g) =
      AdjoinRoot.mk (f.map (algebraMap S Q)) (g.map (algebraMap S Q)) := by
  change aeval (AdjoinRoot.root (f.map (algebraMap S Q))) g = _
  exact AdjoinRoot.aeval_eq_of_algebra (R := S) (S := Q) _ g

variable (hf : f.Monic)

noncomputable def normalizationInclusion :
    AdjoinRoot f →ₐ[S] integralClosure S (AdjoinRoot (f.map (algebraMap S Q))) := by
  haveI : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
  exact (genericBaseChange (Q := Q) f).codRestrict _
    (fun z => IsIntegral.map (genericBaseChange (Q := Q) f) (Algebra.IsIntegral.isIntegral z))

omit [IsDomain S] [IsFractionRing S Q] in
@[simp] theorem normalizationInclusion_val (z : AdjoinRoot f) :
    (normalizationInclusion (Q := Q) f hf z).val = genericBaseChange (Q := Q) f z := rfl

end GenericLattice
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section
variable {Q ι : Type*} [Field Q] [Fintype ι] [DecidableEq ι]

noncomputable def cyclicMap (T : Matrix ι ι Q) (v : ι → Q) :
    AdjoinRoot T.charpoly →ₗ[Q] (ι → Q) := by
  let ev : Q[X] →ₗ[Q] (ι → Q) :=
    (LinearMap.applyₗ v).comp (aeval T.mulVecLin).toLinearMap
  let I := (Ideal.span ({T.charpoly} : Set Q[X])).restrictScalars Q
  exact I.liftQ ev (by
    intro p hp
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hp
    change (aeval T.mulVecLin (T.charpoly * g)) v = 0
    rw [map_mul]
    have hc : aeval T.mulVecLin T.charpoly = 0 := by
      simpa only [Matrix.charpoly_mulVecLin] using T.mulVecLin.aeval_self_charpoly
    rw [hc, zero_mul, LinearMap.zero_apply])

@[simp] theorem cyclicMap_mk (T : Matrix ι ι Q) (v : ι → Q) (p : Q[X]) :
    cyclicMap T v (AdjoinRoot.mk T.charpoly p) = (aeval T.mulVecLin p) v := rfl

end
end PermanentBorder.Conductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ConductorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Conductor
open Matrix Polynomial

section MatrixFactorization
variable {R ι : Type*} [CommRing R] [IsDomain R]
  [Fintype ι] [DecidableEq ι]

abbrev DetQuotient (M : Matrix ι ι R) := R ⧸ Ideal.span {M.det}

end MatrixFactorization

end PermanentBorder.Conductor
namespace PermanentBorder.Conductor
open Matrix Polynomial
section
variable {S ι A : Type*} [CommRing S] [IsDomain S]
  [Fintype ι] [DecidableEq ι] [CommRing A] [Algebra S A]

def matrixEntryIdeal {B : Type*} [CommRing B] (N : Matrix ι ι B) : Ideal B :=
  Ideal.span (Set.range (fun ij : ι × ι => N ij.1 ij.2))

omit [Fintype ι] [DecidableEq ι] in
theorem entry_mem_matrixEntryIdeal {B : Type*} [CommRing B]
    (N : Matrix ι ι B) (i j : ι) : N i j ∈ matrixEntryIdeal N :=
  Ideal.subset_span ⟨(i,j), rfl⟩

end
end PermanentBorder.Conductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ConductorLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.RootLocalization
open Polynomial

section BaseChange
variable {S U : Type*} [CommRing S] [CommRing U] [Algebra S U]
variable (f : S[X]) (g : U[X]) (hfg : f.map (algebraMap S U) = g)

noncomputable def changeRoot : AdjoinRoot f →ₐ[S] AdjoinRoot g :=
  AdjoinRoot.mapAlgHom (Algebra.ofId S U) f g hfg.symm.dvd

@[simp] theorem changeRoot_mk (p : S[X]) :
    changeRoot f g hfg (AdjoinRoot.mk f p) =
      AdjoinRoot.mk g (p.map (algebraMap S U)) := by
  change aeval (AdjoinRoot.root g) p = _
  exact AdjoinRoot.aeval_eq_of_algebra (R := S) (S := U) _ p

@[simp] theorem changeRoot_root :
    changeRoot f g hfg (AdjoinRoot.root f) = AdjoinRoot.root g := by
  simpa only [AdjoinRoot.root, Polynomial.map_X] using changeRoot_mk f g hfg X

end BaseChange
end PermanentBorder.RootLocalization

namespace PermanentBorder.IdealLocalization
section
variable {S B C : Type*} [CommRing S] [CommRing B] [CommRing C]
  [Algebra S B] [Algebra S C]
variable (M : Submonoid S) (j : B →ₐ[S] C) [IsLocalizedModule M j.toLinearMap]

noncomputable def localizedIdeal (I : Ideal B) : Ideal C where
  __ := (I.restrictScalars S).localized₀ M j.toLinearMap
  smul_mem' c _ hx := by
    obtain ⟨x,hx,s,rfl⟩ := hx
    obtain ⟨⟨y,t⟩,hy⟩ := IsLocalizedModule.surj M j.toLinearMap c
    have hy' : IsLocalizedModule.mk' j.toLinearMap y t = c :=
      IsLocalizedModule.mk'_eq_iff.mpr hy.symm
    rw [← hy', smul_eq_mul, IsLocalizedModule.mk'_mul_mk']
    exact ⟨y*x,I.mul_mem_left y hx,t*s,rfl⟩

end
end PermanentBorder.IdealLocalization

namespace PermanentBorder.Conductor
open Polynomial Matrix RootLocalization
section
variable {S U ι : Type*} [CommRing S] [CommRing U] [Algebra S U]
  [Fintype ι] [DecidableEq ι]

noncomputable def matrixRootChange (T : Matrix ι ι S) :
    AdjoinRoot T.charpoly →ₐ[S] AdjoinRoot (T.map (algebraMap S U)).charpoly :=
  changeRoot T.charpoly (T.map (algebraMap S U)).charpoly (T.charpoly_map _).symm

@[simp] theorem matrixRootChange_root (T : Matrix ι ι S) :
    matrixRootChange (U := U) T (AdjoinRoot.root T.charpoly) =
      AdjoinRoot.root (T.map (algebraMap S U)).charpoly := changeRoot_root ..

omit [Fintype ι] [DecidableEq ι] in
theorem matrixEntryIdeal_map {B C : Type*} [CommRing B] [CommRing C]
    (f : B →+* C) (N : Matrix ι ι B) :
    (matrixEntryIdeal N).map f = matrixEntryIdeal (N.map f) := by
  rw [matrixEntryIdeal,Ideal.map_span,matrixEntryIdeal]
  congr 1
  ext x
  simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and,Matrix.map_apply]

end
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Polynomial Matrix Module RootLocalization

@[simp] theorem genericBaseChange_root {V Q : Type*} [CommRing V] [Field Q]
    [Algebra V Q] (f : V[X]) :
    genericBaseChange (Q := Q) f (AdjoinRoot.root f) =
      AdjoinRoot.root (f.map (algebraMap V Q)) := by
  simpa only [AdjoinRoot.root, Polynomial.map_X] using genericBaseChange_mk (Q := Q) f X

section GenericTransport
variable {S U Q ι : Type*} [CommRing S] [CommRing U] [Field Q]
  [Algebra S U] [Algebra S Q] [Algebra U Q] [IsScalarTower S U Q]
  [Fintype ι] [DecidableEq ι]

theorem charpoly_map_tower (T : Matrix ι ι S) :
    T.charpoly.map (algebraMap S Q) =
      (T.map (algebraMap S U)).charpoly.map (algebraMap U Q) := by
  rw [charpoly_map, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]

noncomputable def genericMatrixChange (T : Matrix ι ι S) :
    AdjoinRoot (T.charpoly.map (algebraMap S Q)) ≃ₐ[Q]
      AdjoinRoot ((T.map (algebraMap S U)).charpoly.map (algebraMap U Q)) :=
  AdjoinRoot.algEquivOfEq Q _ _ (charpoly_map_tower T)

end GenericTransport

end PermanentBorder.Conductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.AdjugateNormalForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.AdjugateAlgebra
open Matrix Polynomial

section Commutator
variable {K ι : Type*} [CommRing K] [Fintype ι] [DecidableEq ι]

theorem trace_commutator_adjugate (M Y : Matrix ι ι K) :
    ((M * Y - Y * M) * M.adjugate).trace = 0 := by
  rw [sub_mul, Matrix.trace_sub, Matrix.trace_mul_cycle M Y M.adjugate,
    Matrix.adjugate_mul, Matrix.mul_assoc Y M M.adjugate, Matrix.mul_adjugate]
  simp

theorem trace_commutator_adjugate_scalar (A Y : Matrix ι ι K) (s : K) :
    ((A * Y - Y * A) * (s • (1 : Matrix ι ι K) + A).adjugate).trace = 0 := by
  have he : (s • (1 : Matrix ι ι K) + A) * Y - Y * (s • 1 + A) =
      A * Y - Y * A := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
    abel
  rw [← he]
  exact trace_commutator_adjugate _ _

end Commutator

section PolynomialAdjugate
variable {R : Type*} [CommRing R] {k : ℕ}

theorem natDegree_adjugate_linear_le
    (A B : Matrix (Fin (k+1)) (Fin (k+1)) R) (i j : Fin (k+1)) :
    (((X : R[X]) • A.map C + B.map C).adjugate i j).natDegree ≤ k := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hsub : ((X : R[X]) • A.map C + B.map C).submatrix j.succAbove i.succAbove =
      (X : R[X]) • (A.submatrix j.succAbove i.succAbove).map C +
        (B.submatrix j.succAbove i.succAbove).map C := by ext; rfl
  rw [hsub]
  calc
    _ ≤ ((-1 : R[X]) ^ (↑j + ↑i)).natDegree +
        ((X : R[X]) • (A.submatrix j.succAbove i.succAbove).map C +
        (B.submatrix j.succAbove i.succAbove).map C).det.natDegree := natDegree_mul_le
    _ ≤ 0 + k := by
      gcongr
      · rw [show (-1 : R[X]) ^ (↑j + ↑i) = C ((-1 : R) ^ (↑j + ↑i)) by simp]
        simp only [natDegree_C, le_refl]
      · simpa using natDegree_det_X_add_C_le
          (A.submatrix j.succAbove i.succAbove) (B.submatrix j.succAbove i.succAbove)
    _ = k := zero_add _

theorem coeff_adjugate_linear
    (A B : Matrix (Fin (k+1)) (Fin (k+1)) R) (i j : Fin (k+1)) :
    (((X : R[X]) • A.map C + B.map C).adjugate i j).coeff k = A.adjugate i j := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hsub : ((X : R[X]) • A.map C + B.map C).submatrix j.succAbove i.succAbove =
      (X : R[X]) • (A.submatrix j.succAbove i.succAbove).map C +
        (B.submatrix j.succAbove i.succAbove).map C := by ext; rfl
  rw [hsub, show (-1 : R[X]) ^ (↑j + ↑i) = C ((-1 : R) ^ (↑j + ↑i)) by simp]
  rw [coeff_C_mul]
  congr 1
  simpa using coeff_det_X_add_C_card
    (A.submatrix j.succAbove i.succAbove) (B.submatrix j.succAbove i.succAbove)

end PolynomialAdjugate

section Slope
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

noncomputable def spectralSlope (θ : ι → K) : Matrix ι ι K[X] :=
  Matrix.diagonal (fun i => X + C (θ i))

theorem diagonal_zero_of_trace_slope (θ : ι → K) (hθ : Function.Injective θ)
    (Y : Matrix ι ι K)
    (h : (Y.map C * (spectralSlope θ).adjugate).trace = 0) : ∀ i, Y i i = 0 := by
  intro i
  have he := congrArg (Polynomial.eval (-θ i)) h
  simp only [spectralSlope, Matrix.adjugate_diagonal, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_diagonal, Matrix.map_apply,
    eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X, eval_zero] at he
  have heq : (∑ j : ι, Y j j * ∏ l ∈ Finset.univ.erase j, (-θ i + θ l)) =
      Y i i * ∏ l ∈ Finset.univ.erase i, (-θ i + θ l) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hf : (∏ l ∈ Finset.univ.erase j, (-θ i + θ l)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩)
        simp
      simp [hf]
    · simp
  rw [heq] at he
  have hp : (∏ l ∈ Finset.univ.erase i, (-θ i + θ l)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji := Finset.ne_of_mem_erase hj
    intro hz
    apply hji
    apply hθ
    exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using hz)
  exact (mul_eq_zero.mp he).resolve_right hp

end Slope

section Scaling
variable {K : Type*} [Field K] {k : ℕ}

noncomputable def pencilBase (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    Matrix (Fin (k+1)) (Fin (k+1)) K[X] :=
  (X : K[X]) • (Matrix.diagonal θ).map C + A.map C

noncomputable def scaledPencil (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    Matrix (Fin (k+1)) (Fin (k+1)) K[X][X] :=
  (X : K[X][X]) • (spectralSlope θ).map C + (A.map C).map C

noncomputable def liftCoefficients : K[X] →+* K[X][X] := Polynomial.mapRingHom C

noncomputable def scaledTrace (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) : K[X][X] :=
  (Y.map liftCoefficients * (scaledPencil θ A).adjugate).trace

 theorem scaledPencil_eq (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    scaledPencil θ A = (C (X : K[X]) * (X : K[X][X])) • (1 : Matrix (Fin (k+1)) (Fin (k+1)) K[X][X]) +
      (pencilBase θ A).map liftCoefficients := by
  apply Matrix.ext
  intro i j
  simp only [scaledPencil, pencilBase, spectralSlope, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply,
    liftCoefficients, map_add]
  (split_ifs <;> simp [Polynomial.mapRingHom]); ring

theorem coeff_scaledTrace_top (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) (d : ℕ)
    (hY : ∀ i j, (Y i j).natDegree ≤ d) :
    (scaledTrace θ A Y).coeff (d+k) =
      (Y.map (fun p => C (p.coeff d)) * (spectralSlope θ).adjugate).trace := by
  simp only [scaledTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (Polynomial.map C (Y i j) *
    ((X : K[X][X]) • (spectralSlope θ).map C + (A.map C).map C).adjugate j i).coeff (d+k) = _
  rw [coeff_mul_add_eq_of_natDegree_le
    ((natDegree_map_le).trans (hY i j))
    (natDegree_adjugate_linear_le (spectralSlope θ) (A.map C) j i)]
  simp only [coeff_map]
  rw [coeff_adjugate_linear]

theorem diagonal_top_zero (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) (d : ℕ) (hd : 0<d)
    (hY : ∀ i j, (Y i j).natDegree ≤ d)
    (hT : (scaledTrace θ A Y).natDegree ≤ k) :
    ∀ i, (Y i i).coeff d = 0 := by
  have hh := coeff_eq_zero_of_natDegree_lt (hT.trans_lt (by omega : k < d+k))
  rw [coeff_scaledTrace_top θ A Y d hY] at hh
  exact diagonal_zero_of_trace_slope θ hθ
    (Y.map (fun p => p.coeff d)) hh

end Scaling

section OuterVariableReduction
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

noncomputable def pencilMatrix (A : Matrix ι ι R) : Matrix ι ι R[X] :=
  (X : R[X]) • (1 : Matrix ι ι R[X]) + A.map C

noncomputable def adjTrace (A Y : Matrix ι ι R) : R[X] :=
  (Y.map C * (pencilMatrix A).adjugate).trace

@[simp] theorem adjTrace_zero (A : Matrix ι ι R) : adjTrace A 0 = 0 := by
  simp [adjTrace]

theorem adjTrace_add (A Y Z : Matrix ι ι R) :
    adjTrace A (Y+Z) = adjTrace A Y + adjTrace A Z := by
  have hm : (Y+Z).map C = Y.map C + Z.map C := C.mapMatrix.map_add Y Z
  simp only [adjTrace, hm, add_mul, Matrix.trace_add]

theorem adjTrace_neg (A Y : Matrix ι ι R) : adjTrace A (-Y) = -adjTrace A Y := by
  have hm : (-Y).map C = -Y.map C := C.mapMatrix.map_neg Y
  simp only [adjTrace, hm, neg_mul, Matrix.trace_neg]

theorem adjTrace_smul (A Y : Matrix ι ι R) (a : R) :
    adjTrace A (a • Y) = C a * adjTrace A Y := by
  have hm : (a • Y).map C = C a • Y.map C := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  simp only [adjTrace, hm, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

theorem X_mul_adjTrace (A Y : Matrix ι ι R) :
    X * adjTrace A Y = adjTrace A (-(Y*A)) + C Y.trace * (pencilMatrix A).det := by
  have hM : (X : R[X]) • (pencilMatrix A).adjugate =
      (pencilMatrix A).det • (1 : Matrix ι ι R[X]) -
        A.map C * (pencilMatrix A).adjugate := by
    have he := Matrix.mul_adjugate (pencilMatrix A)
    conv_lhs at he => rw [pencilMatrix, add_mul, Matrix.smul_mul, one_mul]
    exact eq_sub_of_add_eq he
  calc
    _ = (Y.map C * ((X : R[X]) • (pencilMatrix A).adjugate)).trace := by
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      rfl
    _ = (Y.map C * ((pencilMatrix A).det • 1 -
        A.map C * (pencilMatrix A).adjugate)).trace := by rw [hM]
    _ = _ := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, mul_one,
        Matrix.trace_smul, smul_eq_mul, ← Matrix.mul_assoc,
        ← Matrix.map_mul, adjTrace_neg]
      have ht : (Y.map C).trace = C Y.trace := (AddMonoidHom.map_trace (C : R →+* R[X]) Y).symm
      rw [ht]
      dsimp only [adjTrace]
      ring

def HasAdjugateNormalForm (A : Matrix ι ι R) (P : R[X]) : Prop :=
  ∃ (Y : Matrix ι ι R) (H : R[X]), P = adjTrace A Y + H * (pencilMatrix A).det

noncomputable def cofactorIdeal (A : Matrix ι ι R) : Ideal R[X] :=
  Ideal.span (Set.range fun ij : ι × ι => (pencilMatrix A).adjugate ij.1 ij.2)

end OuterVariableReduction

section DegreeNormalForm
variable {R : Type*} [CommRing R] [IsDomain R] {k : ℕ}

omit [IsDomain R] in

theorem natDegree_adjTrace_le
    (A Y : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    (adjTrace A Y).natDegree ≤ k := by
  unfold adjTrace
  change (∑ i, (Y.map C * (pencilMatrix A).adjugate) i i).natDegree ≤ k
  apply natDegree_sum_le_of_forall_le
  intro i hi
  rw [Matrix.mul_apply]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  apply le_trans (natDegree_C_mul_le _ _)
  have hm : (1 : Matrix (Fin (k+1)) (Fin (k+1)) R).map C = 1 := by
    exact C.mapMatrix.map_one
  simpa only [pencilMatrix, hm] using natDegree_adjugate_linear_le (1 : Matrix (Fin (k+1)) (Fin (k+1)) R) A j i

theorem natDegree_det_pencilMatrix
    (A : Matrix (Fin (k+1)) (Fin (k+1)) R) :
    (pencilMatrix A).det.natDegree = k+1 := by
  have hm : (1 : Matrix (Fin (k+1)) (Fin (k+1)) R).map C = 1 := C.mapMatrix.map_one
  have hc : (pencilMatrix A).det.coeff (k+1) = 1 := by
    simpa only [pencilMatrix, hm, Fintype.card_fin, Matrix.det_one] using
      coeff_det_X_add_C_card (1 : Matrix (Fin (k+1)) (Fin (k+1)) R) A
  apply le_antisymm
  · simpa only [pencilMatrix, hm, Fintype.card_fin] using
      natDegree_det_X_add_C_le (1 : Matrix (Fin (k+1)) (Fin (k+1)) R) A
  · exact le_natDegree_of_ne_zero (hc ▸ one_ne_zero)

end DegreeNormalForm

section BivariateScaling
variable {K : Type*} [Field K] {k : ℕ}

noncomputable def scaleHom : K[X][X] →+* K[X][X] :=
  Bivariate.swap.toRingHom.comp (compRingHom (C X * X))

@[simp] theorem scaleHom_C (p : K[X]) : scaleHom (C p) = liftCoefficients p := by
  simp [scaleHom, Bivariate.swap_C, liftCoefficients]

@[simp] theorem scaleHom_X : scaleHom (X : K[X][X]) = C X * X := by
  change Bivariate.swap ((X : K[X][X]).comp (C X * X)) = _
  rw [X_comp, map_mul, Bivariate.swap_X, Bivariate.swap_Y, mul_comm]

theorem scaleHom_pencil (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    (pencilMatrix (pencilBase θ A)).map scaleHom = scaledPencil θ A := by
  rw [scaledPencil_eq]
  apply Matrix.ext
  intro i j
  simp only [pencilMatrix, Matrix.map_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add, map_mul]
  split_ifs <;> simp

theorem scaleHom_adjTrace (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (Y : Matrix (Fin (k+1)) (Fin (k+1)) K[X]) :
    scaleHom (adjTrace (pencilBase θ A) Y) = scaledTrace θ A Y := by
  unfold adjTrace scaledTrace
  have ha : (pencilMatrix (pencilBase θ A)).adjugate.map scaleHom =
      ((pencilMatrix (pencilBase θ A)).map scaleHom).adjugate :=
    RingHom.map_adjugate scaleHom _
  rw [AddMonoidHom.map_trace, Matrix.map_mul, ha, scaleHom_pencil]
  congr 2
  apply Matrix.ext
  intro i j
  exact scaleHom_C _

theorem scaleHom_monomial_monomial (a b : ℕ) (c : K) :
    scaleHom (monomial a (monomial b c)) = monomial (a+b) (monomial a c) := by
  simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, scaleHom_C,
    scaleHom_X, liftCoefficients, coe_mapRingHom, Polynomial.map_C, Polynomial.map_X]
  simp only [mul_pow, pow_add]
  ring

theorem coeff_scaleHom (P : K[X][X]) (d i : ℕ) :
    ((scaleHom P).coeff d).coeff i =
      if i ≤ d then (P.coeff i).coeff (d-i) else 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, coeff_add, hP, hQ]
      split_ifs <;> simp
  | monomial a p =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
          simp only [map_add, coeff_add, hp, hq]
          split_ifs <;> simp
      | monomial b c =>
          rw [scaleHom_monomial_monomial]
          by_cases hai : a = i
          · subst a
            by_cases hib : i+b = d
            · have hi : i ≤ d := by omega
              have hb : b = d-i := by omega
              simp [hi, hb]
            · by_cases hi : i ≤ d
              · have hb : b ≠ d-i := by omega
                simp [coeff_monomial, hi, hib, hb]
              · simp [coeff_monomial, hi, hib]
          · by_cases hab : a+b = d <;> simp [coeff_monomial, hai, hab]

def TotalDegreeLE (P : K[X][X]) (d : ℕ) : Prop :=
  ∀ i j : ℕ, d < i+j → (P.coeff i).coeff j = 0

theorem TotalDegreeLE.outer {P : K[X][X]} {d : ℕ} (hP : TotalDegreeLE P d) :
    P.natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  ext j
  simpa only [coeff_zero] using hP i j (by omega)

theorem TotalDegreeLE.scaled {P : K[X][X]} {d : ℕ} (hP : TotalDegreeLE P d) :
    (scaleHom P).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  ext i
  rw [coeff_scaleHom]
  split_ifs with hi
  · simpa only [coeff_zero] using hP i (n-i) (by omega)
  · simp

theorem totalDegreeLE_iff_scaled_natDegree (P : K[X][X]) (d : ℕ) :
    TotalDegreeLE P d ↔ (scaleHom P).natDegree ≤ d := by
  refine ⟨TotalDegreeLE.scaled, ?_⟩
  intro hd i j hij
  have hc := coeff_eq_zero_of_natDegree_lt (hd.trans_lt hij)
  have hh := congrArg (fun p : K[X] => p.coeff i) hc
  simpa only [coeff_scaleHom, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left,
    coeff_zero] using hh

theorem TotalDegreeLE.mul {P Q : K[X][X]} {d e : ℕ}
    (hP : TotalDegreeLE P d) (hQ : TotalDegreeLE Q e) :
    TotalDegreeLE (P*Q) (d+e) := by
  rw [totalDegreeLE_iff_scaled_natDegree, map_mul]
  exact natDegree_mul_le.trans (Nat.add_le_add hP.scaled hQ.scaled)

theorem TotalDegreeLE.mono {P : K[X][X]} {d e : ℕ}
    (hP : TotalDegreeLE P d) (hde : d ≤ e) : TotalDegreeLE P e :=
  fun i j hij => hP i j (hde.trans_lt hij)

theorem totalDegreeLE_monomial (a b : ℕ) (c : K) :
    TotalDegreeLE (monomial a (monomial b c)) (a+b) := by
  rw [totalDegreeLE_iff_scaled_natDegree, scaleHom_monomial_monomial]
  exact natDegree_monomial_le _

abbrev PlaneIndex (q : ℕ) := {p : Fin (q+2) × Fin (q+2) // p.1 < p.2}

noncomputable def planeMap (q : ℕ) : (PlaneIndex q → K) →ₗ[K] K[X][X] where
  toFun f := ∑ i, monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) (f i))
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum, smul_monomial]

theorem coeff_planeMap (q : ℕ) (f : PlaneIndex q → K) (i : PlaneIndex q) :
    (((planeMap q f).coeff i.val.1.val).coeff (i.val.2.val-i.val.1.val-1)) = f i := by
  classical
  simp only [planeMap, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    by_cases ha : j.val.1.val = i.val.1.val
    · have hb : j.val.2.val-j.val.1.val-1 ≠ i.val.2.val-i.val.1.val-1 := by
        intro h
        apply hji
        apply Subtype.ext
        apply Prod.ext
        · exact Fin.ext ha
        · apply Fin.ext
          have hi := i.property
          have hj := j.property
          change i.val.1.val < i.val.2.val at hi
          change j.val.1.val < j.val.2.val at hj
          omega
      simp only [ha] at hb
      simp [coeff_monomial, ha, hb]
    · simp [coeff_monomial, ha]
  · simp

theorem totalDegreeLE_planeMap (q : ℕ) (f : PlaneIndex q → K) :
    TotalDegreeLE (planeMap q f) q := by
  classical
  intro a b hab
  simp only [planeMap, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hi := i.property
  change i.val.1.val < i.val.2.val at hi
  have hbnd := i.val.2.isLt
  by_cases ha : i.val.1.val = a
  · have hb : i.val.2.val-i.val.1.val-1 ≠ b := by omega
    simp only [ha] at hb
    simp [coeff_monomial, ha, hb]
  · simp [coeff_monomial, ha]

theorem totalDegreeLE_cofactor (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (i j : Fin (k+1)) :
    TotalDegreeLE ((pencilMatrix (pencilBase θ A)).adjugate i j) k := by
  rw [totalDegreeLE_iff_scaled_natDegree]
  have ha : (pencilMatrix (pencilBase θ A)).adjugate.map scaleHom =
      ((pencilMatrix (pencilBase θ A)).map scaleHom).adjugate :=
    RingHom.map_adjugate scaleHom _
  have hh := congrArg (fun M => M i j) ha
  change scaleHom ((pencilMatrix (pencilBase θ A)).adjugate i j) = _ at hh
  rw [hh, scaleHom_pencil]
  exact natDegree_adjugate_linear_le (spectralSlope θ) (A.map C) i j

theorem TotalDegreeLE.sub {P Q : K[X][X]} {d : ℕ}
    (hP : TotalDegreeLE P d) (hQ : TotalDegreeLE Q d) : TotalDegreeLE (P-Q) d := by
  intro i j hij
  simp only [coeff_sub, hP i j hij, hQ i j hij, sub_zero]

theorem TotalDegreeLE.sum {ι : Type*} (s : Finset ι) (f : ι → K[X][X]) {d : ℕ}
    (h : ∀ i ∈ s, TotalDegreeLE (f i) d) : TotalDegreeLE (∑ i ∈ s, f i) d := by
  intro a b hab
  simp only [finsetSum_coeff]
  exact Finset.sum_eq_zero fun i hi => h i hi a b hab

noncomputable def diagonalContraction (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (y : Fin (k+1) → K) : K[X][X] :=
  adjTrace (pencilBase θ A) ((Matrix.diagonal y).map C)

noncomputable def slopeTrace (θ : Fin (k+1) → K) (y : Fin (k+1) → K) : K[X] :=
  ((Matrix.diagonal y).map C * (spectralSlope θ).adjugate).trace

theorem natDegree_adjugate_slope_le (θ : Fin (k+1) → K) (i j : Fin (k+1)) :
    ((spectralSlope θ).adjugate i j).natDegree ≤ k := by
  have hs : spectralSlope θ = (X : K[X]) •
      (1 : Matrix (Fin (k+1)) (Fin (k+1)) K).map C +
      (Matrix.diagonal θ).map C := by
    ext i j
    simp only [spectralSlope, Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hs]
  exact natDegree_adjugate_linear_le 1 (Matrix.diagonal θ) i j

theorem natDegree_slopeTrace_le (θ : Fin (k+1) → K) (y : Fin (k+1) → K) :
    (slopeTrace θ y).natDegree ≤ k := by
  simp only [slopeTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply]
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_le _ _).trans (natDegree_adjugate_slope_le θ j i)

noncomputable def slopeCoefficientMap (θ : Fin (k+1) → K) :
    (Fin (k+1) → K) →ₗ[K] (Fin (k+1) → K) where
  toFun y i := (slopeTrace θ y).coeff i
  map_add' y z := by
    ext i
    simp [slopeTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, finsetSum_coeff, coeff_C_mul, Finset.sum_add_distrib, add_mul]
  map_smul' c y := by
    ext i
    simp [slopeTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, finsetSum_coeff, coeff_C_mul, Finset.mul_sum, mul_assoc]

theorem slopeCoefficientMap_injective (θ : Fin (k+1) → K) (hθ : Function.Injective θ) :
    Function.Injective (slopeCoefficientMap θ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro y hy
  have hz : slopeTrace θ y = 0 := by
    ext n
    simp only [coeff_zero]
    by_cases hn : n < k+1
    · exact congrFun hy ⟨n,hn⟩
    · exact coeff_eq_zero_of_natDegree_lt ((natDegree_slopeTrace_le θ y).trans_lt (by omega))
  have h := diagonal_zero_of_trace_slope θ hθ (Matrix.diagonal y) hz
  funext i
  simpa only [Matrix.diagonal_apply_eq, Pi.zero_apply] using h i

theorem exists_diagonalContraction_top (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (a : ℕ) (ha : a ≤ k) :
    ∃ y : Fin (k+1) → K,
      (scaleHom (diagonalContraction θ A y)).coeff k = monomial a 1 := by
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective (slopeCoefficientMap_injective θ hθ)
    (fun i => (monomial a (1 : K)).coeff i)
  have hs : slopeTrace θ y = monomial a 1 := by
    ext n
    by_cases hn : n < k+1
    · exact congrFun hy ⟨n,hn⟩
    · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_slopeTrace_le θ y).trans_lt (by omega)),
        coeff_eq_zero_of_natDegree_lt ((natDegree_monomial_le (1 : K) : (monomial a (1 : K)).natDegree ≤ a).trans_lt (by omega))]
  refine ⟨y, ?_⟩
  have ht := coeff_scaledTrace_top θ A ((Matrix.diagonal y).map C) 0 (by simp)
  simp only [zero_add] at ht
  rw [diagonalContraction, scaleHom_adjTrace, ht]
  convert hs using 1
  simp [slopeTrace]

theorem TotalDegreeLE.pred_of_top_zero {P : K[X][X]} {d : ℕ}
    (hd : 0 < d) (hP : TotalDegreeLE P d) (hz : (scaleHom P).coeff d = 0) :
    TotalDegreeLE P (d-1) := by
  intro a b hab
  by_cases hlt : d < a+b
  · exact hP a b hlt
  · have he : a+b = d := by omega
    have hc := congrArg (fun p : K[X] => p.coeff a) hz
    rw [coeff_scaleHom] at hc
    simpa only [show a ≤ d by omega, ↓reduceIte, show d-a = b by omega,
      coeff_zero] using hc

theorem eq_sum_bivariate (P : K[X][X]) :
    P = ∑ a ∈ P.support, ∑ b ∈ (P.coeff a).support,
      monomial a (monomial b ((P.coeff a).coeff b)) := by
  calc
    P = ∑ a ∈ P.support, monomial a (P.coeff a) := (sum_monomial_eq P).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← map_sum]
      exact congrArg (monomial a) (sum_monomial_eq (P.coeff a)).symm

theorem map_mem_of_monomials {V : Type*} [AddCommGroup V] [Module K V]
    (f : K[X][X] →ₗ[K] V) (W : Submodule K V) (P : K[X][X])
    (h : ∀ a b, (P.coeff a).coeff b ≠ 0 →
      f (monomial a (monomial b ((P.coeff a).coeff b))) ∈ W) : f P ∈ W := by
  rw [eq_sum_bivariate P, map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [map_sum]
  apply Submodule.sum_mem
  intro b hb
  apply h
  exact mem_support_iff.mp hb

end BivariateScaling

end PermanentBorder.AdjugateAlgebra

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.RowIdeals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.AdjugateAlgebra
open Matrix Polynomial
section RowNormalForm
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

def rowMultiplier (v : ι → R) : Matrix ι ι R := fun i _ => v i

noncomputable def rowPair (A : Matrix ι ι R) (v : ι → R) : R[X] :=
  adjTrace A (rowMultiplier v)

noncomputable def rowEntry (A : Matrix ι ι R) (i : ι) : R[X] :=
  ∑ j, (pencilMatrix A).adjugate j i

noncomputable def rowIdeal (A : Matrix ι ι R) : Ideal R[X] :=
  Ideal.span (Set.range (rowEntry A))

theorem rowPair_eq_sum (A : Matrix ι ι R) (v : ι → R) :
    rowPair A v = ∑ i, C (v i) * rowEntry A i := by
  simp only [rowPair, adjTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.map_apply, rowMultiplier, rowEntry, Finset.mul_sum]

theorem rowPair_add (A : Matrix ι ι R) (v w : ι → R) :
    rowPair A (v+w) = rowPair A v + rowPair A w := by
  exact adjTrace_add _ _ _

theorem rowPair_smul (A : Matrix ι ι R) (a : R) (v : ι → R) :
    rowPair A (a • v) = C a * rowPair A v := by
  exact adjTrace_smul _ _ _

theorem rowPair_zero (A : Matrix ι ι R) : rowPair A 0 = 0 := adjTrace_zero _

theorem adjTrace_mul_comm (A Y : Matrix ι ι R) :
    adjTrace A (Y*A) = adjTrace A (A*Y) := by
  have h := trace_commutator_adjugate_scalar (A.map C) (Y.map C) (X : R[X])
  simp only [sub_mul, Matrix.trace_sub, ← Matrix.map_mul] at h
  exact (sub_eq_zero.mp h).symm

theorem X_mul_rowPair (A : Matrix ι ι R) (v : ι → R) :
    X * rowPair A v = rowPair A (-(A.mulVec v)) +
      C (∑ i, v i) * (pencilMatrix A).det := by
  rw [rowPair, X_mul_adjTrace, adjTrace_neg, adjTrace_mul_comm]
  have h : A * rowMultiplier v = rowMultiplier (A.mulVec v) := by
    ext i j
    rfl
  rw [h]
  change -adjTrace A (rowMultiplier (A.mulVec v)) + _ = _
  rw [← adjTrace_neg]
  rfl

def HasRowNormalForm (A : Matrix ι ι R) (P : R[X]) : Prop :=
  ∃ v : ι → R, ∃ H : R[X], P = rowPair A v + H * (pencilMatrix A).det

namespace HasRowNormalForm
variable {A : Matrix ι ι R} {P Q : R[X]}
theorem zero : HasRowNormalForm A 0 := ⟨0, 0, by simp [rowPair_zero]⟩
theorem add (hP : HasRowNormalForm A P) (hQ : HasRowNormalForm A Q) :
    HasRowNormalForm A (P+Q) := by
  obtain ⟨v,H,rfl⟩ := hP
  obtain ⟨w,J,rfl⟩ := hQ
  exact ⟨v+w,H+J, by rw [rowPair_add]; ring⟩
theorem C_mul (hP : HasRowNormalForm A P) (a : R) :
    HasRowNormalForm A (C a * P) := by
  obtain ⟨v,H,rfl⟩ := hP
  exact ⟨a • v,C a * H, by rw [rowPair_smul]; ring⟩
theorem X_mul (hP : HasRowNormalForm A P) : HasRowNormalForm A (X*P) := by
  obtain ⟨v,H,rfl⟩ := hP
  refine ⟨-(A.mulVec v),C (∑ i, v i) + X*H, ?_⟩
  rw [mul_add, X_mul_rowPair]
  ring
theorem mul (hP : HasRowNormalForm A P) (f : R[X]) : HasRowNormalForm A (f*P) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simpa only [add_mul] using hf.add hg
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, mul_assoc]
    apply HasRowNormalForm.C_mul
    induction n with
    | zero => simpa using hP
    | succ n ih => simpa only [pow_succ', mul_assoc] using ih.X_mul
end HasRowNormalForm

theorem normalForm_of_mem_rowIdeal (A : Matrix ι ι R) (P : R[X])
    (hP : P ∈ rowIdeal A) : HasRowNormalForm A P := by
  let J : Ideal R[X] :=
    { carrier := {P | HasRowNormalForm A P}
      zero_mem' := HasRowNormalForm.zero
      add_mem' := fun h h' => h.add h'
      smul_mem' := fun f _ h => h.mul f }
  have hle : rowIdeal A ≤ J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change HasRowNormalForm A (rowEntry A i)
    refine ⟨Pi.single i 1,0, ?_⟩
    simp [rowPair_eq_sum, Pi.single_apply]
  exact hle hP
end RowNormalForm

section RowDegree
variable {K : Type*} [Field K] {k : ℕ}

theorem rowPair_degree_le (A : Matrix (Fin (k+1)) (Fin (k+1)) K[X])
    (v : Fin (k+1) → K[X]) : (rowPair A v).natDegree ≤ k :=
  natDegree_adjTrace_le _ _

theorem exists_row_multiplier (A : Matrix (Fin (k+1)) (Fin (k+1)) K[X])
    (P : K[X][X]) (hP : P ∈ rowIdeal A) (hdeg : P.natDegree ≤ k) :
    ∃ v : Fin (k+1) → K[X], P = rowPair A v := by
  obtain ⟨v,H,h⟩ := normalForm_of_mem_rowIdeal A P hP
  have hH : H = 0 := by
    by_contra hn
    have hF : (pencilMatrix A).det ≠ 0 := by
      intro hz
      have := natDegree_det_pencilMatrix A
      simp only [hz, natDegree_zero] at this
      omega
    have hd : (H*(pencilMatrix A).det).natDegree ≤ k := by
      have he : H*(pencilMatrix A).det = P - rowPair A v := by rw [h]; ring
      rw [he]
      exact (natDegree_sub_le _ _).trans (max_le hdeg (rowPair_degree_le A v))
    rw [natDegree_mul hn hF, natDegree_det_pencilMatrix] at hd
    omega
  exact ⟨v, by simpa only [hH,zero_mul,add_zero] using h⟩

theorem row_multiplier_is_constant (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K[X]) (d : ℕ)
    (hv : ∀ i, (v i).natDegree ≤ d)
    (hdeg : (scaleHom (rowPair (pencilBase θ A) v)).natDegree ≤ k) :
    ∀ i, v i = C ((v i).coeff 0) := by
  have hs : (scaledTrace θ A (rowMultiplier v)).natDegree ≤ k := by
    simpa only [rowPair, scaleHom_adjTrace] using hdeg
  induction d with
  | zero =>
    intro i
    have he := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (hv i))
    simpa using he
  | succ d ih =>
    apply ih
    intro i
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    by_cases he : n = d+1
    · subst n
      exact diagonal_top_zero θ hθ A (rowMultiplier v) (d+1) (by omega)
        (fun i _ => hv i) hs i
    · exact coeff_eq_zero_of_natDegree_lt ((hv i).trans_lt (by omega))

theorem exists_constant_row_multiplier (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (P : K[X][X])
    (hP : P ∈ rowIdeal (pencilBase θ A)) (ho : P.natDegree ≤ k)
    (ht : (scaleHom P).natDegree ≤ k) :
    ∃ v : Fin (k+1) → K, P = rowPair (pencilBase θ A) (fun i => C (v i)) := by
  obtain ⟨v,hv⟩ := exists_row_multiplier _ P hP ho
  obtain ⟨d,hd⟩ := (Set.finite_range (fun i => (v i).natDegree)).bddAbove
  have hc := row_multiplier_is_constant θ hθ A v d (fun i => hd ⟨i,rfl⟩) (hv ▸ ht)
  exact ⟨fun i => (v i).coeff 0, hv.trans (by congr 1; funext i; exact hc i)⟩
end RowDegree
end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.AdjugateAlgebra
open Matrix Polynomial
section RowLength
variable {K : Type*} [Field K] {k : ℕ}
noncomputable def rowContraction (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K) : K[X][X] :=
  rowPair (pencilBase θ A) (fun i => C (v i))

theorem rowContraction_mem (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K) :
    rowContraction θ A v ∈ rowIdeal (pencilBase θ A) := by
  rw [rowContraction, rowPair_eq_sum]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)

theorem totalDegreeLE_rowEntry (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (i : Fin (k+1)) :
    TotalDegreeLE (rowEntry (pencilBase θ A) i) k := by
  exact TotalDegreeLE.sum _ _ (fun j _ => totalDegreeLE_cofactor θ A j i)

theorem totalDegreeLE_rowContraction (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K) :
    TotalDegreeLE (rowContraction θ A v) k := by
  rw [rowContraction, rowPair_eq_sum]
  apply TotalDegreeLE.sum
  intro i _
  simpa only [zero_add, monomial_zero_left] using
    (totalDegreeLE_monomial 0 0 (v i)).mul (totalDegreeLE_rowEntry θ A i)

theorem rowContraction_top (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (v : Fin (k+1) → K) :
    (scaleHom (rowContraction θ A v)).coeff k = slopeTrace θ v := by
  have ht := coeff_scaledTrace_top θ A (rowMultiplier (fun i => C (v i))) 0
    (fun _ _ => by simp [rowMultiplier])
  simp only [zero_add] at ht
  rw [rowContraction, rowPair, scaleHom_adjTrace, ht]
  simp [slopeTrace, spectralSlope, Matrix.adjugate_diagonal, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_diagonal, Matrix.map_apply, rowMultiplier]

theorem exists_rowContraction_top (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (a : ℕ) (ha : a ≤ k) :
    ∃ v : Fin (k+1) → K,
      (scaleHom (rowContraction θ A v)).coeff k = monomial a 1 := by
  obtain ⟨v,hv⟩ := exists_diagonalContraction_top θ hθ A a ha
  refine ⟨v, ?_⟩
  rw [rowContraction_top]
  have ht := coeff_scaledTrace_top θ A ((Matrix.diagonal v).map C) 0 (by simp)
  simp only [zero_add] at ht
  rw [diagonalContraction, scaleHom_adjTrace, ht] at hv
  convert hv using 1
  simp [slopeTrace]

theorem exists_lower_row_representative
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k)
    (a b : ℕ) (hab : a+b = k) :
    ∃ R : K[X][X], TotalDegreeLE R (k-1) ∧
      monomial a (monomial b 1) - R ∈ rowIdeal (pencilBase θ A) := by
  obtain ⟨v,hv⟩ := exists_rowContraction_top θ hθ A a (by omega)
  let R := monomial a (monomial b (1 : K)) - rowContraction θ A v
  refine ⟨R, ?_, ?_⟩
  · apply TotalDegreeLE.pred_of_top_zero hk
    · exact ((totalDegreeLE_monomial a b (1 : K)).mono hab.le).sub
        (totalDegreeLE_rowContraction θ A v)
    · simp only [R, map_sub, coeff_sub, scaleHom_monomial_monomial, hab,
        coeff_monomial_same, hv, sub_self]
  · simpa only [R, sub_sub_cancel] using rowContraction_mem θ A v

theorem rowIdeal_low_degree_zero (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k)
    {P : K[X][X]} (hP : P ∈ rowIdeal (pencilBase θ A))
    (hd : TotalDegreeLE P (k-1)) : P = 0 := by
  obtain ⟨v,hv⟩ := exists_constant_row_multiplier θ hθ A P hP
    (hd.outer.trans (by omega))
    (hd.scaled.trans (by omega))
  change P = rowContraction θ A v at hv
  have ht : slopeTrace θ v = 0 := by
    rw [← rowContraction_top θ A v, ← hv]
    exact coeff_eq_zero_of_natDegree_lt
      (hd.scaled.trans_lt (by omega))
  have hv0 := diagonal_zero_of_trace_slope θ hθ (Matrix.diagonal v) ht
  have he : v = 0 := funext fun i => by simpa using hv0 i
  rw [hv, he]
  change rowPair (pencilBase θ A) (fun i => C ((0 : Fin (k+1) → K) i)) = 0
  convert rowPair_zero (pencilBase θ A) using 1
  congr 1
  funext i
  exact map_zero C

theorem row_quotient_spanned
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Submodule.span K (Set.range (fun i : PlaneIndex (k-1) =>
      (Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A)))
        (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1)))) = ⊤ := by
  classical
  let I := rowIdeal (pencilBase θ A)
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap
  let W := Submodule.span K (Set.range (fun i : PlaneIndex (k-1) =>
    f (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1))))
  have hmon : ∀ d a b : ℕ, a+b = d → ∀ c : K, f (monomial a (monomial b c)) ∈ W := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a b hab c
      have hscalar : monomial a (monomial b c) = c • monomial a (monomial b (1 : K)) := by
        simp only [smul_monomial, smul_eq_mul, mul_one]
      rw [hscalar, map_smul]
      apply W.smul_mem
      by_cases hd : d < k
      · let i : PlaneIndex (k-1) := ⟨(⟨a, by omega⟩, ⟨a+b+1, by omega⟩), by
          change a < a+b+1
          omega⟩
        apply Submodule.subset_span
        refine ⟨i, ?_⟩
        change f (monomial a (monomial (a+b+1-a-1) (1 : K))) = _
        rw [show a+b+1-a-1 = b by omega]
      · let α := min a k
        let β := k-α
        have hα : α ≤ a := Nat.min_le_left _ _
        have hβ : β ≤ b := by dsimp [β, α]; omega
        have hsum : α+β = k := by dsimp [β, α]; omega
        obtain ⟨R, hR, hmem⟩ := exists_lower_row_representative θ hθ A hk α β hsum
        let Q : K[X][X] := monomial (a-α) (monomial (b-β) 1)
        have heq : f (monomial a (monomial b 1)) = f (Q*R) := by
          apply sub_eq_zero.mp
          rw [← map_sub]
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          have hh := I.mul_mem_left Q hmem
          convert hh using 1
          rw [mul_sub]
          congr 1
          simp only [Q, monomial_mul_monomial, one_mul]
          rw [Nat.sub_add_cancel hα, Nat.sub_add_cancel hβ]
        rw [heq]
        apply map_mem_of_monomials f W (Q*R)
        intro u v huv
        have hde : TotalDegreeLE (Q*R) ((a-α)+(b-β)+(k-1)) :=
          (totalDegreeLE_monomial (a-α) (b-β) (1 : K)).mul hR
        have hle : u+v ≤ (a-α)+(b-β)+(k-1) := by
          by_contra hn
          exact huv (hde u v (by omega))
        exact ih (u+v) (by omega) u v rfl _
  apply top_unique
  intro x _
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply map_mem_of_monomials f W P
  intro a b _
  exact hmon (a+b) a b rfl _

end RowLength
end PermanentBorder.AdjugateAlgebra

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.PencilSeparability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.Conductor
open Matrix Polynomial
section
variable {K S ι : Type*} [Field K] [CommRing S] [Algebra K S]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem charpoly_mem_adjugate_ideal (T : Matrix ι ι S) :
    T.charpoly ∈ matrixEntryIdeal T.charmatrix.adjugate := by
  classical
  rw [Matrix.charpoly, det_eq_sum_mul_adjugate_row _ (Classical.arbitrary ι)]
  exact Ideal.sum_mem _ fun j _ =>
    Ideal.mul_mem_left _ _ (entry_mem_matrixEntryIdeal _ j _)

noncomputable def polynomialCofactorQuotientEquiv (T : Matrix ι ι S) :
    (AdjoinRoot T.charpoly ⧸
      (matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly))).restrictScalars S)
      ≃ₗ[K] S[X] ⧸ matrixEntryIdeal T.charmatrix.adjugate := by
  let J := matrixEntryIdeal T.charmatrix.adjugate
  have h : Ideal.span {T.charpoly} ≤ J :=
    Ideal.span_le.mpr fun _ hx => Set.mem_singleton_iff.mp hx ▸ charpoly_mem_adjugate_ideal T
  let e := (DoubleQuot.quotQuotEquivQuotOfLEₐ K h).toLinearEquiv
  have hm : J.map (Ideal.Quotient.mkₐ K (Ideal.span {T.charpoly})) =
      matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) :=
    matrixEntryIdeal_map (AdjoinRoot.mk T.charpoly) T.charmatrix.adjugate
  rw [hm] at e
  letI : IsScalarTower K (AdjoinRoot T.charpoly) (AdjoinRoot T.charpoly) :=
    AdjoinRoot.isScalarTower_right T.charpoly
  let e₀ := Submodule.Quotient.restrictScalarsEquiv K
    (matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)))
  exact e₀.trans e

end
end PermanentBorder.Conductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Gradients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.GradientAlgebra

open Finset

section AffinePencil
open MvPolynomial
variable {R σ : Type*} [CommRing R]

noncomputable def biCoefficientPart (a b : ℕ) :
    MvPolynomial σ (Polynomial (Polynomial R)) →+ MvPolynomial σ R where
  toFun := AddMonoidAlgebra.map
    ((Polynomial.lcoeff R b).toAddMonoidHom.comp
      (Polynomial.lcoeff (Polynomial R) a).toAddMonoidHom)
  map_zero' := by ext; simp
  map_add' := AddMonoidAlgebra.map_add _

@[simp] theorem coeff_biCoefficientPart (a b : ℕ)
    (P : MvPolynomial σ (Polynomial (Polynomial R))) (d : σ →₀ ℕ) :
    (biCoefficientPart a b P).coeff d = ((P.coeff d).coeff a).coeff b := rfl

@[simp] theorem biCoefficientPart_monomial (a b : ℕ) (d : σ →₀ ℕ)
    (c : Polynomial (Polynomial R)) :
    biCoefficientPart a b (monomial d c) = monomial d ((c.coeff a).coeff b) := by
  classical
  ext d'
  simp only [coeff_biCoefficientPart, coeff_monomial]
  split_ifs <;> simp_all

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def genericAffinePencil (θ : ι → R) :
    Matrix ι ι (MvPolynomial (ι × ι) (Polynomial (Polynomial R))) :=
  fun i j => C (if i = j then Polynomial.X + Polynomial.C
    (Polynomial.X * Polynomial.C (θ i)) else 0) + X (i,j)

noncomputable def fixedAffinePencil (θ : ι → R) (x : Matrix ι ι R) :
    Matrix ι ι (Polynomial (Polynomial R)) := fun i j =>
      (if i = j then Polynomial.X + Polynomial.C
        (Polynomial.X * Polynomial.C (θ i)) else 0) + Polynomial.C (Polynomial.C (x i j))

omit [Fintype ι] in
@[simp] theorem pderiv_genericAffinePencil (θ : ι → R) (i j a b : ι) :
    pderiv (a,b) (genericAffinePencil θ i j) = if (a,b) = (i,j) then 1 else 0 := by
  classical
  simp [genericAffinePencil, pderiv_X, Pi.single_apply, eq_comm]

noncomputable def affineSelector (θ : ι → R) (q : ℕ) : MvPolynomial (ι × ι) R :=
  biCoefficientPart q q (genericAffinePencil θ).permanent

end AffinePencil

end PermanentBorder.GradientAlgebra

namespace PermanentBorder.Selector
open MvPolynomial
section
variable {R σ : Type*} [CommRing R]

noncomputable def bivariateToNested : MvPolynomial (Fin 2) R →+* Polynomial (Polynomial R) :=
  (Polynomial.mapRingHom (uniqueAlgEquiv R (Fin 1)).toRingHom).comp
    (finSuccEquiv R 1).toRingHom

@[simp] lemma bivariateToNested_C (r : R) :
    bivariateToNested (C r) = Polynomial.C (Polynomial.C r) := by
  simp [bivariateToNested, finSuccEquiv_apply]

@[simp] lemma bivariateToNested_X_zero :
    bivariateToNested (X (0 : Fin 2) : MvPolynomial (Fin 2) R) = Polynomial.X := by
  change Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom
    (finSuccEquiv R 1 (X 0)) = _
  rw [finSuccEquiv_X_zero, Polynomial.map_X]

@[simp] lemma bivariateToNested_X_one :
    bivariateToNested (X (1 : Fin 2) : MvPolynomial (Fin 2) R) =
      Polynomial.C Polynomial.X := by
  change Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom
    (finSuccEquiv R 1 (X (Fin.succ (0 : Fin 1)))) = _
  rw [finSuccEquiv_X_succ, Polynomial.map_C]
  congr 1
  simp

noncomputable def interchangeBivariate :
    MvPolynomial (Fin 2) (MvPolynomial σ R) →+*
      MvPolynomial σ (Polynomial (Polynomial R)) :=
  (map bivariateToNested).comp (commAlgEquiv R (Fin 2) σ).toRingHom

@[simp] lemma interchangeBivariate_C_X (i : σ) :
    interchangeBivariate (C (X i) : MvPolynomial (Fin 2) (MvPolynomial σ R)) = X i := by
  simp [interchangeBivariate]

@[simp] lemma interchangeBivariate_C_C (r : R) :
    interchangeBivariate (C (C r) : MvPolynomial (Fin 2) (MvPolynomial σ R)) =
      C (Polynomial.C (Polynomial.C r)) := by
  simp [interchangeBivariate]

@[simp] lemma interchangeBivariate_X_zero :
    interchangeBivariate (X (0 : Fin 2) : MvPolynomial (Fin 2) (MvPolynomial σ R)) =
      C Polynomial.X := by
  simp [interchangeBivariate]

@[simp] lemma interchangeBivariate_X_one :
    interchangeBivariate (X (1 : Fin 2) : MvPolynomial (Fin 2) (MvPolynomial σ R)) =
      C (Polynomial.C (Polynomial.X : Polynomial R)) := by
  simp [interchangeBivariate]
end

end PermanentBorder.Selector

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Centralizers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CentralizerDimension

open Matrix MvPolynomial

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

def centralizer (A : Matrix ι ι K) : Submodule K (Matrix ι ι K) where
  carrier := {B | A * B = B * A}
  zero_mem' := by simp
  add_mem' := by
    intro B C hB hC
    dsimp at hB hC ⊢
    simp only [mul_add, add_mul, hB, hC]
  smul_mem' := by
    intro c B hB
    dsimp at hB ⊢
    simp only [Matrix.mul_smul, Matrix.smul_mul, hB]

@[simp] theorem mem_centralizer (A B : Matrix ι ι K) :
    B ∈ centralizer A ↔ A * B = B * A := Iff.rfl

def centralizerOne (A : Matrix ι ι K) : centralizer A :=
  ⟨1, by simp⟩

noncomputable def centralizerBasis (A : Matrix ι ι K) :
    Module.Basis (Fin (Module.finrank K (centralizer A))) K (centralizer A) :=
  Module.finBasis K (centralizer A)

noncomputable def coordinateMatrix (A : Matrix ι ι K) :
    Matrix ι ι (MvPolynomial (Fin (Module.finrank K (centralizer A))) K) :=
  fun i j => ∑ b, C ((centralizerBasis A b).val i j) * X b

noncomputable def determinantPolynomial (A : Matrix ι ι K) :
    MvPolynomial (Fin (Module.finrank K (centralizer A))) K :=
  (coordinateMatrix A).det

end PermanentBorder.CentralizerDimension

namespace PermanentBorder.MatrixFieldExtension
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Fintype ι] [DecidableEq ι]

theorem rank_map (φ : K →+* L) (M : Matrix ι ι K) :
    (M.map φ).rank = M.rank := by
  classical
  obtain ⟨U, V, d, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal M
  let P := (U.map Matrix.TransvectionStruct.toMatrix).prod
  let Q := (V.map Matrix.TransvectionStruct.toMatrix).prod
  have hP : P.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod U
  have hQ : Q.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod V
  have hP' : (P.map φ).det = 1 := by
    change (φ.mapMatrix P).det = 1
    rw [← φ.map_det, hP, map_one]
  have hQ' : (Q.map φ).det = 1 := by
    change (φ.mapMatrix Q).det = 1
    rw [← φ.map_det, hQ, map_one]
  have h' : P.map φ * M.map φ * Q.map φ = diagonal (φ ∘ d) := by
    simpa only [Matrix.map_mul, Matrix.diagonal_map (map_zero φ), Function.comp_def] using
      congrArg (fun X : Matrix ι ι K => X.map φ) h
  calc
    (M.map φ).rank = (P.map φ * M.map φ * Q.map φ).rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (hQ' ▸ isUnit_one),
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hP' ▸ isUnit_one)]
    _ = (diagonal (φ ∘ d)).rank := congrArg Matrix.rank h'
    _ = (diagonal d).rank := by
      simp only [Matrix.rank_diagonal, Function.comp_apply, map_ne_zero]
    _ = (P * M * Q).rank := congrArg Matrix.rank h.symm
    _ = M.rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (hQ ▸ isUnit_one),
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hP ▸ isUnit_one)]

theorem finrank_ker_map (φ : K →+* L) (M : Matrix ι ι K) :
    Module.finrank L (LinearMap.ker (M.map φ).mulVecLin) =
      Module.finrank K (LinearMap.ker M.mulVecLin) := by
  have h := M.mulVecLin.finrank_range_add_finrank_ker
  have h' := (M.map φ).mulVecLin.finrank_range_add_finrank_ker
  change M.rank + _ = _ at h
  change (M.map φ).rank + _ = _ at h'
  rw [rank_map] at h'
  simp only [Module.finrank_fintype_fun_eq_card] at h h'
  omega

end PermanentBorder.MatrixFieldExtension

namespace PermanentBorder.CentralizerBaseChange
open Matrix CentralizerDimension MatrixFieldExtension
variable {K L ι : Type*} [Field K] [Field L]
  [Fintype ι] [DecidableEq ι]

def equationMatrix (A : Matrix ι ι K) : Matrix (ι × ι) (ι × ι) K :=
  fun i j => (if i.2 = j.2 then A i.1 j.1 else 0) -
    (if i.1 = j.1 then A j.2 i.2 else 0)

theorem equationMatrix_mulVec (A B : Matrix ι ι K) :
    equationMatrix A *ᵥ Function.uncurry B = Function.uncurry (A * B - B * A) := by
  funext ij
  rcases ij with ⟨i,j⟩
  change (∑ a : ι × ι, ((if j = a.2 then A i a.1 else 0) -
    (if i = a.1 then A a.2 j else 0)) * B a.1 a.2) =
    (∑ a, A i a * B a j) - ∑ a, B i a * A a j
  simp only [Fintype.sum_prod_type, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_comm]

omit [Fintype ι] in
@[simp] theorem equationMatrix_map (A : Matrix ι ι K) (φ : K →+* L) :
    equationMatrix (A.map φ) = (equationMatrix A).map φ := by
  ext i j
  simp only [equationMatrix, Matrix.map_apply, map_sub, apply_ite φ, map_zero]

def centralizerKernelEquiv (A : Matrix ι ι K) :
    centralizer A ≃ₗ[K] LinearMap.ker (equationMatrix A).mulVecLin where
  toFun B := ⟨Function.uncurry B.val, by
    change equationMatrix A *ᵥ Function.uncurry B.val = 0
    rw [equationMatrix_mulVec, sub_eq_zero.mpr B.property]
    rfl⟩
  invFun v := ⟨(fun i j => v.val (i,j)), by
    apply sub_eq_zero.mp
    have h := equationMatrix_mulVec A (show Matrix ι ι K from fun i j => v.val (i,j))
    ext i j
    exact (congrFun h (i,j)).symm.trans (congrFun v.property (i,j))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Algebra K L]

theorem finrank_centralizer_map (A : Matrix ι ι K) :
    Module.finrank L (centralizer (A.map (algebraMap K L))) =
      Module.finrank K (centralizer A) := by
  calc
    _ = Module.finrank L (LinearMap.ker (equationMatrix (A.map (algebraMap K L))).mulVecLin) :=
      (centralizerKernelEquiv _).finrank_eq
    _ = Module.finrank L (LinearMap.ker ((equationMatrix A).map (algebraMap K L)).mulVecLin) := by
      rw [equationMatrix_map]
    _ = Module.finrank K (LinearMap.ker (equationMatrix A).mulVecLin) :=
      finrank_ker_map _ _
    _ = _ := (centralizerKernelEquiv _).finrank_eq.symm

def flatten (F : Type*) [Field F] (ι : Type*) :
    Matrix ι ι F ≃ₗ[F] (ι × ι → F) where
  toFun := Function.uncurry
  invFun := Function.curry
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def mapCentralizer (A : Matrix ι ι K) (B : centralizer A) :
    centralizer (A.map (algebraMap K L)) :=
  ⟨B.val.map (algebraMap K L), by
    change A.map _ * B.val.map _ = B.val.map _ * A.map _
    rw [← Matrix.map_mul, ← Matrix.map_mul, B.property]⟩

theorem mapCentralizer_linearIndependent {κ : Type*}
    (A : Matrix ι ι K) (b : Module.Basis κ K (centralizer A)) :
    LinearIndependent L (fun i => mapCentralizer (L := L) A (b i)) := by
  have hb : LinearIndependent K (fun i => Function.uncurry (b i).val) :=
    (b.linearIndependent.map' (centralizer A).subtype (Submodule.ker_subtype _)).map'
      (flatten K ι).toLinearMap (LinearEquiv.ker _)
  have hm : LinearIndependent L (fun i => algebraMap K L ∘ Function.uncurry (b i).val) :=
    (linearIndependent_algebraMap_comp_iff (R := K) (S := L)).mpr hb
  exact hm.of_comp ((flatten L ι).toLinearMap.comp (centralizer (A.map (algebraMap K L))).subtype)

noncomputable def centralizerBasisMap {κ : Type*} [Fintype κ]
    (A : Matrix ι ι K) (b : Module.Basis κ K (centralizer A)) :
    Module.Basis κ L (centralizer (A.map (algebraMap K L))) :=
  basisOfLinearIndependentOfCardEqFinrank' (fun i => mapCentralizer (L := L) A (b i))
    (mapCentralizer_linearIndependent A b)
    (by rw [finrank_centralizer_map, Module.finrank_eq_card_basis b])

@[simp] theorem centralizerBasisMap_apply {κ : Type*} [Fintype κ]
    (A : Matrix ι ι K) (b : Module.Basis κ K (centralizer A)) (i : κ) :
    centralizerBasisMap (L := L) A b i = mapCentralizer A (b i) := by
  simp only [centralizerBasisMap, coe_basisOfLinearIndependentOfCardEqFinrank']

end PermanentBorder.CentralizerBaseChange

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.CoordinateFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CoordinateNormalization
open Matrix MvPolynomial
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Infinite K]
  [Fintype ι] [DecidableEq ι]

noncomputable def basisDeterminant {κ : Type*} [Fintype κ]
    (S : Submodule L ((ι × ι) → L)) (b : Module.Basis κ L S) : MvPolynomial κ L :=
  Matrix.det (of fun i j => ∑ a, C ((b a).val (i,j)) * X a)

end PermanentBorder.CoordinateNormalization

namespace PermanentBorder.OrbitNormalization
open Matrix CentralizerDimension CentralizerBaseChange CoordinateNormalization
variable {L ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]

def intertwinerSpace (A C : Matrix ι ι L) : Submodule L (ι × ι → L) where
  carrier := {v | A * Matrix.of (Function.curry v) = Matrix.of (Function.curry v) * C}
  zero_mem' := by change A * 0 = 0 * C; simp
  add_mem' := by
    intro v w hv hw
    change A * (Matrix.of (Function.curry v) + Matrix.of (Function.curry w)) =
      (Matrix.of (Function.curry v) + Matrix.of (Function.curry w)) * C
    rw [mul_add, add_mul, hv, hw]
  smul_mem' := by
    intro c v hv
    change A * (c • Matrix.of (Function.curry v)) =
      (c • Matrix.of (Function.curry v)) * C
    rw [Matrix.mul_smul, hv, Matrix.smul_mul]

def intertwinerEquivCentralizer (A C : Matrix ι ι L)
    (P : (Matrix ι ι L)ˣ) (hP : A * (P : Matrix ι ι L) = (P : Matrix ι ι L) * C) :
    centralizer C ≃ₗ[L] intertwinerSpace A C := by
  have hCP : C * (↑P⁻¹ : Matrix ι ι L) = (↑P⁻¹ : Matrix ι ι L) * A := by
    have h := congrArg (fun M : Matrix ι ι L => (↑P⁻¹ : Matrix ι ι L) * M * (↑P⁻¹ : Matrix ι ι L)) hP
    simp only [← mul_assoc, Units.inv_mul, one_mul] at h
    simpa only [mul_assoc, Units.mul_inv, mul_one] using h.symm
  refine
    { toFun := fun B => ⟨Function.uncurry ((P : Matrix ι ι L) * B.val), by
        change A * ((P : Matrix ι ι L) * B.val) = ((P : Matrix ι ι L) * B.val) * C
        rw [← mul_assoc, hP, mul_assoc, B.property, ← mul_assoc]⟩
      invFun := fun v => ⟨(↑P⁻¹ : Matrix ι ι L) * Matrix.of (Function.curry v.val), by
        change C * ((↑P⁻¹ : Matrix ι ι L) * Matrix.of (Function.curry v.val)) =
          ((↑P⁻¹ : Matrix ι ι L) * Matrix.of (Function.curry v.val)) * C
        rw [← mul_assoc, hCP, mul_assoc, v.property, ← mul_assoc]⟩
      left_inv := fun B => by
        apply Subtype.ext
        change (↑P⁻¹ : Matrix ι ι L) * ((P : Matrix ι ι L) * B.val) = B.val
        rw [← mul_assoc, Units.inv_mul, one_mul]
      right_inv := fun v => by
        apply Subtype.ext
        change Function.uncurry ((P : Matrix ι ι L) *
          ((↑P⁻¹ : Matrix ι ι L) * Matrix.of (Function.curry v.val))) = v.val
        rw [← mul_assoc, Units.mul_inv, one_mul]
        rfl
      map_add' := fun B D => by
        apply Subtype.ext
        change Function.uncurry ((P : Matrix ι ι L) * (B.val + D.val)) = _
        rw [mul_add]
        rfl
      map_smul' := fun c B => by
        apply Subtype.ext
        change Function.uncurry ((P : Matrix ι ι L) * (c • B.val)) = _
        rw [Matrix.mul_smul]
        rfl }

end PermanentBorder.OrbitNormalization

namespace PermanentBorder.CentralizerParameters
open Matrix MvPolynomial CentralizerDimension CentralizerBaseChange
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

noncomputable def coefficients (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) :
    Fin (Module.finrank K (centralizer C)) → L :=
  (centralizerBasisMap C (centralizerBasis C)).repr B

end PermanentBorder.CentralizerParameters

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Nilpotents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.NilpotentOrbits
open scoped DirectSum
open Submodule Module Polynomial Ideal Submodule.IsPrincipal Submodule.Quotient

section Nilpotent
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev Block (e : ℕ) := K[X] ⧸ Ideal.span {(X : K[X]) ^ e}

end Nilpotent

end PermanentBorder.NilpotentOrbits

namespace PermanentBorder.NilpotentBlocks
open Polynomial Module
open scoped DirectSum
variable {K : Type*} [Field K]

abbrev Block (e : ℕ) := K[X] ⧸ Ideal.span {(X : K[X]) ^ e}

noncomputable def blockBasis (e : ℕ) : Basis (Fin e) K (Block (K := K) e) :=
  (AdjoinRoot.powerBasis' (monic_X_pow e)).basis.reindex (finCongr (natDegree_X_pow e))

@[simp] theorem blockBasis_apply (e : ℕ) (i : Fin e) :
    blockBasis (K := K) e i = Ideal.Quotient.mk _ ((X : K[X]) ^ i.val) := by
  change ((AdjoinRoot.powerBasis' (monic_X_pow e)).basis.reindex
    (finCongr (natDegree_X_pow e))) i = AdjoinRoot.mk _ (X ^ i.val)
  rw [Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simp only [AdjoinRoot.powerBasis'_gen]
  exact (map_pow (AdjoinRoot.mk _) X i.val).symm

noncomputable def sumBasis {n : ℕ} (e : Fin n → ℕ) :
    Basis (Σ i : Fin n, Fin (e i)) K (⨁ i : Fin n, Block (K := K) (e i)) :=
  DFinsupp.basis (fun i => blockBasis (e i))

@[simp] theorem sumBasis_apply {n : ℕ} (e : Fin n → ℕ)
    (i : Fin n) (j : Fin (e i)) :
    sumBasis (K := K) e ⟨i,j⟩ =
      DirectSum.lof K (Fin n) (fun i => Block (K := K) (e i)) i (blockBasis (e i) j) := by
  classical
  simp [sumBasis, DFinsupp.basis, Basis.coe_ofRepr]
  rfl

noncomputable def action {n : ℕ} (e : Fin n → ℕ) :
    Module.End K (⨁ i : Fin n, Block (K := K) (e i)) where
  toFun x := (X : K[X]) • x
  map_add' := smul_add _
  map_smul' := by intro a x; exact smul_comm _ _ _

def shiftMatrix {n : ℕ} (e : Fin n → ℕ) :
    Matrix (Σ i : Fin n, Fin (e i)) (Σ i : Fin n, Fin (e i)) K :=
  fun a b => if a.1 = b.1 ∧ a.2.val = b.2.val + 1 then 1 else 0

@[simp] theorem shiftMatrix_map {L : Type*} [Field L] (φ : K →+* L)
    {n : ℕ} (e : Fin n → ℕ) :
    (shiftMatrix (K := K) e).map φ = shiftMatrix (K := L) e := by
  ext a b
  simp [shiftMatrix]

end PermanentBorder.NilpotentBlocks

namespace PermanentBorder.NilpotentBlocks
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def indexEquiv {n : ℕ} (e : Fin n → ℕ) (he : (∑ i, e i) = n) :
    (Σ i : Fin n, Fin (e i)) ≃ Fin n :=
  Fintype.equivFinOfCardEq (by simpa only [Fintype.card_sigma, Fintype.card_fin] using he)

noncomputable def shapeMatrix {n : ℕ} (e : Fin n → ℕ) (he : (∑ i, e i) = n) :
    Matrix (Fin n) (Fin n) K :=
  (shiftMatrix (K := K) e).reindex (indexEquiv e he) (indexEquiv e he)

@[simp] theorem shapeMatrix_map {L : Type*} [Field L] (φ : K →+* L)
    {n : ℕ} (e : Fin n → ℕ) (he : (∑ i, e i) = n) :
    (shapeMatrix (K := K) e he).map φ = shapeMatrix (K := L) e he := by
  ext i j
  simp [shapeMatrix, Matrix.reindex_apply, shiftMatrix]

end PermanentBorder.NilpotentBlocks

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.PunctualCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.GenericMatrix
open Matrix MvPolynomial
universe u
variable (L : Type u) [Field L] (n : ℕ)

abbrev CoordinateRing := MvPolynomial (Fin n × Fin n) L
abbrev FunctionField := FractionRing (CoordinateRing L n)
noncomputable def coordinateMatrix : Matrix (Fin n) (Fin n) (CoordinateRing L n) :=
  fun i j => X (i,j)
noncomputable def genericMatrix : Matrix (Fin n) (Fin n) (FunctionField L n) :=
  (coordinateMatrix L n).map (algebraMap (CoordinateRing L n) (FunctionField L n))

theorem coordinate_det_ne_zero : (coordinateMatrix L n).det ≠ 0 := by
  intro h
  let f : CoordinateRing L n →ₐ[L] L := aeval (fun ij => (1 : Matrix (Fin n) (Fin n) L) ij.1 ij.2)
  have he : (coordinateMatrix L n).map f = (1 : Matrix (Fin n) (Fin n) L) := by
    ext i j
    exact aeval_X _ _
  have hh := congrArg f h
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, he, Matrix.det_one, map_zero] at hh
  exact one_ne_zero hh

theorem generic_det_ne_zero : (genericMatrix L n).det ≠ 0 := by
  change ((algebraMap (CoordinateRing L n) (FunctionField L n)).mapMatrix
    (coordinateMatrix L n)).det ≠ 0
  rw [← RingHom.map_det]
  exact fun h => coordinate_det_ne_zero L n
    ((IsFractionRing.injective (CoordinateRing L n) (FunctionField L n)) (by simpa using h))

noncomputable def genericUnit : (Matrix (Fin n) (Fin n) (FunctionField L n))ˣ :=
  ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (generic_det_ne_zero L n))).unit

@[simp] theorem genericUnit_val : (genericUnit L n : Matrix (Fin n) (Fin n) (FunctionField L n)) =
    genericMatrix L n := IsUnit.unit_spec _

end PermanentBorder.GenericMatrix

namespace PermanentBorder.CyclicFrames
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

def MonomialBasis (r s : ι → ℕ) (A B : Matrix ι ι L) (v : ι → L) : Prop :=
  ∀ i, (A ^ r i * B ^ s i).mulVec v = Pi.single i 1

end PermanentBorder.CyclicFrames

namespace PermanentBorder.CyclicFrames
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Fintype ι] [DecidableEq ι]

theorem MonomialBasis.map (f : K →+* L) {r s : ι → ℕ}
    {A B : Matrix ι ι K} {v : ι → K} (h : MonomialBasis r s A B v) :
    MonomialBasis r s (A.map f) (B.map f) (f ∘ v) := by
  intro i
  have hh := congrArg (fun w : ι → K => f ∘ w) (h i)
  ext j
  have hj := congrFun hh j
  change f (((A ^ r i * B ^ s i).mulVec v) j) = f ((Pi.single i (1 : K) : ι → K) j) at hj
  rw [RingHom.map_mulVec, Matrix.map_mul] at hj
  have hpa : (A ^ r i).map f = (A.map f) ^ r i := (f.mapMatrix.map_pow A _)
  have hpb : (B ^ s i).map f = (B.map f) ^ s i := (f.mapMatrix.map_pow B _)
  rw [hpa, hpb] at hj
  rw [hj]
  by_cases hij : j = i
  · subst j
    simp
  · simp [hij]

def conjugation (Q : (Matrix ι ι L)ˣ) : Matrix ι ι L →+* Matrix ι ι L where
  toFun A := (Q : Matrix ι ι L) * A * (↑Q⁻¹ : Matrix ι ι L)
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by simp only [mul_add, add_mul]
  map_mul' A B := by
    simp only [mul_assoc]
    rw [← mul_assoc (↑Q⁻¹ : Matrix ι ι L) (↑Q : Matrix ι ι L),
      Units.inv_mul, one_mul]

end PermanentBorder.CyclicFrames
namespace PermanentBorder.PunctualCharts
open Matrix Algebra CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

def tripleEntries {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) (v : Fin n → L) : Set L :=
  (Set.range fun ij : Fin n × Fin n => A ij.1 ij.2) ∪
  (Set.range fun ij : Fin n × Fin n => B ij.1 ij.2) ∪ Set.range v

end PermanentBorder.PunctualCharts

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.CurveParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.CurveParameters
open Matrix Algebra MvPolynomial CyclicFrames
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

structure LocalChart (p : MvPolynomial (Fin 2) K) where
  length : ℕ
  positive : 0 < length
  support : Fin 2 → L
  on_curve : aeval support p = 0
  r : Fin length → ℕ
  s : Fin length → ℕ
  A : Matrix (Fin length) (Fin length) L
  B : Matrix (Fin length) (Fin length) L
  v : Fin length → L
  nilA : IsNilpotent A
  nilB : IsNilpotent B
  commutes : A * B = B * A
  basis_eq : MonomialBasis r s A B v

namespace LocalChart
variable {p : MvPolynomial (Fin 2) K}

def InField (D : LocalChart (L := L) p) (F : IntermediateField K L) : Prop :=
  (∀ i, D.support i ∈ F) ∧ (∀ i j, D.A i j ∈ F) ∧
  (∀ i j, D.B i j ∈ F) ∧ (∀ i, D.v i ∈ F)

end LocalChart

end PermanentBorder.CurveParameters

namespace PermanentBorder.FiniteAlgebras
open Module
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R] [Module.Finite L R]

theorem maximal_power_ne_top (m : MaximalSpectrum R) {e : ℕ} (he : 0 < e) :
    m.asIdeal ^ e ≠ ⊤ := by
  intro h
  exact m.isMaximal.ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self he.ne'))

end PermanentBorder.FiniteAlgebras
namespace PermanentBorder.FiniteAlgebras
open Module MvPolynomial
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R]
  [Module.Finite L R] [IsAlgClosed L]

noncomputable def residueEquiv (m : MaximalSpectrum R) :
    L ≃ₐ[L] R ⧸ m.asIdeal := by
  have : m.asIdeal.IsMaximal := m.isMaximal
  let _ : Field (R ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  exact AlgEquiv.ofBijective (Algebra.ofId L (R ⧸ m.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

noncomputable def residue (m : MaximalSpectrum R) : R →ₐ[L] L :=
  (residueEquiv L R m).symm.toAlgHom.comp (Ideal.Quotient.mkₐ L m.asIdeal)

theorem sub_residue_mem (m : MaximalSpectrum R) (x : R) :
    x - algebraMap L R (residue L R m x) ∈ m.asIdeal := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub]
  change Ideal.Quotient.mk m.asIdeal x - residueEquiv L R m
    ((residueEquiv L R m).symm (Ideal.Quotient.mk m.asIdeal x)) = 0
  rw [AlgEquiv.apply_symm_apply, sub_self]

theorem residue_nilpotent (m : MaximalSpectrum R) (e : ℕ) (x : R) :
    IsNilpotent (Ideal.Quotient.mk (m.asIdeal ^ e) x -
      algebraMap L (R ⧸ m.asIdeal ^ e) (residue L R m x)) := by
  refine ⟨e,?_⟩
  change (Ideal.Quotient.mk (m.asIdeal ^ e)
    (x - algebraMap L R (residue L R m x))) ^ e = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (sub_residue_mem L R m x) e

noncomputable def supportPoint (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) : Fin 2 → L := fun i => residue L R m (q (X i))

theorem supportPoint_on_curve (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) (p : MvPolynomial (Fin 2) L) (hp : q p = 0) :
    aeval (supportPoint L R q m) p = 0 := by
  have h : (residue L R m).comp q = aeval (supportPoint L R q m) := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X, supportPoint]
  rw [← h, AlgHom.comp_apply, hp, map_zero]

end PermanentBorder.FiniteAlgebras

namespace PermanentBorder.PlaneTranslations
open MvPolynomial
variable {L : Type*} [CommRing L]

noncomputable def translate (a : Fin 2 → L) :
    MvPolynomial (Fin 2) L →ₐ[L] MvPolynomial (Fin 2) L :=
  aeval fun i => X i + C (a i)

@[simp] theorem translate_X (a : Fin 2 → L) (i : Fin 2) :
    translate a (X i) = X i + C (a i) := aeval_X _ _

@[simp] theorem translate_C (a : Fin 2 → L) (c : L) :
    translate a (C c) = C c := by exact (translate a).commutes c

theorem translate_comp (a b : Fin 2 → L) :
    (translate a).comp (translate b) = translate (a+b) := by
  ext i
  simp only [AlgHom.comp_apply, translate_X, map_add, translate_C, Pi.add_apply, map_add]
  simp only [add_assoc]

noncomputable def equivalence (a : Fin 2 → L) :
    MvPolynomial (Fin 2) L ≃ₐ[L] MvPolynomial (Fin 2) L :=
  AlgEquiv.ofAlgHom (translate a) (translate (-a))
    (by rw [translate_comp]; ext i; simp)
    (by rw [translate_comp]; ext i; simp)

@[simp] theorem equivalence_X (a : Fin 2 → L) (i : Fin 2) :
    equivalence a (X i) = X i + C (a i) := by
  exact translate_X a i

end PermanentBorder.PlaneTranslations

namespace PermanentBorder.FinitePlaneFrames
open MvPolynomial Module Matrix
variable {L S : Type*} [Field L] [CommRing S] [Algebra L S]

noncomputable def representation {n : ℕ} (b : Basis (Fin n) L S) :
    S →ₐ[L] Matrix (Fin n) (Fin n) L :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lmul L S)

noncomputable def unitVector {n : ℕ} (b : Basis (Fin n) L S) : Fin n → L := b.equivFun 1

end PermanentBorder.FinitePlaneFrames
namespace PermanentBorder.FiniteAlgebras
open Module MvPolynomial Matrix FinitePlaneFrames
variable (L R : Type*) [Field L] [CommRing R] [Algebra L R]
  [Module.Finite L R] [IsAlgClosed L]

noncomputable def localHom (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) (e : ℕ) :
    MvPolynomial (Fin 2) L →ₐ[L] R ⧸ m.asIdeal ^ e :=
  (Ideal.Quotient.mkₐ L (m.asIdeal ^ e)).comp q

noncomputable def shiftedLocalHom (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) (e : ℕ) :
    MvPolynomial (Fin 2) L →ₐ[L] R ⧸ m.asIdeal ^ e :=
  (localHom L R q m e).comp (PlaneTranslations.translate (-supportPoint L R q m))

theorem shiftedLocalHom_X (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) (e : ℕ) (i : Fin 2) :
    shiftedLocalHom L R q m e (X i) = localHom L R q m e (X i) -
      algebraMap L (R ⧸ m.asIdeal ^ e) (supportPoint L R q m i) := by
  simp only [shiftedLocalHom, AlgHom.comp_apply, PlaneTranslations.translate_X,
    map_add, Pi.neg_apply, map_neg]
  rw [show (localHom L R q m e) (C (supportPoint L R q m i)) =
    algebraMap L (R ⧸ m.asIdeal ^ e) (supportPoint L R q m i) from
      (localHom L R q m e).commutes _]
  exact (sub_eq_add_neg _ _).symm

theorem shiftedLocalHom_X_nilpotent (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (m : MaximalSpectrum R) (e : ℕ) (i : Fin 2) :
    IsNilpotent (shiftedLocalHom L R q m e (X i)) := by
  rw [shiftedLocalHom_X]
  exact residue_nilpotent L R m e (q (X i))

omit [IsAlgClosed L] in

theorem local_length_pos (m : MaximalSpectrum R) {e : ℕ} (he : 0 < e) :
    0 < finrank L (R ⧸ m.asIdeal ^ e) := by
  have : Nontrivial (R ⧸ m.asIdeal ^ e) :=
    Ideal.Quotient.nontrivial_iff.mpr (maximal_power_ne_top R m he)
  exact finrank_pos

end PermanentBorder.FiniteAlgebras

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.QuotientFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.FiniteAlgebras
open Module MvPolynomial Matrix FinitePlaneFrames CurveParameters
universe u
variable {K L : Type u} {R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R] [Module.Finite L R] [IsAlgClosed L]

noncomputable def localChart (q : MvPolynomial (Fin 2) L →ₐ[L] R)
    (p : MvPolynomial (Fin 2) K) (hpq : q (p.map (algebraMap K L)) = 0)
    (m : MaximalSpectrum R) (e : ℕ) (he : 0 < e)
    (b : Basis (Fin (finrank L (R ⧸ m.asIdeal ^ e))) L (R ⧸ m.asIdeal ^ e))
    (r s : Fin (finrank L (R ⧸ m.asIdeal ^ e)) → ℕ)
    (hb : CyclicFrames.MonomialBasis r s
      (representation b (shiftedLocalHom L R q m e (X 0)))
      (representation b (shiftedLocalHom L R q m e (X 1))) (unitVector b)) :
    LocalChart (L := L) p where
  length := finrank L (R ⧸ m.asIdeal ^ e)
  positive := local_length_pos L R m he
  support := supportPoint L R q m
  on_curve := by
    have h := supportPoint_on_curve L R q m (p.map (algebraMap K L)) hpq
    simpa only [aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp] using h
  r := r
  s := s
  A := representation b (shiftedLocalHom L R q m e (X 0))
  B := representation b (shiftedLocalHom L R q m e (X 1))
  v := unitVector b
  nilA := (shiftedLocalHom_X_nilpotent L R q m e 0).map (representation b)
  nilB := (shiftedLocalHom_X_nilpotent L R q m e 1).map (representation b)
  commutes := by
    have h := congrArg (representation b) (mul_comm
      (shiftedLocalHom L R q m e (X 0)) (shiftedLocalHom L R q m e (X 1)))
    simpa only [map_mul] using h
  basis_eq := hb

end PermanentBorder.FiniteAlgebras

namespace PermanentBorder.AdjugateAlgebra
open Polynomial Matrix Module
variable {K : Type*} [Field K] {k : ℕ}

@[simp] theorem planeMap_single (d : ℕ) (i : PlaneIndex d) :
    planeMap d (Pi.single i (1 : K)) =
      monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1) := by
  classical
  simp only [planeMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

noncomputable def rowCoordinateMap (θ : Fin (k+1) → K)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    (PlaneIndex (k-1) → K) →ₗ[K] (K[X][X] ⧸ rowIdeal (pencilBase θ A)) :=
  (Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A))).toLinearMap.comp (planeMap (k-1))

theorem rowCoordinateMap_bijective (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Function.Bijective (rowCoordinateMap θ A) := by
  classical
  have hinj : Function.Injective (rowCoordinateMap θ A) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hmem : planeMap (k-1) v ∈ rowIdeal (pencilBase θ A) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hv
    have hz := rowIdeal_low_degree_zero θ hθ A hk hmem (totalDegreeLE_planeMap (k-1) v)
    funext i
    have hc := congrArg (fun p : K[X][X] => (p.coeff i.val.1.val).coeff
      (i.val.2.val-i.val.1.val-1)) hz
    simpa only [coeff_planeMap, coeff_zero, Pi.zero_apply] using hc
  refine ⟨hinj, LinearMap.range_eq_top.mp ?_⟩
  apply top_unique
  rw [← row_quotient_spanned θ hθ A hk]
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  refine ⟨Pi.single i 1, ?_⟩
  simp [rowCoordinateMap]

noncomputable def rowCoordinates (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    (PlaneIndex (k-1) → K) ≃ₗ[K] (K[X][X] ⧸ rowIdeal (pencilBase θ A)) :=
  LinearEquiv.ofBijective (rowCoordinateMap θ A) (rowCoordinateMap_bijective θ hθ A hk)

noncomputable def rowBasis (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) :
    Basis (PlaneIndex (k-1)) K (K[X][X] ⧸ rowIdeal (pencilBase θ A)) :=
  Basis.ofEquivFun (rowCoordinates θ hθ A hk).symm

@[simp] theorem rowBasis_apply (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K) (hk : 0 < k) (i : PlaneIndex (k-1)) :
    rowBasis θ hθ A hk i = (Ideal.Quotient.mkₐ K (rowIdeal (pencilBase θ A)))
      (monomial i.val.1.val (monomial (i.val.2.val-i.val.1.val-1) 1)) := by
  classical
  rw [rowBasis, Basis.coe_ofEquivFun]
  change rowCoordinateMap θ A (Pi.single i 1) = _
  simp [rowCoordinateMap]

end PermanentBorder.AdjugateAlgebra

namespace PermanentBorder.Bivariate
open Polynomial
variable (K : Type*) [CommSemiring K]

noncomputable def equivalence : MvPolynomial (Fin 2) K ≃ₐ[K] K[X][X] :=
  (MvPolynomial.finSuccEquiv K 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)))

@[simp] theorem equivalence_X_zero :
    equivalence K (MvPolynomial.X 0) = (X : K[X][X]) := by
  simp [equivalence, MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem equivalence_X_one :
    equivalence K (MvPolynomial.X 1) = C (X : K[X]) := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X (Fin.succ 0))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp] theorem equivalence_C (c : K) :
    equivalence K (MvPolynomial.C c) = C (C c) := (equivalence K).commutes c

variable {K} {L : Type*} [CommSemiring L]

noncomputable def map (f : K →+* L) : K[X][X] →+* L[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom f)

@[simp] theorem equivalence_monomial (a b : ℕ) :
    equivalence K (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      monomial a (monomial b (1 : K)) := by
  simp only [map_mul, map_pow, equivalence_X_zero, equivalence_X_one]
  rw [← Polynomial.C_pow]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_one, one_mul]
  exact mul_comm _ _

end PermanentBorder.Bivariate

namespace PermanentBorder.Bivariate
open Polynomial
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def InField (F : IntermediateField K L) (P : L[X][X]) : Prop :=
  ∀ a b, (P.coeff a).coeff b ∈ F

end PermanentBorder.Bivariate

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.FiberDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.DeterminantFiberScheme
open Polynomial
universe u
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

noncomputable def pencil (θ : Fin n → R) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R[X][X] :=
  (X : R[X][X]) • 1 +
    (((X : R[X]) • (Matrix.diagonal θ).map C + A.map C).map C)

end PermanentBorder.DeterminantFiberScheme

namespace PermanentBorder.DeterminantFibers
open Polynomial AdjugateAlgebra
universe u
variable {K L : Type u} [Field K] [Infinite K] [Field L] [Algebra K L]
  [IsAlgClosed L] {k : ℕ}

noncomputable def curveCoefficientField (P : L[X][X]) : IntermediateField K L :=
  IntermediateField.adjoin K (Set.range (fun ab : ℕ × ℕ => (P.coeff ab.1).coeff ab.2))

end PermanentBorder.DeterminantFibers

namespace PermanentBorder.SpectralDimension
open MvPolynomial Polynomial Matrix
open Conductor AdjugateAlgebra DeterminantFibers
universe u

noncomputable def normalizationDefect {L : Type u} [Field L] {k : ℕ}
    (θ : Fin (k+1) → L) (A : Matrix (Fin (k+1)) (Fin (k+1)) L) : ℕ∞ :=
  let T := -(pencilBase θ A)
  let Q := FractionRing L[X]
  let R := integralClosure L[X] (AdjoinRoot (T.charpoly.map (algebraMap L[X] Q)))
  Module.length L (R ⧸ LinearMap.range
    (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toLinearMap)

variable (K : Type u) [Field K]

noncomputable def gradientIdeal {k : ℕ} (θ : Fin (k+1) → K) (q : ℕ) :
    Ideal (MvPolynomial (Fin (k+1) × Fin (k+1)) K) :=
  Ideal.span (Set.range (fun ij => pderiv ij (Selector.diagonalCoefficient
    (Matrix.of fun a b => (MvPolynomial.X (a,b) :
      MvPolynomial (Fin (k+1) × Fin (k+1)) K)) (fun i => MvPolynomial.C (θ i)) q)))

end PermanentBorder.SpectralDimension

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Monogenic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.NormalizationDerivation
open Polynomial TensorProduct

section Localization
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyEtale S T]

noncomputable def extendEtale (d : Derivation R S S) : Derivation R T T :=
  ((TensorProduct.AlgebraTensorModule.rid S T T).toLinearMap.comp
    ((d.liftKaehlerDifferential.baseChange T).comp
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap)).compDer
        (KaehlerDifferential.D R T)

@[simp] lemma extendEtale_algebraMap (d : Derivation R S S) (s : S) :
    extendEtale (T := T) d (algebraMap S T s) = algebraMap S T (d s) := by
  simp only [extendEtale, Derivation.coe_comp, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Derivation.coeFn_coe,
    LinearEquiv.coe_coe, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.baseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]

end Localization

section Polynomial
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

noncomputable def coeffDeriv (d : Derivation R S S) : Derivation R S[X] S[X] :=
  PolynomialModule.equivPolynomialSelf.compDer d.mapCoeffs

@[simp] lemma coeffDeriv_coeff (d : Derivation R S S) (p : S[X]) (i : ℕ) :
    (coeffDeriv d p).coeff i = d (p.coeff i) := rfl

@[simp] lemma coeffDeriv_C (d : Derivation R S S) (s : S) :
    coeffDeriv d (C s) = C (d s) := by
  ext i
  simp only [coeffDeriv_coeff, coeff_C]
  split_ifs <;> simp

@[simp] lemma coeffDeriv_X (d : Derivation R S S) :
    coeffDeriv d (X : S[X]) = 0 := by
  ext i
  simp only [coeffDeriv_coeff, coeff_X, coeff_zero]
  split_ifs <;> simp

noncomputable def hamiltonian (d : Derivation R S S) (p : S[X]) :
    Derivation R S[X] S[X] :=
  p.derivative • coeffDeriv d - (coeffDeriv d p) • (derivative'.restrictScalars R)

lemma hamiltonian_self (d : Derivation R S S) (p : S[X]) : hamiltonian d p p = 0 := by
  simp only [hamiltonian, Derivation.sub_apply, Derivation.smul_apply,
    Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul]
  ring

@[simp] lemma hamiltonian_C (d : Derivation R S S) (p : S[X]) (s : S) :
    hamiltonian d p (C s) = p.derivative * C (d s) := by
  simp [hamiltonian]

@[simp] lemma hamiltonian_X (d : Derivation R S S) (p : S[X]) :
    hamiltonian d p X = -(coeffDeriv d p) := by
  simp [hamiltonian]

lemma hamiltonian_preserves_equation (d : Derivation R S S) (p q : S[X])
    (hq : p ∣ q) : p ∣ hamiltonian d p q := by
  obtain ⟨q,rfl⟩ := hq
  rw [Derivation.leibniz, hamiltonian_self]
  simp only [smul_eq_mul, mul_zero, add_zero]
  exact dvd_mul_right _ _

end Polynomial

section Monogenic
variable {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

noncomputable def scaledExtension (d : Derivation R S S) (u : B) (p : S[X])
    (hu : Algebra.adjoin S {u} = ⊤)
    (hp : ∀ q : S[X], aeval u q = 0 ↔ p ∣ q) : Derivation R B B :=
  Derivation.liftOfSurjective
    (f := (aeval u).restrictScalars R)
    (by change Function.Surjective (aeval u : S[X] →ₐ[S] B)
        rwa [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval])
    (d := hamiltonian d p)
    (fun q hq => (hp _).mpr (hamiltonian_preserves_equation d p q ((hp q).mp hq)))

end Monogenic
end PermanentBorder.NormalizationDerivation

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.BranchConductor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.ReducedBranchConductor
open Polynomial

section Ideal
variable {S : Type*} [CommRing S]
noncomputable def gradientIdeal (f b c d : S[X]) (x : S) : Ideal S[X] :=
  Ideal.span {f, b^2+X*d^2,c^2+C x*d^2}
noncomputable def enlargedGradientIdeal (f b c d : S[X]) (x : S) : Ideal S[X] :=
  gradientIdeal f b c d x ⊔ Ideal.span {d^2} * (gradientIdeal f b c d x).radical

end Ideal

end PermanentBorder.ReducedBranchConductor
namespace PermanentBorder.FactorNormalization
open Polynomial UniqueFactorizationMonoid
variable {S Q : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]

section Cofactors
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → S[X])
noncomputable def cofactor (i : ι) : S[X] := ∏ j ∈ Finset.univ.erase i, p j

end Cofactors
end PermanentBorder.FactorNormalization

namespace PermanentBorder.FactorNormalization
open Polynomial
section Reconstruct
variable {S Q ι : Type*} [CommRing S] [Field Q] [Algebra S Q]
  [Fintype ι] [DecidableEq ι]
variable (p : ι → S[X])
local notation "f" => ∏ i, p i
local notation "pQ" => fun i => Polynomial.map (algebraMap S Q) (p i)

noncomputable def component (i : ι) :
    AdjoinRoot ((f).map (algebraMap S Q)) →ₐ[Q] AdjoinRoot (pQ i) :=
  AdjoinRoot.algHomOfDvd Q _ _ (map_dvd (algebraMap S Q)
    (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))

omit [DecidableEq ι] in
@[simp] lemma component_mk (i : ι) (q : Q[X]) :
    component p i (AdjoinRoot.mk ((f).map (algebraMap S Q)) q) =
      AdjoinRoot.mk (pQ i) q := by
  change (AdjoinRoot.algHomOfDvd Q _ _ _) _ = _
  rw [← AdjoinRoot.aeval_eq,← aeval_algHom_apply,AdjoinRoot.algHomOfDvd_root,AdjoinRoot.aeval_eq]

end Reconstruct
end PermanentBorder.FactorNormalization
namespace PermanentBorder.ReducedBranchConductor
open Polynomial

section LocalGlobal
variable {S Q : Type*} [CommRing S] [Field Q] [Algebra S Q]

lemma map_tower (U : Type*) [CommRing U] [Algebra S U] [Algebra U Q]
    [IsScalarTower S U Q] (f : S[X]) :
    f.map (algebraMap S Q) = (f.map (algebraMap S U)).map (algebraMap U Q) := by
  rw [map_map,← IsScalarTower.algebraMap_eq]

noncomputable def genericChange (U : Type*) [CommRing U] [Algebra S U] [Algebra U Q]
    [IsScalarTower S U Q] (f : S[X]) :
    AdjoinRoot (f.map (algebraMap S Q)) ≃ₐ[Q]
      AdjoinRoot ((f.map (algebraMap S U)).map (algebraMap U Q)) :=
  AdjoinRoot.algEquivOfEq Q _ _ (map_tower U f)

end LocalGlobal

end PermanentBorder.ReducedBranchConductor

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.PlaneHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

abbrev Plane := MvPolynomial (Fin 2) K
abbrev weight : Fin 2 → ℤ := fun _ => 1
abbrev H (d : ℤ) := Piece (K := K) weight d

noncomputable def pieceCoordinates (d : ℤ) : H (K := K) d ≃ₗ[K] (DegreeIndex (Fin 2) d → K) where
  toFun p s := p.val.coeff s.val
  invFun b := ⟨∑ s : DegreeIndex (Fin 2) d, monomial s.val (b s), sum_degree_homogeneous d b⟩
  left_inv p := Subtype.ext (homogeneous_sum_degree p.property).symm
  right_inv b := funext (coeff_sum_degree d b)
  map_add' p q := by ext s; rfl
  map_smul' c p := by ext s; exact coeff_smul s.val c p.val

instance piece_finite (d : ℤ) : Module.Finite K (H (K := K) d) :=
  Module.Finite.of_injective (pieceCoordinates d).toLinearMap (pieceCoordinates d).injective

lemma degree_fin_two (s : Fin 2 →₀ ℕ) : s.degree = s 0+s 1 := by
  rw [Finsupp.degree_eq_sum]
  exact Fin.sum_univ_two s

noncomputable def degreeIndexEquiv (n : ℕ) : DegreeIndex (Fin 2) (n : ℤ) ≃ Fin (n+1) where
  toFun s := ⟨s.val 0, by
    have hs : s.val 0+s.val 1 = n := by exact_mod_cast degree_fin_two s.val ▸ s.property
    omega⟩
  invFun i := ⟨Finsupp.equivFunOnFinite.symm (fun j => if j=0 then i.val else n-i.val), by
    rw [degree_fin_two]
    simp only [Finsupp.coe_equivFunOnFinite_symm, ↓reduceIte, Fin.isValue]
    have hh : (1 : Fin 2) ≠ 0 := by decide
    simp only [hh, ↓reduceIte]
    omega⟩
  left_inv s := by
    apply Subtype.ext
    ext i
    have hs : s.val 0+s.val 1 = n := by exact_mod_cast degree_fin_two s.val ▸ s.property
    fin_cases i
    · simp
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
      change (if (1 : Fin 2) = 0 then s.val 0 else n - s.val 0) = s.val 1
      simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
      omega
  right_inv i := by
    apply Fin.ext
    simp

end PermanentBorder.PlaneHilbert

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

noncomputable def varMul (i : Fin 2) (n : ℕ) :
    H (K := K) (n : ℤ) →ₗ[K] H (K := K) ((n+1 : ℕ) : ℤ) where
  toFun p := ⟨X i * p.val, by
    have hh := (homogeneous_intWeight (isHomogeneous_X K i)).mul p.property
    change (X i * p.val).IsWeightedHomogeneous weight ((n+1 : ℕ) : ℤ)
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hh⟩
  map_add' p q := Subtype.ext (mul_add _ _ _)
  map_smul' c p := Subtype.ext (mul_smul_comm _ _ _)

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]

noncomputable abbrev multiplicationRange {a : Plane (K := K)} {e : ℤ}
    (ha : a.IsWeightedHomogeneous weight e) (t : ℤ) :=
  LinearMap.range (mulPiece weight ha t)

end PermanentBorder.PlaneHilbert

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.FilteredPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

noncomputable def filtered (q : Plane (K := K) →ₐ[K] R) : ℕ → Submodule K R
  | 0 => ⊥
  | n+1 => (restrictTotalDegree (Fin 2) K n).map q.toLinearMap

instance filtered_finite (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    Module.Finite K (filtered q n) := by
  cases n with
  | zero => exact inferInstanceAs (Module.Finite K (⊥ : Submodule K R))
  | succ n => exact Module.Finite.map _ _

noncomputable def topComponent (n : ℕ) : Plane (K := K) →ₗ[K] H (K := K) (n : ℤ) :=
  (homogeneousComponent n).codRestrict _ (fun p =>
    homogeneous_intWeight (homogeneousComponent_isHomogeneous n p))

noncomputable def leadingMap (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    H (K := K) (n : ℤ) →ₗ[K] R ⧸ filtered q n :=
  (filtered q n).mkQ.comp (q.toLinearMap.comp (H (K := K) (n : ℤ)).subtype)

noncomputable abbrev leadingRelations (q : Plane (K := K) →ₐ[K] R) (n : ℕ) :
    Submodule K (H (K := K) (n : ℤ)) := LinearMap.ker (leadingMap q n)

noncomputable def filteredH (q : Plane (K := K) →ₐ[K] R) (n : ℕ) : ℕ :=
  Module.finrank K (H (K := K) (n : ℤ) ⧸ leadingRelations q n)

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open MvPolynomial SliceParameters Multigraded
variable {K : Type*} [Field K]
variable (W : (n : ℕ) → Submodule K (H (K := K) (n : ℤ)))

noncomputable def quotientH (n : ℕ) : ℕ := Module.finrank K (H (K := K) (n : ℤ) ⧸ W n)

end PermanentBorder.PlaneHilbert
namespace PermanentBorder.PlaneHilbert
open Finset
variable (h : ℕ → ℕ)
noncomputable def hSum (n : ℕ) : ℕ := ∑ i ∈ range n, h i

end PermanentBorder.PlaneHilbert

namespace PermanentBorder.LowPlane
open MvPolynomial
variable {K : Type*} [Field K]

abbrev Index (B : ℕ) := {s : Fin 2 →₀ ℕ // s.degree < B}

instance index_finite (B : ℕ) : Finite (Index B) := by
  apply Set.Finite.to_subtype
  exact (Finsupp.finite_of_degree_le B).subset (fun _ h => Nat.le_of_lt h)

noncomputable instance index_fintype (B : ℕ) : Fintype (Index B) := Fintype.ofFinite _

lemma plane_degree (s : Fin 2 →₀ ℕ) : s.degree = s 0+s 1 := by
  change s.sum (fun _ a => a) = _
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_two]

noncomputable def indexEquiv (B : ℕ) : Index B ≃ {p : Fin (B+1) × Fin (B+1) // p.1 < p.2} where
  toFun s := ⟨(⟨s.val 0,by have h:=s.property; rw [plane_degree] at h; omega⟩,
    ⟨s.val 0+s.val 1+1,by have h:=s.property; rw [plane_degree] at h; omega⟩),by simp⟩
  invFun p := ⟨Finsupp.single 0 p.val.1.val+Finsupp.single 1 (p.val.2.val-p.val.1.val-1),by
    rw [plane_degree]
    simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from by decide),
      Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 from by decide),add_zero,zero_add]
    have h:=p.property; have h':=p.val.2.isLt
    change p.val.1.val < p.val.2.val at h
    omega⟩
  left_inv s := by
    apply Subtype.ext
    ext i
    fin_cases i
    · simp
    · simp; omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    · simp
    · simp only [Finsupp.add_apply,Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (show (0 : Fin 2) ≠ 1 from by decide),
        Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 from by decide),add_zero,zero_add]
      have h:=p.property
      change p.val.1.val < p.val.2.val at h
      omega

end PermanentBorder.LowPlane

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.HalfPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R]

def InField (F : IntermediateField K L) (p : MvPolynomial (Fin 2) L) : Prop :=
  ∀ s, p.coeff s ∈ F

end PermanentBorder.CurveFamily

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.SingularValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

noncomputable def pointEvaluation {ι : Type*} (x : ι → Fin 2 → L) :
    MvPolynomial (Fin 2) L →ₐ[L] (ι → L) := AlgHom.pi (fun i => aeval (x i))

end PermanentBorder.CurveFamily

namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

abbrev Plane (K : Type*) [CommSemiring K] := MvPolynomial (Fin 2) K

noncomputable def squareForm (a b c d : Plane K) : Plane K :=
  a^2 + X 0*b^2 + X 1*c^2 + X 0*X 1*d^2

end PermanentBorder.FrobeniusPlane

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.DegreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.BinaryLeading
open MvPolynomial
variable {K : Type*} [Field K]

noncomputable def linear (t : K) : MvPolynomial (Fin 2) K := X 1+C t*X 0

end PermanentBorder.BinaryLeading

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert FrobeniusPlane
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [CharP L 2]

noncomputable def halfIdeal (a b c d : Plane L) : Ideal (Plane L) := Ideal.span {a,b,c,d}

end PermanentBorder.CurveFamily

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.WildParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.CurveFamily
open MvPolynomial Module
variable {K : Type*} [Field K]

noncomputable def zeroEvaluation (I : Ideal (MvPolynomial (Fin 2) K)) :
    (MvPolynomial (Fin 2) K ⧸ I) →ₐ[K] (zeroLocus K I → K) :=
  Ideal.Quotient.liftₐ I (pointEvaluation (fun x : zeroLocus K I => x.val)) (by
    intro p hp
    ext x
    exact (mem_zeroLocus_iff.mp x.property) p hp)

end PermanentBorder.CurveFamily

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.ConductorDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace PermanentBorder.CurveFamily
open MvPolynomial Module FrobeniusPlane
open scoped Classical
variable {K : Type*} [Field K] [CharP K 2]

noncomputable def singularIdeal (f : Plane K) : Ideal (Plane K) :=
  Ideal.span {f,pderiv 0 f,pderiv 1 f}

end PermanentBorder.CurveFamily

namespace PermanentBorder.PlaneBivariate
open Polynomial MvPolynomial
variable (K : Type*) [Field K]

noncomputable def toBivariate : MvPolynomial (Fin 2) K →ₐ[K] K[X][X] :=
  aeval ![Polynomial.C Polynomial.X,Polynomial.X]

noncomputable def fromBivariate : K[X][X] →ₐ[K] MvPolynomial (Fin 2) K :=
  Polynomial.eval₂AlgHom (Polynomial.aeval (X 0)) (X 1) (fun _ => Commute.all _ _)

@[simp] lemma to_zero : toBivariate K (X 0)=Polynomial.C Polynomial.X := by simp [toBivariate]
@[simp] lemma to_one : toBivariate K (X 1)=Polynomial.X := by simp [toBivariate]
@[simp] lemma to_C (c : K) : toBivariate K (C c)=Polynomial.C (Polynomial.C c) := by
  simp [toBivariate]
@[simp] lemma from_X : fromBivariate K Polynomial.X=X 1 := by simp [fromBivariate]
@[simp] lemma from_C_X : fromBivariate K (Polynomial.C Polynomial.X)=X 0 := by simp [fromBivariate]
@[simp] lemma from_C_C (c : K) : fromBivariate K (Polynomial.C (Polynomial.C c))=MvPolynomial.C c := by
  simp [fromBivariate]

lemma from_to : (fromBivariate K).comp (toBivariate K) = AlgHom.id K _ := by
  ext i
  fin_cases i <;> simp

lemma to_from : (toBivariate K).comp (fromBivariate K) = AlgHom.id K _ := by
  apply Polynomial.algHom_ext'
  · apply Polynomial.algHom_ext
    simp
  · simp

noncomputable def equiv : MvPolynomial (Fin 2) K ≃ₐ[K] K[X][X] :=
  AlgEquiv.ofAlgHom (toBivariate K) (fromBivariate K) (to_from K) (from_to K)

@[simp] lemma equiv_apply (p : MvPolynomial (Fin 2) K) : equiv K p=toBivariate K p := rfl
@[simp] lemma equiv_symm_apply (p : K[X][X]) : (equiv K).symm p=fromBivariate K p := rfl

end PermanentBorder.PlaneBivariate

namespace PermanentBorder.PlaneScaling
open Polynomial MvPolynomial
variable {K σ : Type*} [Field K]

noncomputable def scale : MvPolynomial σ K →ₐ[K] (MvPolynomial σ K)[X] :=
  MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i)*Polynomial.X)

end PermanentBorder.PlaneScaling

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder.SpectralPlane
open Polynomial MvPolynomial Matrix
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

noncomputable def slope (θ : ι → K) : Matrix ι ι (MvPolynomial (Fin 2) K) :=
  Matrix.diagonal (fun i => BinaryLeading.linear (θ i))
noncomputable def matrix (θ : ι → K) (A : Matrix ι ι K) : Matrix ι ι (MvPolynomial (Fin 2) K) :=
  slope θ + A.map MvPolynomial.C
noncomputable def equation (θ : ι → K) (A : Matrix ι ι K) : MvPolynomial (Fin 2) K :=
  (matrix θ A).det

end PermanentBorder.SpectralPlane

namespace PermanentBorder.EffectiveParameters
open PermanentBorder.Parameters

def sectionSize (k : ℕ) : ℕ := (selectorIndex k+2).choose 2 / 18

end PermanentBorder.EffectiveParameters

end OAI
end


