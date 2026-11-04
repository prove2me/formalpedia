-- Prove2me | Definitions.Def_FreeGroupFactorProof01
-- name    : FreeGroupFactorProof01
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T00:28:23.433212+00:00
-- url     : https://prove2.me/theorems/8ae00bf4-0d80-4454-9949-4386548786cc
-- title:
--   Free group factors: supporting development, part 1 of 12
-- statement:
--   Part 1 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_InterpolatedFactors

set_option linter.all false

namespace OAI
theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e
end OAI

section
namespace OAI

noncomputable section

universe uA uι

open Set Metric
open scoped NNReal Topology BigOperators

open scoped BigOperators ContDiff
namespace FreeGroupFactorMain
namespace PolynomialFlow

section

variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def wordList (w : List (ι × Bool)) (X : ι → A) : A :=
  (w.map (fun ib => if ib.2 then X ib.1 else star (X ib.1))).prod

def word (g : FreeGroup ι) (X : ι → A) : A := wordList g.toWord X

def hamiltonian (S : A) (h : FreeGroup ι →₀ ℝ) (X : ι → A) : A :=
  h.sum (fun g c => (c : ℂ) • (word g X * S * star (word g X)))

def field (S : A) (h : ι → FreeGroup ι →₀ ℝ) (X : ι → A) : ι → A :=
  fun j => Complex.I • (hamiltonian S (h j) X * X j)

end

section
open scoped NNReal BigOperators
variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end

variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end PolynomialFlow
end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A]
variable {ι : Type uι}

def wordHom (U : ι → unitary A) : FreeGroup ι →* A :=
  (unitary A).subtype.comp (FreeGroup.lift U)

@[simp] theorem wordHom_of (U : ι → unitary A) (i : ι) :
    wordHom U (FreeGroup.of i) = (U i : A) := by
  simp [wordHom]

@[simp] theorem wordHom_inv (U : ι → unitary A) (g : FreeGroup ι) :
    wordHom U g⁻¹ = star (wordHom U g) := by
  change ((FreeGroup.lift U g⁻¹ : unitary A) : A) = _
  rw [map_inv]
  rfl

def coefficientHom {G : Type uG} (ρ : G → A) : (G →₀ ℂ) →ₗ[ℂ] A :=
  Finsupp.linearCombination ℂ ρ

@[simp] theorem coefficientHom_single {G : Type uG} (ρ : G → A) (g : G) (c : ℂ) :
    coefficientHom ρ (Finsupp.single g c) = c • ρ g := by
  exact Finsupp.linearCombination_single _ _ _

end UnitaryEvaluation
end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

def extendUnitary (U : ι → unitary A) (C : unitary A) : Option ι → unitary A :=
  fun o => o.elim C U

def laurentValue (C : unitary A) (l : ℤ →₀ ℂ) : A :=
  coefficientHom (fun k : ℤ => ((C ^ k : unitary A) : A)) l

@[simp] theorem wordHom_extend (U : ι → unitary A) (C : unitary A) (g : FreeGroup ι) :
    wordHom (extendUnitary U C) (FreeGroup.map Option.some g) = wordHom U g := by
  have he : (wordHom (extendUnitary U C)).comp (FreeGroup.map Option.some) = wordHom U := by
    apply FreeGroup.ext_hom
    intro i
    simp [extendUnitary]
  exact DFunLike.congr_fun he g

end FreeGroupFactorMain.UnitaryEvaluation

end

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def hilbertReindex {G : Type uG} {H : Type uH} (e : G ≃ H) :
    GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H where
  toFun ξ := ⟨fun h => ξ (e.symm h), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp ξ).summable (by norm_num))⟩
  invFun η := ⟨fun g => η (e g), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp η).summable (by norm_num))⟩
  left_inv ξ := by ext g; simp
  right_inv η := by ext h; simp
  map_add' ξ η := by rfl
  map_smul' c ξ := by rfl
  norm_map' ξ := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change (∑' h : H, ‖ξ (e.symm h)‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) =
      (∑' g : G, ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal)
    exact congrArg (fun t : ℝ => t ^ (1 / (2 : ℝ≥0∞).toReal))
      (e.symm.tsum_eq (fun g => ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal))

@[simp] theorem hilbertReindex_apply {G : Type uG} {H : Type uH} (e : G ≃ H)
    (ξ : GroupHilbert G) (h : H) : hilbertReindex e ξ h = ξ (e.symm h) := rfl

def leftRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulLeft g)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem leftRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : leftRegular g ξ h = ξ (g⁻¹ * h) := rfl

@[simp] theorem leftRegular_one {G : Type uG} [Group G] :
    leftRegular (1 : G) = 1 := by
  ext ξ h
  simp

@[simp] theorem leftRegular_mul {G : Type uG} [Group G] (g h : G) :
    leftRegular (g * h) = leftRegular g * leftRegular h := by
  ext ξ b
  simp [mul_assoc]

theorem leftRegular_mem_leftTranslations {G : Type uG} [Group G] (g : G) :
    leftRegular g ∈ leftTranslations G := ⟨g, fun _ _ => rfl⟩

theorem leftTranslations_eq_range (G : Type uG) [Group G] :
    leftTranslations G = Set.range (leftRegular (G := G)) := by
  ext T
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    ext ξ h
    exact (hg ξ h).symm
  · rintro ⟨g, rfl⟩
    exact leftRegular_mem_leftTranslations g

@[simp] theorem leftRegular_star {G : Type uG} [Group G] (g : G) :
    star (leftRegular g) = leftRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulLeft g)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (g * b) = ξ ((g⁻¹)⁻¹ * b)
  simp

theorem leftRegular_unitary {G : Type uG} [Group G] (g : G) :
    leftRegular g ∈ unitary (GroupOperator G) := by
  rw [Unitary.mem_iff]
  constructor <;> simp [← leftRegular_mul, leftRegular_star, leftRegular_one]

theorem leftRegular_mem_groupVN {G : Type uG} [Group G] (g : G) :
    leftRegular g ∈ groupVonNeumann G := by
  rw [groupVonNeumann, StarSubalgebra.mem_centralizer_iff]
  intro S hS
  have hs := (StarSubalgebra.mem_centralizer_iff ℂ).mp hS
  constructor
  · exact (hs _ (by rw [leftTranslations_eq_range]; exact ⟨g, rfl⟩)).1.symm
  · have hh := congrArg star (hs _ (by rw [leftTranslations_eq_range]; exact ⟨g⁻¹, rfl⟩)).1
    simpa only [star_mul, leftRegular_star, inv_inv] using hh

def groupUnitary {G : Type uG} [Group G] (g : G) : groupVonNeumann G :=
  ⟨leftRegular g, leftRegular_mem_groupVN g⟩

@[simp] theorem canonicalTrace_groupUnitary {G : Type uG} [Group G] [DecidableEq G] (g : G) :
    canonicalTrace (groupUnitary g) = if g = 1 then 1 else 0 := by
  classical
  simp [canonicalTrace, groupUnitary, lp.single_apply, Pi.single_apply]

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

instance groupVN_normedSpaceReal (G : Type uG) [Group G] :
    NormedSpace ℝ (groupVonNeumann G) :=
  NormedSpace.restrictScalars ℝ ℂ (groupVonNeumann G)

 instance groupHilbert_nontrivial (G : Type uG) [Group G] : Nontrivial (GroupHilbert G) := by
  classical
  apply nontrivial_of_ne (lp.single 2 (1 : G) (1 : ℂ)) 0
  intro he
  have hh := congrArg (fun x : GroupHilbert G => x 1) he
  simp at hh

 instance groupVN_normOneClass (G : Type uG) [Group G] : NormOneClass (groupVonNeumann G) where
  norm_one := by
    change ‖(1 : GroupOperator G)‖ = 1
    exact norm_one

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff

 theorem groupUnitary_mem_unitary {G : Type uG} [Group G] (g : G) :
    groupUnitary g ∈ unitary (groupVonNeumann G) := by
  rw [Unitary.mem_iff]
  constructor <;> apply Subtype.ext
  · exact (Unitary.mem_iff.mp (leftRegular_unitary g)).1
  · exact (Unitary.mem_iff.mp (leftRegular_unitary g)).2

 def generatorUnitary {ι : Type uι} (i : ι) : unitary (groupVonNeumann (FreeGroup ι)) :=
  ⟨groupUnitary (FreeGroup.of i), groupUnitary_mem_unitary _⟩

end FreeGroupFactorMain

namespace FreeGroupFactorMain.PolynomialFlow
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end FreeGroupFactorMain.PolynomialFlow

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped ComplexConjugate

abbrev deltaOne {G : Type uG} [Group G] : GroupHilbert G := by
  classical
  exact lp.single 2 1 1

open scoped ComplexConjugate ENNReal

open scoped ComplexConjugate

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH uα uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace ConjugateSectors

end ConjugateSectors

namespace CoordinateProjection

abbrev Hilbert (α : Type uα) := lp (fun _ : α => ℂ) 2

def restrict {α : Type uα} (s : Set α) (ξ : Hilbert α) : Hilbert α := by
  classical
  refine ⟨s.indicator ξ, (lp.memℓp ξ).mono' ?_⟩
  intro a
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

@[simp] theorem restrict_apply {α : Type uα} (s : Set α) (ξ : Hilbert α) (a : α) :
    restrict s ξ a = s.indicator ξ a := rfl

theorem norm_restrict_le {α : Type uα} (s : Set α) (ξ : Hilbert α) :
    ‖restrict s ξ‖ ≤ ‖ξ‖ := by
  classical
  apply lp.norm_mono (by norm_num)
  intro a
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

def linearMap {α : Type uα} (s : Set α) : Hilbert α →ₗ[ℂ] Hilbert α where
  toFun := restrict s
  map_add' ξ η := by
    classical
    ext a
    by_cases ha : a ∈ s <;> simp [Set.indicator, ha]
  map_smul' c ξ := by
    classical
    ext a
    by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

def proj {α : Type uα} (s : Set α) : Hilbert α →L[ℂ] Hilbert α :=
  (linearMap s).mkContinuous 1 (fun ξ => by
    change ‖restrict s ξ‖ ≤ 1 * ‖ξ‖
    simpa only [one_mul] using norm_restrict_le s ξ)

@[simp] theorem proj_apply {α : Type uα} (s : Set α) (ξ : Hilbert α) (a : α) :
    proj s ξ a = s.indicator ξ a := rfl

theorem norm_proj_le {α : Type uα} (s : Set α) : ‖proj s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ξ
  change ‖restrict s ξ‖ ≤ 1 * ‖ξ‖
  simpa only [one_mul] using norm_restrict_le s ξ

theorem star_proj {α : Type uα} (s : Set α) : star (proj s) = proj s := by
  classical
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro ξ η
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

@[simp] theorem complement_apply {α : Type uα} (s : Set α) (ξ : Hilbert α) (a : α) :
    ((1 - proj s) ξ) a = sᶜ.indicator ξ a := by
  classical
  by_cases ha : a ∈ s <;> simp [Set.indicator, ha]

end CoordinateProjection

open scoped BigOperators
namespace FreeSum
variable {ι : Type uι} {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "Op" => H →L[ℂ] H

end FreeSum

open scoped BigOperators ENNReal
open ConjugateSectors CoordinateProjection

open scoped BigOperators

@[simp] theorem groupUnitary_mul {G : Type uG} [Group G] (g h : G) :
    groupUnitary (g*h) = groupUnitary g * groupUnitary h := by
  apply Subtype.ext
  exact leftRegular_mul g h

@[simp] theorem groupUnitary_inv {G : Type uG} [Group G] (g : G) :
    groupUnitary g⁻¹ = star (groupUnitary g) := by
  apply Subtype.ext
  exact (leftRegular_star g).symm

@[simp] theorem groupUnitary_one {G : Type uG} [Group G] : groupUnitary (1 : G) = 1 := by
  apply Subtype.ext
  exact leftRegular_one

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uA uB uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

abbrev Coeff (G : Type uG) := G →₀ ℝ

def coefficientShift {G : Type uG} [Group G] (g : G) : Coeff G ≃+ Coeff G :=
  Finsupp.domCongr (Equiv.mulLeft g)

@[simp] theorem coefficientShift_apply {G : Type uG} [Group G] (g : G) (h : Coeff G) (b : G) :
    coefficientShift g h b = h (g⁻¹ * b) := rfl

@[simp] theorem coefficientShift_one {G : Type uG} [Group G] (h : Coeff G) :
    coefficientShift (1 : G) h = h := by
  ext b
  simp

@[simp] theorem coefficientShift_mul {G : Type uG} [Group G] (g b : G) (h : Coeff G) :
    coefficientShift (g * b) h = coefficientShift g (coefficientShift b h) := by
  ext c
  simp [mul_assoc]

def coefficientAction (G : Type uG) [Group G] : G →* MulAut (Multiplicative (Coeff G)) where
  toFun g := AddEquiv.toMultiplicative (coefficientShift g)
  map_one' := by
    apply MulEquiv.ext
    intro h
    exact coefficientShift_one h.toAdd
  map_mul' g b := by
    apply MulEquiv.ext
    intro h
    exact coefficientShift_mul g b h.toAdd

def cocycleGraph {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) :
    FreeGroup ι →* (Multiplicative (Coeff (FreeGroup ι)) ⋊[coefficientAction (FreeGroup ι)]
      FreeGroup ι) :=
  FreeGroup.lift (fun i => ⟨Multiplicative.ofAdd (h i), FreeGroup.of i⟩)

@[simp] theorem cocycleGraph_right {ι : Type uι} (h : ι → Coeff (FreeGroup ι))
    (g : FreeGroup ι) : (cocycleGraph h g).right = g := by
  have hr : SemidirectProduct.rightHom.comp (cocycleGraph h) = MonoidHom.id _ := by
    ext i
    simp [cocycleGraph]
  exact DFunLike.congr_fun hr g

def freeCocycle {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) (g : FreeGroup ι) :
    Coeff (FreeGroup ι) := (cocycleGraph h g).left.toAdd

@[simp] theorem freeCocycle_of {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) (i : ι) :
    freeCocycle h (FreeGroup.of i) = h i := by
  simp [freeCocycle, cocycleGraph]

@[simp] theorem freeCocycle_one {ι : Type uι} (h : ι → Coeff (FreeGroup ι)) :
    freeCocycle h 1 = 0 := by simp [freeCocycle]

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

def hamiltonianLinear (S : A) (U : ι → unitary A) : (FreeGroup ι →₀ ℝ) →ₗ[ℝ] A :=
  Finsupp.linearCombination ℝ (fun g => wordHom U g * S * star (wordHom U g))

end UnitaryEvaluation

section
open UnitaryEvaluation

def groupUnitaryUHom (G : Type uG) [Group G] : G →* unitary (groupVonNeumann G) where
  toFun g := ⟨groupUnitary g, groupUnitary_mem_unitary g⟩
  map_one' := Subtype.ext groupUnitary_one
  map_mul' g b := Subtype.ext (groupUnitary_mul g b)

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

end
section

variable {A : Type uA} [CStarAlgebra A]

end

namespace UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} [Fintype ι] [DecidableEq ι]

end UnitaryEvaluation

section
open UnitaryEvaluation

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end

def groupL2 {G : Type uG} [Group G] : groupVonNeumann G →L[ℂ] GroupHilbert G :=
  ({ toFun := fun T => (T : GroupOperator G) deltaOne
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : groupVonNeumann G →ₗ[ℂ] GroupHilbert G).mkContinuous 1 (by
    intro T
    calc
      ‖(T : GroupOperator G) deltaOne‖ ≤ ‖T‖ * ‖(deltaOne : GroupHilbert G)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = 1 * ‖T‖ := by simp [deltaOne, lp.norm_single])

abbrev twoNorm {G : Type uG} [Group G] (T : groupVonNeumann G) : ℝ := ‖groupL2 T‖

@[simp] theorem groupL2_apply {G : Type uG} [Group G] (T : groupVonNeumann G) :
    groupL2 T = (T : GroupOperator G) deltaOne := rfl

theorem twoNorm_mul_unitary_left {G : Type uG} [Group G]
    (U : unitary (groupVonNeumann G)) (T : groupVonNeumann G) :
    twoNorm ((U : groupVonNeumann G)*T) = twoNorm T := by
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  exact ⟨congrArg Subtype.val U.property.1, congrArg Subtype.val U.property.2⟩

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

def coefficientNorm {G : Type uG} (h : Coeff G) : ℝ :=
  Real.sqrt (h.sum (fun _ r => r ^ 2))

def firstCoefficients {n : ℕ} (h : Coeff (FreeGroup (Fin n))) :
    Fin n → Coeff (FreeGroup (Fin n)) := fun i => if i.val = 0 then h else 0

namespace PrefixSeparation

end PrefixSeparation

@[simp] theorem coefficientShift_single {G : Type uG} [Group G] (g b : G) (c : ℝ) :
    coefficientShift g (Finsupp.single b c) = Finsupp.single (g * b) c := by
  exact Finsupp.equivMapDomain_single (Equiv.mulLeft g) b c

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.MobiusLog
variable {A : Type uA} [CommCStarAlgebra A] [Nontrivial A]

end FreeGroupFactorMain.MobiusLog
namespace FreeGroupFactorMain.ElementalMobius
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

end FreeGroupFactorMain.ElementalMobius
namespace FreeGroupFactorMain
variable {G : Type uG} [Group G]

@[simp] theorem twoNorm_one : twoNorm (1 : groupVonNeumann G) = 1 := by
  simp [twoNorm, groupL2, deltaOne, lp.norm_single]

@[simp] theorem twoNorm_unitary (U : unitary (groupVonNeumann G)) :
    twoNorm (U : groupVonNeumann G) = 1 := by
  simpa using twoNorm_mul_unitary_left U 1

end FreeGroupFactorMain

open scoped BigOperators
namespace FreeGroupFactorMain.LaurentApprox

section
variable {A : Type uA} [CStarAlgebra A]

def value (C : unitary A) (l : ℤ →₀ ℂ) : A :=
  l.sum (fun m c => c • ((C^m : unitary A) : A))

@[simp] theorem value_add (C : unitary A) (l k : ℤ →₀ ℂ) :
    value C (l+k) = value C l + value C k :=
  (Finsupp.linearCombination ℂ (fun m : ℤ => ((C^m : unitary A) : A))).map_add l k

@[simp] theorem value_sub (C : unitary A) (l k : ℤ →₀ ℂ) :
    value C (l-k) = value C l - value C k :=
  (Finsupp.linearCombination ℂ (fun m : ℤ => ((C^m : unitary A) : A))).map_sub l k

@[simp] theorem value_single (C : unitary A) (m : ℤ) (c : ℂ) :
    value C (Finsupp.single m c) = c • ((C^m : unitary A) : A) := by
  simp [value]

end

variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]

end FreeGroupFactorMain.LaurentApprox

namespace FreeGroupFactorMain
variable {G : Type uG} [Group G]

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain
open scoped ENNReal

variable {G : Type uG} [Group G]

@[simp] theorem groupL2_groupUnitary [DecidableEq G] (g : G) :
    groupL2 (groupUnitary g) = lp.single 2 g (1 : ℂ) := by
  classical
  ext x
  simp [groupL2, groupUnitary, deltaOne, leftRegular_apply,
    lp.single_apply, Pi.single_apply, inv_mul_eq_one, eq_comm]

variable {ι : Type uι}

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

def word (U : ι → unitary A) : FreeGroup ι →* A :=
  (unitary A).subtype.comp (FreeGroup.lift U)

@[simp] theorem word_of (U : ι → unitary A) (i : ι) : word U (FreeGroup.of i) = (U i : A) := by
  simp [word]

@[simp] theorem word_inv (U : ι → unitary A) (g : FreeGroup ι) :
    word U g⁻¹ = star (word U g) := by
  change ((FreeGroup.lift U g⁻¹ : unitary A) : A) = _
  rw [map_inv]
  rfl

@[fun_prop] theorem word_continuous (g : FreeGroup ι) : Continuous (fun U : ι → unitary A => word U g) := by
  induction g using FreeGroup.induction_on with
  | C1 => simpa only [map_one] using (continuous_const : Continuous (fun _ : ι → unitary A => (1 : A)))
  | of i =>
    simp only [word_of]
    exact continuous_subtype_val.comp (continuous_apply i)
  | inv_of i ih => simpa only [word_inv] using ih.star
  | mul g h hg hh =>
    simp only [map_mul]
    exact hg.mul hh

def poly (U : ι → unitary A) (p : FreeGroup ι →₀ ℂ) : A := p.sum (fun g c => c • word U g)

@[simp] theorem poly_zero (U : ι → unitary A) : poly U 0 = 0 := by simp [poly]
@[simp] theorem poly_add (U : ι → unitary A) (p q : FreeGroup ι →₀ ℂ) :
    poly U (p+q) = poly U p + poly U q :=
  (Finsupp.linearCombination ℂ (word U)).map_add p q
@[simp] theorem poly_single (U : ι → unitary A) (g : FreeGroup ι) (c : ℂ) :
    poly U (Finsupp.single g c) = c • word U g := by simp [poly]

@[fun_prop] theorem poly_continuous (p : FreeGroup ι →₀ ℂ) : Continuous (fun U : ι → unitary A => poly U p) := by
  classical
  unfold poly Finsupp.sum
  exact continuous_finsetSum _ (fun g _ => (word_continuous g).const_smul _)

variable {G : Type uG} [Group G]

@[simp] theorem twoNorm_zero : twoNorm (0 : groupVonNeumann G) = 0 := by
  simp [twoNorm]

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain
open UnitaryEvaluation

@[simp] theorem generator_haar {ι : Type uι} (i : ι) (m : ℤ) :
    canonicalTrace (((generatorUnitary i)^m : unitary (groupVonNeumann (FreeGroup ι))) : groupVonNeumann (FreeGroup ι)) =
      if m = 0 then 1 else 0 := by
  classical
  have hz : (((generatorUnitary i)^m : unitary (groupVonNeumann (FreeGroup ι))) : groupVonNeumann (FreeGroup ι)) =
      groupUnitary ((FreeGroup.of i)^m) :=
    congrArg Subtype.val ((groupUnitaryUHom (FreeGroup ι)).map_zpow (FreeGroup.of i) m).symm
  rw [hz,canonicalTrace_groupUnitary]
  have hi : (FreeGroup.of i)^m = 1 ↔ m = 0 := by
    constructor
    · intro h
      have he := congrArg (FreeGroup.lift (fun _ : ι => Multiplicative.ofAdd (1 : ℤ))) h
      simp only [map_zpow,FreeGroup.lift_apply_of,map_one] at he
      simpa using congrArg Multiplicative.toAdd he
    · rintro rfl; simp
  simp only [hi]

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uB uC uG uH uI uK uP uX uY uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation

section
variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B] {ι : Type uι} {κ : Type uκ}

def mapTuple (Φ : A ≃⋆ₐ[ℂ] B) (U : ι → unitary A) : ι → unitary B :=
  fun j => ⟨Φ (U j : A), Unitary.map_mem Φ (U j).property⟩

@[simp] theorem mapTuple_coe (Φ : A ≃⋆ₐ[ℂ] B) (U : ι → unitary A) (j : ι) :
    (mapTuple Φ U j : B) = Φ (U j : A) := rfl

@[simp] theorem word_mapTuple (Φ : A ≃⋆ₐ[ℂ] B) (U : ι → unitary A) (g : FreeGroup ι) :
    word (mapTuple Φ U) g = Φ (word U g) := by
  induction g using FreeGroup.induction_on with
  | C1 => simp only [map_one]
  | of j => simp only [word_of,mapTuple_coe]
  | inv_of j ih => rw [word_inv,word_inv,ih,map_star]
  | mul g h hg hh => rw [map_mul,map_mul,map_mul,hg,hh]

@[simp] theorem poly_mapTuple (Φ : A ≃⋆ₐ[ℂ] B) (U : ι → unitary A) (p : FreeGroup ι →₀ ℂ) :
    poly (mapTuple Φ U) p = Φ (poly U p) := by
  classical
  simp only [poly,Finsupp.sum,map_sum,map_smul,word_mapTuple]

def wordTuple (U : ι → unitary A) (w : κ → FreeGroup ι) : κ → unitary A :=
  fun j => FreeGroup.lift U (w j)

@[simp] theorem word_wordTuple (U : ι → unitary A) (w : κ → FreeGroup ι) (g : FreeGroup κ) :
    word (wordTuple U w) g = word U (FreeGroup.lift w g) := by
  have he : word (wordTuple U w) = (word U).comp (FreeGroup.lift w) := by
    apply FreeGroup.ext_hom
    intro j
    simp only [word_of,MonoidHom.comp_apply,FreeGroup.lift_apply_of]
    rfl
  exact DFunLike.congr_fun he g

instance unitary_isClosed (A : Type uA) [CStarAlgebra A] : IsClosed (unitary A : Set A) :=
  isClosed_unitary

instance unitary_completeSpace (A : Type uA) [CStarAlgebra A] : CompleteSpace (unitary A) := by
  change CompleteSpace ↥(unitary A : Set A)
  infer_instance

end

@[simp] theorem word_canonical {ι : Type uι} (g : FreeGroup ι) :
    word (generatorUnitary (ι := ι)) g = groupUnitary g := by
  have he : word (generatorUnitary (ι := ι)) =
      (unitary (groupVonNeumann (FreeGroup ι))).subtype.comp (groupUnitaryUHom (FreeGroup ι)) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [word_of,MonoidHom.comp_apply]
    rfl
  exact DFunLike.congr_fun he g

abbrev Ambient (n : ℕ) := groupVonNeumann (FreeGroup (Option (Fin n)))
abbrev Tuple (n : ℕ) := Fin n → unitary (Ambient n)
def initial (n : ℕ) : Tuple n := fun j => generatorUnitary (some j)

def orbit (n : ℕ) : Set (Tuple n) :=
  {U | ∃ Φ : Ambient n ≃⋆ₐ[ℂ] Ambient n,
    (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧ U = mapTuple Φ (initial n)}

@[simp] theorem mapTuple_trans {A : Type uA} {B : Type uB} {C : Type uC} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    {ι : Type uι} (Φ : A ≃⋆ₐ[ℂ] B) (Ψ : B ≃⋆ₐ[ℂ] C) (U : ι → unitary A) :
    mapTuple (Φ.trans Ψ) U = mapTuple Ψ (mapTuple Φ U) := rfl

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain

open Generation

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

namespace RankTwo

section
open Monoid.CoprodI

abbrev SyllableGroups (_ : Bool) := Multiplicative ℤ

abbrev NW (i j : Bool) := Monoid.CoprodI.NeWord SyllableGroups i j

variable {ι : Type uι}

variable (start finish : ι → ℤ) (core : ι → NW true true)
variable (hs : ∀ i, start i ≠ 0) (ht : ∀ i, finish i ≠ 0)
include hs ht

variable (hinjs : Function.Injective start) (hinjt : Function.Injective finish)
include hinjs hinjt

end
open Monoid.CoprodI

end RankTwo

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

open scoped ContDiff BigOperators ENNReal
namespace FreeGroupFactorMain

end FreeGroupFactorMain
namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff
open UnitaryEvaluation

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

@[simp] theorem wordHom_map (U : κ → unitary A) (f : ι → κ) (g : FreeGroup ι) :
    wordHom U (FreeGroup.map f g) = wordHom (U ∘ f) g := by
  have he : (wordHom U).comp (FreeGroup.map f) = wordHom (U ∘ f) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  exact DFunLike.congr_fun he g

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive
open UnitaryEvaluation
open scoped ContDiff
variable {ι : Type uι} {κ : Type uκ}

abbrev Ambient (ι : Type uι) (κ : Type uκ) : Type _ := ↥(groupVonNeumann (FreeGroup (Option (ι ⊕ κ))))

instance ambientContinuousSMulReal : ContinuousSMul ℝ (Ambient ι κ) := by
  let : NormedSpace ℝ (Ambient ι κ) := groupVN_normedSpaceReal _
  exact IsBoundedSMul.continuousSMul

def tuple (X : ι → Ambient ι κ) : (ι ⊕ κ) → Ambient ι κ :=
  Sum.elim X (fun k => groupUnitary (FreeGroup.of (some (Sum.inr k))))

theorem tuple_unitary (X : ι → Ambient ι κ) (hX : ∀ i, X i ∈ unitary (Ambient ι κ)) :
    ∀ j, tuple X j ∈ unitary (Ambient ι κ) := by
  intro j
  cases j with
  | inl i => exact hX i
  | inr k => exact groupUnitary_mem_unitary _

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain
open UnitaryEvaluation
open scoped ENNReal

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.Generation

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

abbrev Index := Option (Fin 3 ⊕ ℕ)
abbrev Group := FreeGroup Index
abbrev M := groupVonNeumann Group
abbrev Tuple := Fin 3 → unitary M

def initial : Tuple := fun i => generatorUnitary (some (Sum.inl i))
def extra (q : Option ℕ) : unitary M :=
  generatorUnitary (q.elim none (fun k => some (Sum.inr k)))

end FreeGroupFactorMain.InfiniteGeneration

namespace FreeGroupFactorMain.Generation
variable {G : Type uG} [Group G] {ι : Type uι}

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain.InfiniteGeneration
open Generation

 def orbit : Set Tuple := {U | ∃ Φ : M ≃⋆ₐ[ℂ] M,
    (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧ U = mapTuple Φ initial}

end FreeGroupFactorMain.InfiniteGeneration

end

end OAI
end

section
namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45

namespace Amplification

section

variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

@[simp] theorem corner_one_val (p : A) (hp : IsStarProjection p) :
    ((1 : Corner p hp) : A) = p := rfl

@[simp] theorem corner_mul_val (p : A) (hp : IsStarProjection p) (x y : Corner p hp) :
    ((x*y : Corner p hp) : A) = (x : A)*(y : A) := rfl

end

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

end

open scoped ENNReal

end Amplification

namespace FreeFock
open scoped ENNReal

abbrev Hilbert (α : Type u_14) := lp (fun _ : α => ℂ) 2
variable {α : Type u_15} {β : Type u_16} [DecidableEq α] [DecidableEq β]

end FreeFock
open Filter Topology

namespace Amplification

section
variable {A : Type u_17} {B : Type u_18} [CStarAlgebra A] [CStarAlgebra B]

def subalgebraEquiv (M : StarSubalgebra ℂ A) (N : StarSubalgebra ℂ B)
    (e : A ≃⋆ₐ[ℂ] B) (he : ∀ a, e a∈N ↔ a∈M) : M ≃⋆ₐ[ℂ] N where
  toFun a := ⟨e a,(he a).mpr a.property⟩
  invFun b := ⟨e.symm b,(he _).mp (by rw [StarAlgEquiv.apply_symm_apply];exact b.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)
  map_mul' a b := Subtype.ext (e.map_mul (a:A) (b:A))
  map_add' a b := Subtype.ext (e.map_add (a:A) (b:A))
  map_smul' c a := Subtype.ext (map_smul e c (a:A))
  map_star' a := Subtype.ext (e.map_star' (a:A))

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)]
variable (p : M) (hp : IsStarProjection p)

variable {E : Type u_19} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open scoped ENNReal ComplexConjugate
local instance instDecidableEqNestedHilbert (α : Type u_20) : DecidableEq α := Classical.decEq α

variable {I : Type u_21} {J : Type u_22}

end
section
open scoped ENNReal

variable {I : Type u_35} {J : Type u_36}

variable {G : Type u_37} [Group G]

end

section
open scoped ENNReal
variable {G : Type u_38}

variable [Group G]

end

open scoped ENNReal
variable {G : Type u_45} [Group G]

end Amplification

namespace Interpolation

open Amplification
open scoped ENNReal

end Interpolation

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

universe u_1 u_2 u_3

noncomputable section

namespace FreeGroupFactorMain.Amplification
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K : Submodule ℂ E) [CompleteSpace K]

abbrev RangeCorner := Corner K.starProjection isStarProjection_starProjection

def cornerRestrict (x : RangeCorner K) : K →L[ℂ] K :=
  K.orthogonalProjectionOnto.comp ((x : E →L[ℂ] E).comp K.subtypeL)

def cornerExtend (x : K →L[ℂ] K) : RangeCorner K :=
  ⟨K.subtypeL.comp (x.comp K.orthogonalProjectionOnto),by
    constructor
    · ext ξ
      exact K.starProjection_mem_subspace_eq_self (x (K.orthogonalProjectionOnto ξ))
    · ext ξ
      change (x (K.orthogonalProjectionOnto (K.starProjection ξ)) : E)=_
      rw [K.orthogonalProjectionOnto_starProjection_of_le le_rfl]
      rfl⟩

theorem cornerRestrict_extend (x : K →L[ℂ] K) : cornerRestrict K (cornerExtend K x)=x := by
  ext ξ
  simp only [cornerRestrict,cornerExtend,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem cornerExtend_restrict (x : RangeCorner K) : cornerExtend K (cornerRestrict K x)=x := by
  apply Subtype.ext
  change K.starProjection*(x : E →L[ℂ] E)*K.starProjection=(x : E →L[ℂ] E)
  rw [x.property.1,x.property.2]

theorem cornerRestrict_apply (x : RangeCorner K) (ξ : K) :
    (cornerRestrict K x ξ : E)=(x : E →L[ℂ] E) ξ := by
  change K.starProjection ((x : E →L[ℂ] E) ξ)=_
  exact DFunLike.congr_fun x.property.1 (ξ:E)

def cornerRepresentation : RangeCorner K ≃⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun := cornerRestrict K
  invFun := cornerExtend K
  left_inv := cornerExtend_restrict K
  right_inv := cornerRestrict_extend K
  map_mul' x y := by
    ext ξ
    simp only [cornerRestrict_apply,mul_apply_eq_comp]
    rfl
  map_add' x y := by
    ext ξ
    simp only [cornerRestrict_apply,add_apply,Submodule.coe_add]
    rfl
  map_smul' c x := by
    ext ξ
    simp only [cornerRestrict_apply,smul_apply,SetLike.val_smul]
  map_star' x := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_right ℂ
    intro η
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (cornerRestrict K (star x) ξ : E) (η:E)=
      inner ℂ (ξ:E) (cornerRestrict K x η : E)
    rw [cornerRestrict_apply,cornerRestrict_apply]
    exact ContinuousLinearMap.adjoint_inner_left (x : E →L[ℂ] E) η ξ
end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15

noncomputable section
namespace FreeGroupFactorMain.FreeFock
open scoped ENNReal

abbrev Op (α : Type u_1) := Hilbert α →L[ℂ] Hilbert α
variable {α : Type u_2} {β : Type u_3} [DecidableEq α] [DecidableEq β]

 theorem operator_basis_ext (T U : Op α)
    (h : ∀ a, T (lp.single 2 a 1)=U (lp.single 2 a 1)) : T=U := by
  classical
  apply ContinuousLinearMap.ext
  intro ξ
  have hT := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL T
  have hU := (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ξ).mapL U
  have he (a : α) : T (lp.single 2 a (ξ a))=U (lp.single 2 a (ξ a)) := by
    have hc : lp.single (E := fun _ : α => ℂ) 2 a (ξ a)=
        (ξ a) • lp.single (E := fun _ : α => ℂ) 2 a 1 := by
      ext b
      simp [lp.single_apply,Pi.single_apply]
    rw [hc,map_smul,map_smul,h]
  simp only [he] at hT
  exact hT.unique hU

 def basisEmbedding (a : α) : ℂ →ₗᵢ[ℂ] Hilbert α where
  toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : α => ℂ) 2 a
  norm_map' z := lp.norm_single (E := fun _ : α => ℂ) (by norm_num : 0 < (2 : ℝ≥0∞)) a z

omit [DecidableEq α] in
 theorem embedding_orthogonal (f : α ↪ β) :
    OrthogonalFamily ℂ (fun _ : α => ℂ) (fun a => basisEmbedding (f a)) := by
  classical
  intro a b hab z w
  change inner ℂ (lp.single (E := fun _ : β => ℂ) 2 (f a) z) (lp.single (E := fun _ : β => ℂ) 2 (f b) w)=0
  have hn : f a ≠ f b := fun he => hab (f.injective he)
  simp [lp.inner_single_left,lp.single_apply,hn]

 def hilbertEmbedding (f : α ↪ β) : Hilbert α →ₗᵢ[ℂ] Hilbert β :=
  (embedding_orthogonal f).linearIsometry

@[simp] theorem hilbertEmbedding_single (f : α ↪ β) (a : α) (z : ℂ) :
    hilbertEmbedding f (lp.single 2 a z)=lp.single 2 (f a) z :=
  (embedding_orthogonal f).linearIsometry_apply_single z

 abbrev Fock (α : Type u_4) := Hilbert (List α)
 abbrev Operator (α : Type u_5) := Op (List α)

 def consEmbedding (a : α) : List α ↪ List α := ⟨List.cons a,fun _ _ h => (List.cons.inj h).2⟩

 def creation (a : α) : Operator α := (hilbertEmbedding (consEmbedding a)).toContinuousLinearMap

@[simp] theorem creation_single (a : α) (w : List α) (z : ℂ) :
    creation a (lp.single 2 w z)=lp.single 2 (a::w) z := by
  exact hilbertEmbedding_single (consEmbedding a) w z

 theorem annihilation_single_nil (a : α) (z : ℂ) :
    star (creation a) (lp.single 2 [] z)=0 := by
  classical
  ext w
  have hi := ContinuousLinearMap.adjoint_inner_right (creation a) (lp.single 2 w 1) (lp.single 2 [] z)
  rw [creation_single,lp.inner_single_left,lp.inner_single_left] at hi
  simpa [ContinuousLinearMap.star_eq_adjoint,RCLike.inner_apply,lp.single_apply] using hi

 theorem annihilation_single_cons (a b : α) (w : List α) (z : ℂ) :
    star (creation a) (lp.single 2 (b::w) z)=if a=b then lp.single 2 w z else 0 := by
  classical
  ext v
  have hi := ContinuousLinearMap.adjoint_inner_right (creation a) (lp.single 2 v 1) (lp.single 2 (b::w) z)
  rw [creation_single,lp.inner_single_left,lp.inner_single_left] at hi
  change (star (creation a) (lp.single 2 (b::w) z)) v=_
  have he : (star (creation a) (lp.single 2 (b::w) z)) v=(lp.single (E := fun _ : List α => ℂ) 2 (b::w) z) (a::v) := by
    simpa [ContinuousLinearMap.star_eq_adjoint,RCLike.inner_apply] using hi
  rw [he]
  by_cases hab : a=b
  · subst b
    simp only [lp.single_apply,Pi.single_apply,List.cons.injEq,true_and,ite_true]
  · simp only [lp.single_apply,Pi.single_apply,List.cons.injEq,hab,false_and,ite_false,lp.coeFn_zero,Pi.zero_apply]

 theorem annihilation_creation (a b : α) :
    star (creation a)*creation b=if a=b then 1 else 0 := by
  classical
  apply operator_basis_ext (α := List α)
  intro w
  rw [mul_apply_eq_comp]
  rw [creation_single,annihilation_single_cons]
  by_cases h : a=b <;> simp [h]

 def semicircular (a : α) : Operator α := creation a+star (creation a)

 theorem semicircular_selfAdjoint (a : α) : IsSelfAdjoint (semicircular a) := by
  change star (creation a+star (creation a))=creation a+star (creation a)
  simp only [star_add (R := Operator α),star_star,add_comm]

 def vacuum : Fock α := lp.single 2 [] 1

@[simp] theorem semicircular_vacuum (a : α) : semicircular a vacuum=lp.single 2 [a] 1 := by
  change creation a (lp.single 2 [] 1)+star (creation a) (lp.single 2 [] 1)=_
  rw [creation_single,annihilation_single_nil,add_zero]

 def vacuumTrace (T : Operator α) : ℂ := inner ℂ vacuum (T vacuum)

 theorem vacuumTrace_one : vacuumTrace (1 : Operator α)=1 := by
  classical
  simp only [vacuumTrace,vacuum,one_apply_eq_self,lp.inner_single_left,lp.single_apply_self]
  norm_num

end FreeGroupFactorMain.FreeFock
namespace FreeGroupFactorMain.CoordinateProjection

variable {α : Type u_6} [DecidableEq α]
open scoped Classical

@[simp] theorem proj_single (s : Set α) (a : α) (z : ℂ) :
    proj s (lp.single 2 a z)=if a ∈ s then lp.single (E := fun _ : α => ℂ) 2 a z else 0 := by
  classical
  ext b
  by_cases ha : a ∈ s
  · by_cases hb : b=a <;> simp [proj_apply,Set.indicator,lp.single_apply,ha,hb]
  · by_cases hb : b=a <;> simp [proj_apply,Set.indicator,lp.single_apply,ha,hb]

 theorem projection (s : Set α) : IsStarProjection (proj s) := by
  refine ⟨?_,star_proj s⟩
  apply FreeFock.operator_basis_ext
  intro a
  simp only [mul_apply_eq_comp,proj_single]
  split_ifs <;> simp_all

 theorem commute (s t : Set α) : Commute (proj s) (proj t) := by
  change _ * _ = _ * _
  apply FreeFock.operator_basis_ext
  intro a
  simp only [mul_apply_eq_comp,proj_single]
  split_ifs <;> simp_all

 theorem commute_embedding (s : Set α) (f : α ↪ α)
    (hf : ∀ a, f a ∈ s ↔ a ∈ s) :
    Commute (proj s) (FreeFock.hilbertEmbedding f).toContinuousLinearMap := by
  change _ * _ = _ * _
  apply FreeFock.operator_basis_ext
  intro a
  change proj s (FreeFock.hilbertEmbedding f (lp.single 2 a 1))=
    FreeFock.hilbertEmbedding f (proj s (lp.single 2 a 1))
  rw [FreeFock.hilbertEmbedding_single,proj_single,proj_single]
  simp only [hf]
  split_ifs <;> simp_all

end FreeGroupFactorMain.CoordinateProjection

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_7} [DecidableEq ι]

abbrev Path (ι : Type u_8) := List (ι × Bool) × Bool
abbrev H (ι : Type u_9) := Hilbert (Path ι)
abbrev Operator (ι : Type u_10) := Op (Path ι)

def start (w : Path ι) : Bool := match w.1 with
  | [] => w.2
  | (_,r)::_ => r

def prepend (i : ι) (r : Bool) : Path ι ↪ Path ι :=
  ⟨fun w => ((i,r)::w.1,w.2), by
    rintro ⟨v,s⟩ ⟨w,t⟩ h
    have he := Prod.mk.inj h
    exact Prod.ext (List.cons.inj he.1).2 he.2⟩

def creation (i : ι) (r : Bool) : Operator ι :=
  (hilbertEmbedding (prepend i r)).toContinuousLinearMap

@[simp] theorem creation_single (i : ι) (r : Bool) (w : Path ι) (z : ℂ) :
    creation i r (lp.single 2 w z)=lp.single 2 ((i,r)::w.1,w.2) z :=
  hilbertEmbedding_single (prepend i r) w z

 theorem annihilation_single_nil (i : ι) (r s : Bool) (z : ℂ) :
    star (creation i r) (lp.single 2 ([],s) z)=0 := by
  ext w
  have hi := ContinuousLinearMap.adjoint_inner_right (creation i r)
    (lp.single 2 w 1) (lp.single 2 ([],s) z)
  rw [creation_single,lp.inner_single_left,lp.inner_single_left] at hi
  simpa [ContinuousLinearMap.star_eq_adjoint,RCLike.inner_apply,lp.single_apply] using hi

 theorem annihilation_single_cons (i j : ι) (r s e : Bool)
    (w : List (ι × Bool)) (z : ℂ) :
    star (creation i r) (lp.single 2 ((j,s)::w,e) z)=
      if (i,r)=(j,s) then lp.single 2 (w,e) z else 0 := by
  ext v
  have hi := ContinuousLinearMap.adjoint_inner_right (creation i r)
    (lp.single 2 v 1) (lp.single 2 ((j,s)::w,e) z)
  rw [creation_single,lp.inner_single_left,lp.inner_single_left] at hi
  have he : (star (creation i r) (lp.single 2 ((j,s)::w,e) z)) v=
      (lp.single (E := fun _ : Path ι => ℂ) 2 ((j,s)::w,e) z) ((i,r)::v.1,v.2) := by
    simpa [ContinuousLinearMap.star_eq_adjoint,RCLike.inner_apply] using hi
  rw [he]
  rcases v with ⟨v,t⟩
  by_cases hab : (i,r)=(j,s)
  · simp only [lp.single_apply,Pi.single_apply,Prod.mk.injEq,List.cons.injEq,hab,
      true_and,ite_true]
  · simp only [lp.single_apply,Pi.single_apply,Prod.mk.injEq,List.cons.injEq,hab,
      false_and,ite_false,lp.coeFn_zero,Pi.zero_apply]

def P : Operator ι := CoordinateProjection.proj {w : Path ι | start w=true}

theorem projection_P : IsStarProjection (P : Operator ι) := CoordinateProjection.projection _

theorem P_creation_false (i : ι) : (P : Operator ι)*creation i false=0 := by
  apply operator_basis_ext
  intro w
  simp [mul_apply_eq_comp,creation_single,P,CoordinateProjection.proj_single,start]

def S (u v : ℝ) (i : ι) : Operator ι :=
  (u:ℂ) • creation i true + (v:ℂ) • creation i false +
  star ((u:ℂ) • creation i true + (v:ℂ) • creation i false)

theorem S_selfAdjoint (u v : ℝ) (i : ι) : IsSelfAdjoint (S u v i) := by
  exact IsSelfAdjoint.add_star_self (R := Operator ι) _

end

section
open FreeFock
variable {ι : Type u_11} [DecidableEq ι]

@[simp] theorem P_single (w : Path ι) (z : ℂ) :
    (P : Operator ι) (lp.single 2 w z)=if start w=true then lp.single 2 w z else 0 :=
by
  classical
  have hp := CoordinateProjection.proj_single {w : Path ι | start w=true} w z
  simp only [Set.mem_ofPred_eq] at hp
  unfold P
  by_cases h : start w=true
  · rw [ite_eq_left h]
    rw [ite_eq_left h] at hp
    exact hp
  · rw [ite_eq_right h]
    rw [ite_eq_right h] at hp
    exact hp

@[simp] theorem P_nil_true (z : ℂ) : (P : Operator ι) (lp.single 2 ([],true) z)=
    lp.single 2 ([],true) z := by simp [start]

@[simp] theorem P_nil_false (z : ℂ) : (P : Operator ι) (lp.single 2 ([],false) z)=0 := by simp [start]

@[simp] theorem P_cons (i : ι) (r e : Bool) (w : List (ι×Bool)) (z : ℂ) :
    (P : Operator ι) (lp.single 2 ((i,r)::w,e) z)=
      if r=true then lp.single 2 ((i,r)::w,e) z else 0 := by
  rw [P_single]
  change (if r=true then _ else _) = _
  split_ifs <;> rfl

theorem S_nil (u v : ℝ) (i : ι) (e : Bool) (z : ℂ) :
    S u v i (lp.single 2 ([],e) z)=
      (u:ℂ) • lp.single 2 ([(i,true)],e) z +
      (v:ℂ) • lp.single 2 ([(i,false)],e) z := by
  simp only [S,add_apply,star_add (R := Operator ι),star_smul,Complex.star_def,Complex.conj_ofReal,
    _root_.smul_apply,creation_single,annihilation_single_nil,smul_zero,add_zero]

def ambientAlgebra (u v : ℝ) : StarSubalgebra ℂ (Operator ι) :=
  StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
    (insert P (Set.range (S u v : ι → Operator ι))) : Set (Operator ι))

theorem P_mem_ambient (u v : ℝ) : (P : Operator ι) ∈ ambientAlgebra u v :=
  StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert _ _))

theorem S_mem_ambient (u v : ℝ) (i : ι) : S u v i ∈ ambientAlgebra u v :=
  StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_range_self i)))

end

section
open FreeFock
variable {ι : Type u_12}

def appendPath (w : Path ι) (i : ι) (r : Bool) : Path ι := (w.1++[(i,w.2)],r)
def reverseList : List (ι × Bool) → Bool → Path ι
  | [],e => ([],e)
  | (i,r)::w,e => appendPath (reverseList w e) i r

def reversePath (w : Path ι) : Path ι := reverseList w.1 w.2

@[simp] theorem reverse_nil (e : Bool) : reversePath (([],e) : Path ι)=([],e) := rfl
@[simp] theorem reverse_cons (i : ι) (r e : Bool) (w : List (ι×Bool)) :
    reversePath ((i,r)::w,e)=appendPath (reversePath (w,e)) i r := rfl

@[simp] theorem start_appendPath (w : Path ι) (i : ι) (r : Bool) :
    start (appendPath w i r)=start w := by
  rcases w with ⟨w,e⟩
  cases w <;> rfl

theorem reverse_append (w : List (ι×Bool)) (i : ι) (r e : Bool) :
    reversePath (w++[(i,r)],e)=prepend i e (reversePath (w,r)) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    rcases p with ⟨j,s⟩
    change appendPath (reversePath (w++[(i,r)],e)) j s=
      prepend i e (appendPath (reversePath (w,r)) j s)
    rw [ih]
    rfl

theorem reversePath_involutive : Function.Involutive (reversePath : Path ι → Path ι) := by
  rintro ⟨w,e⟩
  induction w generalizing e with
  | nil => rfl
  | cons p w ih =>
    rcases p with ⟨i,r⟩
    rw [reverse_cons]
    change reversePath ((reversePath (w,e)).1++[(i,(reversePath (w,e)).2)],r)=_
    rw [reverse_append]
    change prepend i r (reversePath (reversePath (w,e)))=_
    rw [ih]
    rfl

@[simp] theorem end_reverse (w : Path ι) : (reversePath w).2=start w := by
  rcases w with ⟨w,e⟩
  cases w with
  | nil => rfl
  | cons a w => cases a; rfl

@[simp] theorem start_reverse (w : Path ι) : start (reversePath w)=w.2 := by
  have h := end_reverse (reversePath w)
  rw [reversePath_involutive] at h
  exact h.symm

@[simp] theorem reversePath_reverse (w : Path ι) : reversePath (reversePath w)=w :=
  reversePath_involutive w

variable [DecidableEq ι]

def reverseEmbedding : Path ι ↪ Path ι := ⟨reversePath,reversePath_involutive.injective⟩
def reverseIsometry : H ι →ₗᵢ[ℂ] H ι := hilbertEmbedding reverseEmbedding
def reverseOperator : Operator ι := reverseIsometry.toContinuousLinearMap

@[simp] theorem reverseOperator_single (w : Path ι) (z : ℂ) :
    reverseOperator (lp.single 2 w z)=lp.single 2 (reversePath w) z :=
  hilbertEmbedding_single reverseEmbedding w z

theorem reverseOperator_square : (reverseOperator : Operator ι)*reverseOperator=1 := by
  apply operator_basis_ext
  intro w
  simp [mul_apply_eq_comp,reverseOperator_single]

theorem reverseOperator_involutive (ξ : H ι) : reverseOperator (reverseOperator ξ)=ξ :=
  DFunLike.congr_fun reverseOperator_square ξ

def reverseEquiv : H ι ≃ₗᵢ[ℂ] H ι :=
  LinearIsometryEquiv.ofSurjective reverseIsometry (fun ξ =>
    ⟨reverseOperator ξ,reverseOperator_involutive ξ⟩)

@[simp] theorem reverseEquiv_apply (ξ : H ι) : reverseEquiv ξ=reverseOperator ξ := rfl
@[simp] theorem reverseEquiv_symm_apply (ξ : H ι) : reverseEquiv.symm ξ=reverseOperator ξ := by
  apply reverseEquiv.injective
  rw [LinearIsometryEquiv.apply_symm_apply,reverseEquiv_apply,reverseOperator_involutive]

def reverseConj : Operator ι ≃⋆ₐ[ℂ] Operator ι := reverseEquiv.conjStarAlgEquiv

@[simp] theorem reverseConj_apply (T : Operator ι) (ξ : H ι) :
    reverseConj T ξ=reverseOperator (T (reverseOperator ξ)) := by
  simp only [reverseConj,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    reverseEquiv_apply,reverseEquiv_symm_apply]

def appendEmbedding (i : ι) (r : Bool) : Path ι ↪ Path ι :=
  ⟨fun w => appendPath w i r, by
    intro w v h
    apply reversePath_involutive.injective
    have he := congrArg reversePath h
    change reversePath (w.1++[(i,w.2)],r)=reversePath (v.1++[(i,v.2)],r) at he
    rw [reverse_append,reverse_append] at he
    exact (prepend i r).injective he⟩

def rightCreation (i : ι) (r : Bool) : Operator ι :=
  (hilbertEmbedding (appendEmbedding i r)).toContinuousLinearMap

@[simp] theorem rightCreation_single (i : ι) (r : Bool) (w : Path ι) (z : ℂ) :
    rightCreation i r (lp.single 2 w z)=lp.single 2 (appendPath w i r) z :=
  hilbertEmbedding_single (appendEmbedding i r) w z

theorem reverseConj_creation (i : ι) (r : Bool) :
    reverseConj (creation i r)=rightCreation i r := by
  apply operator_basis_ext
  intro w
  simp only [reverseConj_apply,reverseOperator_single,creation_single,rightCreation_single,
    reverse_cons,Prod.eta,reversePath_reverse]

def rightP : Operator ι := CoordinateProjection.proj {w : Path ι | w.2=true}

theorem reverseConj_P : reverseConj (P : Operator ι)=rightP := by
  apply operator_basis_ext
  intro w
  simp only [reverseConj_apply,reverseOperator_single,P_single,start_reverse,
    rightP,CoordinateProjection.proj_single,Set.mem_ofPred_eq]
  split_ifs <;> simp [reverseOperator_single]

end

section
open FreeFock
variable {ι : Type u_13} [DecidableEq ι]

end

section
open FreeFock
open scoped ComplexConjugate
variable {ι : Type u_14} [DecidableEq ι]

end

open FreeFock
open scoped ComplexConjugate
variable {ι : Type u_15} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


