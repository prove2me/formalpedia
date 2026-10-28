-- Prove2me | Definitions.Def_OAIQ031A023
-- name    : OAIQ031A023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:57:48.15742+00:00
-- url     : https://prove2.me/theorems/1a679f1d-7faa-4d83-b971-03625102e796
-- title:
--   Definitions bundle OAIQ031A023 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 36 declarations of OpenAI's Lean: 14 definitions, 6 instances and 16 theorems. The definitions and types are `OAI.ArExplicit.coneDiagonalDifferential`, `OAI.ArExplicit.coneEnd`, `OAI.ArExplicit.coneEndA`, `OAI.ArExplicit.coneEndB`, `OAI.ArExplicit.coneEndC`, `OAI.ArExplicit.coneEndUpper`, `OAI.ArExplicit.diagonalSubmodule`, `OAI.ArExplicit.moduleHomPostcomp`, `OAI.ArExplicit.scalarDiagonalEquiv`, `OAI.ArExplicit.scalarExtensionModule`, `OAI.ArExplicit.scalarExtensionQuotientMap`, `OAI.ArExplicit.scalarExtensionRepresentation`, `OAI.ArExplicit.triangleReplaceMiddle`, `OAI.ArExplicit.triangleReplaceMiddleIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_BaseChange_ScalarExtension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtension.lean), [`AuslanderReiten_BaseChange_ScalarExtensionDescent`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionDescent.lean), [`AuslanderReiten_BaseChange_ScalarExtensionStructure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionStructure.lean), [`AuslanderReiten_Cones_ConeComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeComparison.lean), [`AuslanderReiten_Cones_ConeEnd`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeEnd.lean), [`AuslanderReiten_Coordinates_TwoTwistLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/TwoTwistLinear.lean), [`AuslanderReiten_Fibers_FiberExactness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberExactness.lean), [`AuslanderReiten_Fibers_FiberProjectionZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberProjectionZero.lean), [`AuslanderReiten_Homology_TriangleMiddleTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TriangleMiddleTransport.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A042` and `OAIQ031A043`; the statements `OAI.ArExplicit.GorensteinProjective.scalarExtension`, `OAI.ArExplicit.PositiveExtVanish.scalarExtension` and `OAI.ArExplicit.nonprojective_scalarExtension`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w

section BaseChange

variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  (M : Type w) [AddCommGroup M] [Module R M] [Module k M]
  [IsScalarTower k R M]

def scalarExtensionRepresentation :
    E ⊗[k] R →ₐ[E] Module.End E (E ⊗[k] M) :=
  AlgHom.liftEquiv k E R (Module.End E (E ⊗[k] M))
    ((Module.End.baseChangeHom k E M).comp (Algebra.lsmul k k M))

@[instance_reducible]
def scalarExtensionModule : Module (E ⊗[k] R) (E ⊗[k] M) :=
  Module.compHom (E ⊗[k] M) (scalarExtensionRepresentation k E R M).toRingHom

attribute [local instance] scalarExtensionModule

theorem scalarExtension_smul_tmul (e e' : E) (r : R) (m : M) :
    (e ⊗ₜ[k] r) • (e' ⊗ₜ[k] m) = (e * e') ⊗ₜ[k] (r • m) := by
  change ((scalarExtensionRepresentation k E R M) (e ⊗ₜ[k] r)) (e' ⊗ₜ[k] m) = _
  rfl

instance scalarExtensionIsScalarTower :
    IsScalarTower E (E ⊗[k] R) (E ⊗[k] M) :=
  IsScalarTower.of_algebraMap_smul fun e x => by
    change ((scalarExtensionRepresentation k E R M)
      (algebraMap E (E ⊗[k] R) e)) x = e • x
    rw [AlgHom.commutes]
    rfl

instance scalarExtensionBaseIsScalarTower :
    IsScalarTower k (E ⊗[k] R) (E ⊗[k] M) :=
  IsScalarTower.of_algebraMap_smul fun a x => by
    rw [IsScalarTower.algebraMap_apply k E (E ⊗[k] R),
      IsScalarTower.algebraMap_smul (E ⊗[k] R), IsScalarTower.algebraMap_smul E]

end BaseChange

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]

variable (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

def moduleHomPostcomp (f : N →ₗ[R] L) : (M →ₗ[R] N) →ₗ[k] (M →ₗ[R] L) where
  toFun := f.comp
  map_add' g h := by
    ext x
    exact f.map_add _ _
  map_smul' a g := by
    ext m
    exact (f.restrictScalars k).map_smul a (g m)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

variable {k R : Type*} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (E : Type*) [Field E] [Algebra k E]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def scalarExtensionQuotientMap (f : R →ₐ[k] (ι → k)) :
    E ⊗[k] R →ₐ[E] (ι → E) :=
  (Algebra.TensorProduct.piScalarRight k E E ι).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id E E) f)

omit [Module.Finite k R] in
theorem scalarExtensionQuotientMap_surjective (f : R →ₐ[k] (ι → k))
    (hf : Function.Surjective f) : Function.Surjective (scalarExtensionQuotientMap E f) :=
  (Algebra.TensorProduct.piScalarRight k E E ι).surjective.comp
    (Algebra.TensorProduct.map_surjective (AlgHom.id E E) f Function.surjective_id hf)

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeEnd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open CochainComplex.mappingCone

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) [HasHomotopyCofiber φ]
variable {n : ℤ}

def coneEnd (a : Cochain G G n) (b : Cochain F F n) (c : Cochain F G (n - 1)) :
    Cochain (mappingCone φ) (mappingCone φ) n :=
  descCochain φ (liftCochain φ b c (by omega))
    (liftCochain φ (0 : Cochain G F (n + 1)) a rfl) (by omega)

def coneEndA (x : Cochain (mappingCone φ) (mappingCone φ) n) : Cochain G G n :=
  ((Cochain.ofHom (inr φ)).comp x (zero_add n)).comp (snd φ) (add_zero n)

def coneEndB (x : Cochain (mappingCone φ) (mappingCone φ) n) : Cochain F F n :=
  ((inl φ).comp x (show -1 + n = n - 1 by omega)).comp (fst φ).1 (by omega)

def coneEndC (x : Cochain (mappingCone φ) (mappingCone φ) n) : Cochain F G (n - 1) :=
  ((inl φ).comp x (show -1 + n = n - 1 by omega)).comp (snd φ) (add_zero _)

def coneEndUpper (x : Cochain (mappingCone φ) (mappingCone φ) n) : Cochain G F (n + 1) :=
  ((Cochain.ofHom (inr φ)).comp x (zero_add n)).comp (fst φ).1 rfl

@[simp] theorem coneEndA_mk (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) : coneEndA φ (coneEnd φ a b c) = a := by
  simp [coneEndA, coneEnd]

@[simp] theorem coneEndB_mk (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) : coneEndB φ (coneEnd φ a b c) = b := by
  simp [coneEndB, coneEnd]

@[simp] theorem coneEndC_mk (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) : coneEndC φ (coneEnd φ a b c) = c := by
  simp [coneEndC, coneEnd]

@[simp] theorem coneEndUpper_mk (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) : coneEndUpper φ (coneEnd φ a b c) = 0 := by
  simp [coneEndUpper, coneEnd]

theorem coneEnd_ext {x y : Cochain (mappingCone φ) (mappingCone φ) n}
    (ha : coneEndA φ x = coneEndA φ y) (hb : coneEndB φ x = coneEndB φ y)
    (hc : coneEndC φ x = coneEndC φ y) (hu : coneEndUpper φ x = coneEndUpper φ y) : x = y := by
  apply (ext_cochain_from_iff φ (n - 1) n (by omega)).mpr
  constructor
  · exact (ext_cochain_to_iff φ (n - 1) n (by omega)).mpr ⟨hb, hc⟩
  · exact (ext_cochain_to_iff φ n (n + 1) rfl).mpr ⟨hu, ha⟩

theorem coneEnd_reconstruct (x : Cochain (mappingCone φ) (mappingCone φ) n)
    (hu : coneEndUpper φ x = 0) :
    coneEnd φ (coneEndA φ x) (coneEndB φ x) (coneEndC φ x) = x := by
  apply coneEnd_ext φ <;> simp [hu]

@[simp] theorem coneEnd_zero :
    coneEnd φ (0 : Cochain G G n) (0 : Cochain F F n) (0 : Cochain F G (n - 1)) = 0 := by
  simp [coneEnd, descCochain, liftCochain]

theorem coneEnd_differential (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) :
    δ n (n + 1) (coneEnd φ a b c) =
      descCochain φ
        (liftCochain φ (-(δ n (n + 1) b))
          (δ (n - 1) n c + b.comp (Cochain.ofHom φ) (add_zero n) +
            (n + 1).negOnePow • (Cochain.ofHom φ).comp a (zero_add n)) rfl)
        (liftCochain φ (0 : Cochain G F ((n + 1) + 1)) (δ n (n + 1) a) rfl) rfl := by
  rw [coneEnd, δ_descCochain φ _ _ (by omega) (n + 1) rfl,
    δ_liftCochain φ _ _ (by omega) (n + 1) rfl,
    δ_liftCochain φ _ _ rfl ((n + 1) + 1) rfl]
  apply (ext_cochain_from_iff φ n (n + 1) rfl).mpr
  constructor
  · apply (ext_cochain_to_iff φ n (n + 1) rfl).mpr
    constructor <;> simp [liftCochain, descCochain]
  · apply (ext_cochain_to_iff φ (n + 1) ((n + 1) + 1) rfl).mpr
    constructor <;> simp [liftCochain, descCochain]

theorem coneEnd_closed_iff (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) :
    δ n (n + 1) (coneEnd φ a b c) = 0 ↔
      δ n (n + 1) a = 0 ∧ δ n (n + 1) b = 0 ∧
        δ (n - 1) n c + b.comp (Cochain.ofHom φ) (add_zero n) +
          (n + 1).negOnePow • (Cochain.ofHom φ).comp a (zero_add n) = 0 := by
  rw [coneEnd_differential]
  rw [ext_cochain_from_iff φ n (n + 1) rfl]
  simp only [Cochain.comp_zero, inl_descCochain, inr_descCochain]
  rw [ext_cochain_to_iff φ n (n + 1) rfl,
    ext_cochain_to_iff φ (n + 1) ((n + 1) + 1) rfl]
  simp only [liftCochain_fst, liftCochain_snd, Cochain.zero_comp, neg_eq_zero, true_and]
  tauto

theorem coneEnd_all_reconstruct
    (hzero : ∀ m (x : Cochain G F m), x = 0)
    (x : Cochain (mappingCone φ) (mappingCone φ) n) :
    coneEnd φ (coneEndA φ x) (coneEndB φ x) (coneEndC φ x) = x :=
  coneEnd_reconstruct φ x (hzero _ _)

theorem coneEnd_boundary_iff (m : ℤ) (hm : m + 1 = n)
    (a : Cochain G G m) (b : Cochain F F m) (c : Cochain F G (m - 1))
    (a' : Cochain G G n) (b' : Cochain F F n) (c' : Cochain F G m) :
    δ m n (coneEnd φ a b c) =
      descCochain φ (liftCochain φ b' c' hm)
        (liftCochain φ (0 : Cochain G F (n + 1)) a' rfl) hm ↔
      δ m n a = a' ∧ -(δ m n b) = b' ∧
        δ (m - 1) m c + b.comp (Cochain.ofHom φ) (add_zero m) +
          (m + 1).negOnePow • (Cochain.ofHom φ).comp a (zero_add m) = c' := by
  subst n
  rw [coneEnd_differential, ext_cochain_from_iff φ m (m + 1) rfl]
  simp only [inl_descCochain, inr_descCochain]
  rw [ext_cochain_to_iff φ m (m + 1) rfl,
    ext_cochain_to_iff φ (m + 1) ((m + 1) + 1) rfl]
  simp only [liftCochain_fst, liftCochain_snd, true_and]
  tauto

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

def coneDiagonalDifferential (m : ℤ) :
    (Cochain G G n × Cochain F F n) →ₗ[ℤ] (Cochain G G m × Cochain F F m) where
  toFun x := (δ n m x.1, -(δ n m x.2))
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' r x := by ext <;> simp

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TwoTwistLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

def diagonalSubmodule : Submodule k (V × V) where
  carrier := {x | x.1 = x.2}
  zero_mem' := rfl
  add_mem' hx hy := congrArg₂ (· + ·) hx hy
  smul_mem' a _ hx := congrArg (a • ·) hx

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberExactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

section Fiber

variable {k : Type*} [Ring k]
variable {B₀ B₁ B₂ C₀ C₁ C₂ : Type*}
variable [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
variable [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
variable [Module k B₀] [Module k B₁] [Module k B₂]
variable [Module k C₀] [Module k C₁] [Module k C₂]

theorem fiber_cocycle_is_boundary
    (dB₀ : B₀ →ₗ[k] B₁) (dB₁ : B₁ →ₗ[k] B₂)
    (dC₀ : C₀ →ₗ[k] C₁) (dC₁ : C₁ →ₗ[k] C₂)
    (f₀ : B₀ →ₗ[k] C₁) (f₁ : B₁ →ₗ[k] C₂)
    (hf : ∀ a, f₁ (dB₀ a) = dC₁ (f₀ a))
    (hinj : ∀ b, dB₁ b = 0 → (∃ c, f₁ b = dC₁ c) → ∃ a, dB₀ a = b)
    (hsurj : ∀ c, dC₁ c = 0 → ∃ a, dB₀ a = 0 ∧ ∃ e, f₀ a - dC₀ e = c)
    (b : B₁) (c : C₁) (hb : dB₁ b = 0) (hc : f₁ b = dC₁ c) :
    ∃ a : B₀, ∃ e : C₀, dB₀ a = b ∧ f₀ a - dC₀ e = c := by
  obtain ⟨a, ha⟩ := hinj b hb ⟨c, hc⟩
  have hcycle : dC₁ (c - f₀ a) = 0 := by
    rw [map_sub, ← hf, ha, hc, sub_self]
  obtain ⟨u, hu, e, he⟩ := hsurj (c - f₀ a) hcycle
  refine ⟨a + u, e, ?_, ?_⟩
  · rw [map_add, ha, hu, add_zero]
  · rw [map_add, add_sub_assoc, he, add_sub_cancel]

end Fiber
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberProjectionZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit
universe u
variable (k : Type u) [Field k]

def scalarDiagonalEquiv : diagonalSubmodule (k := k) (V := k) ≃ₗ[k] k where
  toFun z := z.val.1
  invFun a := ⟨(a,a), rfl⟩
  left_inv z := Subtype.ext (Prod.ext rfl z.property)
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleMiddleTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Pretriangulated
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (T : Triangle C) {Y : C} (e : T.obj₂ ≅ Y)

def triangleReplaceMiddle : Triangle C :=
  Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃

def triangleReplaceMiddleIso : T ≅ triangleReplaceMiddle T e :=
  Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
    (by
      change T.mor₁ ≫ e.hom = 𝟙 _ ≫ (T.mor₁ ≫ e.hom)
      rw [Category.id_comp])
    (by
      change T.mor₂ ≫ 𝟙 _ = e.hom ≫ (e.inv ≫ T.mor₂)
      rw [Category.comp_id, Iso.hom_inv_id_assoc])
    (by
      change T.mor₃ ≫ (CategoryTheory.shiftFunctor C 1).map (𝟙 _) = 𝟙 _ ≫ T.mor₃
      rw [(CategoryTheory.shiftFunctor C 1).map_id, Category.id_comp, Category.comp_id])

variable [Preadditive C] [Limits.HasZeroObject C]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

theorem triangleReplaceMiddle_distinguished (hT : T ∈ distTriang C) :
    triangleReplaceMiddle T e ∈ distTriang C :=
  (distinguished_iff_of_iso (triangleReplaceMiddleIso T e)).mp hT

end ArExplicit

end

end OAI
end


