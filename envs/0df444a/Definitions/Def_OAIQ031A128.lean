-- Prove2me | Definitions.Def_OAIQ031A128
-- name    : OAIQ031A128
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:05:47.65644+00:00
-- url     : https://prove2.me/theorems/86562bd4-8e0f-489f-9f75-61a48f9303dc
-- title:
--   Definitions bundle OAIQ031A128 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Triangular_TriangularCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularCochain.lean), [`AuslanderReiten_Triangular_TriangularComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularComparison.lean), [`AuslanderReiten_Triangular_TriangularComparisonTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularComparisonTransport.lean), [`AuslanderReiten_Triangular_TriangularProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularProjective.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A116` and `OAIQ031A117` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A138`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A116
import Definitions.Def_OAIQ031A117

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularEFunctor _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularJFunctor _root_.OAI.ArExplicit.TriangularInduction.instFaithfulModuleCatTriangularEFunctor _root_.OAI.ArExplicit.TriangularInduction.instFaithfulModuleCatTriangularJFunctor _root_.OAI.ArExplicit.TriangularInduction.instFullModuleCatTriangularEFunctor _root_.OAI.ArExplicit.TriangularInduction.instFullModuleCatTriangularJFunctor _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

variable {M : Type*} [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]

omit [SMulCommClass k R M] in
theorem eProjective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective (Triangular R F) (TriangularE k R F M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  let : Module.Projective (Triangular R F) (TriangularE k R F (Fin n → R)) :=
    Module.Projective.of_equiv (ePi (k := k) (R := R) (F := F) (M := R) (Fin n)).symm
  apply Module.Projective.of_split (eMap s) (eMap p)
  rw [← eMap_comp, hs, eMap_id]

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.TrivialInduction.baseComm _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory

universe u

variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable [Module.Finite k R] [Module.Finite k F]

theorem eCochain_totallyAcyclic [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : TotallyAcyclicCochain P) :
    TotallyAcyclicCochain (eCochain (k := k) (F := F) P) where
  finite n := by
    let := hP.finite n
    let : Module.Finite k (P.X n) := Module.Finite.trans R (P.X n)
    exact Module.Finite.of_restrictScalars_finite k (Triangular R F) (TriangularE k R F (P.X n))
  projective n := by
    let := hP.finite n
    let := hP.projective n
    exact eProjective
  exactAt n := by
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    have h := hP.exactAt n
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
    exact (LinearMap.exact_iff.mp (eMap_exact (k := k) (F := F) _ _
      (LinearMap.exact_iff.mpr h.symm))).symm
  dualExact n := eHomExact _ _ (hP.dualExact n)

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularComparison
attribute [-instance] _root_.OAI.ArExplicit.BalancedTensor.functor_linear _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TriangularInduction
open CategoryTheory CochainComplex.HomComplex
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P) (n : ℤ)

theorem crossCohomology_postcomp (x : CohomologyClass P P n) :
    crossCohomologyEquiv P P n (fullHomPostcomp v n x) =
      fullHomPostcomp (crossChainMap v) n (mapFullHom (jFunctor k R F) P P n x) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [fullHomPostcomp_mk, crossCohomologyEquiv_mk, mapFullHom_mk, fullHomPostcomp_mk]
  congr 1
  apply Cocycle.ext
  change crossCochainEquiv P P n (x.1.comp (Cochain.ofHom v) (add_zero n)) =
    (x.1.map (jFunctor k R F)).comp (Cochain.ofHom (crossChainMap v)) (add_zero n)
  apply Cochain.ext
  intro i j hij
  rw [crossCochainEquiv_v,
    Cochain.comp_v x.1 (Cochain.ofHom v) (add_zero n) i j j hij (add_zero j),
    Cochain.comp_v (x.1.map (jFunctor k R F)) (Cochain.ofHom (crossChainMap v))
      (add_zero n) i j j hij (add_zero j)]
  simp only [Cochain.ofHom_v, Cochain.map_v]
  exact crossHomAdd_source _ _

theorem crossCohomology_precomp (x : CohomologyClass P P n) :
    crossCohomologyEquiv P P n (fullHomPrecomp v n
      (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n x)) =
      fullHomPrecomp (crossChainMap v) n (mapFullHom (eFunctor k R F) P P n x) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  rw [mapFullHom_mk, fullHomPrecomp_mk, crossCohomologyEquiv_mk,
    mapFullHom_mk, fullHomPrecomp_mk]
  congr 1
  apply Cocycle.ext
  change crossCochainEquiv P P n ((Cochain.ofHom v).comp
      (x.1.map (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F))) (zero_add n)) =
    (Cochain.ofHom (crossChainMap v)).comp (x.1.map (eFunctor k R F)) (zero_add n)
  apply Cochain.ext
  intro i j hij
  rw [crossCochainEquiv_v,
    Cochain.comp_v (Cochain.ofHom v)
      (x.1.map (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)))
      (zero_add n) i i j (add_zero i) hij,
    Cochain.comp_v (Cochain.ofHom (crossChainMap v)) (x.1.map (eFunctor k R F))
      (zero_add n) i i j (add_zero i) hij]
  simp only [Cochain.ofHom_v, Cochain.map_v]
  exact crossHomAdd_target _ _

theorem cross_tensorComparison (a b : CohomologyClass P P n) :
    crossCohomologyEquiv P P n (tensorComparison v n (a,b)) =
      coneComparison (crossChainMap v) n
        (fullHomCohomologyEquiv (eFunctor k R F) P P n a,
          fullHomCohomologyEquiv (jFunctor k R F) P P n b) := by
  change crossCohomologyEquiv P P n (fullHomPostcomp v n b +
    (n+1).negOnePow • fullHomPrecomp v n
      (mapFullHom (BalancedTensor.functor (k := k) (R := R) (S := R) (F := F)) P P n a)) = _
  rw [map_add]
  simp only [Units.smul_def, map_zsmul, crossCohomology_postcomp, crossCohomology_precomp]
  rfl

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularComparisonTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TriangularInduction
open CategoryTheory CochainComplex.HomComplex
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {P : CochainComplex (ModuleCat.{u} R) ℤ}
variable (v : P ⟶ tensorCochain (k := k) (F := F) P) (n : ℤ)

theorem coneComparison_injective_of_tensor
    (h : Function.Injective (tensorComparison v n)) :
    Function.Injective (coneComparison (crossChainMap v) n) := by
  intro x y hxy
  obtain ⟨a,rfl⟩ := (comparisonSourceEquiv (F := F) (P := P) n).surjective x
  obtain ⟨b,rfl⟩ := (comparisonSourceEquiv (F := F) (P := P) n).surjective y
  apply congrArg
  apply h
  apply (crossCohomologyEquiv P P n).injective
  rw [cross_tensorComparison, cross_tensorComparison]
  exact hxy

theorem coneComparison_surjective_of_tensor
    (h : Function.Surjective (tensorComparison v n)) :
    Function.Surjective (coneComparison (crossChainMap v) n) := by
  intro y
  obtain ⟨x,hx⟩ := h ((crossCohomologyEquiv P P n).symm y)
  refine ⟨comparisonSourceEquiv (F := F) (P := P) n x, ?_⟩
  rcases x with ⟨a,b⟩
  rw [comparisonSourceEquiv_apply, ← cross_tensorComparison, hx, AddEquiv.apply_symm_apply]

theorem coneComparison_nonzero_kernel_of_tensor
    (h : ∃ x : CohomologyClass P P n × CohomologyClass P P n,
      x ≠ 0 ∧ tensorComparison v n x = 0) :
    ∃ x : CohomologyClass (eCochain (k := k) (F := F) P)
        (eCochain (k := k) (F := F) P) n ×
      CohomologyClass (jCochain (k := k) (F := F) P)
        (jCochain (k := k) (F := F) P) n,
      x ≠ 0 ∧ coneComparison (crossChainMap v) n x = 0 := by
  obtain ⟨x,hx,h0⟩ := h
  refine ⟨comparisonSourceEquiv (F := F) (P := P) n x, ?_, ?_⟩
  · exact fun he => hx ((comparisonSourceEquiv (F := F) (P := P) n).map_eq_zero_iff.mp he)
  · rcases x with ⟨a,b⟩
    rw [comparisonSourceEquiv_apply, ← cross_tensorComparison, h0, map_zero]

end ArExplicit.TriangularInduction

end

end OAI
end


