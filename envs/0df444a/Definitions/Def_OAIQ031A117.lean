-- Prove2me | Definitions.Def_OAIQ031A117
-- name    : OAIQ031A117
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:53:03.047262+00:00
-- url     : https://prove2.me/theorems/f3ef863a-9087-4983-83b3-9b9a056fa196
-- title:
--   Definitions bundle OAIQ031A117 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 11 declarations of OpenAI's Lean: 2 instances and 9 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_ConeCriterion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeCriterion.lean), [`AuslanderReiten_HomComplex_FullHomExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomExt.lean), [`AuslanderReiten_Resolutions_TrivialInductionComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/TrivialInductionComplex.lean), [`AuslanderReiten_Triangular_TriangularCategory`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularCategory.lean), [`AuslanderReiten_Triangular_TriangularCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularCochain.lean), [`AuslanderReiten_Triangular_TriangularDualExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularDualExact.lean), [`AuslanderReiten_Triangular_TriangularProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularProjective.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A090`, `OAIQ031A093`, `OAIQ031A096`, `OAIQ031A097`, `OAIQ031A103` and `OAIQ031A104` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A128`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A090
import Definitions.Def_OAIQ031A093
import Definitions.Def_OAIQ031A096
import Definitions.Def_OAIQ031A097
import Definitions.Def_OAIQ031A103
import Definitions.Def_OAIQ031A104

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomExt
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison
open CochainComplex CochainComplex.HomComplex

universe u

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

include k

theorem positiveExtVanish_of_fullHom
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L))
    (h : ∀ n : ℕ, 0 < n → Subsingleton (CohomologyClass K L (n : ℤ))) :
    PositiveExtVanish R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) 0) := by
  apply positiveExtVanish_of_stableCokernels hK
  intro n
  let := h (n + 1) (Nat.zero_lt_succ n)
  exact (fullHomSourceStableLinearEquiv (k := k) K L ((n + 1 : ℕ) : ℤ) hK hL).symm.injective.subsingleton

theorem not_projective_of_fullHom_nontrivial
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (h : Nontrivial (CohomologyClass K K 0)) :
    ¬ Module.Projective R (Cokernel (chainOfCochain K) 0) := by
  intro hp
  let := hK.finite 0
  let := hp
  have : Subsingleton (StableHom R (Cokernel (chainOfCochain K) 0)
      (Cokernel (chainOfCochain K) 0)) := ⟨fun a b =>
    (StableHom.eq_zero_of_projective_source a).trans (StableHom.eq_zero_of_projective_source b).symm⟩
  have : Subsingleton (CohomologyClass K K 0) :=
    (fullHomStableZeroLinearEquiv (k := k) K K hK hK.toExactProjectiveComplex).injective.subsingleton
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  exact hab (Subsingleton.elim a b)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeCriterion
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison
open CochainComplex CochainComplex.HomComplex

universe u

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

include k

theorem coneModule_properties
    (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G)
    (hzero : ∀ n (x : Cochain G F n), x = 0)
    (hinj : ∀ n : ℕ, 0 < n → Function.Injective (coneComparison φ (n : ℤ)))
    (hsurj : ∀ n : ℕ, Function.Surjective (coneComparison φ (n : ℤ)))
    (hker : ∃ w : CohomologyClass G G 0 × CohomologyClass F F 0,
      w ≠ 0 ∧ coneComparison φ 0 w = 0) :
    ¬ Module.Projective R (ConeModule φ) ∧
      GorensteinProjective R (ConeModule φ) ∧
      PositiveExtVanish R (ConeModule φ) (ConeModule φ) ∧
      PositiveExtVanish R (ConeModule φ) R := by
  have hC := (mappingCone_totallyAcyclic φ hF hG).to_chain
  have hgp := mappingCone_cokernel_gorenstein φ hF hG
  have hpos (n : ℕ) (hn : 0 < n) :
      Subsingleton (CohomologyClass (mappingCone φ) (mappingCone φ) (n : ℤ)) := by
    apply coneEnd_cohomology_subsingleton φ (n : ℤ) hzero (hinj n hn)
    have hi : (n : ℤ) - 1 = ((n - 1 : ℕ) : ℤ) := by omega
    rw [hi]
    exact hsurj (n - 1)
  obtain ⟨w, hw, hcomp⟩ := hker
  exact ⟨not_projective_of_fullHom_nontrivial (k := k) hC
      (coneEnd_nontrivial_of_kernel φ 0 hzero w hw hcomp),
    hgp, positiveExtVanish_of_fullHom (k := k) hC hC.toExactProjectiveComplex hpos,
    hgp.positiveExt_regular⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_TrivialInductionComplex
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "T" => TrivialExtension k R

variable {ι : Type*} {c : ComplexShape ι}

instance induced_term_finite (P : HomologicalComplex (ModuleCat.{u} R) c) (i : ι)
    [Module.Finite R (P.X i)] [Module.Projective R (P.X i)] :
    Module.Finite T ((inducedComplex (k := k) P).X i) :=
  BalancedTensor.finite

end ArExplicit.TrivialInduction

end

end OAI
end

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

omit [Algebra k R] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
  [SMulCommClass k Rᵐᵒᵖ F] in
theorem jRegular_split :
    (jRegularProjection (k := k) (R := R) (F := F)).comp jRegularInclusion = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext
  exact rfl

instance jRegular_projective : Module.Projective (Triangular R F) (TriangularJ k R F R) :=
  Module.Projective.of_split jRegularInclusion jRegularProjection jRegular_split

variable {M : Type*} [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]

omit [SMulCommClass k R M] in
theorem jProjective [Module.Finite R M] [Module.Projective R M] :
    Module.Projective (Triangular R F) (TriangularJ k R F M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  let : Module.Projective (Triangular R F) (TriangularJ k R F (Fin n → R)) :=
    Module.Projective.of_equiv (jPi (k := k) (R := R) (F := F) (M := R) (Fin n)).symm
  apply Module.Projective.of_split (jMap s) (jMap p)
  rw [← jMap_comp, hs, jMap_id]

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularDualExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularEFunctor _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularJFunctor _root_.OAI.ArExplicit.TriangularInduction.instFaithfulModuleCatTriangularEFunctor _root_.OAI.ArExplicit.TriangularInduction.instFaithfulModuleCatTriangularJFunctor _root_.OAI.ArExplicit.TriangularInduction.instFullModuleCatTriangularEFunctor _root_.OAI.ArExplicit.TriangularInduction.instFullModuleCatTriangularJFunctor _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TriangularInduction

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable {K L M U V : Type*}
variable [AddCommGroup K] [Module k K] [Module R K] [IsScalarTower k R K]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable [AddCommGroup U] [Module k U] [Module R U] [IsScalarTower k R U]
variable [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]

theorem eHomExact (e : K →ₗ[R] L) (d : L →ₗ[R] M) (h : HomExactAt e d) :
    HomExactAt (eMap (k := k) (F := F) e) (eMap d) := by
  intro g hg
  let g₁ := (eRegularProjection (k := k)).comp g
  have hg₁ : g₁.comp (eMap e) = 0 := by
    dsimp [g₁]
    rw [LinearMap.comp_assoc, hg, LinearMap.comp_zero]
  obtain ⟨G, hG⟩ := eHomLift e d h g₁ hg₁
  refine ⟨eRegularInclusion.comp G, ?_⟩
  have hg₂ : (jRegularProjection (k := k)).comp g = 0 := hom_E_J_eq_zero _
  apply LinearMap.ext
  intro x
  have hGx := DFunLike.congr_fun hG x
  change G (eMap d x) = g₁ x at hGx
  change eRegularInclusion (G (eMap d x)) = g x
  rw [hGx]
  have hsplit := regular_decomposition (k := k) (g x)
  have hzero := DFunLike.congr_fun hg₂ x
  change jRegularProjection (g x) = 0 at hzero
  simpa only [hzero, map_zero, add_zero, g₁, LinearMap.comp_apply] using hsplit

omit [Module k K] [IsScalarTower k R K] [Module k L] [IsScalarTower k R L]
  [Module k M] [IsScalarTower k R M] in
theorem jHomExact [Module.Finite R F] [Module.Projective R F]
    (e : K →ₗ[R] L) (d : L →ₗ[R] M) (h : HomExactAt e d) :
    HomExactAt (jMap (k := k) (F := F) e) (jMap d) := by
  intro g hg
  let : Module.Finite R (BalancedTensor k R F R) :=
    Module.Finite.equiv (BalancedTensor.runitLeft (S := R)).symm
  let : Module.Projective R (BalancedTensor k R F R) :=
    Module.Projective.of_equiv (BalancedTensor.runitLeft (S := R)).symm
  let g₁ := (eRegularProjection (k := k)).comp g
  let g₂ := (jRegularProjection (k := k)).comp g
  have hg₁ : g₁.comp (jMap e) = 0 := by
    dsimp [g₁]
    rw [LinearMap.comp_assoc, hg, LinearMap.comp_zero]
  have hg₂ : g₂.comp (jMap e) = 0 := by
    dsimp [g₂]
    rw [LinearMap.comp_assoc, hg, LinearMap.comp_zero]
  obtain ⟨G₁, hG₁⟩ := jHomLift e d h g₁ hg₁
  obtain ⟨G₂, hG₂⟩ := jHomLift e d h g₂ hg₂
  refine ⟨eRegularInclusion.comp G₁ + jRegularInclusion.comp G₂, ?_⟩
  apply LinearMap.ext
  intro x
  change eRegularInclusion (G₁ (jMap d x)) + jRegularInclusion (G₂ (jMap d x)) = g x
  have h₁ : G₁ (jMap d x) = g₁ x := DFunLike.congr_fun hG₁ x
  have h₂ : G₂ (jMap d x) = g₂ x := DFunLike.congr_fun hG₂ x
  rw [h₁, h₂]
  exact regular_decomposition (k := k) (g x)

end ArExplicit.TriangularInduction

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularCategory
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

universe u

variable (k R F : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

theorem eToJCochain_eq_zero (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : Cochain (((eFunctor k R F).mapHomologicalComplex _).obj P)
      (((jFunctor k R F).mapHomologicalComplex _).obj Q) n) : x = 0 := by
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  exact hom_E_J_eq_zero (x.v i j hij).hom

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

omit [Module.Finite k F] in
theorem jCochain_totallyAcyclic [Module.Finite R F] [Module.Projective R F]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : TotallyAcyclicCochain P) :
    TotallyAcyclicCochain (jCochain (k := k) (F := F) P) where
  finite n := by
    let := hP.finite n
    let : Module.Finite k (P.X n) := Module.Finite.trans R (P.X n)
    exact Module.Finite.of_restrictScalars_finite k (Triangular R F) (TriangularJ k R F (P.X n))
  projective n := by
    let := hP.finite n
    let := hP.projective n
    exact jProjective
  exactAt n := by
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    have h := hP.exactAt n
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
    exact (LinearMap.exact_iff.mp (jMap_exact (k := k) (F := F) _ _
      (LinearMap.exact_iff.mpr h.symm))).symm
  dualExact n := jHomExact _ _ (hP.dualExact n)

end ArExplicit.TriangularInduction

end

end OAI
end


