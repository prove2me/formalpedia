-- Prove2me | Definitions.Def_OAIQ031A077
-- name    : OAIQ031A077
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:19:37.727375+00:00
-- url     : https://prove2.me/theorems/27ad2522-030d-494b-a3ab-150619e018a7
-- title:
--   Definitions bundle OAIQ031A077 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 10 definitions and 8 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.cochainHomotopyCokernelEquiv`, `OAI.ArExplicit.CompleteComparison.cochainHomotopyRawEquiv`, `OAI.ArExplicit.CompleteComparison.cochainOfChainCokernelEquiv`, `OAI.ArExplicit.CompleteComparison.fullHomStableEquiv`, `OAI.ArExplicit.CompleteComparison.stableCochainHomotopyIso`, `OAI.ArExplicit.CompleteComparison.stableHomotopyIso`, `OAI.ArExplicit.ConeQuotientMap.stableIsomorphism`, `OAI.ArExplicit.FiniteLeftModule.completeCochainCokernelEquiv`, `OAI.ArExplicit.FiniteLeftModule.resolutionCokernelMap`, `OAI.ArExplicit.StableIsomorphism.trans`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_CochainCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CochainCokernel.lean), [`AuslanderReiten_Cones_ConeQuotientMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeQuotientMap.lean), [`AuslanderReiten_Coordinates_CochainStableComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/CochainStableComparison.lean), [`AuslanderReiten_HomComplex_FullHomComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomComparison.lean), [`AuslanderReiten_HomComplex_FullHomProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomProducts.lean), [`AuslanderReiten_Modules_FiniteModuleTriangle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/FiniteModuleTriangle.lean), [`AuslanderReiten_Resolutions_FiniteCochainResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteCochainResolution.lean), [`AuslanderReiten_Stable_StableHomotopyIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableHomotopyIso.lean), [`AuslanderReiten_Stable_StableIsomorphism`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableIsomorphism.lean).
--
--   **Imports.** It imports the bundle `OAIQ031A061` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A091`, `OAIQ031A092`, `OAIQ031A093`, `OAIQ031A094`, `OAIQ031A096`, `OAIQ031A097`, `OAIQ031A098`, `OAIQ031A101` and `OAIQ031A104`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A061

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]

noncomputable def fullHomStableEquiv
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain (L⟦n⟧))) :
    CochainComplex.HomComplex.CohomologyClass K L n ≃+
      StableHom R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain (L⟦n⟧)) 0) :=
  CochainComplex.HomComplex.CohomologyClass.homAddEquiv.trans
    ((AddEquiv.ofBijective
      (Functor.mapAddHom (negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)))
      ⟨Functor.map_injective _, Functor.map_surjective _⟩).trans
        (homotopyCokernelEquiv hK hL))

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CochainCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory HomologicalComplex

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

variable {K}
variable {L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)

theorem cochainCokernelMap_surjective
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    Function.Surjective (fun f : K ⟶ L => cochainCokernelMap f) := by
  intro u
  let v := (cochainCokernelLinearEquiv L).symm.toLinearMap.comp
    (u.comp (cochainCokernelLinearEquiv K).toLinearMap)
  obtain ⟨F, hF⟩ := cokernelMap_surjective hK hL v
  obtain ⟨φ, rfl⟩ := Functor.map_surjective (negIndexEmbedding.extendFunctor (ModuleCat.{u} R)) F
  refine ⟨φ, ?_⟩
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun (cochainCokernelLinearEquiv_natural φ)
    ((cochainCokernelLinearEquiv K).symm x)
  change (cochainCokernelLinearEquiv L)
    (cokernelMap (extendMap φ negIndexEmbedding) 0 ((cochainCokernelLinearEquiv K).symm x)) =
    cochainCokernelMap φ ((cochainCokernelLinearEquiv K) ((cochainCokernelLinearEquiv K).symm x)) at h
  change cokernelMap (extendMap φ negIndexEmbedding) 0 = v at hF
  rw [hF] at h
  simpa [v] using h.symm

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableIsomorphism
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable (R M N : Type u) [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace StableIsomorphism

variable {R M N}
variable {P : Type u} [AddCommGroup P] [Module R P]

def trans (e : StableIsomorphism R M N) (f : StableIsomorphism R N P) :
    StableIsomorphism R M P where
  hom := StableHom.comp f.hom e.hom
  inv := StableHom.comp e.inv f.inv
  hom_inv_id := by
    rw [← StableHom.comp_assoc, StableHom.comp_assoc f.inv,
      f.hom_inv_id, StableHom.identity_comp, e.hom_inv_id]
  inv_hom_id := by
    rw [← StableHom.comp_assoc, StableHom.comp_assoc e.hom,
      e.inv_hom_id, StableHom.identity_comp, f.inv_hom_id]

end StableIsomorphism
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeQuotientMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.ConeQuotientMap

universe u

variable {R P₁ P₀ I Q₁ Q₀ L : Type u} [Ring R]
variable [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₀] [Module R P₀]
variable [AddCommGroup I] [Module R I] [AddCommGroup Q₁] [Module R Q₁]
variable [AddCommGroup Q₀] [Module R Q₀] [AddCommGroup L] [Module R L]

variable (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] I) (b : Q₁ →ₗ[R] Q₀) (f : P₀ →ₗ[R] Q₀)

variable (i : Source e →ₗ[R] Target b)
variable (p : Target b →ₗ[R] L)
variable (hf : (LinearMap.range b).mkQ.comp f = i.comp (LinearMap.range e).mkQ)
variable (hex : Function.Exact i p)

noncomputable def stableIsomorphism
    [Module.Finite R I] [Module.Projective R I] [Module.Injective R I]
    (hi : Function.Injective i) (hed : d.comp e = 0) (hp : Function.Surjective p) :
    StableIsomorphism R (Cone d b f) L :=
  StableIsomorphism.ofExactProjectiveKernel (kernelInclusion d b f)
    (quotientMap e d b f i p hf hex) (kernelInclusion_injective e d b f i hf hi hed)
    (quotientMap_surjective e d b f i p hf hex hp) (exact e d b f i p hf hex)

end ArExplicit.ConeQuotientMap

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHomotopyIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

noncomputable def stableHomotopyIso (hP : TotallyAcyclicComplex P)
    (hQ : TotallyAcyclicComplex Q) (e : StableIsomorphism R (Cokernel P 0) (Cokernel Q 0)) :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)).obj P ≅
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.down ℤ)).obj Q where
  hom := (homotopyCokernelEquiv hP hQ.toExactProjectiveComplex).symm e.hom
  inv := (homotopyCokernelEquiv hQ hP.toExactProjectiveComplex).symm e.inv
  hom_inv_id := by
    apply (homotopyCokernelEquiv hP hP.toExactProjectiveComplex).injective
    rw [homotopyCokernelEquiv_comp hP hQ hP.toExactProjectiveComplex,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, homotopyCokernelEquiv_id]
    exact e.hom_inv_id
  inv_hom_id := by
    apply (homotopyCokernelEquiv hQ hQ.toExactProjectiveComplex).injective
    rw [homotopyCokernelEquiv_comp hQ hP hQ.toExactProjectiveComplex,
      AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, homotopyCokernelEquiv_id]
    exact e.inv_hom_id

@[simp]
theorem stableHomotopyIso_hom (hP : TotallyAcyclicComplex P)
    (hQ : TotallyAcyclicComplex Q) (e : StableIsomorphism R (Cokernel P 0) (Cokernel Q 0)) :
    homotopyCokernelEquiv hP hQ.toExactProjectiveComplex (stableHomotopyIso hP hQ e).hom =
      e.hom := AddEquiv.apply_symm_apply _ _

noncomputable def stableCochainHomotopyIso
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : TotallyAcyclicComplex (chainOfCochain L))
    (e : StableIsomorphism R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) 0)) :
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K ≅
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L :=
  (negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)).preimageIso
    (stableHomotopyIso hK hL e)

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_CochainStableComparison
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory HomologicalComplex

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

noncomputable def cochainHomotopyCokernelEquiv
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L) ≃+
      StableHom R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) 0) :=
  (AddEquiv.ofBijective
    (Functor.mapAddHom (negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)))
    ⟨Functor.map_injective _, Functor.map_surjective _⟩).trans
      (homotopyCokernelEquiv hK hL)

@[simp]
theorem cochainHomotopyCokernelEquiv_map
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) (f : K ⟶ L) :
    cochainHomotopyCokernelEquiv hK hL ((HomotopyCategory.quotient _ _).map f) =
      StableHom.classOf R _ _ (cokernelMap (extendMap f negIndexEmbedding) 0) := by
  exact homotopyCokernelEquiv_map hK hL _

@[simp]
theorem stableCochainHomotopyIso_hom
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : TotallyAcyclicComplex (chainOfCochain L))
    (e : StableIsomorphism R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) 0)) :
    cochainHomotopyCokernelEquiv hK hL.toExactProjectiveComplex
      (stableCochainHomotopyIso hK hL e).hom = e.hom := by
  change homotopyCokernelEquiv hK hL.toExactProjectiveComplex
    ((negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)).map
      ((negIndexEmbedding.extendHomotopyFunctor (ModuleCat.{u} R)).preimageIso
        (stableHomotopyIso hK hL e)).hom) = _
  erw [Functor.preimageIso_hom, Functor.map_preimage, stableHomotopyIso_hom]

noncomputable def cochainHomotopyRawEquiv
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) :
    ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L) ≃+
      StableHom R (CochainCokernel K) (CochainCokernel L) :=
  (cochainHomotopyCokernelEquiv hK hL).trans
    (((StableIsomorphism.ofLinearEquiv (cochainCokernelLinearEquiv K).symm).sourceAddEquiv).trans
      (StableIsomorphism.ofLinearEquiv (cochainCokernelLinearEquiv L)).targetAddEquiv)

@[simp]
theorem cochainHomotopyRawEquiv_map
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L)) (f : K ⟶ L) :
    cochainHomotopyRawEquiv hK hL ((HomotopyCategory.quotient _ _).map f) =
      StableHom.classOf R _ _ (cochainCokernelMap f) := by
  simp only [cochainHomotopyRawEquiv, AddEquiv.trans_apply, cochainHomotopyCokernelEquiv_map,
    StableIsomorphism.sourceAddEquiv, StableIsomorphism.targetAddEquiv,
    StableIsomorphism.ofLinearEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    StableHom.comp_classOf]
  congr 1
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun (cochainCokernelLinearEquiv_natural f)
    ((cochainCokernelLinearEquiv K).symm x)
  simpa using h

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProducts
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n m : ℤ}

@[simp]
theorem fullHomStableEquiv_mk (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain (L⟦n⟧))) (x : Cocycle K L n) :
    fullHomStableEquiv K L n hK hL (CohomologyClass.mk x) =
      StableHom.classOf R _ _ (cokernelMap (cocycleComparisonMap x) 0) := by
  exact homotopyCokernelEquiv_map hK hL (cocycleComparisonMap x)

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteCochainResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace CompleteComparison

def cochainOfChainCokernelEquiv (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    CochainCokernel (cochainOfChain P) ≃ₗ[R] Cokernel P 0 :=
  LinearEquiv.refl R _

theorem cochainOfChain_totallyAcyclic (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hP : TotallyAcyclicComplex P) : TotallyAcyclicCochain (cochainOfChain P) where
  finite i := hP.finite (-i)
  projective i := hP.projective (-i)
  exactAt i := by
    rw [(cochainOfChain P).exactAt_iff' (i := i - 1) (j := i) (k := i + 1)
      (by simp) (by simp), ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hP.exactAt_of_indices (by change -(i - 1) = -i + 1; omega)
      (by change -(i + 1) = -i - 1; omega)
  dualExact i := by
    exact hP.dualExact_of_indices (by change -(i - 1) = -i + 1; omega)
      (by change -(i + 1) = -i - 1; omega)

end CompleteComparison

namespace FiniteLeftModule

open CompleteComparison

variable {k : Type u} [Field k] [Algebra k R] [Module.Finite k R]

theorem completeCochain_totallyAcyclic (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    TotallyAcyclicCochain (M.completeCochain τ) :=
  cochainOfChain_totallyAcyclic _ (M.completeComplex_totallyAcyclic τ)

noncomputable def completeCochainCokernelEquiv (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R) :
    CochainCokernel (M.completeCochain τ) ≃ₗ[R] M.carrier :=
  (cochainOfChainCokernelEquiv (M.completeComplex τ)).trans (M.completeCokernelEquiv τ)

end FiniteLeftModule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_FiniteModuleTriangle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit.FiniteLeftModule

open CompleteComparison

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {M N L : FiniteLeftModule k R}

def resolutionCokernelMap (f : M.carrier →ₗ[R] N.carrier) :
    CochainCokernel (M.completeCochain τ) →ₗ[R] CochainCokernel (N.completeCochain τ) :=
  (N.completeCochainCokernelEquiv τ).symm.toLinearMap.comp
    (f.comp (M.completeCochainCokernelEquiv τ).toLinearMap)

end ArExplicit.FiniteLeftModule

end

end OAI
end


