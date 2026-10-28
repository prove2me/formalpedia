-- Prove2me | Definitions.Def_OAIQ031A104
-- name    : OAIQ031A104
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:40:31.415725+00:00
-- url     : https://prove2.me/theorems/ab65c1a4-8246-4f0c-b485-fbd159ae396b
-- title:
--   Definitions bundle OAIQ031A104 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 2 definitions and 4 theorems. The definitions and types are `OAI.ArExplicit.TriangularInduction.ePi`, `OAI.ArExplicit.TriangularInduction.jPi`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_MappingConeTotal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/MappingConeTotal.lean), [`AuslanderReiten_Triangular_TriangularDualExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularDualExact.lean), [`AuslanderReiten_Triangular_TriangularExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularExact.lean), [`AuslanderReiten_Triangular_TriangularFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularFunctor.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A043`, `OAIQ031A077`, `OAIQ031A078`, `OAIQ031A082` and `OAIQ031A089` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A117`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A043
import Definitions.Def_OAIQ031A077
import Definitions.Def_OAIQ031A078
import Definitions.Def_OAIQ031A082
import Definitions.Def_OAIQ031A089

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeTotal
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex CompleteComparison
open CochainComplex CochainComplex.HomComplex

universe u

variable {R : Type u} [Ring R]
variable {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)

theorem mappingCone_cokernel_gorenstein
    (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G) :
    GorensteinProjective R (Cokernel (chainOfCochain (mappingCone φ)) 0) :=
  gorensteinProjective_of_totallyAcyclic _ _ (mappingCone_totallyAcyclic φ hF hG).to_chain
    (LinearEquiv.refl R _)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularFunctor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularEFunctor _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {M N L : Type*}
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def ePi : TriangularE k R F (ι → M) ≃ₗ[Triangular R F] (ι → TriangularE k R F M) where
  toFun x i := ⟨x.top i, BalancedTensor.piRight (S := R) x.bottom i⟩
  invFun y := ⟨fun i => (y i).top, (BalancedTensor.piRight (S := R)).symm (fun i => (y i).bottom)⟩
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_smul' a x := by
    ext i
    · rfl
    · change BalancedTensor.piRight (S := R)
          (BalancedTensor.tmul a.off x.top + a.bottom • x.bottom) i =
        BalancedTensor.tmul a.off (x.top i) + a.bottom • BalancedTensor.piRight (S := R) x.bottom i
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply]
      rfl

def jPi : TriangularJ k R F (ι → M) ≃ₗ[Triangular R F] (ι → TriangularJ k R F M) where
  toFun x i := ⟨0, x.bottom i⟩
  invFun y := ⟨0, fun i => (y i).bottom⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' a x := by ext; simp

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularDualExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularEFunctor _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

omit [Module k K] [IsScalarTower k R K] [Module k L] [IsScalarTower k R L]
  [Module k M] [IsScalarTower k R M] in
theorem jHomLift (e : K →ₗ[R] L) (d : L →ₗ[R] M) (h : HomExactAt e d)
    [Module.Finite R V] [Module.Projective R V]
    {ψ : BalancedTensor k R F U →ₗ[R] V}
    (g : TriangularJ k R F L →ₗ[Triangular R F] TriangularModule k R F U V ψ)
    (hg : g.comp (jMap e) = 0) :
    ∃ G : TriangularJ k R F M →ₗ[Triangular R F] TriangularModule k R F U V ψ,
      G.comp (jMap d) = g := by
  have ha : (TriangularModule.bottomMap g).comp e = 0 := by
    ext x
    exact congrArg TriangularModule.bottom (DFunLike.congr_fun hg ⟨0, x⟩)
  obtain ⟨b, hb⟩ := h.projective (TriangularModule.bottomMap g) ha
  refine ⟨jHom b, ?_⟩
  apply jHomEquiv.injective
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hb x

end ArExplicit.TriangularInduction

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TriangularInduction.instAdditiveModuleCatTriangularEFunctor _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {M N L : Type*}
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M] [SMulCommClass k R M]
variable [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N] [SMulCommClass k R N]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L] [SMulCommClass k R L]

omit [IsScalarTower k R F] [SMulCommClass k Rᵐᵒᵖ F] [SMulCommClass k R M] in
theorem eMap_exact [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
    (e : M →ₗ[R] N) (d : N →ₗ[R] L) (hex : Function.Exact e d) :
    Function.Exact (eMap (k := k) (F := F) e) (eMap d) := by
  have ht := BalancedTensor.mapRight_exact (k := k) (F := F) (S := R) e d hex
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := (hex z.top).mp (congrArg TriangularModule.top hz)
    obtain ⟨y, hy⟩ := (ht z.bottom).mp (congrArg TriangularModule.bottom hz)
    exact ⟨⟨x, y⟩, TriangularModule.ext hx hy⟩
  · rintro ⟨w, rfl⟩
    apply TriangularModule.ext
    · exact (hex (e w.top)).mpr ⟨w.top, rfl⟩
    · exact (ht (BalancedTensor.mapRight (S := R) e w.bottom)).mpr ⟨w.bottom, rfl⟩

omit [Algebra k R] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
  [SMulCommClass k Rᵐᵒᵖ F] [Module k M] [IsScalarTower k R M] [SMulCommClass k R M]
  [Module k N] [IsScalarTower k R N] [SMulCommClass k R N]
  [Module k L] [IsScalarTower k R L] [SMulCommClass k R L] in
theorem jMap_exact (e : M →ₗ[R] N) (d : N →ₗ[R] L) (hex : Function.Exact e d) :
    Function.Exact (jMap (k := k) (F := F) e) (jMap d) := by
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := (hex z.bottom).mp (congrArg TriangularModule.bottom hz)
    exact ⟨⟨0, x⟩, TriangularModule.ext (Subsingleton.elim _ _) hx⟩
  · rintro ⟨w, rfl⟩
    exact TriangularModule.ext (Subsingleton.elim _ _) ((hex (e w.bottom)).mpr ⟨w.bottom, rfl⟩)

end ArExplicit.TriangularInduction

end OAI
end


