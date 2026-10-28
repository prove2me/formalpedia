-- Prove2me | Definitions.Def_OAIQ031A039
-- name    : OAIQ031A039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:01:09.235416+00:00
-- url     : https://prove2.me/theorems/ab280182-7dcc-4c9e-bf08-0e89b13d6484
-- title:
--   Definitions bundle OAIQ031A039 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 10 definitions, 3 instances and 7 theorems. The definitions and types are `OAI.ArExplicit.EnvelopingBimodule.prodRightEquiv`, `OAI.ArExplicit.ExternalTensor.tensorSemilinear`, `OAI.ArExplicit.ExternalTensor.tensorSemilinearEquiv`, `OAI.ArExplicit.Triangular.diagonalAlg`, `OAI.ArExplicit.Triangular.quotientMap`, `OAI.ArExplicit.VectorCochain.Diagonal`, `OAI.ArExplicit.VectorCochain.diagonalTermMap`, `OAI.ArExplicit.cokernelProductEquiv`, `OAI.ArExplicit.fullHomPostcompLinear`, `OAI.ArExplicit.rawSyzygyInclusion`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_CokernelProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/CokernelProduct.lean), [`AuslanderReiten_Cones_ConeConnectingCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeConnectingCoordinates.lean), [`AuslanderReiten_Ext_ExtKunnethMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtKunnethMap.lean), [`AuslanderReiten_HomComplex_FullHomCompositionLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomCompositionLinear.lean), [`AuslanderReiten_Homology_VectorCochainKunnethMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorCochainKunnethMap.lean), [`AuslanderReiten_Tensor_EnvelopingBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBimodule.lean), [`AuslanderReiten_Tensor_EnvelopingProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingProducts.lean), [`AuslanderReiten_Tensor_ExternalEnveloping`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalEnveloping.lean), [`AuslanderReiten_Tensor_ExternalTensorSemilinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorSemilinear.lean), [`AuslanderReiten_Triangular_TriangularRadical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularRadical.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A002`, `OAIQ031A005`, `OAIQ031A006`, `OAIQ031A013`, `OAIQ031A017` and `OAIQ031A018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A056` and `OAIQ031A057`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A002
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A006
import Definitions.Def_OAIQ031A013
import Definitions.Def_OAIQ031A017
import Definitions.Def_OAIQ031A018

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CokernelProduct
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

variable {R M N P Q : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

def cokernelProductEquiv (f : M →ₗ[R] N) (g : P →ₗ[R] Q) :
    ((N × Q) ⧸ LinearMap.range (f.prodMap g)) ≃ₗ[R]
      (N ⧸ LinearMap.range f) × (Q ⧸ LinearMap.range g) :=
  LinearEquiv.ofBijective (cokernelProductMap f g) (cokernelProductMap_bijective f g)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeConnectingCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable (H : CochainComplex (ModuleCat.{u} R) ℤ)

def rawSyzygyInclusion : RawSyzygy H →ₗ[R] H.X 0 :=
  (LinearMap.range (H.d (-2) (-1)).hom).liftQ (H.d (-1) 0).hom
    (LinearMap.range_le_ker_iff.mpr (congrArg ModuleCat.Hom.hom (H.d_comp_d (-2) (-1) 0)))

theorem rawSyzygyInclusion_cover :
    ((LinearMap.range (H.d (-1) 0).hom).mkQ).comp (rawSyzygyInclusion H) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (H.d (-2) (-1)).hom) z
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainKunnethMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.VectorCochain
universe u
variable (k : Type u) [Field k]
variable (P Q : CochainComplex (ModuleCat.{u} k) ℕ)

abbrev Diagonal (n : ℕ) := ExternalTensor.Diagonal n

variable {P Q} {P' Q' : CochainComplex (ModuleCat.{u} k) ℕ}

def diagonalTermMap (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ) :
    (∀ p : Diagonal n, P.X p.val.1 ⊗[k] Q.X p.val.2) →ₗ[k]
      (∀ p : Diagonal n, P'.X p.val.1 ⊗[k] Q'.X p.val.2) where
  toFun x p := TensorProduct.map (f.f p.val.1).hom (g.f p.val.2).hom (x p)
  map_add' x y := by funext p; exact map_add _ _ _
  map_smul' a x := by
    funext p
    exact (TensorProduct.map (f.f p.val.1).hom (g.f p.val.2).hom).map_smul a (x p)

theorem diagonalTermMap_single (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ)
    (p : Diagonal n) (x : P.X p.val.1 ⊗[k] Q.X p.val.2) :
    diagonalTermMap k f g n (Pi.single p x) =
      Pi.single p (TensorProduct.map (f.f p.val.1).hom (g.f p.val.2).hom x) := by
  classical
  funext r
  by_cases h : r=p
  · subst r
    simp only [diagonalTermMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same]
  · simp only [diagonalTermMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_of_ne h,
      map_zero]

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtKunnethMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k : Type u) [Field k]

theorem tensor_conjugate {E F G H : Type u}
    [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
    [Module k E] [Module k F] [Module k G] [Module k H]
    (e : E ≃ₗ[k] F) (d : G ≃ₗ[k] H) (f : E →ₗ[k] E) (g : G →ₗ[k] G)
    (x : E ⊗[k] G) :
    TensorProduct.map e.toLinearMap d.toLinearMap (TensorProduct.map f g x) =
      TensorProduct.map (e.toLinearMap.comp (f.comp e.symm.toLinearMap))
        (d.toLinearMap.comp (g.comp d.symm.toLinearMap))
        (TensorProduct.map e.toLinearMap d.toLinearMap x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y => simp only [TensorProduct.map_tmul, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomCompositionLinear
attribute [-instance] _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} (n : ℤ)

def fullHomPostcompLinear (f : L ⟶ M) : CohomologyClass K L n →ₗ[k] CohomologyClass K M n where
  __ := fullHomPostcomp f n
  map_smul' a x := by
    change fullHomPostcomp f n (a • x) = a • fullHomPostcomp f n x
    obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
    rw [← CompleteComparison.fullHom_mk_smul, fullHomPostcomp_mk, fullHomPostcomp_mk,
      ← CompleteComparison.fullHom_mk_smul]
    congr 1
    apply Subtype.ext
    exact Cochain.smul_comp a x.val (Cochain.ofHom f) (add_zero n)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBimodule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open scoped TensorProduct

universe u

namespace EnvelopingBimodule

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))

variable [Module k M]

variable [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]

instance instSMulCommClassMulOpposite_1 : SMulCommClass k Rᵐᵒᵖ (EnvelopingBimodule k R M) where
  smul_comm a r x := by
    simp only [← IsScalarTower.algebraMap_smul Rᵐᵒᵖ a, ← mul_smul, Algebra.commutes]

end EnvelopingBimodule
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingProducts
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.EnvelopingBimodule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M N : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))

def prodRightEquiv : EnvelopingBimodule k R (ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (M × N)) ≃ₗ[Rᵐᵒᵖ]
    EnvelopingBimodule k R M × EnvelopingBimodule k R N where
  toFun x := (⟨x.value.1⟩, ⟨x.value.2⟩)
  invFun x := ⟨(x.1.value, x.2.value)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem prod_right_projective
    [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M)]
    [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R N)] :
    Module.Projective Rᵐᵒᵖ
      (EnvelopingBimodule k R (ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (M × N))) :=
  Module.Projective.of_equiv (prodRightEquiv M N).symm

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalEnveloping
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

instance forwardInverse : RingHomInvPair (envelopingEquiv k A B).toRingHom
    (envelopingEquiv k A B).symm.toRingHom where
  comp_eq := by apply RingHom.ext; intro x; exact (envelopingEquiv k A B).symm_apply_apply x
  comp_eq₂ := by apply RingHom.ext; intro x; exact (envelopingEquiv k A B).apply_symm_apply x

instance backwardInverse : RingHomInvPair (envelopingEquiv k A B).symm.toRingHom
    (envelopingEquiv k A B).toRingHom where
  comp_eq := by apply RingHom.ext; intro x; exact (envelopingEquiv k A B).apply_symm_apply x
  comp_eq₂ := by apply RingHom.ext; intro x; exact (envelopingEquiv k A B).symm_apply_apply x

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorSemilinear
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable {M N M' N' : Type u}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
variable [Module k M] [Module k N] [Module k M'] [Module k N']
variable [Module A M] [Module B N] [Module A M'] [Module B N']
variable [IsScalarTower k A M] [IsScalarTower k B N]
variable [IsScalarTower k A M'] [IsScalarTower k B N']
variable (h : A ≃ₐ[k] A) (j : B ≃ₐ[k] B)
variable (e : M →ₗ[k] M') (f : N →ₗ[k] N')
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ b n, f (b • n) = j b • f n)

include he hf in
theorem tensorSemilinear_smul (r : A ⊗[k] B) (x : moduleObject k A B M N) :
    TensorProduct.map e f (r • x) =
      (Algebra.TensorProduct.map h.toAlgHom j.toAlgHom r) •
        (show moduleObject k A B M' N' from TensorProduct.map e f x) := by
  let w : M ⊗[k] N := x
  change TensorProduct.map e f (representation k A B M N r w) =
    representation k A B M' N' (Algebra.TensorProduct.map h.toAlgHom j.toAlgHom r)
      (TensorProduct.map e f w)
  induction r using OAI.tensorInductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a b =>
    induction w using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul m n =>
      change e (a • m) ⊗ₜ[k] f (b • n) = (h a • e m) ⊗ₜ[k] (j b • f n)
      rw [he, hf]

def tensorSemilinear : moduleObject k A B M N →ₗ[A ⊗[k] B]
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.map h.toAlgHom j.toAlgHom).toRingHom).obj
        (moduleObject k A B M' N') where
  toAddHom := (TensorProduct.map e f).toAddHom
  map_smul' := tensorSemilinear_smul k A B h j e f he hf

@[simp] theorem tensorSemilinear_tmul (m : M) (n : N) :
    tensorSemilinear k A B h j e f he hf (m ⊗ₜ[k] n) = e m ⊗ₜ[k] f n := rfl

def tensorSemilinearEquiv (e : M ≃ₗ[k] M') (f : N ≃ₗ[k] N')
    (he : ∀ a m, e (a • m) = h a • e m)
    (hf : ∀ b n, f (b • n) = j b • f n) :
    moduleObject k A B M N ≃ₗ[A ⊗[k] B]
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.map h.toAlgHom j.toAlgHom).toRingHom).obj
          (moduleObject k A B M' N') :=
  LinearEquiv.ofBijective (tensorSemilinear k A B h j e.toLinearMap f.toLinearMap he hf)
    (TensorProduct.congr e f).bijective

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularRadical
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Triangular

variable {R F : Type*} [Ring R] [AddCommGroup F]
variable [Module R F] [Module Rᵐᵒᵖ F] [SMulCommClass R Rᵐᵒᵖ F]

section Scalars

variable (k : Type*) [CommRing k] [Algebra k R] [Module k F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass k Rᵐᵒᵖ F]

def diagonalAlg : Triangular R F →ₐ[k] R × R where
  __ := diagonal
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rfl

variable {S : Type*} [Ring S] [Algebra k S]

def quotientMap (f : R →ₐ[k] S) : Triangular R F →ₐ[k] S × S :=
  (f.prodMap f).comp (diagonalAlg k)

theorem quotientMap_surjective (f : R →ₐ[k] S) (hf : Function.Surjective f) :
    Function.Surjective (quotientMap (F := F) k f) := by
  rintro ⟨s, t⟩
  obtain ⟨r, hr⟩ := hf s
  obtain ⟨r', hr'⟩ := hf t
  exact ⟨⟨r, r', 0⟩, Prod.ext hr hr'⟩

end Scalars
end ArExplicit.Triangular

end OAI
end


