-- Prove2me | Definitions.Def_OAIQ031A108
-- name    : OAIQ031A108
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:42:41.827275+00:00
-- url     : https://prove2.me/theorems/97d2389a-3f7c-4b1a-8803-1fc31f7681d6
-- title:
--   Definitions bundle OAIQ031A108 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 6 declarations of OpenAI's Lean: 1 definition and 5 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.homKunnethEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Ext_ExtTensorAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtTensorAction.lean), [`AuslanderReiten_HomComplex_HomKunnethClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomKunnethClass.lean), [`AuslanderReiten_Tensor_ExternalTensorCubicExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubicExt.lean), [`AuslanderReiten_Tensor_ExternalTensorCubicProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorCubicProducts.lean), [`AuslanderReiten_Tensor_ExternalTensorHomCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHomCubic.lean), [`AuslanderReiten_Tensor_ExternalTensorHomKunneth`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHomKunneth.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A068`, `OAIQ031A094` and `OAIQ031A095` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A123`, `OAIQ031A130` and `OAIQ031A131`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A068
import Definitions.Def_OAIQ031A094
import Definitions.Def_OAIQ031A095

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomKunneth
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

def homKunnethEquiv (n : ℕ) :
    (homCochain k (A ⊗[k] B) (complex k A B P Q) (moduleObject k A B U V)).homology n ≃ₗ[k]
      (Π₀ p : Diagonal n,
        ((homCochain k A P U).homology p.val.1 ⊗[k] (homCochain k B Q V).homology p.val.2)) :=
  (((homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).mapIso
    (homCochainTotalIso k A B P Q U V)).symm.toLinearEquiv).trans
      (VectorCochain.kunnethLinearEquiv k (MonoidalCategory.curriedTensor (ModuleCat.{u} k))
        (homCochain k A P U) (homCochain k B Q V) n)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomKunnethClass
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]
variable (i j n : ℕ) (h : i+j=n)
variable (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
variable (hf : f.comp (P.d (i+1) i).hom=0) (hg : g.comp (Q.d (j+1) j).hom=0)
include hf hg

theorem homKunnethEquiv_elementary
    (xf : LinearMap.ker ((homCochain k A P U).d i (i+1)).hom)
    (xg : LinearMap.ker ((homCochain k B Q V).d j (j+1)).hom)
    (hx : xf.val=f) (hy : xg.val=g)
    (z : LinearMap.ker ((homCochain k (A ⊗[k] B) (complex k A B P Q)
      (moduleObject k A B U V)).d n (n+1)).hom)
    (hz : z.val=elementaryHom k A B P Q U V i j n h f g) :
    homKunnethEquiv k A B P Q U V n
      (VectorCochain.literalClass k _ n z) =
      (DFinsupp.single ⟨(i,j),h⟩
        (VectorCochain.literalClass k (homCochain k A P U) i xf ⊗ₜ[k]
          VectorCochain.literalClass k (homCochain k B Q V) j xg) :
        Π₀ p : Diagonal n, (homCochain k A P U).homology p.val.1 ⊗[k]
          (homCochain k B Q V).homology p.val.2) := by
  let w : LinearMap.ker ((homCochainTotal k A B P Q U V).d n (n+1)).hom :=
    ⟨(homCochainInclusion k A B P Q U V i j n h).hom (f ⊗ₜ[k] g),
      elementary_total_closed k A B P Q U V i j n h f g hf hg⟩
  let e := (homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).mapIso
    (homCochainTotalIso k A B P Q U V)
  have hmap := VectorCochain.literalClass_map k (homCochainTotalIso k A B P Q U V).hom n w z
    (by exact hz.symm)
  have hcancel : e.inv.hom (VectorCochain.literalClass k _ n z) =
      VectorCochain.literalClass k _ n w := by
    rw [← hmap]
    exact e.toLinearEquiv.symm_apply_apply _
  change VectorCochain.kunnethLinearEquiv k (MonoidalCategory.curriedTensor (ModuleCat.{u} k))
    (homCochain k A P U) (homCochain k B Q V) n
      (e.inv.hom (VectorCochain.literalClass k _ n z)) = _
  rw [hcancel]
  apply VectorCochain.kunnethLinearEquiv_literal_tmul k _ _ i j n h xf xg w
  change (homCochainInclusion k A B P Q U V i j n h).hom (f ⊗ₜ[k] g) =
    (homCochainInclusion k A B P Q U V i j n h).hom (xf.val ⊗ₜ[k] xg.val)
  rw [hx, hy]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

theorem elementary_firstCubic
    (p : ∀ n, P.X (n+3) ⟶ P.X n)
    (i j n : ℕ) (h : i+j=n) (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (elementaryHom k A B P Q U V i j n h f g).comp (firstCubic k A B P Q p n) =
      elementaryHom k A B P Q U V (i+3) j (n+3) (by omega) (f.comp (p i).hom) g := by
  apply cubic_hom_ext k A B P Q (n+3)
  rintro ⟨⟨a,b⟩,hab⟩ x
  simp only [LinearMap.comp_apply, firstCubic_insert]
  rcases a with _ | (_ | (_ | a))
  · simp only [firstCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V (i+3) j (n+3) (by omega)
      (f.comp (p i).hom) g 0 b hab (by intro he; have := congrArg Prod.fst he; omega) x).symm
  · simp only [firstCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V (i+3) j (n+3) (by omega)
      (f.comp (p i).hom) g 1 b hab (by intro he; have := congrArg Prod.fst he; omega) x).symm
  · simp only [firstCubicEntry, LinearMap.zero_apply, map_zero]
    exact (elementary_cubicInsert_ne k A B P Q U V (i+3) j (n+3) (by omega)
      (f.comp (p i).hom) g 2 b hab (by intro he; have := congrArg Prod.fst he; omega) x).symm
  · by_cases ha : a=i
    · subst a
      have hb : b=j := by omega
      subst b
      simp only [firstCubicEntry, LinearMap.comp_apply, elementary_cubicInsert_same]
      exact map_first_comp k A B U V f g (p i).hom x
    · have hn : (a,b)≠(i,j) := by intro he; exact ha (congrArg Prod.fst he)
      have hn' : (a+3,b)≠(i+3,j) := by intro he; have := congrArg Prod.fst he; omega
      simp only [firstCubicEntry, LinearMap.comp_apply]
      rw [elementary_cubicInsert_ne k A B P Q U V i j n h f g a b (by omega) hn,
        elementary_cubicInsert_ne k A B P Q U V (i+3) j (n+3) (by omega)
          (f.comp (p i).hom) g (a+3) b hab hn']

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)

variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

omit [Module.Finite k A] [Module.Finite k B] in
theorem firstCubicExt_action {N : ModuleCat.{u} (A ⊗[k] B)} {n : ℕ}
    (f : (projectiveResolution k A B P Q).complex.X n ⟶ N)
    (hf : (projectiveResolution k A B P Q).complex.d (n+1) n ≫ f=0) :
    (firstCubicExt k A B P Q p hp).comp ((projectiveResolution k A B P Q).extMk f (n+1) rfl hf)
      (by omega : 3+n=n+3) =
      (projectiveResolution k A B P Q).extMk (firstComparison k A B P Q p n ≫ f) (n+4) rfl
        (ResolutionProducts.cubicPrecomp_closed (projectiveResolution k A B P Q)
          (firstComparison k A B P Q p) (firstComparison_comm k A B P Q p hp) f hf) :=
  ResolutionProducts.cubic_endExt_comp_extMk (k := k) (projectiveResolution k A B P Q)
    (firstComparison k A B P Q p) (firstComparison_comm k A B P Q p hp) f hf

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtTensorAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)

omit [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)] in
theorem firstCubicExt_elementary (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    (firstCubicExt k A B P Q p hp).comp
      (elementaryExt k A B P Q U V i j n h f g hf hg) (by omega : 3+n=n+3) =
      elementaryExt k A B P Q U V (i+3) j (n+3) (by omega) (f.comp (p i).hom) g
        (firstFactor_closed A P U p hp i f hf) hg := by
  unfold elementaryExt
  erw [firstCubicExt_action]
  have he : firstComparison k A B P Q p n ≫
      ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X n)
        (Y := moduleObject k A B U V) (elementaryHom k A B P.complex Q.complex U V i j n h f g) =
      ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X (n+3))
        (Y := moduleObject k A B U V)
        (elementaryHom k A B P.complex Q.complex U V (i+3) j (n+3) (by omega) (f.comp (p i).hom) g) :=
    ModuleCat.hom_ext (elementary_firstCubic k A B P.complex Q.complex U V p i j n h f g)
  exact extMk_of_eq (projectiveResolution k A B P Q) _ _ _ _ he

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorCubicProducts
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (p : ∀ n, P.complex.X (n+3) ⟶ P.complex.X n)
variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)
variable (hp : ∀ n, p (n+1) ≫ P.complex.d (n+1) n = P.complex.d (n+4) (n+3) ≫ p n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

theorem cubicExt_commute :
    (firstCubicExt k A B P Q p hp).comp (secondCubicExt k A B P Q r hr) rfl =
      (secondCubicExt k A B P Q r hr).comp (firstCubicExt k A B P Q p hp) rfl := by
  apply ResolutionProducts.cubic_endExt_commute (k := k)
    (projectiveResolution k A B P Q)
    (firstComparison k A B P Q p) (secondComparison k A B P Q r)
    (firstComparison_comm k A B P Q p hp) (secondComparison_comm k A B P Q r hr)
  apply ModuleCat.hom_ext
  exact (cubic_commute k A B P.complex Q.complex p r 0).symm

end ArExplicit.ExternalTensor

end

end OAI
end


