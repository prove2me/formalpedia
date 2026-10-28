-- Prove2me | Definitions.Def_OAIQ031A140
-- name    : OAIQ031A140
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:16:41.955139+00:00
-- url     : https://prove2.me/theorems/30942bfa-3ad8-4dc8-95db-96dac2c43709
-- title:
--   Definitions bundle OAIQ031A140 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 5 definitions and 4 theorems. The definitions and types are `OAI.ArExplicit.FullPositive.atDegree`, `OAI.ArExplicit.FullPositive.model`, `OAI.ArExplicit.FullPositive.modelOfComposite`, `OAI.ArExplicit.FullPositive.positive`, `OAI.ArExplicit.TwoCone.skeletonCokernelInclusion`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_TwoConeSkeleton`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeSkeleton.lean), [`AuslanderReiten_Ext_ExtKunnethClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtKunnethClass.lean), [`AuslanderReiten_HomComplex_HomCochainNativeClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainNativeClass.lean), [`AuslanderReiten_Homology_FullPositiveComposite`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/FullPositiveComposite.lean), [`AuslanderReiten_Homology_FullPositiveModel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/FullPositiveModel.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A129`, `OAIQ031A130`, `OAIQ031A134` and `OAIQ031A135` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A146` and `OAIQ031A149`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A129
import Definitions.Def_OAIQ031A130
import Definitions.Def_OAIQ031A134
import Definitions.Def_OAIQ031A135

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeSkeleton
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

def skeletonCokernelInclusion (n : ℕ) : SkeletonCokernel D n →ₗ[R] Cokernel D n :=
  (skeletonCokernelCoordinates D n).symm.toLinearMap.comp
    (ConeCokernel.inclusion (skeletonD D n) (-(D.d (n + 4))) (topAttaching D n))

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainNativeClass
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (Y : Type u) [AddCommGroup Y] [Module R Y] [Module k Y] [IsScalarTower k R Y]

theorem homCochainNativeExtEquiv_literal (n : ℕ)
    (f : P.complex.X n →ₗ[R] Y) (hf : f.comp (P.complex.d (n+1) n).hom=0) :
    homCochainNativeExtEquiv k R P Y n
      (VectorCochain.literalClass k (homCochain k R P.complex Y) n ⟨f,homCochain_mem_cycles k R P Y n f hf⟩) =
      P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := ModuleCat.of R Y) f)
        (n+1) rfl (ModuleCat.hom_ext hf) := by
  let C := canonicalHomCochain k R P.complex (ModuleCat.of R Y)
  let z : LinearMap.ker (C.d n (n+1)).hom := ⟨f,by
    change (C.d n (n+1)).hom f=0
    dsimp only [C, canonicalHomCochain]
    rw [homCochain_d]
    exact hf⟩
  have hz := VectorCochain.literalClass_map k (homCochainScalarIso k R P.complex Y).hom n
    (⟨f,homCochain_mem_cycles k R P Y n f hf⟩ : LinearMap.ker ((homCochain k R P.complex Y).d n (n+1)).hom) z rfl
  change homCochainExtEquiv k R (Y := ModuleCat.of R Y) P n
    ((homologyMap (homCochainScalarIso k R P.complex Y).hom n).hom
      (VectorCochain.literalClass k (homCochain k R P.complex Y) n ⟨f,homCochain_mem_cycles k R P Y n f hf⟩)) = _
  rw [hz]
  have he := homCochainExtEquiv_cycleClass k R (Y := ModuleCat.of R Y) P n z
  erw [homCochainCycleClass_eq_literal] at he
  exact he

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtKunnethClass
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable (i j n : ℕ) (h : i+j=n)
variable (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
variable (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0)

include hf hg in

theorem extKunnethEquiv_elementary :
    extKunnethEquiv k A B P Q U V n
      ((projectiveResolution k A B P Q).extMk
        (ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X n)
          (Y := moduleObject k A B U V)
          (elementaryHom k A B P.complex Q.complex U V i j n h f g)) (n+1) rfl
        (ModuleCat.hom_ext (elementary_closed k A B P.complex Q.complex U V i j n h f g hf hg))) =
      (Pi.single ⟨(i,j),h⟩
        (P.extMk (ModuleCat.ofHom f) (i+1) rfl (ModuleCat.hom_ext hf) ⊗ₜ[k]
          Q.extMk (ModuleCat.ofHom g) (j+1) rfl (ModuleCat.hom_ext hg)) :
          ∀ p : Diagonal n, Ext X U p.val.1 ⊗[k] Ext Y V p.val.2) := by
  let e := elementaryHom k A B P.complex Q.complex U V i j n h f g
  have he := elementary_closed k A B P.complex Q.complex U V i j n h f g hf hg
  let z := (⟨e,homCochain_mem_cycles k (A ⊗[k] B) (projectiveResolution k A B P Q)
    (moduleObject k A B U V) n e he⟩ :
    LinearMap.ker ((homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex)
      (moduleObject k A B U V)).d n (n+1)).hom)
  let xf := (⟨f,homCochain_mem_cycles k A P U i f hf⟩ :
    LinearMap.ker ((homCochain k A P.complex U).d i (i+1)).hom)
  let xg := (⟨g,homCochain_mem_cycles k B Q V j g hg⟩ :
    LinearMap.ker ((homCochain k B Q.complex V).d j (j+1)).hom)
  have hext := homCochainNativeExtEquiv_literal k (A ⊗[k] B)
    (projectiveResolution k A B P Q) (moduleObject k A B U V) n e he
  change extKunnethEquiv k A B P Q U V n
    ((projectiveResolution k A B P Q).extMk
      (ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X n)
        (Y := moduleObject k A B U V) e) (n+1) rfl (ModuleCat.hom_ext he)) = _
  refine (congrArg (extKunnethEquiv k A B P Q U V n) hext.symm).trans ?_
  unfold extKunnethEquiv
  erw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  have hk := homKunnethEquiv_elementary k A B P.complex Q.complex U V i j n h f g hf hg
    xf xg rfl rfl z rfl
  erw [hk]
  funext a
  by_cases ha : a=⟨(i,j),h⟩
  · subst a
    simp only [DFinsupp.linearEquivFunOnFintype_apply, DFinsupp.single_eq_same,
      LinearEquiv.piCongrRight_apply, Pi.single_eq_same, TensorProduct.congr_tmul]
    rw [homCochainExtEquiv_literal k A P U i f hf, homCochainExtEquiv_literal k B Q V j g hg]
  · simp only [DFinsupp.linearEquivFunOnFintype_apply, DFinsupp.single_eq_of_ne ha,
      LinearEquiv.piCongrRight_apply, Pi.single_eq_of_ne ha, map_zero]

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_FullPositiveModel
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.FullPositive
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (X : ModuleCat.{u} R)
open CompleteComparison TateKoszul
local notation "H" => CohomologyClass K K

def atDegree (D : NonnegativeChart (k := k) K X) (a : ℤ) (n : ℕ) (ha : a=(n:ℤ)) : H a ≃ₗ[k] Ext X X n :=
  (degreeEquiv (k := k) H ha).trans (D.equiv n)

theorem atDegree_product (D : NonnegativeChart (k := k) K X) (a b : ℤ) (n m r : ℕ)
    (ha : a=(n:ℤ)) (hb : b=(m:ℤ)) (hr : n+m=r)
    (x : H a) (y : H b) :
    atDegree K X D (a+b) r (by omega) (fullHomProduct x y) =
      (atDegree K X D a n ha x).comp (atDegree K X D b m hb y) hr := by
  subst r
  subst a
  subst b
  exact D.product n m x y

def positive (D : NonnegativeChart (k := k) K X)
    (f : ∀ n : ℕ, Ext X X (3*n) ≃ₗ[k] BinaryKoszul.Piece k n) (n : ℕ) : H (3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n :=
  (atDegree K X D (3*(n:ℤ)) (3*n) (by omega)).trans (f n)

theorem positive_transport (D : NonnegativeChart (k := k) K X)
    (f : ∀ n : ℕ, Ext X X (3*n) ≃ₗ[k] BinaryKoszul.Piece k n) (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a) :
    positive K X D f n (degreeEquiv (k := k) H ha v) =
      f n (atDegree K X D a (3*n) (by omega) v) := by
  subst a
  rfl

def model (D : NonnegativeChart (k := k) K X)
    (f : ∀ n : ℕ, Ext X X (3*n) ≃ₗ[k] BinaryKoszul.Piece k n)
    (p q : Ext X X 3)
    (off : ∀ (n : ℕ), (¬ 3 ∣ n) → ∀ x : Ext X X n, x=0)
    (lx : ∀ n (x : Ext X X (3*n)),
      f (n+1) (p.comp x (by omega : 3+3*n=3*(n+1))) = BinaryKoszul.mulX k n (f n x))
    (ly : ∀ n (x : Ext X X (3*n)),
      f (n+1) (q.comp x (by omega : 3+3*n=3*(n+1))) = BinaryKoszul.mulY k n (f n x))
    (rx : ∀ n (x : Ext X X (3*n)),
      f (n+1) (x.comp p (by omega : 3*n+3=3*(n+1))) = BinaryKoszul.mulX k n (f n x))
    (ry : ∀ n (x : Ext X X (3*n)),
      f (n+1) (x.comp q (by omega : 3*n+3=3*(n+1))) = BinaryKoszul.mulY k n (f n x)) :
    FullTate.PositiveModel (k := k) K ((D.equiv 3).symm p) ((D.equiv 3).symm q) where
  positive := positive K X D f
  outside a ha hn := by
    obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le ha
    have hd : ¬ 3 ∣ n := by
      rintro ⟨m,hm⟩
      exact hn m (by omega)
    exact ⟨fun x y => (D.equiv n).injective ((off n hd _).trans (off n hd _).symm)⟩
  right_x a n ha v := by
    change positive K X D f (n+1) (degreeEquiv (k := k) H _ (fullHomProduct v ((D.equiv 3).symm p))) = _
    erw [positive_transport, atDegree_product K X D a 3 (3*n) 3 (3*(n+1)) (by omega) rfl (by omega)]
    change f (n+1) ((atDegree K X D a (3*n) (by omega) v).comp (D.equiv 3 ((D.equiv 3).symm p)) _) = _
    rw [LinearEquiv.apply_symm_apply, rx, positive_transport]
  right_y a n ha v := by
    change positive K X D f (n+1) (degreeEquiv (k := k) H _ (fullHomProduct v ((D.equiv 3).symm q))) = _
    erw [positive_transport, atDegree_product K X D a 3 (3*n) 3 (3*(n+1)) (by omega) rfl (by omega)]
    change f (n+1) ((atDegree K X D a (3*n) (by omega) v).comp (D.equiv 3 ((D.equiv 3).symm q)) _) = _
    rw [LinearEquiv.apply_symm_apply, ry, positive_transport]
  left_x a n ha v := by
    change positive K X D f (n+1) (degreeEquiv (k := k) H _ (fullHomProduct ((D.equiv 3).symm p) v)) = _
    erw [positive_transport, atDegree_product K X D 3 a 3 (3*n) (3*(n+1)) rfl (by omega) (by omega)]
    change f (n+1) ((D.equiv 3 ((D.equiv 3).symm p)).comp (atDegree K X D a (3*n) (by omega) v) _) = _
    rw [LinearEquiv.apply_symm_apply, lx, positive_transport]
  left_y a n ha v := by
    change positive K X D f (n+1) (degreeEquiv (k := k) H _ (fullHomProduct ((D.equiv 3).symm q) v)) = _
    erw [positive_transport, atDegree_product K X D 3 a 3 (3*n) (3*(n+1)) rfl (by omega) (by omega)]
    change f (n+1) ((D.equiv 3 ((D.equiv 3).symm q)).comp (atDegree K X D a (3*n) (by omega) v) _) = _
    rw [LinearEquiv.apply_symm_apply, ly, positive_transport]

end ArExplicit.FullPositive

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_FullPositiveComposite
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FullPositive
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (X : ModuleCat.{u} R)
variable {C : ℕ → Type u} [∀ n, AddCommGroup (C n)] [∀ n, Module k (C n)]

def modelOfComposite (D : NonnegativeChart (k := k) K X)
    (e : ∀ n, Ext X X n ≃ₗ[k] C n)
    (f : ∀ n, C (3*n) ≃ₗ[k] BinaryKoszul.Piece k n)
    (p q : Ext X X 3)
    (off : ∀ n, (¬ 3 ∣ n) → ∀ x : Ext X X n, x=0)
    (lx : ∀ n (x : Ext X X (3*n)),
      f (n+1) (e (3*n+3) (p.comp x (by omega))) = BinaryKoszul.mulX k n (f n (e (3*n) x)))
    (ly : ∀ n (x : Ext X X (3*n)),
      f (n+1) (e (3*n+3) (q.comp x (by omega))) = BinaryKoszul.mulY k n (f n (e (3*n) x)))
    (rx : ∀ n (x : Ext X X (3*n)),
      f (n+1) (e (3*n+3) (x.comp p (by omega))) = BinaryKoszul.mulX k n (f n (e (3*n) x)))
    (ry : ∀ n (x : Ext X X (3*n)),
      f (n+1) (e (3*n+3) (x.comp q (by omega))) = BinaryKoszul.mulY k n (f n (e (3*n) x))) :
    FullTate.PositiveModel (k := k) K ((D.equiv 3).symm p) ((D.equiv 3).symm q) :=
  model K X D (fun n => (e (3*n)).trans (f n)) p q off lx ly rx ry

end ArExplicit.FullPositive

end

end OAI
end


