-- Prove2me | Definitions.Def_OAIQ031A130
-- name    : OAIQ031A130
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:05:43.084428+00:00
-- url     : https://prove2.me/theorems/2777ebcf-a7ae-4051-93c8-c9addfd9cc1a
-- title:
--   Definitions bundle OAIQ031A130 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 8 definitions, 1 inductive type or structure and 8 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.extKunnethEquiv`, `OAI.ArExplicit.ExternalTensor.firstActionUnderKunneth`, `OAI.ArExplicit.ExternalTensor.homCochainExtEquiv`, `OAI.ArExplicit.ExternalTensor.homCochainNativeExtEquiv`, `OAI.ArExplicit.ExternalTensor.homCyclesToExt`, `OAI.ArExplicit.ExternalTensor.homShortExtEquiv`, `OAI.ArExplicit.ExternalTensor.secondActionUnderKunneth`, `OAI.ArExplicit.FullTate.PositiveModel`, `OAI.ArExplicit.ModuleBar.tensorSecond`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarTensorExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorExt.lean), [`AuslanderReiten_Complete_FullTateModel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/FullTateModel.lean), [`AuslanderReiten_Ext_ExtKunneth`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtKunneth.lean), [`AuslanderReiten_Ext_ExtKunnethActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtKunnethActions.lean), [`AuslanderReiten_Ext_TExtPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExtPolynomial.lean), [`AuslanderReiten_Ext_TExtRecurrence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TExtRecurrence.lean), [`AuslanderReiten_HomComplex_HomCochainExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainExt.lean), [`AuslanderReiten_HomComplex_HomCochainExtClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainExtClass.lean), [`AuslanderReiten_HomComplex_HomCochainNativeClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainNativeClass.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A108`, `OAIQ031A118`, `OAIQ031A119` and `OAIQ031A120` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A139`, `OAIQ031A140`, `OAIQ031A141`, `OAIQ031A143` and `OAIQ031A145`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A108
import Definitions.Def_OAIQ031A118
import Definitions.Def_OAIQ031A119
import Definitions.Def_OAIQ031A120

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

def homCyclesToExt (n : ℕ) :
    LinearMap.ker (homShort k R (Y := Y) P n).g.hom →ₗ[k] Ext X Y n where
  toFun f := P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val)
    (n+1) rfl (homCycle_closed k R P n f)
  map_add' f g := (P.add_extMk
    (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val)
    (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) g.val) (n+1) rfl
      (homCycle_closed k R P n f) (homCycle_closed k R P n g)).symm
  map_smul' a f := ResolutionHomology.extMk_smul P n
    (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val) (homCycle_closed k R P n f) a

theorem homCyclesToExt_surjective (n : ℕ) :
    Function.Surjective (homCyclesToExt k R (Y := Y) P n) := by
  intro a
  obtain ⟨f, hf, hfa⟩ := P.extMk_surjective a (n+1) rfl
  refine ⟨⟨f.hom, ?_⟩, hfa⟩
  change (homShort k R (Y := Y) P n).g.hom f.hom = 0
  rw [homShort_outgoing]
  exact congrArg ModuleCat.Hom.hom hf

theorem homCyclesToExt_kernel (n : ℕ) :
    LinearMap.ker (homCyclesToExt k R (Y := Y) P n) =
      LinearMap.range (homShort k R (Y := Y) P n).moduleCatToCycles := by
  ext x
  cases n with
  | zero =>
    constructor
    · intro hx
      have hx0 : ModuleCat.ofHom x.val = 0 :=
        (ResolutionHomology.extMk_zeroDegree_eq_zero_iff P _ (homCycle_closed k R P 0 x)).mp hx
      refine ⟨0, Subtype.ext ?_⟩
      change (0 : P.complex.X 0 →ₗ[R] Y) = x.val
      exact (congrArg ModuleCat.Hom.hom hx0).symm
    · rintro ⟨f, rfl⟩
      have hf0 : (homShort k R (Y := Y) P 0).moduleCatToCycles f = 0 := by
        apply Subtype.ext
        change (homShort k R (Y := Y) P 0).f.hom f = 0
        rw [homShort_incoming_zero]
        rfl
      rw [hf0]
      exact map_zero _
  | succ n =>
    constructor
    · intro hx
      obtain ⟨f, hf⟩ := (P.extMk_eq_zero_iff (ModuleCat.ofHom x.val)
        (n+2) rfl (homCycle_closed k R P (n+1) x) n rfl).mp hx
      refine ⟨f.hom, Subtype.ext ?_⟩
      change (homShort k R (Y := Y) P (n+1)).f.hom f.hom = x.val
      rw [homShort_incoming_succ]
      exact congrArg ModuleCat.Hom.hom hf
    · rintro ⟨f, rfl⟩
      apply (P.extMk_eq_zero_iff _ (n+2) rfl
        (homCycle_closed k R P (n+1) ((homShort k R (Y := Y) P (n+1)).moduleCatToCycles f)) n rfl).mpr
      refine ⟨ModuleCat.ofHom f, ?_⟩
      apply ModuleCat.hom_ext
      change f.comp (P.complex.d (n+1) n).hom =
        (homShort k R (Y := Y) P (n+1)).f.hom f
      rw [homShort_incoming_succ]
      rfl

def homShortExtEquiv (n : ℕ) :
    (homShort k R (Y := Y) P n).homology ≃ₗ[k] Ext X Y n :=
  (homShort k R (Y := Y) P n).moduleCatHomologyIso.toLinearEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (homCyclesToExt_kernel k R P n).symm).trans
      ((homCyclesToExt k R P n).quotKerEquivOfSurjective
        (homCyclesToExt_surjective k R P n)))

def homCochainExtEquiv (n : ℕ) :
    (homCochain k R P.complex Y).homology n ≃ₗ[k] Ext X Y n :=
  ((homCochain k R P.complex Y).homologyIsoSc' (n-1) n (n+1)
    (by cases n <;> simp) (by simp)).toLinearEquiv.trans (homShortExtEquiv k R P n)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtKunneth
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def homCochainNativeExtEquiv {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
    (Y : Type u) [AddCommGroup Y] [Module R Y] [Module k Y] [IsScalarTower k R Y]
    (n : ℕ) : (homCochain k R P.complex Y).homology n ≃ₗ[k]
      Ext X (ModuleCat.of R Y) n :=
  (((homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n).mapIso
    (homCochainScalarIso k R P.complex Y)).toLinearEquiv).trans
      (homCochainExtEquiv k R (Y := ModuleCat.of R Y) P n)

variable (A B : Type u) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [Module.Finite k A] [Module.Finite k B]
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

def extKunnethEquiv (n : ℕ) :
    Ext (moduleObject k A B X Y) (moduleObject k A B U V) n ≃ₗ[k]
      (∀ p : Diagonal n, Ext X U p.val.1 ⊗[k] Ext Y V p.val.2) :=
  (homCochainNativeExtEquiv k (A ⊗[k] B) (projectiveResolution k A B P Q)
    (moduleObject k A B U V) n).symm.trans
    ((homKunnethEquiv k A B P.complex Q.complex U V n).trans
      ((DFinsupp.linearEquivFunOnFintype (R := k)).trans
        (LinearEquiv.piCongrRight fun p => TensorProduct.congr
          (homCochainExtEquiv k A (Y := U) P p.val.1)
          (homCochainExtEquiv k B (Y := V) Q p.val.2))))

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainExtClass
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

theorem homCochainExtEquiv_cycleClass (n : ℕ)
    (f : LinearMap.ker (homShort k R (Y := Y) P n).g.hom) :
    homCochainExtEquiv k R P n (homCochainCycleClass k R P n f) =
      P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val)
        (n+1) rfl (homCycle_closed k R P n f) := by
  change ((Submodule.quotEquivOfEq _ _ (homCyclesToExt_kernel k R P n).symm).trans
      ((homCyclesToExt k R P n).quotKerEquivOfSurjective
        (homCyclesToExt_surjective k R P n)))
    ((homCochainQuotientEquiv k R P n)
      ((homCochainQuotientEquiv k R P n).symm (Submodule.Quotient.mk f))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainNativeClass
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem homCochainExtEquiv_literal (N : ModuleCat.{u} R) (n : ℕ)
    (f : P.complex.X n →ₗ[R] N) (hf : f.comp (P.complex.d (n+1) n).hom=0) :
    homCochainExtEquiv k R (Y := N) P n
      (VectorCochain.literalClass k (homCochain k R P.complex N) n
        ⟨f,homCochain_mem_cycles k R P N n f hf⟩) =
      P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := N) f)
        (n+1) rfl (ModuleCat.hom_ext hf) := by
  let z : LinearMap.ker (homShort k R (Y := N) P n).g.hom :=
    ⟨f,homCochain_mem_cycles k R P N n f hf⟩
  have he := homCochainExtEquiv_cycleClass k R (Y := N) P n z
  rw [homCochainCycleClass_eq_literal] at he
  exact he

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtKunnethActions
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

def firstActionUnderKunneth (n : ℕ) : extCoefficients k A B X U Y V n →ₗ[k]
    extCoefficients k A B X U Y V (n+3) :=
  (extKunnethEquiv k A B P Q U V (n+3)).toLinearMap.comp
    ((Ext.bilinearCompOfLinear k (moduleObject k A B X Y) (moduleObject k A B X Y)
      (moduleObject k A B U V) 3 n (n+3) (by omega) (firstCubicExt k A B P Q p hp)).comp
        (extKunnethEquiv k A B P Q U V n).symm.toLinearMap)

variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

def secondActionUnderKunneth (n : ℕ) : extCoefficients k A B X U Y V n →ₗ[k]
    extCoefficients k A B X U Y V (n+3) :=
  (extKunnethEquiv k A B P Q U V (n+3)).toLinearMap.comp
    ((Ext.bilinearCompOfLinear k (moduleObject k A B X Y) (moduleObject k A B X Y)
      (moduleObject k A B U V) 3 n (n+3) (by omega) (secondCubicExt k A B P Q r hr)).comp
        (extKunnethEquiv k A B P Q U V n).symm.toLinearMap)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]

variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]

variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)

def tensorSecond : Ext (ExternalTensor.moduleObject k R S M N)
    (ExternalTensor.moduleObject k R S M N) 3 :=
  (ExternalTensor.selfExtScalarEquiv k R S M N 3).symm (nativeTensorSecond k R S M N r hr)

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_FullTateModel
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.FullTate
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R] [CharP k 2]
open CompleteComparison TateKoszul
variable (τ : FrobeniusTrace k R) (hs : ∀ a b : R, τ.trace (a*b)=τ.trace (b*a))
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
local notation "H" => CohomologyClass K K

structure PositiveModel (p q : H 3) where
  positive : ∀ n : ℕ, H (3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n
  outside : ∀ a : ℤ, 0 ≤ a → (∀ n : ℕ, a ≠ 3*(n:ℤ)) → Subsingleton (H a)
  right_x : ∀ (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a),
    positive (n+1) (degreeEquiv (k := k) H (show a+3=3*((n+1:ℕ):ℤ) by omega)
      (fullHomProduct v p)) = BinaryKoszul.mulX k n (positive n (degreeEquiv (k := k) H ha v))
  right_y : ∀ (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a),
    positive (n+1) (degreeEquiv (k := k) H (show a+3=3*((n+1:ℕ):ℤ) by omega)
      (fullHomProduct v q)) = BinaryKoszul.mulY k n (positive n (degreeEquiv (k := k) H ha v))
  left_x : ∀ (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a),
    positive (n+1) (degreeEquiv (k := k) H (show 3+a=3*((n+1:ℕ):ℤ) by omega)
      (fullHomProduct p v)) = BinaryKoszul.mulX k n (positive n (degreeEquiv (k := k) H ha v))
  left_y : ∀ (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a),
    positive (n+1) (degreeEquiv (k := k) H (show 3+a=3*((n+1:ℕ):ℤ) by omega)
      (fullHomProduct q v)) = BinaryKoszul.mulY k n (positive n (degreeEquiv (k := k) H ha v))

end ArExplicit.FullTate

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExtRecurrence
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD

theorem tConnecting_multiply_surjective (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) (n : ℤ) (hn : n + 3 ≠ 0) :
    Function.Surjective (fun b : ShiftedHom (tSimpleDerived q) (tSimpleDerived q) n =>
      ShiftedHom.comp (tConnecting q hq hq1 h) b rfl) := by
  let e := TriangleRecurrence.shiftedMapEquiv (tSimpleDerived q) (tSimpleDerived q) 3 n (n + 3) rfl
  let e' := ((shiftFunctorAdd' (DerivedCategory (ModuleCat T)) (2 : ℤ) 1 3 (by decide)).app
    (tSimpleDerived q)).homFromEquiv (Z := (tSimpleDerived q)⟦n + 3⟧)
  have hh := (TriangleRecurrence.connecting_surjective (tInductionTriangle q hq hq1 h)
    (tInductionTriangle_distinguished q hq hq1 h) ((tSimpleDerived q)⟦n + 3⟧)
    (tInducedDerived_hom_zero q hq1 (n + 3) hn)).comp (e'.surjective.comp e.surjective)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ext b
  simp only [e, e', TriangleRecurrence.shiftedMapEquiv,
    ShiftedHom.comp, Category.assoc, tConnecting]
  rfl

theorem tSimpleDerived_low_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) (n : ℤ) (hn : 0 < n) (hn3 : n < 3)
    (f : tSimpleDerived q ⟶ (tSimpleDerived q)⟦n⟧) : f = 0 := by
  rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
  · have hs := tConnecting_multiply_surjective q hq hq1 h (-2) (by decide)
    obtain ⟨b, hb⟩ := hs f
    rw [tSimpleDerived_negative_zero q (-2) (by decide) b] at hb
    simpa only [ShiftedHom.comp_zero] using hb.symm
  · have hs := tConnecting_multiply_surjective q hq hq1 h (-1) (by decide)
    obtain ⟨b, hb⟩ := hs f
    rw [tSimpleDerived_negative_zero q (-1) (by decide) b] at hb
    simpa only [ShiftedHom.comp_zero] using hb.symm

theorem tSelfExt_low_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) (n : ℕ) (hn : 0 < n) (hn3 : n < 3) (x : TSelfExt q n) : x = 0 := by
  apply (Abelian.Ext.homEquiv (X := ModuleCat.of T (Simple q))
    (Y := ModuleCat.of T (Simple q)) (n := n)).injective
  simpa only [Abelian.Ext.zero_hom, tSimpleDerived] using! tSimpleDerived_low_zero q hq hq1 h (n : ℤ) (by omega) (by omega) x.hom

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TExtPolynomial
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD
variable (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

theorem tSelfExt_zero_of_not_dvd (n : ℕ) (hn : ¬ 3 ∣ n) (x : TSelfExt q n) : x = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn3 : n < 3
    · exact tSelfExt_low_zero q hq hq1 h n (by omega) hn3 x
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      obtain ⟨y, rfl⟩ := (tTau_multiply_bijective q hq hq1 h m).surjective x
      have hm : ¬ 3 ∣ m := by
        intro hm
        exact hn (dvd_add hm (dvd_refl 3))
      rw [ih m (by omega) hm y]
      exact Abelian.Ext.comp_zero _ _ _ _ _

end ArExplicit.Resolution

end

end OAI
end


