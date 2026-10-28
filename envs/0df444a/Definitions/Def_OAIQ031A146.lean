-- Prove2me | Definitions.Def_OAIQ031A146
-- name    : OAIQ031A146
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:28:40.786701+00:00
-- url     : https://prove2.me/theorems/feab0f80-bc78-4e61-ad69-2adbe0fe49d2
-- title:
--   Definitions bundle OAIQ031A146 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 23 declarations of OpenAI's Lean: 3 definitions and 20 theorems. The definitions and types are `OAI.ArExplicit.Resolution.tTensorCoefficientEquiv`, `OAI.ArExplicit.Resolution.tTensorCoefficients`, `OAI.ArExplicit.Resolution.tTensorScalarAt`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarTensorClass`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorClass.lean), [`AuslanderReiten_Bar_ModuleBarTensorExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorExt.lean), [`AuslanderReiten_Bar_ModuleBarTensorGeneration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorGeneration.lean), [`AuslanderReiten_Ext_ExtKunnethActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtKunnethActions.lean), [`AuslanderReiten_Ext_ExtTensorAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtTensorAction.lean), [`AuslanderReiten_Ext_TTensorActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorActions.lean), [`AuslanderReiten_Ext_TTensorPolynomial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TTensorPolynomial.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A139`, `OAIQ031A140` and `OAIQ031A141` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A151` and `OAIQ031A153`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A139
import Definitions.Def_OAIQ031A140
import Definitions.Def_OAIQ031A141

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtTensorAction
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
variable [CharP k 2] [Module.Finite k A] [Module.Finite k B]
variable [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

omit [CharP k 2] [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)]
  [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))] in
theorem elementaryExt_kunneth (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n h f g hf hg) =
      (Pi.single ⟨(i,j),h⟩
        (P.extMk (ModuleCat.ofHom (X := P.complex.X i) (Y := U) f) (i+1) rfl (ModuleCat.hom_ext hf) ⊗ₜ[k]
          Q.extMk (ModuleCat.ofHom (X := Q.complex.X j) (Y := V) g) (j+1) rfl (ModuleCat.hom_ext hg)) :
        extCoefficients k A B X U Y V n) :=
  extKunnethEquiv_elementary k A B P Q U V i j n h f g hf hg

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtKunnethActions
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

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat B)] in
theorem firstActionUnderKunneth_elementary (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    firstActionUnderKunneth k A B P Q U V p hp n
      (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n h f g hf hg)) =
    coefficientFirst k A B X U Y V
      (ResolutionProducts.endExt P (ResolutionProducts.natCubicCocycle (k := k) P p hp)) n
      (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n h f g hf hg)) := by
  unfold firstActionUnderKunneth
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change extKunnethEquiv k A B P Q U V (n+3)
    ((firstCubicExt k A B P Q p hp).comp (elementaryExt k A B P Q U V i j n h f g hf hg) (by omega)) = _
  rw [firstCubicExt_elementary, elementaryExt_kunneth, elementaryExt_kunneth,
    coefficientFirst_single, ResolutionProducts.cubic_endExt_comp_extMk (k := k)]
  rfl

omit [CharP k 2] [Module.Finite k A] [Module.Finite k B]
  [HasDerivedCategory (ModuleCat A)] [HasDerivedCategory (ModuleCat B)]
  [HasDerivedCategory (ModuleCat (A ⊗[k] B))] in
theorem coefficients_ext (n : ℕ)
    (L R : extCoefficients k A B X U Y V n →ₗ[k] extCoefficients k A B X U Y V (n+3))
    (h : ∀ (i j : ℕ) (hij : i+j=n)
      (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
      (hf : f.comp (P.complex.d (i+1) i).hom=0)
      (hg : g.comp (Q.complex.d (j+1) j).hom=0),
      L (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n hij f g hf hg)) =
      R (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n hij f g hf hg))) : L=R := by
  classical
  apply LinearMap.pi_ext
  intro d t
  induction t using OAI.tensorInductionOn with
  | add a b ha hb => simp only [Pi.single_add, map_add, ha, hb]
  | tmul x y =>
    obtain ⟨f,hf,rfl⟩ := P.extMk_surjective x (d.val.1+1) rfl
    obtain ⟨g,hg,rfl⟩ := Q.extMk_surjective y (d.val.2+1) rfl
    let hf' := congrArg ModuleCat.Hom.hom hf
    let hg' := congrArg ModuleCat.Hom.hom hg
    have he := elementaryExt_kunneth k A B P Q U V d.val.1 d.val.2 n d.property f.hom g.hom hf' hg'
    have hl := h d.val.1 d.val.2 d.property f.hom g.hom hf' hg'
    exact (congrArg L he.symm).trans (hl.trans (congrArg R he))

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat B)] in
theorem firstActionUnderKunneth_eq (n : ℕ) :
    firstActionUnderKunneth k A B P Q U V p hp n =
      coefficientFirst k A B X U Y V
        (ResolutionProducts.endExt P (ResolutionProducts.natCubicCocycle (k := k) P p hp)) n := by
  apply coefficients_ext k A B P Q U V n
  intro i j hij f g hf hg
  exact firstActionUnderKunneth_elementary k A B P Q U V p hp i j n hij f g hf hg

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat B)] in
theorem firstCubicExt_kunneth (n : ℕ)
    (x : Ext (moduleObject k A B X Y) (moduleObject k A B U V) n) :
    extKunnethEquiv k A B P Q U V (n+3) ((firstCubicExt k A B P Q p hp).comp x (by omega)) =
      coefficientFirst k A B X U Y V
        (ResolutionProducts.endExt P (ResolutionProducts.natCubicCocycle (k := k) P p hp)) n
          (extKunnethEquiv k A B P Q U V n x) := by
  have he := LinearMap.congr_fun (firstActionUnderKunneth_eq k A B P Q U V p hp n)
    (extKunnethEquiv k A B P Q U V n x)
  simp only [firstActionUnderKunneth, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] at he
  exact he

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat B)] in
theorem firstCubicExt_kunneth_of_class (a : Ext X X 3)
    (ha : ResolutionProducts.endExt P (ResolutionProducts.natCubicCocycle (k := k) P p hp) = a)
    (n : ℕ) (x : Ext (moduleObject k A B X Y) (moduleObject k A B U V) n) :
    extKunnethEquiv k A B P Q U V (n+3) ((firstCubicExt k A B P Q p hp).comp x (by omega)) =
      coefficientFirst k A B X U Y V a n (extKunnethEquiv k A B P Q U V n x) := by
  rw [← ha]
  exact firstCubicExt_kunneth k A B P Q U V p hp n x

variable (r : ∀ n, Q.complex.X (n+3) ⟶ Q.complex.X n)
variable (hr : ∀ n, r (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (n+4) (n+3) ≫ r n)

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat A)] in
theorem secondActionUnderKunneth_elementary (i j n : ℕ) (h : i+j=n)
    (f : P.complex.X i →ₗ[A] U) (g : Q.complex.X j →ₗ[B] V)
    (hf : f.comp (P.complex.d (i+1) i).hom=0) (hg : g.comp (Q.complex.d (j+1) j).hom=0) :
    secondActionUnderKunneth k A B P Q U V r hr n
      (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n h f g hf hg)) =
    coefficientSecond k A B X U Y V
      (ResolutionProducts.endExt Q (ResolutionProducts.natCubicCocycle (k := k) Q r hr)) n
      (extKunnethEquiv k A B P Q U V n (elementaryExt k A B P Q U V i j n h f g hf hg)) := by
  unfold secondActionUnderKunneth
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  change extKunnethEquiv k A B P Q U V (n+3)
    ((secondCubicExt k A B P Q r hr).comp (elementaryExt k A B P Q U V i j n h f g hf hg) (by omega)) = _
  rw [secondCubicExt_elementary, elementaryExt_kunneth, elementaryExt_kunneth,
    coefficientSecond_single, ResolutionProducts.cubic_endExt_comp_extMk (k := k)]
  rfl

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat A)] in
theorem secondActionUnderKunneth_eq (n : ℕ) :
    secondActionUnderKunneth k A B P Q U V r hr n =
      coefficientSecond k A B X U Y V
        (ResolutionProducts.endExt Q (ResolutionProducts.natCubicCocycle (k := k) Q r hr)) n := by
  apply coefficients_ext k A B P Q U V n
  intro i j hij f g hf hg
  exact secondActionUnderKunneth_elementary k A B P Q U V r hr i j n hij f g hf hg

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat A)] in
theorem secondCubicExt_kunneth (n : ℕ)
    (x : Ext (moduleObject k A B X Y) (moduleObject k A B U V) n) :
    extKunnethEquiv k A B P Q U V (n+3) ((secondCubicExt k A B P Q r hr).comp x (by omega)) =
      coefficientSecond k A B X U Y V
        (ResolutionProducts.endExt Q (ResolutionProducts.natCubicCocycle (k := k) Q r hr)) n
          (extKunnethEquiv k A B P Q U V n x) := by
  have he := LinearMap.congr_fun (secondActionUnderKunneth_eq k A B P Q U V r hr n)
    (extKunnethEquiv k A B P Q U V n x)
  simp only [secondActionUnderKunneth, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] at he
  exact he

omit [Module.Finite k A] [Module.Finite k B] [HasDerivedCategory (ModuleCat A)] in
theorem secondCubicExt_kunneth_of_class (b : Ext Y Y 3)
    (hb : ResolutionProducts.endExt Q (ResolutionProducts.natCubicCocycle (k := k) Q r hr) = b)
    (n : ℕ) (x : Ext (moduleObject k A B X Y) (moduleObject k A B U V) n) :
    extKunnethEquiv k A B P Q U V (n+3) ((secondCubicExt k A B P Q r hr).comp x (by omega)) =
      coefficientSecond k A B X U Y V b n (extKunnethEquiv k A B P Q U V n x) := by
  rw [← hb]
  exact secondCubicExt_kunneth k A B P Q U V r hr n x

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

omit [HasDerivedCategory (ModuleCat S)] in
theorem nativeTensorFirst_action (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) :
    nativeTensorKunneth k R S M N (n+3) ((nativeTensorFirst k R S M N p hp).comp x (by omega)) =
      ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) (extClass3 k R M p hp) n
          (nativeTensorKunneth k R S M N n x) := by
  unfold nativeTensorKunneth nativeTensorFirst
  exact ExternalTensor.firstCubicExt_kunneth_of_class k R S
    (nativeResolution k R M) (nativeResolution k S N) (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeCubicMap k R M p) (nativeCubicMap_comm k R M p hp) _
    (nativeCubicMap_class k R M p hp) n x

omit [HasDerivedCategory (ModuleCat R)] in
theorem nativeTensorSecond_action (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) :
    nativeTensorKunneth k R S M N (n+3) ((nativeTensorSecond k R S M N r hr).comp x (by omega)) =
      ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) (extClass3 k S N r hr) n
          (nativeTensorKunneth k R S M N n x) := by
  unfold nativeTensorKunneth nativeTensorSecond
  exact ExternalTensor.secondCubicExt_kunneth_of_class k R S
    (nativeResolution k R M) (nativeResolution k S N) (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeCubicMap k S N r) (nativeCubicMap_comm k S N r hr) _
    (nativeCubicMap_class k S N r hr) n x

omit [HasDerivedCategory (ModuleCat S)] in
theorem tensorFirst_action (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N (n+3) ((tensorFirst k R S M N p hp).comp x (by omega)) =
      ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) (extClass3 k R M p hp) n
          (tensorKunneth k R S M N n x) := by
  unfold tensorKunneth
  simp only [LinearEquiv.trans_apply, ExternalTensor.selfExtScalarEquiv_comp,
    tensorFirst, LinearEquiv.apply_symm_apply]
  exact nativeTensorFirst_action k R S M N p hp n _

omit [HasDerivedCategory (ModuleCat R)] in
theorem tensorSecond_action (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N (n+3) ((tensorSecond k R S M N r hr).comp x (by omega)) =
      ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) (extClass3 k S N r hr) n
          (tensorKunneth k R S M N n x) := by
  unfold tensorKunneth
  simp only [LinearEquiv.trans_apply, ExternalTensor.selfExtScalarEquiv_comp,
    tensorSecond, LinearEquiv.apply_symm_apply]
  exact nativeTensorSecond_action k R S M N r hr n _

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorClass
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)

omit [HasDerivedCategory (ModuleCat.{u} S)] in
theorem tensorFirst_action_of_class (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
    (ha : extClass3 k R M p hp = a) (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N (n+3) ((tensorFirst k R S M N p hp).comp x (by omega)) =
      ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) a n (tensorKunneth k R S M N n x) := by
  rw [tensorFirst_action, ha]

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem tensorSecond_action_of_class (a : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
    (ha : extClass3 k S N r hr = a) (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N (n+3) ((tensorSecond k R S M N r hr).comp x (by omega)) =
      ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) a n (tensorKunneth k R S M N n x) := by
  rw [tensorSecond_action, ha]

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorGeneration
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
  (ha : extClass3 k R M p hp = a)
  (b : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
  (hb : extClass3 k S N r hr = b)
include ha hb

theorem tensor_generation (n : ℕ)
    (hgen : ∀ z : ExternalTensor.extCoefficients k R S
        (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (n+3),
      ∃ u v : ExternalTensor.extCoefficients k R S
        (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n,
        z = ExternalTensor.coefficientFirst k R S
          (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a n u +
        ExternalTensor.coefficientSecond k R S
          (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b n v)
    (x : Ext (ExternalTensor.moduleObject k R S M N)
      (ExternalTensor.moduleObject k R S M N) (n+3)) :
    ∃ u v : Ext (ExternalTensor.moduleObject k R S M N)
        (ExternalTensor.moduleObject k R S M N) n,
      x = (tensorFirst k R S M N p hp).comp u (by omega) +
        (tensorSecond k R S M N r hr).comp v (by omega) :=
  ResolutionProducts.generationOfAddEquiv
    (tensorFirst k R S M N p hp) (tensorSecond k R S M N r hr)
    (tensorKunneth k R S M N n).toAddEquiv
    (tensorKunneth k R S M N (n+3)).toAddEquiv
    (ExternalTensor.coefficientFirst k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a n)
    (ExternalTensor.coefficientSecond k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b n)
    (tensorFirst_action_of_class k R S M N p hp a ha n)
    (tensorSecond_action_of_class k R S M N r hr b hb n) hgen x

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorPolynomial
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

abbrev tTensorCoefficients (n : ℕ) :=
  ExternalTensor.extCoefficients k (T k q) (T k q)
    (ModuleCat.of (T k q) (Simple q)) (ModuleCat.of (T k q) (Simple q))
    (ModuleCat.of (T k q) (Simple q)) (ModuleCat.of (T k q) (Simple q)) n

include hq hq1 h

theorem tTensorCoefficient_off_diagonal (n : ℕ) (p : ExternalTensor.Diagonal (3*n))
    (hp : ¬ ∃ i, polynomialDiagonal n i = p)
    (z : TSelfExt q p.val.1 ⊗[k] TSelfExt q p.val.2) : z=0 := by
  by_cases h₁ : 3 ∣ p.val.1
  · have h₂ : ¬ 3 ∣ p.val.2 := fun h₂ => hp (polynomialDiagonal_hits n p h₁ h₂)
    exact tensor_zero_right (tSelfExt_zero_of_not_dvd q hq hq1 h p.val.2 h₂) z
  · exact tensor_zero_left (tSelfExt_zero_of_not_dvd q hq hq1 h p.val.1 h₁) z

def tTensorCoefficientEquiv (n : ℕ) : tTensorCoefficients q (3*n) ≃ₗ[k] (Fin (n+1) → k) :=
  (supportedPiEquiv (fun p : ExternalTensor.Diagonal (3*n) =>
      TSelfExt q p.val.1 ⊗[k] TSelfExt q p.val.2) (polynomialDiagonal n)
      (polynomialDiagonal_injective n) (tTensorCoefficient_off_diagonal q hq hq1 h n)).trans
    (LinearEquiv.piCongrRight fun i =>
      (TensorProduct.congr (tExplicitCoefficientEquiv q hq hq1 h i.val).symm
        (tExplicitCoefficientEquiv q hq hq1 h (n-i.val)).symm).trans (TensorProduct.lid k k))

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TTensorActions
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)

def tTensorScalarAt (n : ℕ) (z : tTensorCoefficients q n) (a b : ℕ) (hab : 3*a+3*b=n) : k :=
  tTensorScalarEquiv q hq hq1 h a b (z ⟨(3*a,3*b),hab⟩)

theorem tTensorScalarAt_congr (n : ℕ) (z : tTensorCoefficients q n)
    {a b a' b' : ℕ} (ha : a=a') (hb : b=b') (hab : 3*a+3*b=n) (hab' : 3*a'+3*b'=n) :
    tTensorScalarAt q hq hq1 h n z a b hab = tTensorScalarAt q hq hq1 h n z a' b' hab' := by
  subst a'
  subst b'
  rfl

@[simp]
theorem tTensorCoefficientEquiv_apply (n : ℕ) (z : tTensorCoefficients q (3*n)) (i : Fin (n+1)) :
    tTensorCoefficientEquiv q hq hq1 h n z i =
      tTensorScalarEquiv q hq hq1 h i.val (n-i.val) (z (polynomialDiagonal n i)) := rfl

end ArExplicit.Resolution

end

end OAI
end


