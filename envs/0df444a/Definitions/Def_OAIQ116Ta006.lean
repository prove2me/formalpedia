-- Prove2me | Definitions.Def_OAIQ116Ta006
-- name    : OAIQ116Ta006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:46:08.07399+00:00
-- url     : https://prove2.me/theorems/442325f4-5c48-4379-98b6-6545417aa07f
-- title:
--   Definitions bundle OAIQ116Ta006 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 40 definitions, 8 instances and 48 theorems. The definitions and types are `OAI.Tachikawa.BimoduleTensorHom.equiv`, `OAI.Tachikawa.C.InducedBoundaries`, `OAI.Tachikawa.C.InducedRange`, `OAI.Tachikawa.C.InducedTwoCycles`, `OAI.Tachikawa.C.TSimple`, `OAI.Tachikawa.C.balancedInducedResolution`, `OAI.Tachikawa.C.boundaryInclusion`, `OAI.Tachikawa.C.comparisonComponent`, `OAI.Tachikawa.C.cyclesTwistComparison`, `OAI.Tachikawa.C.forwardD`, `OAI.Tachikawa.C.forwardObj`, `OAI.Tachikawa.C.inducedD`, `OAI.Tachikawa.C.inducedObj`, `OAI.Tachikawa.C.inducedTwistComparison`, `OAI.Tachikawa.C.inducedTwoBoundary`, `OAI.Tachikawa.C.projectiveResolution`, `OAI.Tachikawa.C.reverseD`, `OAI.Tachikawa.C.reverseObj`, `OAI.Tachikawa.C.rhoJ`, `OAI.Tachikawa.C.rhoT`, `OAI.Tachikawa.C.rhoV`, `OAI.Tachikawa.C.rhoX`, `OAI.Tachikawa.C.t`, `OAI.Tachikawa.C.tTwist`, `OAI.Tachikawa.C.x`, `OAI.Tachikawa.Enveloping.fiberCover`, `OAI.Tachikawa.Enveloping.fiberFst`, `OAI.Tachikawa.Enveloping.fiberInl`, `OAI.Tachikawa.Enveloping.fiberInm`, `OAI.Tachikawa.Enveloping.fiberInr`, `OAI.Tachikawa.Enveloping.fiberMiddle`, `OAI.Tachikawa.Enveloping.fiberProjection`, `OAI.Tachikawa.Enveloping.fiberSnd`, `OAI.Tachikawa.Triangular.Alg`, `OAI.Tachikawa.Triangular.Off`, `OAI.Tachikawa.Triangular.lower`, `OAI.Tachikawa.Triangular.off`, `OAI.Tachikawa.Triangular.upper`, `OAI.Tachikawa.TrivialInduction.inverseTwist`, `OAI.Tachikawa.TrivialInduction.twistComparison`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: [`Tachikawa_Bimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Bimodule.lean), [`Tachikawa_Corner`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Corner.lean), [`Tachikawa_Delta`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Delta.lean), [`Tachikawa_DerivedInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/DerivedInduction.lean), [`Tachikawa_Period`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Period.lean), [`Tachikawa_ReverseResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/ReverseResolution.lean), [`Tachikawa_StableLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/StableLift.lean), [`Tachikawa_Tensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Tensor.lean), [`Tachikawa_Triangular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Triangular.lean).
--
--   **Imports.** It imports the bundles `OAIQ116Ta003` and `OAIQ116Ta004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ116Ta017`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta003
import Definitions.Def_OAIQ116Ta004

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Tensor
attribute [-instance] _root_.OAI.Tachikawa.BalancedTensor.rightComm _root_.OAI.Tachikawa.BalancedTensor.rightModule _root_.OAI.Tachikawa.BalancedTensor.rightTower _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.BalancedTensor
variable {k R S M M' N N' N'' : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k S M']
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']
  [AddCommGroup N''] [Module k N''] [Module R N''] [IsScalarTower k R N'']

lemma mapRight_exact [SMulCommClass S Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (he : Function.Exact f g) :
    Function.Exact (mapRight (k := k) (S := S) (M := M) f)
      (mapRight (k := k) (S := S) (M := M) g) := by
  intro x
  constructor
  · intro hx
    have hz : mapRight (k := k) (S := k) (M := M) g (restrictEquiv x) = 0 := by
      rw [← restrictEquiv_mapRight, hx,map_zero]
    obtain ⟨y,hy⟩ := (field_mapRight_exact (k := k) f g he (restrictEquiv x)).mp hz
    refine ⟨restrictEquiv.symm y, ?_⟩
    apply restrictEquiv.injective
    rw [restrictEquiv_mapRight, LinearEquiv.apply_symm_apply, hy]
  · rintro ⟨y,rfl⟩
    rw [← LinearMap.comp_apply, ← mapRight_comp, he.linearMap_comp_eq_zero, mapRight_zero]
    rfl

end Tachikawa.BalancedTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Corner
attribute [-instance] _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section



namespace Tachikawa.C
open CategoryTheory
variable {k : Type*} [Field k] [CharP k 2] (q : k)

def projectiveResolution (hq : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    ProjectiveResolution (ModuleCat.of (C k q) (Simple q)) :=
  resolutionOfExact _ (resObj q) (resD q) (ModuleCat.ofHom (augmentation q))
    (resD_exact q hq) (exact_augmentation q (by simpa only [pow_one] using hq 1 (by omega)))
    (augmentation_surjective q) (fun n => by cases n <;> dsimp [resObj] <;> infer_instance)

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Period
attribute [-instance] _root_.OAI.Tachikawa.AlgebraInduction.resFinite _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace C
variable [CharP k 2] (q : k)
abbrev TSimple := TrivialInflation k (C k q) (Simple q)

def inducedObj (n : ℕ) : ModuleCat (T q) :=
  ModuleCat.of (T q) (TrivialInduction.Obj k (C k q) (resObj q n))
def inducedD (n : ℕ) : inducedObj q (n+1) ⟶ inducedObj q n :=
  ModuleCat.ofHom (TrivialInduction.map (resD q n).hom)

lemma inducedD_comp (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    inducedD q (n+1) ≫ inducedD q n = 0 := by
  apply ModuleCat.hom_ext
  change (TrivialInduction.map (resD q n).hom).comp (TrivialInduction.map (resD q (n+1)).hom) = 0
  rw [← TrivialInduction.map_comp, (resD_exact q hp n).linearMap_comp_eq_zero, TrivialInduction.map_zero]

end C
end Tachikawa



namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (H : k) (hH : H ≠ 0) (M : ModuleCat R)

abbrev inverseTwist : ModuleCat (TrivialExtension k R) ⥤ ModuleCat (TrivialExtension k R) :=
  AlgebraInduction.res (TrivialExtension.scaleDual H hH).symm.toAlgHom

def twistComparison : (inverseTwist (R := R) H hH).obj ((functor (k := k)).obj M) ⟶
    (functor (k := k)).obj M :=
  ModuleCat.ofHom (X := (inverseTwist (R := R) H hH).obj ((functor (k := k)).obj M))
    (Y := (functor (k := k)).obj M)
    { toFun := fun x => (x.1,H • x.2)
      map_add' := fun x y => by exact Prod.ext rfl (smul_add H x.2 y.2)
      map_smul' := fun a x => by
        apply Prod.ext
        · rfl
        · change H • (Nakayama.evaluationBilinear (H⁻¹ • a.snd) x.1 + a.fst • x.2) =
            Nakayama.evaluationBilinear a.snd x.1 + a.fst • (H • x.2)
          rw [smul_add,LinearMap.map_smul_of_tower,LinearMap.smul_apply,smul_smul,
            mul_inv_cancel₀ hH,one_smul,smul_comm H a.fst] }

end Tachikawa.TrivialInduction



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev InducedBoundaries := LinearMap.range (inducedD q 2).hom

end Tachikawa.C



namespace Tachikawa.RightCorner
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {p : R} (hp : p*p=p)

@[simp] lemma homEquivScalar_apply (f : LeftCorner p →ₗ[R] R) :
    homEquivScalar (k := k) hp f = homEquiv hp f := rfl

lemma homEquivScalar_precomp {r : R} (hr : r*r=r) (b : R) (hpb : p*b=b) (hbr : b*r=b)
    (f : LeftCorner r →ₗ[R] R) :
    homEquivScalar (k := k) hp (f.comp (LeftCorner.mulRight b hbr)) =
      mulLeft b hpb (homEquivScalar (k := k) hr f) :=
  homEquiv_precomp hp hr b hpb hbr f

end Tachikawa.RightCorner



namespace Tachikawa.C
variable {k : Type} [Field k] [CharP k 2] (q : k)

omit [CharP k 2] in
lemma homEquiv_vHom : RightCorner.homEquiv (e_idempotent q) (vHom q) = ec q 0 0 0 0 0 1 :=
  Subtype.ext (vHom_generator q)

lemma dualTwoCycle_decompose (hq : q ≠ 0) (hq1 : 1+q ≠ 0)
    (a : LinearMap.ker (lambdaEll q q)) :
    a.val = lambdaEll q 1 (ec q (a.val.val 2) (a.val.val 4) 0 0 0 0) + ec q 0 0 0 0 0 (a.val.val 6) := by
  obtain ⟨h0,h3,h5⟩ := dualTwoCycle_coords q hq hq1 a
  rw [lambdaEll_ec]
  have he := ec_eta q a.val
  rw [h0,h3,h5] at he
  apply he.symm.trans
  apply Subtype.ext
  change (ec q 0 (a.val.val 2) (a.val.val 2) (a.val.val 4) 0 (a.val.val 6)).val =
    (ec q 0 (a.val.val 2) (1 * a.val.val 2) (1 * a.val.val 4 + q * 0) 0 ((1+1)*0)).val +
      (ec q 0 0 0 0 0 (a.val.val 6)).val
  ext i
  rw [add_apply]
  fin_cases i <;> simp [ec]

omit [CharP k 2] in
lemma homRight_vHom_six (a : C k q) :
    (RightCorner.homEquiv (e_idempotent q) (Nakayama.homRight (k := k) a (vHom q))).val 6 = a 1 := by
  change (vHom q (LeftCorner.generator (e_idempotent q)) * a) 6 = a 1
  rw [vHom_generator]
  change (0*a 6 + 1*a 1 + 0*a 5 + 0*a 5 + 0*a 9) = a 1
  simp

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev InducedTwoCycles := LinearMap.ker (TrivialInduction.map (k := k) (rhoEll q 1))

omit [CharP k 2] in
lemma twoCycles_first (x : InducedTwoCycles q) : rhoEll q 1 x.val.1 = 0 := by
  exact congrArg Prod.fst x.property

omit [CharP k 2] in
lemma twoCycles_second (x : InducedTwoCycles q) :
    Nakayama.map (rhoEll q 1) x.val.2 = 0 := by
  exact congrArg Prod.snd x.property

def inducedTwoBoundary (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    inducedObj q 3 →ₗ[T q] InducedTwoCycles q :=
  (inducedD q 2).hom.codRestrict _ (fun x => by
    have h := congrArg (fun f : inducedObj q 3 ⟶ inducedObj q 1 => f x) (inducedD_comp q hp 1)
    change (TrivialInduction.map (rhoEll q (q^0))) ((inducedD q 2).hom x) = 0 at h
    change (TrivialInduction.map (rhoEll q 1)) ((inducedD q 2).hom x) = 0
    simpa only [pow_zero] using h)

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev InducedRange (n : ℕ) := LinearMap.range (inducedD q n).hom

def boundaryInclusion (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :
    InducedBoundaries q →ₗ[T q] InducedTwoCycles q where
  toFun x := ⟨(show TrivialInduction.Obj k (C k q) (Ce q) from x.val), by
    obtain ⟨y,hy⟩ := x.property
    exact (congrArg (TrivialInduction.map (k := k) (rhoEll q 1)) hy).symm.trans
      (inducedTwoBoundary q hp y).property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q H : k) (hH : H ≠ 0)

abbrev tTwist := TrivialInduction.inverseTwist (R := C k q) H hH

omit [CharP k 2] in
def inducedTwistComparison (n : ℕ) :
    (tTwist q H hH).obj (inducedObj q n) ⟶ inducedObj q n :=
  TrivialInduction.twistComparison H hH (resObj q n)

set_option maxHeartbeats 800000 in
omit [CharP k 2] in
def cyclesTwistComparison :
    (tTwist q H hH).obj (ModuleCat.of (T q) (InducedTwoCycles q)) ⟶
      ModuleCat.of (T q) (InducedTwoCycles q) :=
  ModuleCat.ofHom (X := (tTwist q H hH).obj (ModuleCat.of (T q) (InducedTwoCycles q)))
    (Y := ModuleCat.of (T q) (InducedTwoCycles q))
    { toFun := fun x => ⟨(x.val.1,H • x.val.2), by
        change (rhoEll q 1 x.val.1,Nakayama.map (rhoEll q 1) (H • x.val.2)) = (0,0)
        rw [twoCycles_first q x,(Nakayama.map (rhoEll q 1)).map_smul_of_tower,
          twoCycles_second q x,smul_zero]⟩
      map_add' := fun x y => Subtype.ext ((inducedTwistComparison q H hH 2).hom.map_add x.val y.val)
      map_smul' := fun r x => Subtype.ext ((inducedTwistComparison q H hH 2).hom.map_smul r x.val) }

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

def t : C k q := ![0,0,0,0,0,0,0,1,0,0]
lemma t_mul_e : t q * e q = t q := by rw [mul_e]; rfl

def rhoT : Cf q →ₗ[C k q] Ce q := LeftCorner.mulRight (t q) (t_mul_e q)

lemma rhoT_cf (a u v n : k) :
    rhoT q (cf q a u v n) = ce q 0 (q*u) u (q*v) a (q*n) := by
  apply Subtype.ext
  ext i
  change mul q ![0,a,0,0,0,u,v,0,0,n] (t q) i = _
  fin_cases i <;> simp [mul, t, ce]

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

def x : C k q := ![0,0,1,0,0,0,0,0,0,0]
lemma j_mul_e : j q * e q = j q := by rw [mul_e]; rfl
lemma x_mul_e : x q * e q = x q := by rw [mul_e]; rfl
lemma v_mul_f : v q * f q = v q := by rw [mul_f]; rfl

def rhoJ : Cf q →ₗ[C k q] Ce q := LeftCorner.mulRight (j q) (j_mul_e q)
def rhoX : Ce q →ₗ[C k q] Ce q := LeftCorner.mulRight (x q) (x_mul_e q)
def rhoV : Ce q →ₗ[C k q] Cf q := LeftCorner.mulRight (v q) (v_mul_f q)

lemma rhoJ_cf (a u v n : k) : rhoJ q (cf q a u v n) = ce q 0 0 0 u 0 a := by
  apply Subtype.ext
  ext i
  change mul q ![0,a,0,0,0,u,v,0,0,n] (j q) i = _
  fin_cases i <;> simp [mul, j, ce]

lemma rhoX_ce (a b c d t j : k) : rhoX q (ce q a b c d t j) = ce q 0 a 0 c 0 t := by
  apply Subtype.ext
  ext i
  change mul q ![a,0,b,c,d,0,0,t,j,0] (x q) i = _
  fin_cases i <;> simp [mul, x, ce]

lemma rhoV_ce (a b c d t j : k) : rhoV q (ce q a b c d t j) = cf q 0 0 a 0 := by
  apply Subtype.ext
  ext i
  change mul q ![a,0,b,c,d,0,0,t,j,0] (v q) i = _
  fin_cases i <;> simp [mul, v, cf]

lemma reverseCoeff_nonexceptional (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) (n : ℕ) :
    1 + q^2 * reverseCoeff q (n+1) ≠ 0 := by
  have he : q^2 * reverseCoeff q (n+1) = (q^(n+1))⁻¹ := by
    unfold reverseCoeff
    rw [show n+1+2=2+(n+1) by omega, pow_add, mul_inv_rev]
    field_simp
  rw [he]
  exact one_add_inv_power_ne_zero q hp (n+1) (by omega)

variable [CharP k 2]

omit [CharP k 2] in
lemma comparison_one (hq : q ≠ 0) :
    (rhoEll q (reverseCoeff q 0)).comp (q • rhoX q) = (rhoJ q).comp (rhoU q) := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.map_smul_of_tower,
    ← ce_eta q a, rhoX_ce, rhoEll_ce, LinearMap.comp_apply, rhoU_ce, rhoJ_cf]
  apply Subtype.ext
  ext i
  change q * (ce q 0 0 (reverseCoeff q 0 * 0)
    (q * reverseCoeff q 0 * a.val 0 + 0) 0 ((1 + q^2 * reverseCoeff q 0) * 0)).val i =
    (ce q 0 0 0 (a.val 0) 0 0).val i
  fin_cases i <;> simp [ce, reverseCoeff, hq]
  field_simp

omit [CharP k 2] in
lemma comparison_two :
    (rhoT q).comp (rhoV q) = (q • rhoX q).comp (rhoEll q 1) := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, ← ce_eta q a, rhoV_ce, rhoT_cf,
    LinearMap.comp_apply, LinearMap.smul_apply, rhoEll_ce, rhoX_ce]
  apply Subtype.ext
  ext i
  change (ce q 0 (q * 0) 0 (q * a.val 0) 0 (q * 0)).val i =
    q * (ce q 0 0 0 (1 * a.val 0) 0 0).val i
  fin_cases i <;> simp [ce]

omit [CharP k 2] in
lemma comparison_bottom : (rhoEll q (reverseCoeff q 1)).comp (rhoJ q) = 0 := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, ← cf_eta q a, rhoJ_cf, rhoEll_ce]
  simp [ce_eq_zero]

omit [CharP k 2] in
lemma comparison_top (c : k) : (rhoV q).comp (rhoEll q c) = 0 := by
  apply LinearMap.ext
  intro a
  rw [LinearMap.comp_apply, ← ce_eta q a, rhoEll_ce, rhoV_ce]
  simp [cf_eq_zero]

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
variable {k : Type} [Field k] [CharP k 2] (q : k)

def forwardObj : ℤ → ModuleCat (C k q)
  | .ofNat n => resObj q n
  | .negSucc _ => ModuleCat.of _ PUnit

def forwardD : ∀ j : ℤ, forwardObj q (j+1) ⟶ forwardObj q j
  | .ofNat n => resD q n
  | .negSucc 0 => 0
  | .negSucc (_+1) => 0

def reverseObj : ℤ → ModuleCat (C k q)
  | .ofNat 0 => ModuleCat.of _ (Ce q)
  | .ofNat 1 => ModuleCat.of _ (Ce q)
  | .ofNat 2 => ModuleCat.of _ (Cf q)
  | .ofNat (_+3) => ModuleCat.of _ PUnit
  | .negSucc _ => ModuleCat.of _ (Ce q)

def reverseD : ∀ j : ℤ, reverseObj q (j+1) ⟶ reverseObj q j
  | .ofNat 0 => ModuleCat.ofHom (rhoEll q (reverseCoeff q 0))
  | .ofNat 1 => ModuleCat.ofHom (rhoT q)
  | .ofNat (_+2) => 0
  | .negSucc 0 => ModuleCat.ofHom (rhoEll q (reverseCoeff q 1))
  | .negSucc (n+1) => ModuleCat.ofHom (rhoEll q (reverseCoeff q (n+2)))

def comparisonComponent : ∀ j, forwardObj q j ⟶ reverseObj q j
  | .ofNat 0 => ModuleCat.ofHom (rhoJ q)
  | .ofNat 1 => ModuleCat.ofHom (q • rhoX q)
  | .ofNat 2 => ModuleCat.ofHom (rhoV q)
  | .ofNat (_+3) => 0
  | .negSucc _ => 0

omit [CharP k 2] in
lemma comparison_comm (hq : q ≠ 0) (j : ℤ) :
    comparisonComponent q (j+1) ≫ reverseD q j =
      forwardD q j ≫ comparisonComponent q j := by
  cases j with
  | ofNat n =>
    rcases n with _ | _ | _ | n
    · exact ModuleCat.hom_ext (comparison_one q hq)
    · change ModuleCat.ofHom (rhoV q) ≫ ModuleCat.ofHom (rhoT q) =
        ModuleCat.ofHom (rhoEll q (q^0)) ≫ ModuleCat.ofHom (q • rhoX q)
      simp only [pow_zero]
      exact ModuleCat.hom_ext (comparison_two q)
    · change (0 : ModuleCat.of (C k q) (Ce q) ⟶ ModuleCat.of (C k q) PUnit) ≫ 0 =
        ModuleCat.ofHom (rhoEll q (q^1)) ≫ ModuleCat.ofHom (rhoV q)
      rw [zero_comp]
      exact (ModuleCat.hom_ext (comparison_top q _)).symm
    · change (0 : ModuleCat.of (C k q) (Ce q) ⟶ ModuleCat.of (C k q) PUnit) ≫ 0 = _ ≫ 0
      erw [zero_comp]
  | negSucc n =>
    cases n with
    | zero =>
      change ModuleCat.ofHom (rhoJ q) ≫ ModuleCat.ofHom (rhoEll q (reverseCoeff q 1)) = 0 ≫ 0
      rw [zero_comp]
      exact ModuleCat.hom_ext (comparison_bottom q)
    | succ n =>
      change 0 ≫ _ = 0 ≫ 0
      rw [zero_comp, zero_comp]

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory CategoryTheory.Limits
variable {k : Type} [Field k] [CharP k 2] (q : k)

lemma comparison_injective_cycles (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (x : Cf q) (h : ∃ z : Ce q, rhoEll q (reverseCoeff q 0) z = rhoJ q x) :
    ∃ a : Ce q, rhoU q a = x := by
  obtain ⟨z,hz⟩ := h
  have he := congrArg (fun a : Ce q => a.val 8) hz
  rw [← ce_eta q z, rhoEll_ce, ← cf_eta q x, rhoJ_cf] at he
  change (1 + q^2 * reverseCoeff q 0) * z.val 7 = x.val 1 at he
  have hzero : 1+q^2*reverseCoeff q 0 = 0 := by
    simp [reverseCoeff, hq, CharTwo.add_self_eq_zero]
  rw [hzero, zero_mul] at he
  apply (exact_augmentation q (by simpa only [pow_one] using hp 1 (by omega)) x).mp
  exact he.symm

lemma comparison_surjective_cycles (hq : q ≠ 0)
    (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)
    (y : Ce q) (h : rhoEll q (reverseCoeff q 1) y = 0) :
    ∃ x : Cf q, ∃ z : Ce q, rhoEll q (reverseCoeff q 0) z = rhoJ q x-y := by
  rw [← ce_eta q y, rhoEll_ce, ce_eq_zero] at h
  obtain ⟨_, ha, _, hb, _, ht⟩ := h
  have ht' : y.val 7 = 0 := (mul_eq_zero.mp ht).resolve_left
    (reverseCoeff_nonexceptional q hq hp 0)
  have hc : y.val 3 = reverseCoeff q 0 * y.val 2 := by
    rw [← reverseCoeff_step q hq 0]
    have he := eq_neg_of_add_eq_zero_left hb
    simpa only [CharTwo.neg_eq] using he.symm
  have hy := ce_eta q y
  rw [ha,ht',hc] at hy
  refine ⟨cf q (y.val 8) 0 0 0, ce q (y.val 2) 0 (y.val 4) 0 0 0, ?_⟩
  rw [rhoEll_ce, rhoJ_cf]
  conv_rhs => rw [← hy]
  apply Subtype.ext
  ext i
  change (ce q 0 (y.val 2) (reverseCoeff q 0 * y.val 2)
    (q * reverseCoeff q 0 * 0 + y.val 4) 0 ((1+q^2*reverseCoeff q 0)*0)).val i =
    (ce q 0 0 0 0 0 (y.val 8)).val i -
    (ce q 0 (y.val 2) (reverseCoeff q 0 * y.val 2) (y.val 4) 0 (y.val 8)).val i
  fin_cases i <;> simp [ce, CharTwo.neg_eq]

end Tachikawa.C



end


end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Bimodule
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra



namespace BimoduleTensorHom
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {M : ModuleCat (Enveloping.Alg k S R)} {X : ModuleCat R} {Z : ModuleCat S}

def equiv : (M ⟶ HomBimodule.obj (k := k) X Z) ≃ₗ[k] (Enveloping.evalObj X M ⟶ Z) where
  toFun := uncurry
  invFun := curry
  left_inv := curry_uncurry
  right_inv := uncurry_curry
  map_add' f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    exact HomBimodule.k_smul_apply X Z c (f m) x

lemma uncurry_precompose {N : ModuleCat (Enveloping.Alg k S R)}
    (a : N ⟶ M) (f : M ⟶ HomBimodule.obj (k := k) X Z) :
    uncurry (a ≫ f) = Enveloping.evalMap X a ≫ uncurry f := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  rfl

end BimoduleTensorHom
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
namespace BimoduleTensorHom
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {M : ModuleCat.{0} (Enveloping.Alg k S R)} {X : ModuleCat.{0} R} {Z Z' : ModuleCat.{0} S}

lemma uncurry_postcompose (f : M ⟶ HomBimodule.obj (k := k) X Z) (g : Z ⟶ Z') :
    uncurry (f ≫ HomBimodule.postMap X g) = uncurry f ≫ g := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  rfl

end BimoduleTensorHom
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.C
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k] [CharP k 2] (q : k)

abbrev balancedInducedResolution (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0) :=
  ((AlgebraInduction.functor (TrivialInduction.inclusion (k := k) (R := C k q))).mapHomologicalComplex _).obj
    (projectiveResolution q hp).complex

end Tachikawa.C



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableLift
attribute [-instance] _root_.OAI.Tachikawa.Triangular.instProjectiveCarrierOneFree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.BalancedTensor
variable {k R S M M' N : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k S M'] [IsScalarTower k Rᵐᵒᵖ M'] [SMulCommClass S Rᵐᵒᵖ M']
  [AddCommGroup N] [Module k N] [Module R N]

lemma mapLeft_injective_of_right_split (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (r : M' →ₗ[Rᵐᵒᵖ] M) (hr : ∀ m, r (f m) = m) :
    Function.Injective (mapLeft (k := k) (N := N) f hf) := by
  let g := mapLeft (k := k) (S := k) (N := N) (r.restrictScalars k) r.map_smul
  have hg : ∀ x : T (k := k) (R := R) (S := k) (M := M) (N := N),
      g (mapLeft (k := k) (S := k) (N := N) (f.restrictScalars k) hf x) = x := by
    intro x
    induction x using induction_on with
    | h0 => simp only [map_zero]
    | ht m n => exact congrArg (fun m => mk (k := k) (R := R) (S := k) m n) (hr m)
    | ha x y hx hy => simp only [map_add, hx, hy]
  intro x y h
  apply (restrictEquiv (k := k) (R := R) (S := S)).injective
  have h' := congrArg (restrictEquiv (k := k) (R := R) (S := S)) h
  rw [restrictEquiv_mapLeft, restrictEquiv_mapLeft] at h'
  exact (hg _).symm.trans ((congrArg g h').trans (hg _))

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R S M P Q N : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup P] [Module k P] [Module S P] [Module Rᵐᵒᵖ P]
  [IsScalarTower k S P] [IsScalarTower k Rᵐᵒᵖ P] [SMulCommClass S Rᵐᵒᵖ P]
  [AddCommGroup Q] [Module k Q] [Module S Q] [Module Rᵐᵒᵖ Q]
  [IsScalarTower k S Q] [IsScalarTower k Rᵐᵒᵖ Q] [SMulCommClass S Rᵐᵒᵖ Q]
  [AddCommGroup N] [Module k N] [Module R N]

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ P]
  [SMulCommClass S Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ P] in
lemma mapLeft_surjective (f : M →ₗ[S] P)
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) (hs : Function.Surjective f) :
    Function.Surjective (mapLeft (k := k) (N := N) f hf) := by
  intro x
  induction x using induction_on with
  | h0 => exact ⟨0,map_zero _⟩
  | ht m n =>
    obtain ⟨m',rfl⟩ := hs m
    exact ⟨mk m' n,rfl⟩
  | ha x y hx hy =>
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact ⟨a+b,map_add _ _ _⟩

lemma mapLeft_exact_of_right_splitting (f : M →ₗ[S] P) (g : P →ₗ[S] Q)
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (hg : ∀ (r : Rᵐᵒᵖ) m, g (r • m) = r • g m)
    (r : P →ₗ[Rᵐᵒᵖ] M) (s : Q →ₗ[Rᵐᵒᵖ] P)
    (hid : ∀ p, f (r p) + s (g p) = p) (hz : ∀ m, g (f m) = 0) :
    Function.Exact (mapLeft (k := k) (N := N) f hf) (mapLeft (k := k) (N := N) g hg) := by
  let F := mapLeft (k := k) (S := k) (N := N) (f.restrictScalars k) hf
  let G := mapLeft (k := k) (S := k) (N := N) (g.restrictScalars k) hg
  let Rr := mapLeft (k := k) (S := k) (N := N) (r.restrictScalars k) r.map_smul
  let Ss := mapLeft (k := k) (S := k) (N := N) (s.restrictScalars k) s.map_smul
  have hid' (x : T (k := k) (R := R) (S := k) (M := P) (N := N)) :
      F (Rr x) + Ss (G x) = x := by
    induction x using induction_on with
    | h0 => simp only [map_zero,add_zero]
    | ht p n =>
      change mk (f (r p)) n + mk (s (g p)) n = mk p n
      rw [← LinearMap.add_apply,← map_add,hid]
    | ha x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm,hx,hy]
  have hz' (x : T (k := k) (R := R) (S := S) (M := M) (N := N)) :
      mapLeft (k := k) (N := N) g hg (mapLeft (k := k) (N := N) f hf x) = 0 := by
    induction x using induction_on with
    | h0 => simp only [map_zero]
    | ht m n => change mk (g (f m)) n = 0; rw [hz,map_zero,LinearMap.zero_apply]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
  intro x
  constructor
  · intro hx
    let x' := restrictEquiv (k := k) (R := R) (S := S) x
    have hG : G x' = 0 := by
      simpa only [restrictEquiv_mapLeft,map_zero] using
        congrArg (restrictEquiv (k := k) (R := R) (S := S)) hx
    refine ⟨(restrictEquiv (k := k) (R := R) (S := S)).symm (Rr x'),?_⟩
    apply (restrictEquiv (k := k) (R := R) (S := S)).injective
    rw [restrictEquiv_mapLeft,LinearEquiv.apply_symm_apply]
    have h := hid' x'
    rw [hG,map_zero,add_zero] at h
    exact h
  · rintro ⟨y,rfl⟩
    exact hz' y
end Tachikawa.BalancedTensor



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat.{0} R) {M N : ModuleCat.{0} (Alg k S R)}

lemma evalMap_injective [FiniteDimensional k R] [FiniteDimensional k M]
    [Module.Projective Rᵐᵒᵖ (Obj M)] (t : SymmetrizingForm (k := k) (R := R))
    (f : M ⟶ N) (hf : Function.Injective f) : Function.Injective (evalMap X f) := by
  let : Module.Injective Rᵐᵒᵖ Rᵐᵒᵖ := t.op.injective
  let : Module.Finite Rᵐᵒᵖ (Obj M) := Module.Finite.of_restrictScalars_finite k Rᵐᵒᵖ (Obj M)
  let : Module.Injective Rᵐᵒᵖ (Obj M) := injective_of_finite_projective
  obtain ⟨r,hr⟩ := Module.Injective.extension_property Rᵐᵒᵖ (Obj M) (Obj M) (Obj N)
    (rightMap f) hf LinearMap.id
  exact BalancedTensor.mapLeft_injective_of_right_split (leftMap f) (rightMap f).map_smul r
    (fun m => LinearMap.congr_fun hr m)

end Tachikawa.Enveloping



namespace Tachikawa.BimoduleTensorHom
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]
  (tR : SymmetrizingForm (k := k) (R := R))
  (tS : SymmetrizingForm (k := k) (R := S))
  {M : ModuleCat.{0} (Enveloping.Alg k S R)} {X : ModuleCat.{0} R} {Z : ModuleCat.{0} S}
  [FiniteDimensional k M] [FiniteDimensional k X]

omit [FiniteDimensional k X] in
include tR tS in

lemma factors_of_uncurry [Module.Projective Rᵐᵒᵖ (Enveloping.Obj M)]
    {f : M ⟶ HomBimodule.obj (k := k) X Z}
    (hf : (uncurry f).hom ∈ projectiveFactors (k := k)) :
    f.hom ∈ projectiveFactors (k := k) := by
  obtain ⟨P,hPf,hPp,a,b,hab⟩ := hf
  let := hPf
  let := hPp
  let : Module.Injective S S := tS.injective
  let : Module.Injective S P := injective_of_finite_projective
  let J := ModuleCat.of (Enveloping.Alg k S R)
    (Fin (Module.finrank k M) → Enveloping.Alg k S R)
  let i : M ⟶ J := ModuleCat.ofHom ((tS.tensor tR.op).freeEmbedding (M := M))
  have hi : Function.Injective i := (tS.tensor tR.op).freeEmbedding_injective
  have hei := Enveloping.evalMap_injective X tR i hi
  obtain ⟨a',ha'⟩ := Module.Injective.extension_property S P (Enveloping.evalObj X M)
    (Enveloping.evalObj X J) (Enveloping.evalMap X i).hom hei a
  let ag : Enveloping.evalObj X J ⟶ Z := ModuleCat.ofHom (b.comp a')
  let g : J ⟶ HomBimodule.obj (k := k) X Z := curry ag
  have hcomp : i ≫ g = f := by
    apply (equiv (k := k)).injective
    change uncurry (i ≫ g) = uncurry f
    rw [uncurry_precompose]
    change Enveloping.evalMap X i ≫ uncurry (curry ag) = _
    rw [uncurry_curry]
    apply ModuleCat.hom_ext
    change (b.comp a').comp (Enveloping.evalMap X i).hom = (uncurry f).hom
    rw [LinearMap.comp_assoc, ha', hab]
  exact ⟨J, inferInstance, inferInstance, i.hom, g.hom, ModuleCat.hom_ext_iff.mp hcomp⟩

end Tachikawa.BimoduleTensorHom



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Delta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R)

instance instLinearModuleCatAlgEvaluation : (evaluation (S := S) (k := k) X).Linear k where
  map_smul {M N} f c := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    change BalancedTensor.mk (k := k) (R := R) (S := S) (N := X)
      (leftMap (c • f) m) x = c • BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := X) (leftMap f m) x
    change BalancedTensor.mk (k := k) (R := R) (S := S) (N := X)
      (c • leftMap f m) x = _
    exact congrArg (fun h : X →ₗ[k] evalType X N => h x)
      ((BalancedTensor.mk (k := k) (R := R) (S := S) (M := Obj N) (N := X)).map_smul_of_tower c
        (leftMap f m))

@[simp] lemma evalMap_smul {M N : ModuleCat (Alg k S R)} (c : k) (f : M ⟶ N) :
    evalMap X (c • f) = c • evalMap X f :=
  (evaluation X).map_smul c f

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra

namespace Enveloping
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

variable (U V Y : FiniteModule k (Alg k R S)) (g : U.obj ⟶ Y.obj) (h : V.obj ⟶ Y.obj)

def fiberCover : ModuleCat (Alg k R S) := ModuleCat.of (Alg k R S) (Fin Y.cover.rank → Alg k R S)
def fiberMiddle : ModuleCat (Alg k R S) :=
  ModuleCat.of (Alg k R S) (U.obj × (V.obj × fiberCover Y))

def fiberProjection : fiberMiddle U V Y ⟶ Y.obj :=
  ModuleCat.ofHom (g.hom.coprod (h.hom.coprod Y.cover.map))

end Enveloping
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable (U V Y : FiniteModule k (Alg k R S))

def fiberInl : U.obj ⟶ fiberMiddle U V Y := ModuleCat.ofHom (LinearMap.inl _ _ _)
def fiberInm : V.obj ⟶ fiberMiddle U V Y :=
  ModuleCat.ofHom ((LinearMap.inr _ _ _).comp (LinearMap.inl _ _ _))
def fiberInr : fiberCover Y ⟶ fiberMiddle U V Y :=
  ModuleCat.ofHom ((LinearMap.inr _ _ _).comp (LinearMap.inr _ _ _))
def fiberFst : fiberMiddle U V Y ⟶ U.obj := ModuleCat.ofHom (LinearMap.fst _ _ _)
def fiberSnd : fiberMiddle U V Y ⟶ V.obj :=
  ModuleCat.ofHom ((LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _))

@[simp] lemma fiberInl_fst : fiberInl U V Y ≫ fiberFst U V Y = 𝟙 _ := rfl
@[simp] lemma fiberInl_snd : fiberInl U V Y ≫ fiberSnd U V Y = 0 := rfl
@[simp] lemma fiberInm_fst : fiberInm U V Y ≫ fiberFst U V Y = 0 := rfl
@[simp] lemma fiberInm_snd : fiberInm U V Y ≫ fiberSnd U V Y = 𝟙 _ := rfl
@[simp] lemma fiberInr_fst : fiberInr U V Y ≫ fiberFst U V Y = 0 := rfl
@[simp] lemma fiberInr_snd : fiberInr U V Y ≫ fiberSnd U V Y = 0 := rfl

variable (g : U.obj ⟶ Y.obj) (h : V.obj ⟶ Y.obj)
@[simp] lemma fiberInl_projection : fiberInl U V Y ≫ fiberProjection U V Y g h = g := by
  ext x
  change g x + (h 0 + Y.cover.map 0) = g x
  simp only [map_zero,add_zero]
@[simp] lemma fiberInm_projection : fiberInm U V Y ≫ fiberProjection U V Y g h = h := by
  ext x
  change g 0 + (h x + Y.cover.map 0) = h x
  simp only [map_zero,add_zero,zero_add]
@[simp] lemma fiberInr_projection : fiberInr U V Y ≫ fiberProjection U V Y g h =
    ModuleCat.ofHom Y.cover.map := by
  ext x
  change g 0 + (h 0 + Y.cover.map x) = Y.cover.map x
  simp only [map_zero,zero_add]
end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Triangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def Off (F : ModuleCat (Enveloping.Alg k R R)) : Type := Enveloping.Obj F
instance instAddCommGroupOff (F : ModuleCat (Enveloping.Alg k R R)) : AddCommGroup (Off F) :=
  inferInstanceAs (AddCommGroup (Enveloping.Obj F))
instance instModuleOff (F : ModuleCat (Enveloping.Alg k R R)) : Module k (Off F) :=
  inferInstanceAs (Module k (Enveloping.Obj F))
instance instModuleProdOff (F : ModuleCat (Enveloping.Alg k R R)) : Module (R × R) (Off F) :=
  Module.compHom (Enveloping.Obj F) (RingHom.snd R R)
instance instModuleMulOppositeProdOff (F : ModuleCat (Enveloping.Alg k R R)) : Module (R × R)ᵐᵒᵖ (Off F) :=
  Module.compHom (Enveloping.Obj F) (RingHom.op (RingHom.fst R R))
instance instSMulCommClassProdMulOppositeOff (F : ModuleCat (Enveloping.Alg k R R)) : SMulCommClass (R × R) (R × R)ᵐᵒᵖ (Off F) where
  smul_comm a b x := smul_comm a.2 (MulOpposite.op b.unop.1) (show Enveloping.Obj F from x)
instance instIsScalarTowerProdOff (F : ModuleCat (Enveloping.Alg k R R)) : IsScalarTower k (R × R) (Off F) where
  smul_assoc c a x := smul_assoc c a.2 (show Enveloping.Obj F from x)
instance instIsScalarTowerMulOppositeProdOff (F : ModuleCat (Enveloping.Alg k R R)) : IsScalarTower k (R × R)ᵐᵒᵖ (Off F) where
  smul_assoc c a x := smul_assoc c (MulOpposite.op a.unop.1) (show Enveloping.Obj F from x)

abbrev Alg (F : ModuleCat (Enveloping.Alg k R R)) := TrivSqZeroExt (R × R) (Off F)

variable (F : ModuleCat (Enveloping.Alg k R R))
def upper : Alg F →ₐ[k] R := (AlgHom.fst k R R).comp (TrivSqZeroExt.fstHom k (R × R) (Off F))
def lower : Alg F →ₐ[k] R := (AlgHom.snd k R R).comp (TrivSqZeroExt.fstHom k (R × R) (Off F))

def off : Alg F →ₗ[k] Enveloping.Obj F where
  toFun a := a.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma upper_apply (a : Alg F) : upper F a = a.fst.1 := rfl
@[simp] lemma lower_apply (a : Alg F) : lower F a = a.fst.2 := rfl
@[simp] lemma off_apply (a : Alg F) : off F a = a.snd := rfl

end Tachikawa.Triangular



namespace Tachikawa.BalancedTensor
variable {k R S M N : Type*} [Field k] [Ring R] [Ring S] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [AddCommGroup N] [Module k N] [Module R N]

@[simp] lemma mk_zero_left (n : N) :
    mk (k := k) (R := R) (S := S) (0 : M) n = 0 :=
  congrArg (fun f : N →ₗ[k] T (k := k) (R := R) (S := S) (M := M) (N := N) => f n)
    (map_zero (mk (k := k) (R := R) (S := S)))
@[simp] lemma mk_add_left (a b : M) (n : N) :
    mk (k := k) (R := R) (S := S) (a+b) n = mk a n + mk b n :=
  congrArg (fun f : N →ₗ[k] T (k := k) (R := R) (S := S) (M := M) (N := N) => f n)
    (map_add (mk (k := k) (R := R) (S := S)) a b)
@[simp] lemma mk_smul_left (s : S) (a : M) (n : N) :
    mk (k := k) (R := R) (S := S) (s • a) n = s • mk a n :=
  congrArg (fun f : N →ₗ[k] T (k := k) (R := R) (S := S) (M := M) (N := N) => f n)
    (map_smul (mk (k := k) (R := R) (S := S)) s a)

end Tachikawa.BalancedTensor



end

end OAI
end


