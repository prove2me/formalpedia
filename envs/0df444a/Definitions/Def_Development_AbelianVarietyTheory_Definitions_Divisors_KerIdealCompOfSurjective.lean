-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:31:04.795595+00:00
-- url     : https://prove2.me/theorems/d725b797-d01d-49fa-aabc-76eb7169e656
-- title:
--   Ker Ideal Comp Of Surjective
-- statement:
--   Definitions and structural lemmas for Ker Ideal Comp Of Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_map_comp
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply


set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv
namespace GlobalTheory.PDiv
section Conv
variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
section Points
variable [Bialgebra R A] [Bialgebra R C] [Algebra R B] [Algebra R D]
def pointsMap (B : Type*) [CommRing B] [Algebra R B] (f : C →ₐc[R] A) :
    WithConv (A →ₐ[R] B) →* WithConv (C →ₐ[R] B) where
  toFun x := toConv (x.ofConv.comp (f : C →ₐ[R] A))
  map_one' := by ext c; simp
  map_mul' x y := congrArg toConv (AlgHom.convMul_comp_bialgHom_distrib x y f)
@[simp] theorem ptsMap_ofConv (f : C →ₐc[R] A) (x : WithConv (A →ₐ[R] B)) :
    (pointsMap B f x).ofConv = x.ofConv.comp (f : C →ₐ[R] A) := rfl
def ptsPush (A : Type*) [CommRing A] [Bialgebra R A] (g : B →ₐ[R] D) :
    WithConv (A →ₐ[R] B) →* WithConv (A →ₐ[R] D) where
  toFun x := toConv (g.comp x.ofConv)
  map_one' := by ext c; simp
  map_mul' x y := congrArg toConv (AlgHom.comp_convMul_distrib g x y)
@[simp] theorem ptsPush_ofConv (g : B →ₐ[R] D) (x : WithConv (A →ₐ[R] B)) :
    (ptsPush A g x).ofConv = g.comp x.ofConv := rfl
end Points
variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]
def toPts [IsCocomm R C] : WithConv (C →ₐc[R] A) →* WithConv (C →ₐ[R] A) where
  toFun f := toConv (f.ofConv : C →ₐ[R] A)
  map_one' := rfl
  map_mul' _ _ := rfl
@[simp] theorem toPts_ofConv [IsCocomm R C] (f : WithConv (C →ₐc[R] A)) :
    (toPts f).ofConv = (f.ofConv : C →ₐ[R] A) := rfl
theorem toPts_injective [IsCocomm R C] :
    Function.Injective (toPts : WithConv (C →ₐc[R] A) → _) := fun _ _ h =>
  ofConv_injective (BialgHom.coe_toAlgHom_injective (congrArg ofConv h))
def precomp [IsCocomm R C] [IsCocomm R D] (A : Type*) [CommRing A] [Bialgebra R A]
    (h : D →ₐc[R] C) : WithConv (C →ₐc[R] A) →* WithConv (D →ₐc[R] A) where
  toFun f := toConv (f.ofConv.comp h)
  map_one' := toPts_injective (map_one (pointsMap A h))
  map_mul' f g := toPts_injective (map_mul (pointsMap A h) (toPts f) (toPts g))
@[simp] theorem precomp_ofConv [IsCocomm R C] [IsCocomm R D] (h : D →ₐc[R] C)
    (f : WithConv (C →ₐc[R] A)) : (precomp A h f).ofConv = f.ofConv.comp h := rfl
def postcomp (C : Type*) [CommRing C] [Bialgebra R C] [IsCocomm R C] (h : A →ₐc[R] B) :
    WithConv (C →ₐc[R] A) →* WithConv (C →ₐc[R] B) where
  toFun f := toConv (h.comp f.ofConv)
  map_one' := toPts_injective (map_one (ptsPush C (h : A →ₐ[R] B)))
  map_mul' f g := toPts_injective (map_mul (ptsPush C (h : A →ₐ[R] B)) (toPts f) (toPts g))
@[simp] theorem postcomp_ofConv [IsCocomm R C] (h : A →ₐc[R] B)
    (f : WithConv (C →ₐc[R] A)) : (postcomp C h f).ofConv = h.comp f.ofConv := rfl
variable (R A) in

def mulBy [IsCocomm R A] (n : ℕ) : A →ₐc[R] A := (toConv (BialgHom.id R A) ^ n).ofConv
variable (R A) in

abbrev augIdeal : Ideal A := RingHom.ker (counitAlgHom R A)
abbrev kerIdeal (f : C →ₐc[R] A) : Ideal A := Ideal.map (f : C →ₐ[R] A) (augIdeal R C)
variable (R A) in

abbrev torsionIdeal [IsCocomm R A] (n : ℕ) : Ideal A := kerIdeal (mulBy R A n)
def liftSurj (i : A →ₐc[R] B) (hi : Function.Surjective i) (f : A →ₐc[R] C)
    (h : RingHom.ker i ≤ RingHom.ker f) : B →ₐc[R] C :=
  .ofAlgHom (AlgHom.liftOfSurjective (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h)
    (AlgHom.ext fun b => by
      obtain ⟨a, rfl⟩ := hi b
      have := AlgHom.liftOfSurjective_apply (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h a
      simp at this
      simp [this])
    (AlgHom.ext fun b => by
      obtain ⟨a, rfl⟩ := hi b
      have h1 := AlgHom.liftOfSurjective_comp (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h
      have h2 := AlgHom.liftOfSurjective_apply (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h a
      have h3 := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom i) a
      have h4 := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom f) a
      generalize AlgHom.liftOfSurjective (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h = g at h1 h2 ⊢
      change Algebra.TensorProduct.map g g ((comulAlgHom R B).comp (i : A →ₐ[R] B) a) =
        comulAlgHom R C (g ((i : A →ₐ[R] B) a))
      rw [h2]
      refine (congrArg (Algebra.TensorProduct.map g g) h3).symm.trans (Eq.trans ?_ h4)
      change Algebra.TensorProduct.map g g (Algebra.TensorProduct.map (i : A →ₐ[R] B)
        (i : A →ₐ[R] B) (comulAlgHom R A a)) = _
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, h1]
      rfl)
@[simp] theorem liftSurj_apply (i : A →ₐc[R] B) (hi : Function.Surjective i) (f : A →ₐc[R] C)
    (h : RingHom.ker i ≤ RingHom.ker f) (a : A) : liftSurj i hi f h (i a) = f a :=
  AlgHom.liftOfSurjective_apply (i : A →ₐ[R] B) hi (f : A →ₐ[R] C) h a
variable (R A) in

abbrev Cot : Type _ := AugCot (counitAlgHom R A)
variable (R) in

abbrev dUnit (a : A) : Cot R A := AugCot.d (counitAlgHom R A) a
def cotMap (f : C →ₐc[R] A) : Cot R C →ₗ[R] Cot R A :=
  AugCot.map (f : C →ₐ[R] A) (BialgHomClass.counitAlgHom_comp f)
@[simp] theorem cotMap_d (f : C →ₐc[R] A) (c : C) : cotMap f (dUnit R c) = dUnit R (f c) :=
  AugCot.map_d _ _ c
@[simp] theorem cotMap_id : cotMap (BialgHom.id R A) = LinearMap.id :=
  AugCot.hom_ext fun c => by simp
section Dual
variable [Module.Finite R A] [Module.Projective R A] [Module.Finite R C] [Module.Projective R C]
  [IsCocomm R A] [IsCocomm R C]
variable (R A C) in

def dualMonoidHom :
    WithConv (C →ₐc[R] A) →* WithConv (CartierDual R A →ₐc[R] CartierDual R C) where
  toFun f := toConv (CartierDual.map f.ofConv)
  map_one' := ofConv_injective <| BialgHom.ext fun φ => CartierDual.ext_apply fun c => by
    change φ.ofConv (algebraMap R A (counit c)) = (algebraMap R (CartierDual R C) (φ.ofConv 1)) c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul]
    change _ = φ.ofConv 1 * counit c
    rw [smul_eq_mul, mul_comm]
  map_mul' f g := ofConv_injective <| BialgHom.ext fun φ => CartierDual.ext_apply fun c => by
    have r := Coalgebra.Repr.arbitrary R c
    have h : (f * g).ofConv c = ∑ i ∈ r.index, f.ofConv (r.left i) * g.ofConv (r.right i) :=
      r.convMul_apply (toConv f.ofConv.toLinearMap) (toConv g.ofConv.toLinearMap)
    change φ.ofConv ((f * g).ofConv c) = (LinearMap.mul' R _ (TensorProduct.map
      (CartierDual.transpose f.ofConv.toLinearMap) (CartierDual.transpose g.ofConv.toLinearMap)
      (comul φ))) c
    rw [CartierDual.mul'_apply, CartierDual.pair_map_transpose, h, ← r.eq]
    simp only [map_sum, TensorProduct.map_tmul, CartierDual.pair_comul_tmul]
    rfl
omit [IsCocomm R A] in

@[simp] theorem dualMonoidHom_ofConv (f : WithConv (C →ₐc[R] A)) :
    (dualMonoidHom R A C f).ofConv = CartierDual.map f.ofConv := rfl
end Dual
end Conv
section Mu
variable (R : Type*) [CommRing R] (m : ℕ)
def muT : AddMonoidAlgebra R (ZMod m) := AddMonoidAlgebra.single 1 1
theorem isGroupLikeElem_muT : IsGroupLikeElem R (muT R m) :=
  AddMonoidAlgebra.isGroupLikeElem_single_one _
theorem muT_pow (k : ℕ) : muT R m ^ k = AddMonoidAlgebra.single (k : ZMod m) 1 := by
  simp [muT, AddMonoidAlgebra.single_pow]
variable {R m} [NeZero m] {B : Type*} [CommRing B] [Algebra R B]
theorem mu_algHom_ext {x y : AddMonoidAlgebra R (ZMod m) →ₐ[R] B}
    (h : x (muT R m) = y (muT R m)) : x = y :=
  AddMonoidAlgebra.algHom_ext (fun k => by
    rw [← ZMod.natCast_zmod_val k, ← muT_pow R m, map_pow, map_pow, h]) (Subsingleton.elim _ _)
variable (R) in

def muPoint (u : B) (hu : u ^ m = 1) : AddMonoidAlgebra R (ZMod m) →ₐ[R] B :=
  AddMonoidAlgebra.lift R B (ZMod m)
    { toFun := fun k => u ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun k l => by
        rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hu, pow_add] }
theorem muPoint_single (u : B) (hu : u ^ m = 1) (k : ZMod m) :
    muPoint R u hu (AddMonoidAlgebra.single k 1) = u ^ k.val := by
  simp [muPoint]
@[simp] theorem muPoint_muT (u : B) (hu : u ^ m = 1) : muPoint R u hu (muT R m) = u := by
  have h : (1 : ZMod m).val = 1 % m := by rw [← ZMod.val_natCast, Nat.cast_one]
  rw [muT, muPoint_single, h, ← pow_eq_pow_mod _ hu, pow_one]
def muChar {A : Type*} [CommRing A] [Bialgebra R A] (u : A) (hg : IsGroupLikeElem R u)
    (hu : u ^ m = 1) : AddMonoidAlgebra R (ZMod m) →ₐc[R] A :=
  .ofAlgHom (muPoint R u hu)
    (mu_algHom_ext (by simp [hg.counit_eq_one, (isGroupLikeElem_muT R m).counit_eq_one]))
    (mu_algHom_ext (by
      simp [hg.comul_eq_tmul_self, (isGroupLikeElem_muT R m).comul_eq_tmul_self]))
end Mu
section PPow
variable {p : ℕ} [Fact p.Prime] {M : Type*} [Monoid M]
def digit (n : ℕ) (a : ℤ_[p]) : ℕ := (PadicInt.toZModPow n a).val
end PPow
end GlobalTheory.PDiv


