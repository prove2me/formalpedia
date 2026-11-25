-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:51.187619+00:00
-- url     : https://prove2.me/theorems/ab88b9b9-cc3a-4e16-836a-8f67352fbc65
-- title:
--   Padic Action Const Injective
-- statement:
--   Definitions and structural lemmas for Padic Action Const Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PadicActionConstInjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_map_surjective
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_map
import Theorems.Thm_GlobalTheory_PDivGroup_exists_comp_res_iff
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_kerIdeal_le_ker_iff
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
import Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_ker_iff
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
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT


set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
namespace GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]
@[reducible] def triv (p : ℕ) (O : Type) [CommRing O] : PDivGroup p O where
  height := 0
  A _ := O
  rank_eq n q := by
    have := q.nontrivial
    simp [rankAtStalk_eq_finrank_of_free]
  res _ := BialgHom.id O O
  res_surjective _ := Function.surjective_id
  ker_res n := by
    refine le_antisymm (fun a ha => ?_) ?_
    · rw [show a = 0 from ha]; exact zero_mem _
    · refine (kerIdeal_le_ker_iff _ (AlgHom.id O O)).2 fun c => ?_
      simpa using (mulBy O O (p ^ n) : O →ₐ[O] O).commutes c
example [Fact p.Prime] {G : PDivGroup p O} {Λ : Type} [Ring Λ] (ρ : Action Λ G) (a b : Λ)
    (t : G.Tate) : ρ.onTate O (a * b) t = ρ.onTate O a (ρ.onTate O b t) := by
  rw [map_mul]; rfl
section Prod
variable (A B : Type) [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]
def inl : A →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (BialgHom.id O A) (Bialgebra.unitBialgHom O B)).comp
    (Bialgebra.TensorProduct.rid O O A).symm.toBialgHom
def inr : B →ₐc[O] A ⊗[O] B :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom O A) (BialgHom.id O B)).comp
    (Bialgebra.TensorProduct.lid O B).symm.toBialgHom
variable {A B}
theorem inl_apply (a : A) : inl (O := O) A B a = a ⊗ₜ 1 :=
  congrArg (fun y : B => a ⊗ₜ[O] y) (map_one (Bialgebra.unitBialgHom O B))
theorem inr_apply (b : B) : inr (O := O) A B b = 1 ⊗ₜ b :=
  congrArg (fun y : A => y ⊗ₜ[O] b) (map_one (Bialgebra.unitBialgHom O A))
theorem pts_ext {E : Type} [CommRing E] [Algebra O E] {x y : WithConv (A ⊗[O] B →ₐ[O] E)}
    (h1 : pointsMap E (inl A B) x = pointsMap E (inl A B) y)
    (h2 : pointsMap E (inr A B) x = pointsMap E (inr A B) y) : x = y := by
  refine ofConv_injective (Algebra.TensorProduct.ext' fun a b => ?_)
  have e1 : x.ofConv (inl A B a) = y.ofConv (inl A B a) := DFunLike.congr_fun (congrArg ofConv h1) a
  have e2 : x.ofConv (inr A B b) = y.ofConv (inr A B b) := DFunLike.congr_fun (congrArg ofConv h2) b
  have e : a ⊗ₜ[O] b = inl A B a * inr A B b := by simp [inl_apply, inr_apply]
  rw [e, map_mul, map_mul, e1, e2]
end Prod
@[reducible] def prod (G H : PDivGroup p O) : PDivGroup p O where
  height := G.height + H.height
  A n := G.A n ⊗[O] H.A n
  rank_eq n q := by
    rw [rankAtStalk_tensorProduct, Pi.mul_apply, G.rank_eq, H.rank_eq, mul_add, pow_add]
  res n := Bialgebra.TensorProduct.map (G.res n) (H.res n)
  res_surjective n := TensorProduct.map_surjective (g := (G.res n).toLinearMap) (g' := (H.res n).toLinearMap) (G.res_surjective n) (H.res_surjective n)
  ker_res n := by
    refine le_antisymm (fun a ha => ?_) ?_
    · let π := Ideal.Quotient.mkₐ O (torsionIdeal O (G.A (n + 1) ⊗[O] H.A (n + 1)) (p ^ n))
      have h1 := (torsionIdeal_le_ker_iff (p ^ n) π).1
        fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
      obtain ⟨y, hy⟩ := (G.exists_comp_res_iff n (pointsMap _ (inl _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      obtain ⟨z, hz⟩ := (H.exists_comp_res_iff n (pointsMap _ (inr _ _) (toConv π)).ofConv).2
        (by rw [toConv_ofConv, ← map_pow, h1, map_one])
      have h2 : (Algebra.TensorProduct.lift y z fun _ _ => .all _ _).comp
          (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
            G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n) = π :=
        Algebra.TensorProduct.ext' fun a b => by
          have e1 : y (G.res n a) = π (inl _ _ a) := DFunLike.congr_fun hy a
          have e2 : z (H.res n b) = π (inr _ _ b) := DFunLike.congr_fun hz b
          change y (G.res n a) * z (H.res n b) = _
          rw [e1, e2, ← map_mul, inl_apply, inr_apply]
          simp
      have h3 := (DFunLike.congr_fun h2 a).symm
      rw [AlgHom.comp_apply] at h3
      erw [show Bialgebra.TensorProduct.map (G.res n) (H.res n) a = 0 from ha, map_zero] at h3
      exact Ideal.Quotient.eq_zero_iff_mem.1 h3
    · refine (torsionIdeal_le_ker_iff (p ^ n) (Bialgebra.TensorProduct.map (G.res n) (H.res n) :
          G.A (n + 1) ⊗[O] H.A (n + 1) →ₐ[O] G.A n ⊗[O] H.A n)).2 (pts_ext ?_ ?_)
      · rw [map_pow, map_one]
        refine (G.exists_comp_res_iff n _).1 ⟨(inl (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inl _ _ (G.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inl _ _ a)
        simp [inl_apply]
      · rw [map_pow, map_one]
        refine (H.exists_comp_res_iff n _).1 ⟨(inr (O := O) (G.A n) (H.A n)).toAlgHom, AlgHom.ext fun a => ?_⟩
        change inr _ _ (H.res n a) = Bialgebra.TensorProduct.map (G.res n) (H.res n) (inr _ _ a)
        simp [inr_apply]
def swap (G : PDivGroup p O) : End (prod G G) :=
  ⟨fun n => (Bialgebra.TensorProduct.comm O (G.A n) (G.A n)).toBialgHom, fun n =>
    BialgHom.coe_toAlgHom_injective (Algebra.TensorProduct.ext' fun _ _ => rfl)⟩
def fst (G H : PDivGroup p O) : prod G H ⟶ G :=
  ⟨fun _ => inl _ _, fun n => BialgHom.ext fun a => by
    change Bialgebra.TensorProduct.map (G.res n) (H.res n) (inl _ _ a) = inl _ _ (G.res n a)
    simp [inl_apply]⟩
def incl (G H : PDivGroup p O) : G ⟶ prod G H :=
  ⟨fun n => (Bialgebra.TensorProduct.rid O O (G.A n)).toBialgHom.comp
      (Bialgebra.TensorProduct.map (BialgHom.id O _) (Bialgebra.counitBialgHom O _)),
    fun n => BialgHom.coe_toAlgHom_injective (Algebra.TensorProduct.ext' fun a b => by
      change G.res n (counit (R := O) b • a) = counit (R := O) (H.res n b) • G.res n a
      rw [map_smul, CoalgHomClass.counit_comp_apply])⟩
def swapAction [Fact p.Prime] (G : PDivGroup p O) : Action (Polynomial ℤ_[p]) (prod G G) :=
  (Polynomial.aeval (swap G)).toRingHom
example [Fact p.Prime] : (prod (mu p O) (const p O)).height = 2 := rfl
end GlobalTheory.PDivGroup.Test


