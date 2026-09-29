-- Prove2me | solution 1 for AlgebraicCurve.kw_cart_C_pow_pred_smul_D
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7c1531a2-64bc-5fe0-ba3e-e02ed6e2deb4

import Definitions.Def_AlgebraicGeometry_KwCartierDlogFixednessEngine
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_kw_cart_C_pow_pred_smul_D

set_option autoImplicit false

noncomputable section

open AlgebraicCurve.KwPke AlgebraicCurve.KwCart AlgebraicCurve.KwCfx

namespace CartMintSol

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]
variable (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
  (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
  (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
  (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)

private def CC : Ω[F⁄K] →+ Ω[F⁄K] :=
  AddMonoidHom.mk' (kw_cart_C (K := K) t hdt hspan hsep hdeg)
    (fun ω ω' => kw_cart_C_add t hdt hspan hsep hdeg ω ω')

private theorem CC_apply (ω : Ω[F⁄K]) :
    CC t hdt hspan hsep hdeg ω = kw_cart_C (K := K) t hdt hspan hsep hdeg ω := rfl

private theorem CC_semilinear (a : F) (ω : Ω[F⁄K]) :
    CC t hdt hspan hsep hdeg (a ^ ℓ • ω) = a • CC t hdt hspan hsep hdeg ω :=
  kw_cart_C_semilinear t hdt hspan hsep hdeg a ω

private theorem repr_pow_basis {k : ℕ} (hk : k < ℓ) :
    kw_cart_repr t hsep hdeg (t ^ k)
      = fun j : Fin ℓ => if j = ⟨k, hk⟩ then 1 else 0 := by
  refine kw_cart_repr_unique t hsep hdeg ?_
  rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin ℓ)]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

private theorem repr_pow_top_eq_zero {k : ℕ} (hk : k + 1 < ℓ) :
    kw_cart_repr t hsep hdeg (t ^ k)
      ⟨ℓ - 1, by have := hℓ.out.pos; omega⟩ = 0 := by
  have hklt : k < ℓ := by omega
  rw [repr_pow_basis t hsep hdeg hklt]
  have hne : (⟨ℓ - 1, by have := hℓ.out.pos; omega⟩ : Fin ℓ) ≠ ⟨k, hklt⟩ := by
    intro he
    have hv : ℓ - 1 = k := by injection he
    omega
  exact if_neg hne

private theorem root_zero : kw_cart_root (0 : kw_pke_pthPowers F ℓ) = 0 :=
  kw_cart_root_unique (by simp [zero_pow hℓ.out.ne_zero])

private theorem C_pow_smul_Dt {k : ℕ} (hk : k + 1 < ℓ) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg
      (t ^ k • KaehlerDifferential.D K F t) = 0 := by
  have hcoord : kw_cart_dtCoord t hdt hspan
      (t ^ k • KaehlerDifferential.D K F t) = t ^ k :=
    kw_cart_dtCoord_unique t hdt hspan rfl
  rw [kw_cart_C, hcoord, repr_pow_top_eq_zero t hsep hdeg hk, root_zero, zero_smul]

private theorem C_D_eq_zero (f : F) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg (KaehlerDifferential.D K F f) = 0 := by
  rw [kw_cfx_D_eq t hsep hdeg f, kw_cfx_fstarOf, Finset.sum_smul, ← CC_apply, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · simp [h0]
  · obtain ⟨w, hw⟩ := (kw_pke_mem_pthPowers_iff F ℓ).mp
      (kw_cart_repr t hsep hdeg f i).2
    have hcast : (((i : ℕ) : F)) ^ ℓ = ((i : ℕ) : F) := kw_cfx_t4_natCast_pow (i : ℕ)
    have hsplit : ((i : ℕ) : F) * ((kw_cart_repr t hsep hdeg f i : F))
        * t ^ ((i : ℕ) - 1) = (((i : ℕ) : F) * w) ^ ℓ * t ^ ((i : ℕ) - 1) := by
      rw [mul_pow, hcast, hw]
    have hlt : ((i : ℕ) - 1) + 1 < ℓ := by
      have h2 := i.isLt
      omega
    rw [hsplit, mul_smul, CC_semilinear, CC_apply,
      C_pow_smul_Dt t hdt hspan hsep hdeg hlt, smul_zero]

private theorem C_pow_pred_smul_D (g : F) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg
      (g ^ (ℓ - 1) • KaehlerDifferential.D K F g) = KaehlerDifferential.D K F g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [map_zero, smul_zero, ← CC_apply, map_zero]
  · obtain ⟨q, rfl⟩ : ∃ q, ℓ = q + 1 :=
      ⟨ℓ - 1, by have := hℓ.out.one_lt; omega⟩
    rw [Nat.add_sub_cancel]
    have hkey : g ^ q • KaehlerDifferential.D K F g
        = g ^ (q + 1) • (g⁻¹ • KaehlerDifferential.D K F g) := by
      rw [smul_smul, pow_succ, mul_assoc, mul_inv_cancel₀ hg, mul_one]
    have hfix := kw_cfx_C_dlog_fixed (K := K) t hdt hspan hsep hdeg hg
    rw [AlgebraicCurve.kw_hwcd_dlog] at hfix
    rw [hkey, kw_cart_C_semilinear, hfix, smul_smul, mul_inv_cancel₀ hg, one_smul]

private theorem C_dlog_fixed_all (g : F) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg
      (g⁻¹ • KaehlerDifferential.D K F g) = g⁻¹ • KaehlerDifferential.D K F g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [map_zero, smul_zero, ← CC_apply, map_zero]
  · have h := kw_cfx_C_dlog_fixed (K := K) t hdt hspan hsep hdeg hg
    simpa only [AlgebraicCurve.kw_hwcd_dlog] using h

private theorem C_pow_smul_D_eq_zero (g : F) {i : ℕ} (hi : i + 1 < ℓ) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg
      (g ^ i • KaehlerDifferential.D K F g) = 0 := by
  have hne : ((i + 1 : ℕ) : F) ≠ 0 := by
    intro h0
    have hdvd := (CharP.cast_eq_zero_iff F ℓ (i + 1)).1 h0
    exact absurd (Nat.le_of_dvd (Nat.succ_pos i) hdvd) (not_le.2 hi)
  have hleib : KaehlerDifferential.D K F (g ^ (i + 1))
      = ((i + 1 : ℕ) : F) • (g ^ i • KaehlerDifferential.D K F g) := by
    rw [(KaehlerDifferential.D K F).leibniz_pow g (i + 1), Nat.add_sub_cancel,
      Nat.cast_smul_eq_nsmul]
  have hcp : (((i + 1 : ℕ) : F)⁻¹) ^ ℓ = ((i + 1 : ℕ) : F)⁻¹ := by
    rw [inv_pow, ← frobenius_def, map_natCast]
  have hrew : g ^ i • KaehlerDifferential.D K F g
      = (((i + 1 : ℕ) : F)⁻¹) ^ ℓ • KaehlerDifferential.D K F (g ^ (i + 1)) := by
    rw [hcp, hleib, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hrew, kw_cart_C_semilinear, C_D_eq_zero t hdt hspan hsep hdeg, smul_zero]

private theorem C_digits (g : F) (a : Fin ℓ → F) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg
      ((∑ i : Fin ℓ, a i ^ ℓ * g ^ (i : ℕ)) • KaehlerDifferential.D K F g) =
      a ⟨ℓ - 1, Nat.sub_lt (Fact.out : ℓ.Prime).pos Nat.one_pos⟩ •
        KaehlerDifferential.D K F g := by
  have hp : ℓ.Prime := Fact.out
  rw [Finset.sum_smul, ← CC_apply, map_sum,
    Finset.sum_eq_single (⟨ℓ - 1, Nat.sub_lt hp.pos Nat.one_pos⟩ : Fin ℓ)]
  · rw [mul_smul, CC_semilinear, CC_apply, C_pow_pred_smul_D t hdt hspan hsep hdeg g]
  · intro i _ hi
    have hi' : (i : ℕ) ≠ ℓ - 1 := fun h => hi (Fin.ext h)
    have hlt : (i : ℕ) + 1 < ℓ := by
      have := i.isLt
      omega
    rw [mul_smul, CC_semilinear, CC_apply,
      C_pow_smul_D_eq_zero t hdt hspan hsep hdeg g hlt, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end CartMintSol

theorem solution {K F : Type*} [Field K] [Field F]
    [Algebra K F] {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ] (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F,
      IsSeparable (AlgebraicCurve.KwPke.kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (AlgebraicCurve.KwPke.kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (g : F) :
    AlgebraicCurve.KwCart.kw_cart_C (K := K) t hdt hspan hsep hdeg
      (g ^ (ℓ - 1) • KaehlerDifferential.D K F g) = KaehlerDifferential.D K F g :=
  CartMintSol.C_pow_pred_smul_D t hdt hspan hsep hdeg g

end
end S_AlgebraicCurve_kw_cart_C_pow_pred_smul_D
end P2MW
export P2MW.S_AlgebraicCurve_kw_cart_C_pow_pred_smul_D (solution)
