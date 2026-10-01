-- Prove2me | solution 1 for AlonMilman.Diameter.rayleigh_eq_2_1
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:36:39.198435+00:00
-- url     : https://prove2.me/submissions/2705caab-b269-47a5-8b7e-6eb19560d47e

import Definitions.Def_AlonMilman_Diameter_lambda1
import Mathlib.Tactic

open Matrix Finset WithLp
open scoped InnerProductSpace

namespace AlonProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable abbrev ev := (G.isHermitian_lapMatrix ℝ).eigenvalues₀
noncomputable abbrev basis :=
  (isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis
    finrank_euclideanSpace

theorem ev_nonneg (i : Fin (Fintype.card V)) : 0 ≤ ev G i := by
  have h := (G.posSemidef_lapMatrix ℝ).eigenvalues_nonneg
    ((Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card V) ≃ V) i)
  simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h

theorem eigen (i : Fin (Fintype.card V)) :
    G.lapMatrix ℝ *ᵥ ⇑(basis G i) = ev G i • ⇑(basis G i) := by
  have h := (isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).apply_eigenvectorBasis
    finrank_euclideanSpace i
  exact congrArg (fun x : EuclideanSpace ℝ V => (x : V → ℝ)) h

theorem last_zero (hn : 2 ≤ Fintype.card V) :
    ev G ⟨Fintype.card V - 1, by omega⟩ = 0 := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hd := G.det_lapMatrix_eq_zero
  rw [(G.isHermitian_lapMatrix ℝ).det_eq_prod_eigenvalues] at hd
  obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hd
  apply le_antisymm _ (ev_nonneg G _)
  let i := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card V) ≃ V).symm v
  have hi : ev G i = 0 := hv
  rw [← hi]
  apply (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone
  apply Fin.le_iff_val_le_val.mpr
  change i.val ≤ Fintype.card V - 1
  have := i.isLt
  omega

theorem constant_of_zero (hG : G.Connected) (i : Fin (Fintype.card V)) (hi : ev G i = 0)
    (u v : V) : basis G i u = basis G i v := by
  have h := eigen G i
  rw [hi,zero_smul] at h
  exact (G.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp h) u v (hG.preconnected u v)

theorem zero_unique (hG : G.Connected) (i j : Fin (Fintype.card V))
    (hi : ev G i = 0) (hj : ev G j = 0) : i = j := by
  by_contra hij
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.arbitrary V
  have hnormi := (basis G).inner_eq_one i
  have hnormj := (basis G).inner_eq_one j
  have horth := (basis G).inner_eq_zero hij
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct] at *
  have hi' : ∀ u, basis G i u = basis G i v := fun u => constant_of_zero G hG i hi u v
  have hj' : ∀ u, basis G j u = basis G j v := fun u => constant_of_zero G hG j hj u v
  simp_rw [hi',hj',sum_const,card_univ,nsmul_eq_mul] at hnormi hnormj horth
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (show Fintype.card V ≠ 0 by omega)
  have hvi : basis G i v ≠ 0 := by intro h; rw [h] at hnormi; simp at hnormi
  have hvj : basis G j v ≠ 0 := by intro h; rw [h] at hnormj; simp at hnormj
  exact (mul_ne_zero hn (mul_ne_zero hvj hvi)) horth

theorem gap_pos (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    0 < AlonMilman.Diameter.lambda1 G := by
  rw [AlonMilman.Diameter.lambda1, dif_pos hn]
  apply lt_of_le_of_ne (ev_nonneg G _) (Ne.symm _)
  intro h
  have hh := zero_unique G hG ⟨Fintype.card V - 2, by omega⟩
    ⟨Fintype.card V - 1, by omega⟩ h (last_zero G hn)
  have := congrArg Fin.val hh
  change Fintype.card V - 2 = Fintype.card V - 1 at this
  omega

theorem last_coeff_zero (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (f : V → ℝ) (hf : ∑ v, f v = 0) :
    (basis G).repr (toLp 2 f) ⟨Fintype.card V - 1, by omega⟩ = 0 := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.arbitrary V
  rw [OrthonormalBasis.repr_apply_apply,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct]
  simp_rw [constant_of_zero G hG _ (last_zero G hn) _ v]
  rw [← Finset.sum_mul,hf,zero_mul]

theorem parseval (x y : EuclideanSpace ℝ V) :
    ∑ i, (basis G).repr x i * (basis G).repr y i =
      (x : V → ℝ) ⬝ᵥ (y : V → ℝ) := by
  have h := (basis G).repr.inner_map_map x y
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,mul_comm] using h

theorem repr_mul (f : V → ℝ) (i : Fin (Fintype.card V)) :
    (basis G).repr (toLp 2 (G.lapMatrix ℝ *ᵥ f)) i =
      ev G i * (basis G).repr (toLp 2 f) i := by
  exact (isSymmetric_toEuclideanLin_iff.mpr (G.isHermitian_lapMatrix ℝ)).eigenvectorBasis_apply_self_apply
    finrank_euclideanSpace (toLp 2 f) i

theorem rayleigh (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (f : V → ℝ) (hf : ∑ v, f v = 0) :
    AlonMilman.Diameter.lambda1 G * (f ⬝ᵥ f) ≤ f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) := by
  let c := (basis G).repr (toLp 2 f)
  have hc := last_coeff_zero G hG hn f hf
  change c ⟨Fintype.card V - 1, by omega⟩ = 0 at hc
  have hnrm := parseval G (toLp 2 f) (toLp 2 f)
  have hq := parseval G (toLp 2 f) (toLp 2 (G.lapMatrix ℝ *ᵥ f))
  simp only [repr_mul] at hq
  change ∑ i, c i * c i = f ⬝ᵥ f at hnrm
  change ∑ i, c i * (ev G i * c i) = f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) at hq
  rw [← hnrm, ← hq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases he : i = ⟨Fintype.card V - 1, by omega⟩
  · subst i
    rw [hc]
    simp
  · have hle : i ≤ (⟨Fintype.card V - 2, by omega⟩ : Fin (Fintype.card V)) := by
      apply Fin.le_iff_val_le_val.mpr
      change i.val ≤ Fintype.card V - 2
      have hiLt := i.isLt
      have hv : i.val ≠ Fintype.card V - 1 := fun h => he (Fin.ext h)
      omega
    have hge := (G.isHermitian_lapMatrix ℝ).eigenvalues₀_antitone hle
    rw [AlonMilman.Diameter.lambda1, dif_pos hn]
    nlinarith [sq_nonneg (c i),mul_nonneg (sub_nonneg.mpr hge) (sq_nonneg (c i))]
end AlonProof

open AlonMilman.Diameter

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (f : V → ℝ) (hf : ∑ v, f v = 0) :
    lambda1 G * (f ⬝ᵥ f) ≤ f ⬝ᵥ (G.lapMatrix ℝ *ᵥ f) := by
  exact AlonProof.rayleigh G hG hn f hf


