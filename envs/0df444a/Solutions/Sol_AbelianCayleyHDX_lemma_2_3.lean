-- Prove2me | solution 1 for AbelianCayleyHDX.lemma_2_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:38:37.501186+00:00
-- url     : https://prove2.me/submissions/562bbd0b-e30a-469f-b0ac-8e58f377cad9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AbelianCayleyHDX_lemma_3_2
import Theorems.Thm_AbelianCayleyHDX_lemma_3_5
import Theorems.Thm_AbelianCayleyHDX_lemma_3_6
import Theorems.Thm_AbelianCayleyHDX_lemma_3_7
import Theorems.Thm_AbelianCayleyHDX_explicit_HD_matrices
import Definitions.Def_AbelianCayleyHDX_IsGoodRelationMatrix
import Definitions.Def_AbelianCayleyHDX_kerF2
import Definitions.Def_AbelianCayleyHDX_PH
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
open Filter RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.Spec

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If a real symmetric matrix fixes the constants and all its mean-zero eigenvectors have
eigenvalues in `[-λ, λ]`, then it has norm at most `λ` on mean-zero vectors. -/
theorem norm_le_of_eig (P : Matrix ι ι ℝ) (hsym : Pᵀ = P) (h1 : P *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (heig : ∀ (μ : ℝ) (f : ι → ℝ), f ≠ 0 → ∑ i, f i = 0 → P *ᵥ f = μ • f → |μ| ≤ lam)
    (f : ι → ℝ) (hf : ∑ i, f i = 0) :
    Real.sqrt (∑ i, (P *ᵥ f) i ^ 2) ≤ lam * Real.sqrt (∑ i, f i ^ 2) := by
  have hH : P.IsHermitian := by
    unfold Matrix.IsHermitian; rw [conjTranspose_eq_transpose_of_trivial]; exact hsym
  set b := hH.eigenvectorBasis
  set μ := hH.eigenvalues
  -- coordinates in the eigenbasis
  set c : ι → ℝ := fun k => ∑ i, b k i * f i with hc
  have hb : ∀ k, P *ᵥ ⇑(b k) = μ k • ⇑(b k) := fun k => hH.mulVec_eigenvectorBasis k
  -- dot products
  have hsymdot : ∀ u v : ι → ℝ, (P *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (P *ᵥ v) := by
    intro u v
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]
  -- Parseval in the eigenbasis
  have hpars : ∀ g : ι → ℝ, ∑ i, g i ^ 2 = ∑ k, (∑ i, b k i * g i) ^ 2 := by
    intro g
    have := b.sum_sq_norm_inner_right (WithLp.toLp 2 g)
    simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] at this
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [mul_comm]
  have hcoef : ∀ k, ∑ i, b k i * (P *ᵥ f) i = μ k * c k := by
    intro k
    have := hsymdot (⇑(b k)) f
    rw [hb k] at this
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [hc]; simp only
    rw [Finset.mul_sum, ← this]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have key : ∀ k, (μ k * c k) ^ 2 ≤ lam ^ 2 * c k ^ 2 := by
    intro k
    by_cases hck : c k = 0
    · simp [hck]
    have hbk0 : (⇑(b k) : ι → ℝ) ≠ 0 := by
      intro h; apply hck; simp [hc, h]
    suffices hμ : |μ k| ≤ lam by
      rw [mul_pow]
      have : μ k ^ 2 ≤ lam ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hμ 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    -- the mean of `b k`
    set m : ℝ := (∑ i, b k i) / Fintype.card ι
    have hcard : (0 : ℝ) < Fintype.card ι := by
      have : Nonempty ι := by
        by_contra hne; rw [not_nonempty_iff] at hne
        apply hbk0; funext i; exact (IsEmpty.false i).elim
      exact_mod_cast Fintype.card_pos
    by_cases hμ1 : μ k = 1
    · -- the mean-zero part of `b k` is fixed by `P`
      set w : ι → ℝ := fun i => b k i - m
      have hw : P *ᵥ w = (1 : ℝ) • w := by
        have : w = ⇑(b k) - m • (fun _ => (1 : ℝ)) := by
          funext i; simp [w]
        rw [this, Matrix.mulVec_sub, Matrix.mulVec_smul, hb k, h1, hμ1, one_smul, one_smul]
      have hwsum : ∑ i, w i = 0 := by
        simp only [w, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [m]; field_simp; ring
      by_cases hw0 : w = 0
      · exfalso; apply hck
        have : ∀ i, b k i = m := by
          intro i; have := congrFun hw0 i; simp only [w, Pi.zero_apply] at this; linarith
        simp only [hc, this, ← Finset.mul_sum, hf, mul_zero]
      · have := heig 1 w hw0 hwsum hw
        rw [hμ1]; simpa using this
    · -- `b k` is orthogonal to the constants
      have hsum0 : ∑ i, b k i = 0 := by
        have := hsymdot (⇑(b k)) (fun _ => 1)
        rw [hb k, h1] at this
        simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_one] at this
        rw [← Finset.mul_sum] at this
        have h' : (μ k - 1) * ∑ i, b k i = 0 := by linarith
        rcases mul_eq_zero.1 h' with h'' | h''
        · exact absurd (by linarith) hμ1
        · exact h''
      exact heig (μ k) (⇑(b k)) hbk0 hsum0 (hb k)
  have hsq : ∑ i, (P *ᵥ f) i ^ 2 ≤ lam ^ 2 * ∑ i, f i ^ 2 := by
    rw [hpars (P *ᵥ f), hpars f, Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [hcoef k]; exact key k
  calc Real.sqrt (∑ i, (P *ᵥ f) i ^ 2) ≤ Real.sqrt (lam ^ 2 * ∑ i, f i ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = lam * Real.sqrt (∑ i, f i ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlam]

end AbelianCayleyHDX.Spec

namespace AbelianCayleyHDX.R23

open Finset

lemma charP_two_of_card {F : Type*} [Field F] [Fintype F] (h : ℕ) (hh : 1 ≤ h)
    (hF : Fintype.card F = (2 ^ h) ^ 2) : CharP F 2 := by
  have h0 : ((Fintype.card F : ℕ) : F) = 0 := FiniteField.cast_card_eq_zero F
  rw [hF] at h0
  push_cast at h0
  have h2 : (2 : F) = 0 := by
    rw [← pow_mul] at h0
    exact pow_eq_zero_iff (by omega) |>.1 h0
  exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2

section Dhat
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {t : ℕ} (D : Finset (PG t F))

lemma mem_Dhat {b : Fin t → F} : b ∈ Dhat D ↔ ∃ hb : b ≠ 0, Projectivization.mk F b hb ∈ D := by
  classical
  simp [Dhat]

lemma Dhat_eq : Dhat D = D.biUnion (fun d => Finset.univ.image fun u : Fˣ => (u : F) • d.rep) := by
  ext b
  rw [mem_Dhat, Finset.mem_biUnion]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hb0, hbD⟩
    refine ⟨_, hbD, ?_⟩
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F b hb0
    refine ⟨a⁻¹, ?_⟩
    rw [← ha, Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul]
  · rintro ⟨d, hd, u, rfl⟩
    have h0 : (u : F) • d.rep ≠ 0 := smul_ne_zero u.ne_zero d.rep_nonzero
    refine ⟨h0, ?_⟩
    have : Projectivization.mk F ((u : F) • d.rep) h0 = d := by
      have := (Projectivization.mk_eq_mk_iff' F _ _ h0 d.rep_nonzero).2 ⟨u, rfl⟩
      rwa [Projectivization.mk_rep] at this
    rw [this]; exact hd

lemma card_Dhat : (Dhat D).card = D.card * (Fintype.card F - 1) := by
  classical
  rw [Dhat_eq, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (g := fun _ => Fintype.card F - 1)]
    · simp
    · intro d _
      rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_units]
      intro u v huv
      exact Units.ext (smul_left_injective F d.rep_nonzero huv)
  · intro d _ d' _ hdd
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro b hb hb'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hb hb'
    obtain ⟨u, rfl⟩ := hb
    obtain ⟨u', hu'⟩ := hb'
    apply hdd
    have := (Projectivization.mk_eq_mk_iff' F _ _ d.rep_nonzero d'.rep_nonzero).2
      ⟨((u : F))⁻¹ * u', by rw [mul_smul, hu', smul_smul, inv_mul_cancel₀ u.ne_zero, one_smul]⟩
    rwa [Projectivization.mk_rep, Projectivization.mk_rep] at this

lemma D_nonempty (ht : 1 ≤ t) (hD : IsSpanning D) : D.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hspan := hD
  unfold IsSpanning at hspan
  rw [h, Finset.coe_empty, Set.image_empty, Submodule.span_empty] at hspan
  have : (Pi.single ⟨0, ht⟩ 1 : Fin t → F) ∈ (⊥ : Submodule F (Fin t → F)) := by
    rw [hspan]; trivial
  rw [Submodule.mem_bot] at this
  have := congrFun this ⟨0, ht⟩
  simp at this

end Dhat

/-- The real-arithmetic step: eigenvalue bounds of Lemma 3.7 and the distance bound of
Lemma 3.2 give `|μ| ≤ λ`. -/
lemma arith (q N Δ L μ lam : ℝ) (hq : 8 ≤ q) (hN : 1 ≤ N) (hL : L = (q ^ 2 - 1) * N)
    (hΔ : (q - 5) * N ≤ (q - 2) * Δ) (hlam : 3 / (q - 2) ≤ lam)
    (h1 : -1 / (q ^ 2 - 2) ≤ μ)
    (h2 : μ ≤ max (1 - q ^ 2 * Δ / L) (1 / ((q ^ 2 - 2) * (q ^ 2 - 1)))) : |μ| ≤ lam := by
  have hq2 : 0 < q - 2 := by linarith
  have hQ2 : q - 2 ≤ q ^ 2 - 2 := by nlinarith
  have hQ1 : 0 < q ^ 2 - 1 := by nlinarith
  have hLpos : 0 < L := by rw [hL]; positivity
  have h3 : 1 / (q ^ 2 - 2) ≤ 3 / (q - 2) := by
    rw [div_le_div_iff₀ (by linarith) hq2]; nlinarith
  rw [abs_le]
  constructor
  · have : -lam ≤ -1 / (q ^ 2 - 2) := by
      rw [neg_div]; linarith
    linarith
  · rcases le_max_iff.1 h2 with h | h
    · -- `1 - q²Δ/L ≤ 3/(q-2)`
      have hΔ' : (q - 5) / (q - 2) * N ≤ Δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hq2]; linarith
      have hNpos : 0 < N := by linarith
      have hratio : (q - 5) / (q - 2) ≤ q ^ 2 * Δ / L := by
        rw [hL, le_div_iff₀ (by positivity)]
        have : (q - 5) / (q - 2) * ((q ^ 2 - 1) * N) ≤ (q ^ 2 - 1) * Δ := by
          have := mul_le_mul_of_nonneg_left hΔ' hQ1.le
          linarith
        nlinarith
      have e : 1 - (q - 5) / (q - 2) = 3 / (q - 2) := by field_simp; ring
      linarith
    · have : 1 / ((q ^ 2 - 2) * (q ^ 2 - 1)) ≤ 1 / (q ^ 2 - 2) := by
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]; nlinarith
      linarith

lemma card_filter_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (P : α → Prop)
    [DecidablePred P] [DecidablePred fun b => P (e.symm b)] :
    (Finset.univ.filter fun b => P (e.symm b)).card = (Finset.univ.filter P).card := by
  apply Finset.card_equiv e.symm
  intro b; simp

end AbelianCayleyHDX.R23

set_option maxHeartbeats 1000000 in
open AbelianCayleyHDX AbelianCayleyHDX.R23 AbelianCayleyHDX.Spec in
open Classical in
theorem solution (lam : ℝ) (hlam : 0 < lam) (h : ℕ) (hq : 8 ≤ 2 ^ h)
    (hqlam : 3 / ((2 : ℝ) ^ h - 2) ≤ lam) :
    ∃ C : ℝ, 0 < C ∧ ∃ t : ℕ → ℕ, Tendsto t atTop atTop ∧
      ∃ (R ρ : ℕ → ℕ) (H : ∀ j, Matrix (Fin (R j)) (Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j))) (ZMod 2)),
        (∀ j, 3 * R j = ρ j * (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)) ∧ (ρ j : ℝ) ≤ C * (t j : ℝ) ∧
          IsGoodRelationMatrix (H j) (ρ j) ∧
          2 * (h : ℝ) * (2 : ℝ) ^ ((t j : ℝ) / 3) ≤ (Module.finrank (ZMod 2) (kerF2 (H j)) : ℝ) ∧
          ∃ G : SimpleGraph (Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j))), G.Connected ∧
            ∃ d : ℕ, G.IsRegularOfDegree d ∧ PH (H j) (ρ j) = (1 / (d : ℝ)) • G.adjMatrix ℝ ∧
            ∀ f : Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)) → ℝ, ∑ i, f i = 0 →
              Real.sqrt (∑ i, ((PH (H j) (ρ j)).mulVec f i) ^ 2) ≤ lam * Real.sqrt (∑ i, f i ^ 2)) ∧
        ∃ Mach : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial ℕ, ∀ j,
          HMBinPacking.OutputsWithin Mach (encNat j)
            (encNat (R j) ++ encNat (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)) ++ encList encVec (List.ofFn (H j)))
            (p.eval (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j))) := by
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · norm_num at hq
    · exact hpos
  -- the field `F = 𝔽_{q²}`
  let F := GaloisField 2 (2 * h)
  letI : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = (2 ^ h) ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * h) (by omega), ← pow_mul, mul_comm]
  haveI : CharP F 2 := charP_two_of_card h hh hF
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨C, hC, t, ht, ht1, D, hDprop, hDmach⟩ := lemma_3_2 h hq F hF
  obtain ⟨Mach, p, hMach⟩ := hDmach (Fintype.equivFin F)
  obtain ⟨R, eR, eΩ, Mach', p', hMach'⟩ :=
    explicit_HD_matrices h F hF t D (Fintype.equivFin F) Mach p hMach
  set ρ : ℕ → ℕ := fun j => ((2 ^ h) ^ 2 - 2) * (Dhat (D j)).card / 2 with hρdef
  have hq64 : 64 ≤ (2 ^ h) ^ 2 := by nlinarith
  have hev : ∀ j, 2 * ρ j = ((2 ^ h) ^ 2 - 2) * (Dhat (D j)).card := by
    intro j
    have h2 : 2 ∣ (2 ^ h) ^ 2 - 2 := by
      have : 2 ∣ (2 ^ h) ^ 2 := Dvd.dvd.pow (dvd_pow_self 2 (by omega)) (by norm_num)
      omega
    obtain ⟨k, hk⟩ := h2
    simp only [hρdef, hk, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  refine ⟨C * ((2 : ℝ) ^ h) ^ 4, by positivity, t, ht, R, ρ,
    fun j => (HD (D j)).reindex (eR j) (eΩ j), fun j => ?_, Mach', p', hMach'⟩
  -- fix `j`
  obtain ⟨hspan, hcardD, hΔ, hA⟩ := hDprop j
  have L35 := lemma_3_5 h hq hF (ht1 j) (D j) hspan
  have L36 := lemma_3_6 h hq hF (ht1 j) (D j) hspan
  have L37 := lemma_3_7 h hq hF (ht1 j) (D j) hspan
  obtain ⟨hR6, hinj, hrow, hcol, -, hgraph⟩ := L35
  obtain ⟨hreg, hgram, hPD⟩ := hgraph (ρ j) (hev j)
  obtain ⟨-, -, -, hker, -, -, hmd⟩ := L36
  obtain ⟨hconn, heig⟩ := L37
  beta_reduce
  generalize hH' : (HD (D j)).reindex (eR j) (eΩ j) = H'
  have hH'apply : ∀ r c, H' r c = HD (D j) ((eR j).symm r) ((eΩ j).symm c) := by
    intro r c; rw [← hH']; rfl
  have hDne := D_nonempty (D j) (ht1 j) hspan
  have hDhat : 0 < (Dhat (D j)).card := by
    rw [card_Dhat]; exact Nat.mul_pos (Finset.card_pos.2 hDne) (by rw [hF]; omega)
  have hρpos : 0 < ρ j := by
    have := hev j
    have : 0 < ((2 ^ h) ^ 2 - 2) * (Dhat (D j)).card := Nat.mul_pos (by omega) hDhat
    omega
  have hcolρ : ∀ c, colWeight (HD (D j)) c = ρ j := by
    intro c; have := hcol c; have := hev j; omega
  -- cardinalities
  have hcardR : Fintype.card (RowIdx (D j)) = R j := by
    rw [Fintype.card_congr (eR j), Fintype.card_fin]
  have hcardΩ : Fintype.card (Omega F (t j)) = ((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j) := by
    rw [Fintype.card_congr (eΩ j), Fintype.card_fin]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `3R = ρM`
    rw [hcardR, hcardΩ] at hR6
    have := hev j
    nlinarith
  · -- `ρ ≤ C' t`
    have hq2 : (8 : ℝ) ≤ 2 ^ h := by exact_mod_cast hq
    have h1 : (ρ j : ℝ) ≤ ((2 : ℝ) ^ h) ^ 4 * (D j).card := by
      have e1 : (2 * ρ j : ℕ) ≤ (2 ^ h) ^ 2 * ((D j).card * (2 ^ h) ^ 2) := by
        rw [hev j, card_Dhat, hF]
        apply Nat.mul_le_mul (Nat.sub_le _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      have e2 : ((2 * ρ j : ℕ) : ℝ) ≤ (((2 ^ h) ^ 2 * ((D j).card * (2 ^ h) ^ 2) : ℕ) : ℝ) := by
        exact_mod_cast e1
      push_cast at e2
      have : (0 : ℝ) ≤ ρ j := by positivity
      nlinarith
    have h2 : ((2 : ℝ) ^ h) ^ 4 * (D j).card ≤ ((2 : ℝ) ^ h) ^ 4 * (C * t j) :=
      mul_le_mul_of_nonneg_left hcardD (by positivity)
    linarith
  · -- good relation matrix
    refine ⟨?_, ?_, hρpos, ?_, ?_⟩
    · intro r r' hrr
      have : HD (D j) ((eR j).symm r) = HD (D j) ((eR j).symm r') := by
        funext ω
        have := congrFun hrr (eΩ j ω)
        simpa [hH'apply] using this
      exact (eR j).symm.injective (hinj this)
    · intro r
      unfold rowWeight
      have e : (Finset.univ.filter fun c => H' r c ≠ 0).card =
          (Finset.univ.filter fun ω => HD (D j) ((eR j).symm r) ω ≠ 0).card :=
        Finset.card_equiv (eΩ j).symm (by intro c; simp [hH'apply])
      exact e.trans (hrow _)
    · intro c
      unfold colWeight
      have e : (Finset.univ.filter fun r => H' r c ≠ 0).card =
          (Finset.univ.filter fun r => HD (D j) r ((eΩ j).symm c) ≠ 0).card :=
        Finset.card_equiv (eR j).symm (by intro r; simp [hH'apply])
      exact e.trans (hcolρ _)
    · have transport : ∀ v ∈ rowspan H', (fun ω => v (eΩ j ω)) ∈ rowspan (HD (D j)) := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨r, rfl⟩ := hx
          apply Submodule.subset_span
          refine ⟨(eR j).symm r, ?_⟩
          funext ω; simp [hH'apply]
        | zero => exact Submodule.zero_mem _
        | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
        | smul a x _ hx => exact Submodule.smul_mem _ a hx
      intro v hv hv0
      have hv' := transport v hv
      have hne : (fun ω => v (eΩ j ω)) ≠ 0 := by
        intro h0; apply hv0; funext c
        have := congrFun h0 ((eΩ j).symm c); simpa using this
      have h3 := hmd _ hv' hne
      have e : (Finset.univ.filter fun c => v c ≠ 0).card =
          (Finset.univ.filter fun ω => v (eΩ j ω) ≠ 0).card :=
        Finset.card_equiv (eΩ j).symm (by intro c; simp)
      rw [e]; exact h3
  · -- the kernel
    have hinjK : Module.finrank (ZMod 2) (kerF2 (HD (D j))) ≤
        Module.finrank (ZMod 2) (kerF2 H') := by
      let f := LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (eΩ j).symm
      have hle : (kerF2 (HD (D j))).map (f : (Omega F (t j) → ZMod 2) →ₗ[ZMod 2] _) ≤ kerF2 H' := by
        rintro _ ⟨w, hw, rfl⟩
        have hw : w ∈ kerF2 (HD (D j)) := hw
        unfold kerF2 at hw ⊢
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw ⊢
        funext r
        have := congrFun hw ((eR j).symm r)
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this ⊢
        rw [← this]
        simp only [f, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
          LinearMap.funLeft_apply, hH'apply]
        exact Fintype.sum_equiv (eΩ j).symm _ _ (fun c => rfl)
      calc Module.finrank (ZMod 2) (kerF2 (HD (D j)))
          = Module.finrank (ZMod 2) ((kerF2 (HD (D j))).map
              (f : (Omega F (t j) → ZMod 2) →ₗ[ZMod 2] _)) :=
            (LinearEquiv.finrank_map_eq f _).symm
        _ ≤ Module.finrank (ZMod 2) (kerF2 H') := Submodule.finrank_mono hle
    have e1 : (2 * h * Module.finrank F (affineSpace (D j)) : ℝ) ≤
        Module.finrank (ZMod 2) (kerF2 H') := by
      have : 2 * h * Module.finrank F (affineSpace (D j)) ≤ Module.finrank (ZMod 2) (kerF2 H') :=
        hker.trans hinjK
      exact_mod_cast this
    have : 2 * (h : ℝ) * (2 : ℝ) ^ ((t j : ℝ) / 3) ≤
        2 * h * (Module.finrank F (affineSpace (D j)) : ℝ) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    push_cast at e1
    linarith
  · -- the graph
    let G : SimpleGraph (Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j))) :=
      (colGraph (D j)).comap (eΩ j).symm
    have hPHent : ∀ a b, PH H' (ρ j) a b = PD (D j) ((eΩ j).symm a) ((eΩ j).symm b) := by
      intro a b
      have hPDdef : PD (D j) = PH (HD (D j)) (ρ j) := by
        unfold PD; rw [hF]
      rw [hPDdef]
      simp only [PH, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Htilde, Matrix.of_apply, hH'apply, smul_eq_mul]
      congr 2
      · exact Fintype.sum_equiv (eR j).symm _ _ (fun r => rfl)
      · simp [Matrix.one_apply]
    refine ⟨G, (SimpleGraph.Iso.comap (eΩ j).symm (colGraph (D j))).connected_iff.2 hconn,
      2 * ρ j, ?_, ?_, ?_⟩
    · intro a
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter,
        ← hreg ((eΩ j).symm a), ← SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.neighborFinset_eq_filter]
      exact card_filter_equiv (eΩ j) (fun ω => (colGraph (D j)).Adj ((eΩ j).symm a) ω)
    · ext a b
      rw [hPHent, hPD, Matrix.smul_apply, Matrix.smul_apply, SimpleGraph.adjMatrix_apply,
        SimpleGraph.adjMatrix_apply]
      push_cast
      rfl
    · intro f hf
      set g : Omega F (t j) → ℝ := fun ω => f (eΩ j ω) with hg
      have hgsum : ∑ ω, g ω = 0 := by
        rw [← hf]; exact Fintype.sum_equiv (eΩ j) _ _ (fun ω => rfl)
      have hmul : ∀ a, (PH H' (ρ j)).mulVec f a = (PD (D j)).mulVec g ((eΩ j).symm a) := by
        intro a
        simp only [Matrix.mulVec, dotProduct, hPHent, hg]
        exact Fintype.sum_equiv (eΩ j).symm _ _ (fun c => by simp)
      have hsym : Matrix.transpose (PD (D j)) = PD (D j) := by
        rw [hPD, Matrix.transpose_smul, SimpleGraph.transpose_adjMatrix]
      have h1 : (PD (D j)).mulVec (fun _ => (1 : ℝ)) = fun _ => 1 := by
        funext ω
        rw [hPD, Matrix.smul_mulVec, Pi.smul_apply]
        have := SimpleGraph.adjMatrix_mulVec_const_apply_of_regular (α := ℝ) (a := 1) hreg
          (v := ω)
        have this' : Matrix.mulVec ((colGraph (D j)).adjMatrix ℝ) (fun _ => (1 : ℝ)) ω =
            ((2 * ρ j : ℕ) : ℝ) * 1 := this
        rw [this', smul_eq_mul]
        have : (0 : ℝ) < ρ j := by exact_mod_cast hρpos
        push_cast; field_simp
      have heig' : ∀ (μ : ℝ) (f : Omega F (t j) → ℝ), f ≠ 0 → ∑ i, f i = 0 →
          (PD (D j)).mulVec f = μ • f → |μ| ≤ lam := by
        intro μ f hf0 hfs hfe
        obtain ⟨e1, e2⟩ := heig μ f hf0 hfs hfe
        have hN : (1 : ℝ) ≤ (D j).card := by exact_mod_cast Finset.card_pos.2 hDne
        have hL : ((Dhat (D j)).card : ℝ) = (((2 : ℝ) ^ h) ^ 2 - 1) * (D j).card := by
          rw [card_Dhat, hF]; push_cast
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        exact arith ((2 : ℝ) ^ h) (D j).card (Delta (D j)) (Dhat (D j)).card μ lam
          (by exact_mod_cast hq) hN hL hΔ hqlam e1 e2
      have key := norm_le_of_eig (PD (D j)) hsym h1 lam hlam.le heig' g hgsum
      have s1 : ∑ i, ((PH H' (ρ j)).mulVec f i) ^ 2 = ∑ ω, ((PD (D j)).mulVec g ω) ^ 2 := by
        simp only [hmul]
        exact Fintype.sum_equiv (eΩ j).symm _ _ (fun c => rfl)
      have s2 : ∑ i, f i ^ 2 = ∑ ω, g ω ^ 2 := by
        exact (Fintype.sum_equiv (eΩ j) _ _ (fun ω => rfl)).symm
      rw [s1, s2]; exact key
