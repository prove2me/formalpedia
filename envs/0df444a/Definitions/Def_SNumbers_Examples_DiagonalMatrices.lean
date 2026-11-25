-- Prove2me | Definitions.Def_SNumbers_Examples_DiagonalMatrices
-- name    : SNumbers_Examples_DiagonalMatrices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T03:59:31.068885+00:00
-- url     : https://prove2.me/theorems/0f2cb774-40c1-531b-bb4e-8163f0fe8e42
-- title:
--   Diagonal Matrices
-- statement:
--   Definitions and structural lemmas for Diagonal Matrices, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/DiagonalMatrices.lean

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.MeanInequalities
public import Theorems.Thm_ContinuousLinearMap_rank_comp_comp_le
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_idEmbed_eq
public import Theorems.Thm_SNumbers_approximationNumber_le_norm_sub
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_approximationSet_nonempty
public import Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_exists_flat_vector_weighted
public import Theorems.Thm_SNumbers_finrank_piLp
public import Theorems.Thm_SNumbers_idEmbed_apply
public import Theorems.Thm_SNumbers_isStrictSNumberSequence_approximationNumber
public import Theorems.Thm_SNumbers_norm_padFin_clm_le
public import Theorems.Thm_SNumbers_norm_projFin_clm_le
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SNumbers_padFin_castLE
public import Theorems.Thm_SNumbers_padFin_projFin_apply
public import Theorems.Thm_SNumbers_piLp_norm_mono
public import Theorems.Thm_SNumbers_rank_id_piLp
public import Theorems.Thm_SNumbers_toReal_pos_of_ne_top
public import Theorems.Thm_Submodule_liftQL_mkQL
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.bernsteinNumber_zero_eq_norm
attribute [local simp] SNumbers.idEmbed_apply
attribute [local simp] SNumbers.padFin_apply
attribute [local simp] Submodule.liftQL_mkQL


set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open scoped ENNReal
open ContinuousLinearMap
namespace SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
noncomputable def DiagCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] (σ : Fin m → 𝕜) :
    PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (fun i => σ i • x i)
      map_add' := fun x y => by
        ext i; simp [mul_add]
      map_smul' := fun c x => by
        ext i; simp [mul_left_comm] }
@[simp] lemma DiagCLM_apply (σ : Fin m → 𝕜) (x : PiLp p (fun _ : Fin m => 𝕜))
    (i : Fin m) : (DiagCLM p σ x) i = σ i • x i := rfl
theorem norm_DiagCLM [Nonempty (Fin m)] (σ : Fin m → 𝕜) :
    ‖DiagCLM p σ‖ = ⨆ i, ‖σ i‖ := by
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max (fun i => ‖σ i‖)
  have hMeq : (⨆ i, ‖σ i‖) = ‖σ j₀‖ :=
    le_antisymm (ciSup_le hj₀) (le_ciSup (Finite.bddAbove_range fun i => ‖σ i‖) j₀)
  rw [hMeq]
  refine le_antisymm ?_ ?_
  · -- Upper bound: `‖D_σ x‖ ≤ ‖σ j₀‖ * ‖x‖` for all `x`.
    refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    calc ‖DiagCLM p σ x‖
        ≤ ‖σ j₀ • x‖ := by
          refine piLp_norm_mono fun i => ?_
          rw [DiagCLM_apply, PiLp.smul_apply, norm_smul, norm_smul]
          exact mul_le_mul_of_nonneg_right (hj₀ i) (norm_nonneg _)
      _ = ‖σ j₀‖ * ‖x‖ := norm_smul _ _
  · -- Lower bound: test on the basis vector `e_{j₀} = single p j₀ 1`.
    set e : PiLp p (fun _ : Fin m => 𝕜) := PiLp.single p j₀ (1 : 𝕜) with he_def
    have hDe : DiagCLM p σ e = PiLp.single p j₀ (σ j₀) := by
      ext k
      rcases eq_or_ne k j₀ with rfl | hk
      · simp [he_def]
      · simp [he_def, hk]
    have he : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
    have hbound := (DiagCLM p σ).le_opNorm e
    rw [hDe, PiLp.norm_single, he, mul_one] at hbound
    exact hbound
theorem approximationNumber_DiagCLM_le {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLM p σ) n ≤ ‖σ ⟨n, hn⟩‖ := by
  have : Nonempty (Fin m) := ⟨⟨n, hn⟩⟩
  -- The rank-`≤ n` approximant `L = D_σ ∘ Pₙ`, written as `B ∘ id_{ℓ^p_n} ∘ A`
  -- so its rank is bounded by `dim ℓ^p_n = n`.
  set A : PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin n => 𝕜) :=
    projFin hn.le with hA
  set B : PiLp p (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    (DiagCLM p σ).comp padFin with hB
  set L := B.comp ((ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin n => 𝕜))).comp A) with hL
  -- The residual diagonal `ρ`: the entries from index `n` on.
  set ρ : Fin m → 𝕜 := fun i => if (i : ℕ) < n then 0 else σ i with hρ
  have hLrank : L.rank ≤ (n : Cardinal) :=
    (ContinuousLinearMap.rank_comp_comp_le A _ B).trans_eq (rank_id_piLp n)
  -- `D_σ - L = DiagCLM ρ`.
  have hres : DiagCLM p σ - L = DiagCLM p ρ := by
    ext x i
    simp only [hL, hA, hB, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, DiagCLM_apply, PiLp.sub_apply]
    rw [padFin_projFin_apply]
    by_cases hi : (i : ℕ) < n <;> simp [hρ, hi]
  -- The residual norm is `⨆_{i ≥ n} ‖σ i‖ = ‖σ_n‖`.
  have hsup : (⨆ i, ‖ρ i‖) = ‖σ ⟨n, hn⟩‖ := by
    refine le_antisymm (ciSup_le fun i => ?_) ?_
    · by_cases hi : (i : ℕ) < n
      · simp [hρ, hi]
      · have hle : (⟨n, hn⟩ : Fin m) ≤ i := by
          simp only [Fin.le_def]; omega
        simpa [hρ, hi] using hσ hle
    · have : ‖σ ⟨n, hn⟩‖ = ‖ρ ⟨n, hn⟩‖ := by simp [hρ]
      rw [this]
      exact le_ciSup (Finite.bddAbove_range fun i => ‖ρ i‖) (⟨n, hn⟩ : Fin m)
  calc approximationNumber (DiagCLM p σ) n
      ≤ ‖DiagCLM p σ - L‖ := approximationNumber_le_norm_sub hLrank
    _ = ‖DiagCLM p ρ‖ := by rw [hres]
    _ = ⨆ i, ‖ρ i‖ := norm_DiagCLM ρ
    _ = ‖σ ⟨n, hn⟩‖ := hsup
theorem le_sn_DiagCLM {s : Family 𝕜} (hs : IsStrictSNumberSequence s)
    {σ : Fin m → 𝕜} (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    ‖σ ⟨n, hn⟩‖ ≤ s (DiagCLM p σ) n := by
  rcases eq_or_ne ‖σ ⟨n, hn⟩‖ 0 with h0 | h0
  · rw [h0]; exact hs.nonneg _ _
  have hpos : 0 < ‖σ ⟨n, hn⟩‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
  have hnm : n + 1 ≤ m := hn
  have : Nonempty (Fin (n + 1)) := ⟨⟨0, Nat.succ_pos n⟩⟩
  -- The top `n+1` entries dominate `‖σ_n‖`, hence are nonzero.
  have hdom : ∀ j : Fin (n + 1), ‖σ ⟨n, hn⟩‖ ≤ ‖σ (Fin.castLE hnm j)‖ := by
    intro j
    refine hσ ?_
    simp only [Fin.le_def, Fin.val_castLE]
    omega
  have hne : ∀ j : Fin (n + 1), σ (Fin.castLE hnm j) ≠ 0 := fun j hj => by
    have := hdom j; rw [hj, norm_zero] at this; exact absurd this (not_le.mpr hpos)
  -- The factorisation `id = B ∘ D_σ ∘ A`.
  set A : PiLp p (fun _ : Fin (n + 1) => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    padFin with hA
  set B : PiLp p (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin (n + 1) => 𝕜) :=
    (DiagCLM p fun j => (σ (Fin.castLE hnm j))⁻¹).comp (projFin hnm) with hB
  have hfact : B.comp ((DiagCLM p σ).comp A)
      = ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin (n + 1) => 𝕜)) := by
    ext w j
    simp only [hB, hA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      DiagCLM_apply, projFin_apply]
    rw [padFin_castLE, smul_smul, inv_mul_cancel₀ (hne j), one_smul]
  -- Norm bounds on the factors.
  have hAle : ‖A‖ ≤ 1 := by rw [hA]; exact norm_padFin_clm_le hnm
  have hBle : ‖B‖ ≤ ‖σ ⟨n, hn⟩‖⁻¹ := by
    rw [hB]
    calc ‖(DiagCLM p fun j => (σ (Fin.castLE hnm j))⁻¹).comp (projFin hnm)‖
        ≤ ‖DiagCLM p fun j => (σ (Fin.castLE hnm j))⁻¹‖ * ‖projFin hnm‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (⨆ j, ‖(σ (Fin.castLE hnm j))⁻¹‖) * 1 := by
          rw [norm_DiagCLM]
          exact mul_le_mul_of_nonneg_left (norm_projFin_clm_le hnm)
            (Real.iSup_nonneg fun j => norm_nonneg _)
      _ = ⨆ j, ‖(σ (Fin.castLE hnm j))⁻¹‖ := mul_one _
      _ ≤ ‖σ ⟨n, hn⟩‖⁻¹ := by
          refine ciSup_le fun j => ?_
          rw [norm_inv]
          exact inv_anti₀ hpos (hdom j)
  -- Assemble via (S3) and (S5').
  have hideal := hs.ideal A (DiagCLM p σ) B n
  rw [hfact, hs.strictly_normalised_at_id n
    (Module.lt_rank_of_lt_finrank (by rw [finrank_piLp]; omega))] at hideal
  have hsnn : 0 ≤ s (DiagCLM p σ) n := hs.nonneg _ _
  have hchain : (1 : ℝ) ≤ ‖σ ⟨n, hn⟩‖⁻¹ * s (DiagCLM p σ) n := by
    calc (1 : ℝ) ≤ ‖B‖ * s (DiagCLM p σ) n * ‖A‖ := hideal
      _ ≤ ‖σ ⟨n, hn⟩‖⁻¹ * s (DiagCLM p σ) n * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hBle hsnn) hAle (norm_nonneg _)
            (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hsnn)
      _ = ‖σ ⟨n, hn⟩‖⁻¹ * s (DiagCLM p σ) n := mul_one _
  have hfinal := mul_le_mul_of_nonneg_left hchain (norm_nonneg (σ ⟨n, hn⟩))
  rwa [mul_one, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at hfinal
theorem approximationNumber_DiagCLM_eq {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  le_antisymm (approximationNumber_DiagCLM_le hσ hn)
    (le_sn_DiagCLM isStrictSNumberSequence_approximationNumber hσ hn)
@[simp] lemma DiagCLM_one :
    DiagCLM p (fun _ : Fin m => (1 : 𝕜)) = ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin m => 𝕜)) := by
  ext x i; simp
section MixedExponent
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
noncomputable def DiagCLMpq (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (σ : Fin m → 𝕜) :
    PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp p (fun i => σ i • x i)
      map_add' := fun x y => by ext i; simp [mul_add]
      map_smul' := fun c x => by ext i; simp [mul_left_comm] }
@[simp] lemma DiagCLMpq_apply (σ : Fin m → 𝕜) (x : PiLp q (fun _ : Fin m => 𝕜)) (i : Fin m) :
    (DiagCLMpq p q σ x) i = σ i • x i := rfl
@[simp] lemma DiagCLMpq_self (σ : Fin m → 𝕜) : DiagCLMpq p p σ = DiagCLM p σ := by
  ext x i; simp
@[simp] lemma DiagCLMpq_one : DiagCLMpq p q (fun _ : Fin m => (1 : 𝕜)) = idEmbed p q := by
  ext x i; simp
noncomputable def diagExp (p q : ℝ≥0∞) : ℝ := (1 / p.toReal - 1 / q.toReal)⁻¹
lemma diagExp_inv (p q : ℝ≥0∞) : (diagExp p q)⁻¹ = 1 / p.toReal - 1 / q.toReal :=
  inv_inv _
omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- For `p < q < ∞`, `p` is finite. -/
lemma p_ne_top (hpq : p < q) (hq : q ≠ ∞) : p ≠ ∞ := ne_top_of_le_ne_top hq hpq.le
omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- The real parts are strictly ordered: `p.toReal < q.toReal`. -/
lemma toReal_lt (hpq : p < q) (hq : q ≠ ∞) : p.toReal < q.toReal :=
  (ENNReal.toReal_lt_toReal (p_ne_top hpq hq) hq).mpr hpq
omit [Fact (1 ≤ q)] in
/-- `1/p − 1/q > 0` (real parts), the reciprocal of which is `r`. -/
lemma one_div_sub_pos (hpq : p < q) (hq : q ≠ ∞) :
    0 < 1 / p.toReal - 1 / q.toReal := by
  have hP : 0 < p.toReal := toReal_pos_of_ne_top (p_ne_top hpq hq)
  have hPQ : p.toReal < q.toReal := toReal_lt hpq hq
  exact sub_pos.mpr (one_div_lt_one_div_of_lt hP hPQ)
omit [Fact (1 ≤ q)] in
/-- `r > 0`. -/
lemma diagExp_pos (hpq : p < q) (hq : q ≠ ∞) : 0 < diagExp p q :=
  inv_pos.mpr (one_div_sub_pos hpq hq)
lemma holderTriple_diagExp (hpq : p < q) (hq : q ≠ ∞) :
    (diagExp p q).HolderTriple q.toReal p.toReal where
  inv_add_inv_eq_inv := by rw [diagExp_inv]; ring
  left_pos := diagExp_pos hpq hq
  right_pos := toReal_pos_of_ne_top hq
lemma diagExp_eq (hpq : p < q) (hq : q ≠ ∞) :
    diagExp p q = p.toReal * q.toReal / (q.toReal - p.toReal) := by
  have hP : (0 : ℝ) < p.toReal := toReal_pos_of_ne_top (p_ne_top hpq hq)
  have hQ : (0 : ℝ) < q.toReal := toReal_pos_of_ne_top hq
  rw [diagExp, div_sub_div _ _ hP.ne' hQ.ne', one_mul, mul_one, inv_div]
lemma diagExp_hexp1 (hpq : p < q) (hq : q ≠ ∞) :
    (1 + diagExp p q / q.toReal) * p.toReal = diagExp p q := by
  have hQ : (0 : ℝ) < q.toReal := toReal_pos_of_ne_top hq
  have hPQ : p.toReal < q.toReal := toReal_lt hpq hq
  have hQP : q.toReal - p.toReal ≠ 0 := sub_ne_zero.mpr hPQ.ne'
  rw [diagExp_eq hpq hq]
  field_simp
  ring
lemma diagExp_hexp2 (hpq : p < q) (hq : q ≠ ∞) :
    diagExp p q / q.toReal * (q.toReal - p.toReal) = p.toReal := by
  have hQ : (0 : ℝ) < q.toReal := toReal_pos_of_ne_top hq
  have hPQ : p.toReal < q.toReal := toReal_lt hpq hq
  have hQP : q.toReal - p.toReal ≠ 0 := sub_ne_zero.mpr hPQ.ne'
  rw [diagExp_eq hpq hq]
  field_simp
lemma diagExp_inv_add (hpq : p < q) (hq : q ≠ ∞) :
    1 / diagExp p q + 1 / q.toReal = 1 / p.toReal := by
  simpa only [one_div] using (holderTriple_diagExp hpq hq).inv_add_inv_eq_inv
theorem norm_DiagCLMpq_apply_le (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (x : PiLp q (fun _ : Fin m => 𝕜)) :
    ‖DiagCLMpq p q σ x‖
      ≤ (∑ i, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) * ‖x‖ := by
  have hpf : p ≠ ∞ := p_ne_top hpq hq
  have hP : 0 < p.toReal := toReal_pos_of_ne_top hpf
  have hQ : 0 < q.toReal := toReal_pos_of_ne_top hq
  have hR : 0 < diagExp p q := diagExp_pos hpq hq
  have hPne : p.toReal ≠ 0 := hP.ne'
  have hQne : q.toReal ≠ 0 := hQ.ne'
  have hRne : diagExp p q ≠ 0 := hR.ne'
  rw [PiLp.norm_eq_sum hP, PiLp.norm_eq_sum hQ]
  -- Rewrite the codomain sum `∑ ‖σ_i • x_i‖^p = ∑ (‖σ_i‖·‖x_i‖)^p`.
  have hlhs : ∑ i, ‖(DiagCLMpq p q σ x) i‖ ^ p.toReal
      = ∑ i, (‖σ i‖ * ‖x i‖) ^ p.toReal :=
    Finset.sum_congr rfl fun i _ => by rw [DiagCLMpq_apply, norm_smul]
  rw [hlhs]
  -- Nonnegativity of the two `L^r` / `L^q` sums.
  have hSσ : 0 ≤ ∑ i, ‖σ i‖ ^ diagExp p q :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  have hSx : 0 ≤ ∑ i, ‖x i‖ ^ q.toReal :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _
  -- Hölder for the triple `(r, q, p)`.
  have hhold := Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg Finset.univ
    (holderTriple_diagExp hpq hq) (f := fun i => ‖σ i‖) (g := fun i => ‖x i‖)
    (fun i _ => norm_nonneg _) (fun i _ => norm_nonneg _)
  have hTnn : 0 ≤ ∑ i, (‖σ i‖ * ‖x i‖) ^ p.toReal :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
  have h2 := Real.rpow_le_rpow hTnn hhold (by positivity : (0 : ℝ) ≤ 1 / p.toReal)
  rw [Real.mul_rpow (Real.rpow_nonneg hSσ _) (Real.rpow_nonneg hSx _),
    ← Real.rpow_mul hSσ, ← Real.rpow_mul hSx] at h2
  have e1 : p.toReal / diagExp p q * (1 / p.toReal) = 1 / diagExp p q := by
    field_simp
  have e2 : p.toReal / q.toReal * (1 / p.toReal) = 1 / q.toReal := by
    field_simp
  rwa [e1, e2] at h2
theorem norm_DiagCLMpq_le (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜) :
    ‖DiagCLMpq p q σ‖ ≤ (∑ i, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) :=
  opNorm_le_bound _
    (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _)
    (norm_DiagCLMpq_apply_le hpq hq σ)
noncomputable def diagTail (p q : ℝ≥0∞) (σ : Fin m → 𝕜) (n : ℕ) : ℝ :=
  (∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), ‖σ i‖ ^ diagExp p q) ^
    (1 / diagExp p q)
theorem approximationNumber_DiagCLMpq_le (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    {n : ℕ} (hn : n ≤ m) :
    approximationNumber (DiagCLMpq p q σ) n ≤ diagTail p q σ n := by
  have hR : 0 < diagExp p q := diagExp_pos hpq hq
  -- The rank-`≤ n` approximant `L = (D_σ ∘ padFin) ∘ id_{ℓ^q_n} ∘ projFin`.
  set A : PiLp q (fun _ : Fin m => 𝕜) →L[𝕜] PiLp q (fun _ : Fin n => 𝕜) :=
    projFin hn with hA
  set B : PiLp q (fun _ : Fin n => 𝕜) →L[𝕜] PiLp p (fun _ : Fin m => 𝕜) :=
    (DiagCLMpq p q σ).comp padFin with hB
  set L := B.comp ((ContinuousLinearMap.id 𝕜 (PiLp q (fun _ : Fin n => 𝕜))).comp A) with hL
  -- The residual diagonal `ρ`: entries from index `n` on.
  set ρ : Fin m → 𝕜 := fun i => if (i : ℕ) < n then 0 else σ i with hρ
  have hLrank : L.rank ≤ (n : Cardinal) :=
    (ContinuousLinearMap.rank_comp_comp_le A _ B).trans_eq (rank_id_piLp n)
  -- `D_σ − L = D_ρ`.
  have hres : DiagCLMpq p q σ - L = DiagCLMpq p q ρ := by
    ext x i
    simp only [hL, hA, hB, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, DiagCLMpq_apply, PiLp.sub_apply]
    rw [padFin_projFin_apply]
    by_cases hi : (i : ℕ) < n <;> simp [hρ, hi]
  -- The residual `ℓ^r`-sum is the tail sum.
  have hsum : ∑ i, ‖ρ i‖ ^ diagExp p q
      = ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), ‖σ i‖ ^ diagExp p q := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin m => n ≤ (i : ℕ))
        (fun i => ‖ρ i‖ ^ diagExp p q)]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), ‖ρ i‖ ^ diagExp p q
        = ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), ‖σ i‖ ^ diagExp p q := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      simp only [hρ, if_neg (not_lt.mpr hi.2)]
    have h2 : ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ n ≤ (i : ℕ)), ‖ρ i‖ ^ diagExp p q = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [Finset.mem_filter, not_le] at hi
      simp only [hρ, if_pos hi.2, norm_zero, Real.zero_rpow hR.ne']
    rw [h1, h2, add_zero]
  calc approximationNumber (DiagCLMpq p q σ) n
      ≤ ‖DiagCLMpq p q σ - L‖ := approximationNumber_le_norm_sub hLrank
    _ = ‖DiagCLMpq p q ρ‖ := by rw [hres]
    _ ≤ (∑ i, ‖ρ i‖ ^ diagExp p q) ^ (1 / diagExp p q) := norm_DiagCLMpq_le hpq hq ρ
    _ = diagTail p q σ n := by rw [diagTail, hsum]
lemma norm_ratio_of_flat_weighted (hpq : p < q) (hq : q ≠ ∞) (σ x : Fin m → 𝕜)
    (hle : ∀ i, ‖x i‖ ≤ ‖σ i‖ ^ (diagExp p q / q.toReal))
    {S : Finset (Fin m)}
    (hS : ∀ i ∈ S, ‖x i‖ = ‖σ i‖ ^ (diagExp p q / q.toReal)) :
    (∑ i ∈ S, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q)
        * ‖(WithLp.toLp q x : PiLp q (fun _ : Fin m => 𝕜))‖
      ≤ ‖DiagCLMpq p q σ (WithLp.toLp q x)‖ := by
  have hpf : p ≠ ∞ := p_ne_top hpq hq
  have hP : 0 < p.toReal := toReal_pos_of_ne_top hpf
  have hQ : 0 < q.toReal := toReal_pos_of_ne_top hq
  have hR : 0 < diagExp p q := diagExp_pos hpq hq
  have hPQ : p.toReal < q.toReal := toReal_lt hpq hq
  -- The three relevant norms.
  have hnormD : ‖DiagCLMpq p q σ (WithLp.toLp q x)‖
      = (∑ i, (‖σ i‖ * ‖x i‖) ^ p.toReal) ^ (1 / p.toReal) := by
    rw [PiLp.norm_eq_sum hP]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (DiagCLMpq p q σ (WithLp.toLp q x)) i = σ i • x i from rfl, norm_smul]
  have hnormx : ‖(WithLp.toLp q x : PiLp q (fun _ : Fin m => 𝕜))‖
      = (∑ i, ‖x i‖ ^ q.toReal) ^ (1 / q.toReal) := by
    rw [PiLp.norm_eq_sum hQ]
  set T : ℝ := ∑ i, (‖σ i‖ * ‖x i‖) ^ p.toReal with hTdef
  have hTnn : 0 ≤ T :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
  -- Claim (i): the `S`-sum of `‖σ_i‖^r` is at most `T`.
  have hterm1 : ∀ i ∈ S, (‖σ i‖ * ‖x i‖) ^ p.toReal = ‖σ i‖ ^ diagExp p q := by
    intro i hi
    rw [hS i hi]
    rcases eq_or_ne ‖σ i‖ 0 with h0 | h0
    · rw [h0, zero_mul, Real.zero_rpow hP.ne']
      exact (Real.zero_rpow hR.ne').symm
    · have hpos : 0 < ‖σ i‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
      have hmul : ‖σ i‖ * ‖σ i‖ ^ (diagExp p q / q.toReal)
          = ‖σ i‖ ^ (1 + diagExp p q / q.toReal) := by
        rw [Real.rpow_add hpos, Real.rpow_one]
      rw [hmul, ← Real.rpow_mul (norm_nonneg _), diagExp_hexp1 hpq hq]
  have claim_i : ∑ i ∈ S, ‖σ i‖ ^ diagExp p q ≤ T := by
    calc ∑ i ∈ S, ‖σ i‖ ^ diagExp p q
        = ∑ i ∈ S, (‖σ i‖ * ‖x i‖) ^ p.toReal :=
          (Finset.sum_congr rfl hterm1).symm
      _ ≤ ∑ i, (‖σ i‖ * ‖x i‖) ^ p.toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _)
  -- Claim (ii): `∑ ‖x_i‖^q ≤ T` pointwise.
  have hterm2 : ∀ i, ‖x i‖ ^ q.toReal ≤ (‖σ i‖ * ‖x i‖) ^ p.toReal := by
    intro i
    rcases eq_or_ne ‖x i‖ 0 with h0 | h0
    · rw [h0, Real.zero_rpow hQ.ne']
      positivity
    · have hxpos : 0 < ‖x i‖ := (norm_nonneg _).lt_of_ne (Ne.symm h0)
      have hbase : ‖x i‖ ^ (q.toReal - p.toReal) ≤ ‖σ i‖ ^ p.toReal := by
        calc ‖x i‖ ^ (q.toReal - p.toReal)
            ≤ (‖σ i‖ ^ (diagExp p q / q.toReal)) ^ (q.toReal - p.toReal) :=
              Real.rpow_le_rpow (norm_nonneg _) (hle i) (by linarith)
          _ = ‖σ i‖ ^ p.toReal := by
              rw [← Real.rpow_mul (norm_nonneg _), diagExp_hexp2 hpq hq]
      calc ‖x i‖ ^ q.toReal
          = ‖x i‖ ^ (q.toReal - p.toReal) * ‖x i‖ ^ p.toReal := by
            rw [← Real.rpow_add hxpos]; congr 1; ring
        _ ≤ ‖σ i‖ ^ p.toReal * ‖x i‖ ^ p.toReal :=
            mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (norm_nonneg _) _)
        _ = (‖σ i‖ * ‖x i‖) ^ p.toReal := (Real.mul_rpow (norm_nonneg _) (norm_nonneg _)).symm
  have claim_ii : ∑ i, ‖x i‖ ^ q.toReal ≤ T := Finset.sum_le_sum fun i _ => hterm2 i
  -- Combine.
  rw [hnormD, hnormx]
  have hSσnn : 0 ≤ ∑ i ∈ S, ‖σ i‖ ^ diagExp p q :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have hxQnn : 0 ≤ ∑ i, ‖x i‖ ^ q.toReal :=
    Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
  have hcR : (∑ i ∈ S, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) ≤ T ^ (1 / diagExp p q) :=
    Real.rpow_le_rpow hSσnn claim_i (by positivity)
  have hxq : (∑ i, ‖x i‖ ^ q.toReal) ^ (1 / q.toReal) ≤ T ^ (1 / q.toReal) :=
    Real.rpow_le_rpow hxQnn claim_ii (by positivity)
  calc (∑ i ∈ S, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q)
          * (∑ i, ‖x i‖ ^ q.toReal) ^ (1 / q.toReal)
      ≤ T ^ (1 / diagExp p q) * T ^ (1 / q.toReal) :=
        mul_le_mul hcR hxq (Real.rpow_nonneg hxQnn _) (Real.rpow_nonneg hTnn _)
    _ = T ^ (1 / p.toReal) := by
        rcases eq_or_lt_of_le hTnn with hT0 | hTpos
        · rw [← hT0, Real.zero_rpow (one_div_ne_zero hR.ne'),
            Real.zero_rpow (one_div_ne_zero hQ.ne'),
            Real.zero_rpow (one_div_ne_zero hP.ne'), mul_zero]
        · rw [← Real.rpow_add hTpos, diagExp_inv_add hpq hq]
omit [Fact (1 ≤ q)] in
/-- **Selection inequality.** For `‖σ_i‖^r` antitone, the tail sum is dominated by
the sum over any `S` with `|S| ≥ m − n`. -/
lemma tail_sum_le_sum_of_card_ge (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n ≤ m)
    {S : Finset (Fin m)} (hScard : m - n ≤ S.card) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)), ‖σ i‖ ^ diagExp p q
      ≤ ∑ i ∈ S, ‖σ i‖ ^ diagExp p q := by
  classical
  have hR : 0 < diagExp p q := diagExp_pos hpq hq
  set f : Fin m → ℝ := fun i => ‖σ i‖ ^ diagExp p q with hf
  set tail : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)) with htail
  have hfanti : ∀ {a b : Fin m}, a ≤ b → f b ≤ f a := fun {a b} hab =>
    Real.rpow_le_rpow (norm_nonneg _) (hσ hab) hR.le
  have hfnn : ∀ i, 0 ≤ f i := fun i => Real.rpow_nonneg (norm_nonneg _) _
  -- Every `f`-value on `tail \ S` is dominated by every `f`-value on `S \ tail`.
  have hdom : ∀ b ∈ tail \ S, ∀ a ∈ S \ tail, f b ≤ f a := by
    intro b hb a ha
    simp only [Finset.mem_sdiff, htail, Finset.mem_filter, Finset.mem_univ, true_and] at hb ha
    obtain ⟨hbn, -⟩ := hb
    obtain ⟨-, han⟩ := ha
    exact hfanti (by rw [Fin.le_def]; omega)
  -- Cardinality count: `tail` has `m − n` elements, so `|tail \ S| ≤ |S \ tail|`.
  have hlt : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n)).card = n := by
    rw [show (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n))
          = Finset.univ.image (Fin.castLE hn) from ?_,
      Finset.card_image_of_injective _ (Fin.castLE_injective hn), Finset.card_univ,
      Fintype.card_fin]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi; exact ⟨⟨(i : ℕ), hi⟩, by simp⟩
    · rintro ⟨j, rfl⟩; simp only [Fin.val_castLE]; exact j.isLt
  have hcard_tail : tail.card = m - n := by
    have heq : tail = (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n))ᶜ := by
      ext i; simp [htail, Finset.mem_filter, not_lt]
    rw [heq, Finset.card_compl, Fintype.card_fin, hlt]
  have hcard_le : (tail \ S).card ≤ (S \ tail).card := by
    have h1 : (tail \ S).card + (tail ∩ S).card = tail.card :=
      Finset.card_sdiff_add_card_inter tail S
    have h2 : (S \ tail).card + (S ∩ tail).card = S.card :=
      Finset.card_sdiff_add_card_inter S tail
    rw [Finset.inter_comm] at h1
    omega
  -- The domination sum inequality via a common threshold `M`.
  have key : ∑ i ∈ tail \ S, f i ≤ ∑ i ∈ S \ tail, f i := by
    rcases (tail \ S).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; exact Finset.sum_nonneg fun i _ => hfnn i
    · obtain ⟨a0, ha0⟩ := hne
      set M : ℝ := (tail \ S).sup' ⟨a0, ha0⟩ f with hM
      have hMnn : 0 ≤ M := le_trans (hfnn a0) (Finset.le_sup' f ha0)
      calc ∑ i ∈ tail \ S, f i
          ≤ (tail \ S).card • M := Finset.sum_le_card_nsmul _ _ _ fun i hi => Finset.le_sup' f hi
        _ = ((tail \ S).card : ℝ) * M := nsmul_eq_mul _ _
        _ ≤ ((S \ tail).card : ℝ) * M := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard_le) hMnn
        _ = (S \ tail).card • M := (nsmul_eq_mul _ _).symm
        _ ≤ ∑ i ∈ S \ tail, f i :=
            Finset.card_nsmul_le_sum _ _ _ fun a ha =>
              Finset.sup'_le ⟨a0, ha0⟩ f fun b hb => hdom b hb a ha
  -- Assemble via `∑_A = ∑_{A∩B} + ∑_{A\B}`.
  have htails : ∑ i ∈ tail, f i = ∑ i ∈ tail ∩ S, f i + ∑ i ∈ tail \ S, f i :=
    (Finset.sum_inter_add_sum_sdiff tail S f).symm
  have hSs : ∑ i ∈ S, f i = ∑ i ∈ S ∩ tail, f i + ∑ i ∈ S \ tail, f i :=
    (Finset.sum_inter_add_sum_sdiff S tail f).symm
  rw [Finset.inter_comm S tail] at hSs
  rw [htails, hSs]
  linarith [key]
lemma exists_norm_ratio_ge_DiagCLMpq (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m)
    (V : Submodule 𝕜 (PiLp q (fun _ : Fin m => 𝕜)))
    (hV : m - n ≤ Module.finrank 𝕜 V) :
    ∃ x ∈ V, x ≠ 0 ∧ diagTail p q σ n * ‖x‖ ≤ ‖DiagCLMpq p q σ x‖ := by
  have hR : 0 < diagExp p q := diagExp_pos hpq hq
  rcases eq_or_ne (diagTail p q σ n) 0 with htail0 | htailne
  · -- Vanishing tail: any nonzero vector of `V` works.
    have hVne : V ≠ ⊥ := fun h => by rw [h, finrank_bot] at hV; omega
    obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
    exact ⟨x, hxV, hx0, by rw [htail0, zero_mul]; exact norm_nonneg _⟩
  · -- Positive tail: use the weighted flat vector.
    set e : PiLp q (fun _ : Fin m => 𝕜) ≃ₗ[𝕜] (Fin m → 𝕜) :=
      WithLp.linearEquiv q 𝕜 (Fin m → 𝕜) with he
    have hkV' : m - n ≤
        Module.finrank 𝕜 (V.map (e : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] (Fin m → 𝕜))) :=
      le_of_le_of_eq hV (LinearEquiv.finrank_map_eq e V).symm
    obtain ⟨z, hzV', hzle, hzcard⟩ := exists_flat_vector_weighted (k := m - n)
      (fun i => ‖σ i‖ ^ (diagExp p q / q.toReal))
      (fun i => Real.rpow_nonneg (norm_nonneg _) _) hkV'
    obtain ⟨v, hvV, hev⟩ := Submodule.mem_map.mp hzV'
    have hxV : e.symm z ∈ V := by rw [← hev]; simpa using hvV
    set S : Finset (Fin m) :=
      Finset.univ.filter (fun i => ‖z i‖ = ‖σ i‖ ^ (diagExp p q / q.toReal)) with hSdef
    have hScard : m - n ≤ S.card := hzcard
    -- The flat vector is nonzero (else its saturated set forces `diagTail = 0`).
    have hzne : z ≠ 0 := by
      intro hz0
      apply htailne
      have hZcard : m - n ≤ (Finset.univ.filter (fun i => ‖σ i‖ = 0)).card := by
        refine le_trans hScard (Finset.card_le_card fun i hi => ?_)
        rw [hSdef, Finset.mem_filter] at hi
        rw [Finset.mem_filter]
        refine ⟨hi.1, ?_⟩
        have hzero : ‖σ i‖ ^ (diagExp p q / q.toReal) = 0 := by rw [← hi.2, hz0]; simp
        exact ((Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _)).mp hzero).1
      have hsel := tail_sum_le_sum_of_card_ge hpq hq σ hσ hn.le hZcard
      have hZsum : ∑ i ∈ Finset.univ.filter (fun i => ‖σ i‖ = 0), ‖σ i‖ ^ diagExp p q = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [Finset.mem_filter] at hi; rw [hi.2, Real.zero_rpow hR.ne']
      have htailnn : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)),
          ‖σ i‖ ^ diagExp p q :=
        Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _
      have heq0 : ∑ i ∈ Finset.univ.filter (fun i : Fin m => n ≤ (i : ℕ)),
          ‖σ i‖ ^ diagExp p q = 0 := le_antisymm (hZsum ▸ hsel) htailnn
      rw [diagTail, heq0, Real.zero_rpow (one_div_ne_zero hR.ne')]
    have hxne : e.symm z ≠ 0 := fun h0 => hzne (by simpa using congrArg e h0)
    refine ⟨e.symm z, hxV, hxne, ?_⟩
    have hratio := norm_ratio_of_flat_weighted hpq hq σ z hzle (S := S)
      (fun i hi => by rw [hSdef, Finset.mem_filter] at hi; exact hi.2)
    have hdiagle : diagTail p q σ n
        ≤ (∑ i ∈ S, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) := by
      rw [diagTail]
      exact Real.rpow_le_rpow
        (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
        (tail_sum_le_sum_of_card_ge hpq hq σ hσ hn.le hScard) (by positivity)
    calc diagTail p q σ n * ‖e.symm z‖
        ≤ (∑ i ∈ S, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) * ‖e.symm z‖ :=
          mul_le_mul_of_nonneg_right hdiagle (norm_nonneg _)
      _ ≤ ‖DiagCLMpq p q σ (e.symm z)‖ := hratio
theorem le_approximationNumber_DiagCLMpq (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    diagTail p q σ n ≤ approximationNumber (DiagCLMpq p q σ) n := by
  refine le_csInf (approximationSet_nonempty _ _) ?_
  rintro r ⟨L, hL, rfl⟩
  have hker : m - n ≤ Module.finrank 𝕜 (LinearMap.ker
      (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) := by
    have hrn := (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜]
      PiLp p (fun _ : Fin m => 𝕜)).finrank_range_add_finrank_ker
    have hrange : Module.finrank 𝕜 (LinearMap.range
        (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) ≤ n :=
      Module.finrank_le_of_rank_le hL
    rw [finrank_piLp] at hrn
    omega
  obtain ⟨x, hxV, hxne, hxbound⟩ := exists_norm_ratio_ge_DiagCLMpq hpq hq σ hσ hn
    (LinearMap.ker (L : PiLp q (fun _ : Fin m => 𝕜) →ₗ[𝕜] PiLp p (fun _ : Fin m => 𝕜))) hker
  have hLx : L x = 0 := LinearMap.mem_ker.mp hxV
  have happ : (DiagCLMpq p q σ - L) x = DiagCLMpq p q σ x := by
    simp [hLx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hxne
  refine le_of_mul_le_mul_right ?_ hxpos
  calc diagTail p q σ n * ‖x‖
      ≤ ‖DiagCLMpq p q σ x‖ := hxbound
    _ = ‖(DiagCLMpq p q σ - L) x‖ := by rw [happ]
    _ ≤ ‖DiagCLMpq p q σ - L‖ * ‖x‖ := (DiagCLMpq p q σ - L).le_opNorm x
theorem approximationNumber_DiagCLMpq_eq (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLMpq p q σ) n = diagTail p q σ n :=
  le_antisymm (approximationNumber_DiagCLMpq_le hpq hq σ hn.le)
    (le_approximationNumber_DiagCLMpq hpq hq σ hσ hn)
example (hpq : p < q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m) :
    diagTail p q (fun _ : Fin m => (1 : 𝕜)) n
      = ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
  have h1 := approximationNumber_DiagCLMpq_eq hpq hq (fun _ : Fin m => (1 : 𝕜))
    (fun _ _ _ => le_refl _) hn
  rw [DiagCLMpq_one] at h1
  rw [← h1]
  exact approximationNumber_idEmbed_eq hpq.le hq hn
example (σ : Fin m → 𝕜) (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    approximationNumber (DiagCLMpq p p σ) n = ‖σ ⟨n, hn⟩‖ := by
  rw [DiagCLMpq_self]; exact approximationNumber_DiagCLM_eq hσ hn
end MixedExponent
end SNumbers


