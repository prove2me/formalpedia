-- Prove2me | Definitions.Def_RPLib_S3_EllipticTermC
-- name    : RPLib_S3_EllipticTermC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:06:19.910907+00:00
-- url     : https://prove2.me/theorems/c053bc59-ff7c-4423-bc89-ee6fa40cf953
-- title:
--   The Eichler-Selberg trace formula, elliptic term part C: assembly of the elliptic term
-- statement:
--   The elliptic part of the kernel diagonal splits by trace $t$ with $t^2 < 4n$; each class contributes $-U_{k-2}(t,n)$ times its weight, where $U_{k-2}(t, n) = (\rho^{k-1} - \bar\rho^{k-1})/(\rho - \bar\rho)$ for the roots $\rho, \bar\rho$ of $X^2 - tX + n$; summed, the elliptic contribution to $\operatorname{Tr}(T_n \langle \delta \rangle)$ equals the elliptic term $A_2$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings); H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977

import Mathlib
import Definitions.Def_RPLib_S3_EllipticTermB
import Definitions.Def_RPLib_S3_KernelB2

/-!
# S3-EllCentralTerms, part C: assembly of the elliptic term

* `ellPart k M n δ' z`: the elliptic part `Σ'_{g ∈ Δ, t(g)² < 4 det g} φ_g(z)` of the kernel diagonal.
* `ellPart_eq`: it splits as `Σ_{t} (Σ'_{EllPos t} + Σ'_{EllNeg t})`, `t = i - 2n`, `i < 4n + 1`.
* `orbI_add` / `ell_norm`: `n^{k-1} B_k⁻¹ (I(ρ) + I(conj ρ)) = -U_{k-2}(t, n)`.
* `ellCount_adj`: `ellCount M δ' t n = ellCount M e t n` when `δ' e = n` (adjugate map `EllPos → EllNeg`).
* `ell_trace_term`: `n^{k-1} B_k⁻¹ ∫_{Γ₁(M)\ℍ} ellPart = ellG1 M k n δ` for `δ' = n δ`.
-/

open MeasureTheory Metric Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal Manifold MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllTerm

open RamanujanPetersson.Bergman RamanujanPetersson.Kernel RP.FundDomain RP.Petersson

/-! ## Part 1: the `U` identity and the normalisation -/

lemma conj_ellRho (t n : ℤ) : conj (ellRho t n) = ((t : ℂ) - Complex.I * (ellS t n : ℂ)) / 2 := by
  simp only [ellRho, map_div₀, map_add, map_mul, map_intCast, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

lemma ellRho_add (t n : ℤ) : ellRho t n + conj (ellRho t n) = t := by
  rw [conj_ellRho, ellRho]; ring

lemma ellRho_mul {t n : ℤ} (h : t ^ 2 ≤ 4 * n) : ellRho t n * conj (ellRho t n) = n := by
  have hs := ellS_sq h
  rw [conj_ellRho, ellRho]
  linear_combination (1 / 4 : ℂ) * hs + (-(ellS t n : ℂ) ^ 2 / 4) * Complex.I_sq

lemma ellRho_sub_ne {t n : ℤ} (h : t ^ 2 < 4 * n) : ellRho t n - conj (ellRho t n) ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  rw [Complex.sub_im, Complex.conj_im, ellRho_im, Complex.zero_im] at him
  have := ellS_pos h
  linarith

/-- `(ρ - ρ̄) U_m(t, n) = ρ^{m+1} - ρ̄^{m+1}`. -/
lemma U_rho (m : ℕ) {t n : ℤ} (h : t ^ 2 ≤ 4 * n) :
    (ellRho t n - conj (ellRho t n)) * (S3.chebU m t n : ℂ) =
      ellRho t n ^ (m + 1) - conj (ellRho t n) ^ (m + 1) := by
  have hU : (S3.chebU m t n : ℂ) =
      SymTrace.U m (ellRho t n + conj (ellRho t n)) (ellRho t n * conj (ellRho t n)) := by
    rw [ellRho_add, ellRho_mul h, S3.chebU]
    have h1 := SymTrace.map_U (Int.castRingHom ℂ) m t n
    simp only [eq_intCast] at h1
    exact h1
  have hg := geom_sum₂_mul (ellRho t n) (conj (ellRho t n)) (m + 1)
  simp only [Nat.add_sub_cancel] at hg
  rw [hU, SymTrace.U_add_mul, mul_comm (ellRho t n - conj (ellRho t n)), hg]

/-- `I(ρ) + I(ρ̄) = -4π (-2i)^{-(m+2)} U_m(t,n) / ((m+1) n^{m+1})`. -/
lemma orbI_add (m : ℕ) {t n : ℤ} (hn : 0 < n) (h : t ^ 2 < 4 * n) :
    orbI m (ellRho t n) + orbI m (conj (ellRho t n)) =
      -(4 * ((-2 * Complex.I) ^ (m + 2))⁻¹ * π * (S3.chebU m t n : ℂ) / (((m : ℂ) + 1) * (n : ℂ) ^ (m + 1))) := by
  have hD := ellRho_sub_ne h
  have hD' : conj (ellRho t n) - ellRho t n ≠ 0 := by
    intro h0; apply hD; linear_combination -h0
  have hmul := ellRho_mul h.le
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hρ : ellRho t n ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmul; exact hn0 hmul.symm
  have hρ' : conj (ellRho t n) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact hn0 hmul.symm
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hc : (-2 * Complex.I) ^ (m + 2) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hUe : (S3.chebU m t n : ℂ) =
      (ellRho t n ^ (m + 1) - conj (ellRho t n) ^ (m + 1)) / (ellRho t n - conj (ellRho t n)) := by
    rw [eq_div_iff hD, mul_comm]; exact U_rho m h.le
  rw [hUe, ← hmul, mul_pow (ellRho t n) (conj (ellRho t n))]
  simp only [orbI, Complex.conj_conj]
  field_simp
  ring

lemma negI_mul_I (m : ℕ) : (-2 * Complex.I) ^ (m + 2) * Complex.I ^ (m + 2) = 2 ^ (m + 2) := by
  rw [← mul_pow]
  congr 1
  linear_combination (-2 : ℂ) * Complex.I_sq

/-- **Normalisation:** `n^{m+1} B_{m+2}⁻¹ (I(ρ) + I(ρ̄)) = -U_m(t, n)`. -/
lemma ell_norm (m : ℕ) {t n : ℤ} (hn : 0 < n) (h : t ^ 2 < 4 * n) :
    (n : ℂ) ^ (m + 1) * (bergmanConst (m + 2))⁻¹ * (orbI m (ellRho t n) + orbI m (conj (ellRho t n))) =
      -(S3.chebU m t n : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hc : (-2 * Complex.I) ^ (m + 2) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hP : Complex.I ^ (m + 2) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm2 : ((m + 2 : ℕ) : ℂ) - 1 = (m : ℂ) + 1 := by push_cast; ring
  rw [orbI_add m hn h, bergmanConst, hm2, ← negI_mul_I m]
  field_simp

/-! ## Part 2: `ellCount` facts -/

/-- `ellCount` vanishes off the elliptic range (no reduced forms of discriminant `≥ 0`). -/
lemma ellCount_eq_zero {M : ℕ} [NeZero M] (δ' : ZMod M) {t : ℤ} {n : ℕ} (h : 4 * (n : ℤ) ≤ t ^ 2) :
    S3.ellCount M δ' t n = 0 := by
  unfold S3.ellCount
  refine Finset.sum_eq_zero fun Q hQ => ?_
  exfalso
  obtain ⟨a, b, c⟩ := Q
  rw [S3.redForms, Finset.mem_filter] at hQ
  obtain ⟨-, h1, h2, h3, h4, h5, -⟩ := hQ
  have e1 : 1 ≤ a := h1
  have e2 : b ^ 2 - 4 * a * c = t ^ 2 - 4 * n := h2
  have e3 : -a ≤ b := h3
  have e4 : b ≤ a := h4
  have e5 : a ≤ c := h5
  nlinarith [mul_nonneg (sub_nonneg.2 e4) (by linarith : (0 : ℤ) ≤ a + b),
    mul_le_mul_of_nonneg_left e5 (by linarith : (0 : ℤ) ≤ a),
    mul_pos (by linarith : (0 : ℤ) < a) (by linarith : (0 : ℤ) < a)]

lemma adjM_adjM (g : S3.Conj.Mat) : adjM (adjM g) = g := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [adjM]

lemma adjM_00 (g : S3.Conj.Mat) : adjM g 0 0 = g 1 1 := by simp [adjM]
lemma adjM_01 (g : S3.Conj.Mat) : adjM g 0 1 = -g 0 1 := by simp [adjM]
lemma adjM_10 (g : S3.Conj.Mat) : adjM g 1 0 = -g 1 0 := by simp [adjM]
lemma adjM_11 (g : S3.Conj.Mat) : adjM g 1 1 = g 0 0 := by simp [adjM]

lemma adjM_trace (g : S3.Conj.Mat) : (adjM g).trace = g.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, adjM_00, adjM_11]; ring

lemma adjM_conj (h : SL(2, ℤ)) (g : S3.Conj.Mat) :
    adjM (S3.Conj.conj h g) = S3.Conj.conj h (adjM g) := by
  obtain ⟨e00, e01, e10, e11⟩ := conj_entries h g
  obtain ⟨f00, f01, f10, f11⟩ := conj_entries h (adjM g)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, adjM_00, adjM_01, adjM_10, adjM_11,
      e00, e01, e10, e11, f00, f01, f10, f11] <;> ring

/-- From `a ≡ u`, `c ≡ 0` and `u v = det` (with `u` a unit): `d ≡ v`. -/
lemma cast_11 {M : ℕ} {x : S3.Conj.Mat} {u v : ZMod M} (hu : IsUnit u)
    (hdet : u * v = ((x.det : ℤ) : ZMod M)) (h00 : ((x 0 0 : ℤ) : ZMod M) = u)
    (h10 : ((x 1 0 : ℤ) : ZMod M) = 0) : ((x 1 1 : ℤ) : ZMod M) = v := by
  have h : ((x.det : ℤ) : ZMod M) = u * ((x 1 1 : ℤ) : ZMod M) := by
    rw [Matrix.det_fin_two]; push_cast; rw [h00, h10]; ring
  exact hu.mul_left_cancel (h.symm.trans hdet.symm)

lemma adj_mem_neg {M : ℕ} {δ' e : ZMod M} {t : ℤ} {n : ℕ} (hu : IsUnit δ') (he : δ' * e = n)
    {x : S3.Conj.Mat} (hx : x ∈ S3.Conj.EllPos M δ' t n) : adjM x ∈ S3.Conj.EllNeg M e t n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := S3.Conj.mem_EllPos_iff'.1 hx
  rw [S3.Conj.mem_EllNeg_iff', det_adjM, adjM_trace, adjM_00, adjM_10]
  refine ⟨h1, h2, by linarith, h4, cast_11 hu (by rw [h1, he, Int.cast_natCast]) h5 h6, ?_⟩
  push_cast; rw [h6, neg_zero]

lemma adj_mem_pos {M : ℕ} {δ' e : ZMod M} {t : ℤ} {n : ℕ} (hv : IsUnit e) (he : δ' * e = n)
    {x : S3.Conj.Mat} (hx : x ∈ S3.Conj.EllNeg M e t n) : adjM x ∈ S3.Conj.EllPos M δ' t n := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := S3.Conj.mem_EllNeg_iff'.1 hx
  rw [S3.Conj.mem_EllPos_iff', det_adjM, adjM_trace, adjM_00, adjM_10]
  refine ⟨h1, h2, by linarith, h4, cast_11 hv (by rw [h1, mul_comm, he, Int.cast_natCast]) h5 h6, ?_⟩
  push_cast; rw [h6, neg_zero]

/-- The adjugate bijection `EllPos M δ' t n ≃ EllNeg M e t n` (`δ' e = n`). -/
def adjEquiv {M : ℕ} (δ' e : ZMod M) (t : ℤ) (n : ℕ) (hu : IsUnit δ') (hv : IsUnit e) (he : δ' * e = n) :
    S3.Conj.EllPos M δ' t n ≃ S3.Conj.EllNeg M e t n where
  toFun x := ⟨adjM x, adj_mem_neg hu he x.2⟩
  invFun x := ⟨adjM x, adj_mem_pos hv he x.2⟩
  left_inv x := Subtype.ext (adjM_adjM x.1)
  right_inv x := Subtype.ext (adjM_adjM x.1)

/-- **`ellCount M δ' t n = ellCount M e t n`** when `δ' e = n` (both units). -/
theorem ellCount_adj {M : ℕ} [NeZero M] (δ' e : ZMod M) (t : ℤ) (n : ℕ) (hu : IsUnit δ') (hv : IsUnit e)
    (he : δ' * e = n) : S3.ellCount M δ' t n = S3.ellCount M e t n := by
  rw [← S3.Conj.classSum_EllPos δ' t n, ← S3.Conj.classSum_EllNeg M e t n]
  exact S3.Conj.classSum_congr (MulEquiv.refl _) (adjEquiv δ' e t n hu hv he)
    (fun h x => Subtype.ext (adjM_conj (h : SL(2, ℤ)) x.1))

/-! ## Part 3: the elliptic part of the diagonal and its partition -/

/-- The elliptic part of the kernel diagonal: `Σ'_{g ∈ Δ, (a+d)² < 4 det g} φ_g(z)`. -/
def ellPart (k M : ℕ) (n : ℤ) (δ' : ZMod M) (z : ℍ) : ℂ :=
  ∑' g : DeltaSet M n δ', if ((g : S3.Conj.Mat) 0 0 + (g : S3.Conj.Mat) 1 1) ^ 2 < 4 * (g : S3.Conj.Mat).det
    then phiG k g z else 0

lemma of_EllPos {M : ℕ} {δ' : ZMod M} {s : ℤ} {n : ℕ} {g : S3.Conj.Mat} (hg : g ∈ S3.Conj.EllPos M δ' s n) :
    g ∈ DeltaSet M n δ' ∧ (g 0 0 + g 1 1) ^ 2 < 4 * g.det ∧ g 0 0 + g 1 1 = s := by
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := S3.Conj.mem_EllPos_iff'.1 hg
  rw [← Matrix.trace_fin_two, h2, h1]
  exact ⟨⟨h1, h6, h5⟩, h4, rfl⟩

lemma of_EllNeg {M : ℕ} {δ' : ZMod M} {s : ℤ} {n : ℕ} {g : S3.Conj.Mat} (hg : g ∈ S3.Conj.EllNeg M δ' s n) :
    g ∈ DeltaSet M n δ' ∧ (g 0 0 + g 1 1) ^ 2 < 4 * g.det ∧ g 0 0 + g 1 1 = s := by
  obtain ⟨h1, h2, -, h4, h5, h6⟩ := S3.Conj.mem_EllNeg_iff'.1 hg
  rw [← Matrix.trace_fin_two, h2, h1]
  exact ⟨⟨h1, h6, h5⟩, h4, rfl⟩

/-- Pointwise partition of the elliptic indicator by trace and sign of `c`. -/
lemma ind_eq {M : ℕ} (δ' : ZMod M) {n : ℕ} (hn : 0 < n) (f : S3.Conj.Mat → ℂ) (g : S3.Conj.Mat) :
    (DeltaSet M n δ').indicator (fun g => if (g 0 0 + g 1 1) ^ 2 < 4 * g.det then f g else 0) g =
      ∑ i ∈ Finset.range (4 * n + 1),
        ((S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n).indicator f g +
          (S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n).indicator f g) := by
  by_cases hge : g ∈ DeltaSet M n δ' ∧ (g 0 0 + g 1 1) ^ 2 < 4 * g.det
  · obtain ⟨hD, hE⟩ := hge
    rw [Set.indicator_of_mem hD, if_pos hE]
    obtain ⟨hdet, h10, h00⟩ := hD
    set t := g 0 0 + g 1 1 with ht
    have hE' : t ^ 2 < 4 * (n : ℤ) := by rw [← hdet]; exact hE
    have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
    have hsq : t ^ 2 < (2 * (n : ℤ)) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hn1 (by linarith : (0 : ℤ) ≤ n)]
    obtain ⟨hlo', hhi'⟩ := abs_lt.1 (abs_lt_of_sq_lt_sq hsq (by linarith))
    have hlo : -(2 * (n : ℤ)) ≤ t := hlo'.le
    have hhi : t ≤ 2 * (n : ℤ) := hhi'.le
    have hi0 : (((t + 2 * n).toNat : ℕ) : ℤ) - 2 * n = t := by
      rw [Int.toNat_of_nonneg (by linarith)]; ring
    have hmem : (t + 2 * n).toNat ∈ Finset.range (4 * n + 1) := by
      rw [Finset.mem_range]; omega
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · rw [hi0]
      have hc := ell_c_ne_zero g hE
      have htr : g.trace = t := by rw [Matrix.trace_fin_two]
      rcases lt_or_gt_of_ne hc with hneg | hpos
      · have hN : g ∈ S3.Conj.EllNeg M δ' t n := S3.Conj.mem_EllNeg_iff'.2 ⟨hdet, htr, hneg, hE', h00, h10⟩
        have hP : g ∉ S3.Conj.EllPos M δ' t n := fun hP =>
          absurd (S3.Conj.mem_EllPos_iff'.1 hP).2.2.1 (not_lt.2 hneg.le)
        rw [Set.indicator_of_mem hN, Set.indicator_of_notMem hP, zero_add]
      · have hP : g ∈ S3.Conj.EllPos M δ' t n := S3.Conj.mem_EllPos_iff'.2 ⟨hdet, htr, hpos, hE', h00, h10⟩
        have hN : g ∉ S3.Conj.EllNeg M δ' t n := fun hN =>
          absurd (S3.Conj.mem_EllNeg_iff'.1 hN).2.2.1 (not_lt.2 hpos.le)
        rw [Set.indicator_of_mem hP, Set.indicator_of_notMem hN, add_zero]
    · intro i _ hi
      have hne : (i : ℤ) - 2 * n ≠ t := by
        intro h; apply hi; rw [← hi0] at h; omega
      have hP : g ∉ S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n := fun hP => hne (of_EllPos hP).2.2.symm
      have hN : g ∉ S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n := fun hN => hne (of_EllNeg hN).2.2.symm
      rw [Set.indicator_of_notMem hP, Set.indicator_of_notMem hN, add_zero]
  · have hL : (DeltaSet M n δ').indicator (fun g => if (g 0 0 + g 1 1) ^ 2 < 4 * g.det then f g else 0) g = 0 := by
      by_cases hD : g ∈ DeltaSet M n δ'
      · rw [Set.indicator_of_mem hD, if_neg (fun hE => hge ⟨hD, hE⟩)]
      · rw [Set.indicator_of_notMem hD]
    rw [hL]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    have hP : g ∉ S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n := fun hP =>
      hge ⟨(of_EllPos hP).1, (of_EllPos hP).2.1⟩
    have hN : g ∉ S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n := fun hN =>
      hge ⟨(of_EllNeg hN).1, (of_EllNeg hN).2.1⟩
    rw [Set.indicator_of_notMem hP, Set.indicator_of_notMem hN, add_zero]

/-- **Partition of the elliptic part** by trace `t = i - 2n` and the sign of `c`. -/
theorem ellPart_eq {M : ℕ} (k : ℕ) (hk : 3 ≤ k) (δ' : ZMod M) {n : ℕ} (hn : 0 < n) (z : ℍ) :
    ellPart k M n δ' z = ∑ i ∈ Finset.range (4 * n + 1),
      (∑' x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n, phiG k x z +
        ∑' x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n, phiG k x z) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hsP : ∀ s : ℤ, Summable ((S3.Conj.EllPos M δ' s n).indicator (fun g : S3.Conj.Mat => phiG k g z)) :=
    fun s => summable_subtype_iff_indicator.1 (summable_phiG_sub k hk hn' δ' (X := S3.Conj.EllPos M δ' s n)
      Subtype.val Subtype.val_injective (fun x => (of_EllPos x.2).1) z)
  have hsN : ∀ s : ℤ, Summable ((S3.Conj.EllNeg M δ' s n).indicator (fun g : S3.Conj.Mat => phiG k g z)) :=
    fun s => summable_subtype_iff_indicator.1 (summable_phiG_sub k hk hn' δ' (X := S3.Conj.EllNeg M δ' s n)
      Subtype.val Subtype.val_injective (fun x => (of_EllNeg x.2).1) z)
  rw [ellPart, tsum_subtype (DeltaSet M n δ') (fun g : S3.Conj.Mat =>
      if (g 0 0 + g 1 1) ^ 2 < 4 * g.det then phiG k g z else 0),
    tsum_congr (ind_eq δ' hn (fun g => phiG k g z)),
    Summable.tsum_finsetSum (fun (i : ℕ) _ => (hsP ((i : ℤ) - 2 * n)).add (hsN ((i : ℤ) - 2 * n)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_add (hsP _) (hsN _), ← tsum_subtype, ← tsum_subtype]

/-! ## Part 4: the integral of the elliptic part -/

/-- **Elliptic unfolding:** `∫_{Γ₁\ℍ} ellPart = Σ_t ellCount(δ', t) (I(ρ_t) + I(ρ̄_t))`. -/
theorem ellPart_integral {M : ℕ} [NeZero M] (hM : 3 ≤ M) (m : ℕ) (hm : 1 ≤ m) (δ' : ZMod M) {n : ℕ}
    (hn : 0 < n) :
    IntegrableOn (ellPart (m + 2) M n δ') (fdom (Gamma1 M)) ∧
      ∫ z in fdom (Gamma1 M), ellPart (m + 2) M n δ' z =
        ∑ i ∈ Finset.range (4 * n + 1), ((S3.ellCount M δ' ((i : ℤ) - 2 * n) n : ℚ) : ℂ) *
          (orbI m (ellRho ((i : ℤ) - 2 * n) n) + orbI m (conj (ellRho ((i : ℤ) - 2 * n) n))) := by
  have hfun : ellPart (m + 2) M n δ' = fun z => ∑ i ∈ Finset.range (4 * n + 1),
      (∑' x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n, phiG (m + 2) x z +
        ∑' x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n, phiG (m + 2) x z) :=
    funext (ellPart_eq (m + 2) (by omega) δ' hn)
  have hint : ∀ i ∈ Finset.range (4 * n + 1), Integrable (fun z =>
      ∑' x : S3.Conj.EllPos M δ' ((i : ℤ) - 2 * n) n, phiG (m + 2) x z +
        ∑' x : S3.Conj.EllNeg M δ' ((i : ℤ) - 2 * n) n, phiG (m + 2) x z)
      (volume.restrict (fdom (Gamma1 M))) := fun i _ =>
    (ellPos_unfold hM m hm δ' _ hn).1.add (ellNeg_unfold hM m hm δ' _ hn).1
  rw [hfun]
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_add (ellPos_unfold hM m hm δ' ((i : ℤ) - 2 * n) hn).1 (ellNeg_unfold hM m hm δ' ((i : ℤ) - 2 * n) hn).1,
    (ellPos_unfold hM m hm δ' ((i : ℤ) - 2 * n) hn).2, (ellNeg_unfold hM m hm δ' ((i : ℤ) - 2 * n) hn).2, mul_add]

/-! ## Part 5: the elliptic term of the trace formula -/

/-- **Elliptic term:** with `δ' = n δ`, `n^{k-1} B_k⁻¹ ∫_{Γ₁(M)\ℍ} ellPart = ellG1 M k n δ`. -/
theorem ell_trace_term {M : ℕ} [NeZero M] (hM : 3 ≤ M) {k : ℕ} (hk : 3 ≤ k) {n : ℕ} (hn : 0 < n)
    (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    IntegrableOn (ellPart k M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M)) (fdom (Gamma1 M)) ∧
      (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ *
          ∫ z in fdom (Gamma1 M), ellPart k M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z =
        ((S3.ellG1 M k n (δ : ZMod M) : ℚ) : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  obtain ⟨hI, hval⟩ := ellPart_integral hM m hm ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) hn
  refine ⟨hI, ?_⟩
  have hu : IsUnit ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) := Units.isUnit _
  have hv : IsUnit ((δ : ZMod M)⁻¹) := by rw [ZMod.inv_coe_unit]; exact Units.isUnit _
  have he : ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) * (δ : ZMod M)⁻¹ = n := by
    rw [ZMod.inv_coe_unit, Units.val_mul, coe_unitOf hnM, mul_assoc, Units.mul_inv, mul_one]
  rw [hval, S3.ellG1, Finset.mul_sum, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  simp only [Rat.cast_neg, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases ht : ((i : ℤ) - 2 * n) ^ 2 < 4 * (n : ℤ)
  · rw [ellCount_adj _ _ _ n hu hv he]
    have hN := ell_norm m (t := (i : ℤ) - 2 * n) (n := (n : ℤ)) (by exact_mod_cast hn) ht
    push_cast at hN
    rw [mul_left_comm, hN]
    ring
  · have h4 : 4 * (n : ℤ) ≤ ((i : ℤ) - 2 * n) ^ 2 := not_lt.1 ht
    rw [ellCount_eq_zero _ h4, ellCount_eq_zero _ h4]
    simp

end RamanujanPetersson.EllTerm


