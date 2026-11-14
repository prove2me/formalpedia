-- Prove2me | Definitions.Def_RPLib_S3_KernelC
-- name    : RPLib_S3_KernelC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:02:30.200804+00:00
-- url     : https://prove2.me/theorems/96b7f531-5c30-4c9e-bb86-d7b7982cd6e2
-- title:
--   The Eichler-Selberg trace formula, kernel part C: the coset sum is $T_n \langle \delta \rangle$
-- statement:
--   For the Hermite normal form representatives, $n^{k-1} \sum_i (a_i - c_i w)^{-k} f(\operatorname{adj}(\alpha_i) w) = (T_n \langle \delta \rangle f)(w)$ for every $f \in S_k(\Gamma_1(M))$, where $T_n$ is the Hecke operator and $\langle \delta \rangle$ the diamond operator.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Sections 5.2 and 5.3

import Mathlib
import Definitions.Def_RPLib_S3_KernelB2
import Definitions.Def_RPLib_S1_HeckeAlgebra
import Definitions.Def_RPLib_S1_QExp
import Definitions.Def_RPLib_S1_FinDim

/-!
# S3-Kernel, part C: the coset sum is `n^(1-k) T_n ⟨δ⟩ f`

* `cosetSum_eq`: `n^(k-1) Σ_i (a_i - c_i w)^(-k) f(adj α_i · w) = (T_n ⟨δ⟩ f)(w)` for the HNF representatives
  `α_i = alphaHNF n (n δ) i` (proved on `S_k(M, χ)` by `q`-expansions, then for all `f` by `sum_proj`).
-/

open Filter Complex UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Topology Manifold ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Kernel

open RP.FundDomain RP.Petersson RamanujanPetersson.Bergman RamanujanPetersson.Diamond
  RamanujanPetersson.Hecke
open RamanujanPetersson.HeckeAlgebra (heckeTn coeff_heckeTn_chi)

/-! ### Affine points of `ℍ` -/

/-- The point `(a τ + b) / d` (`a, d > 0`). -/
def affPt (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) : ℍ :=
  UpperHalfPlane.mk (((a : ℂ) * τ + (b : ℂ)) / (d : ℂ)) (by
    rw [Complex.div_ofReal_im, Complex.add_im, Complex.im_ofReal_mul, Complex.ofReal_im, add_zero]
    exact div_pos (mul_pos ha τ.im_pos) hd)

lemma coe_affPt (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    (affPt a b d ha hd τ : ℂ) = ((a : ℂ) * τ + (b : ℂ)) / (d : ℂ) := UpperHalfPlane.coe_mk _ _

lemma divisor_pos' {n : ℕ} (A : n.divisors) : 0 < A.1 := Nat.pos_of_mem_divisors A.2

lemma quot_pos {n : ℕ} (_hn : 0 < n) (A : n.divisors) : 0 < n / A.1 :=
  Nat.div_pos (Nat.divisor_le A.2) (divisor_pos' A)

/-- `((A τ) + j) / D` with `D = n / A`. -/
def ptA {n : ℕ} (hn : 0 < n) (A : n.divisors) (j : ℕ) (τ : ℍ) : ℍ :=
  affPt 1 j ((n / A.1 : ℕ) : ℝ) one_pos (Nat.cast_pos.2 (quot_pos hn A))
    (affPt (A.1 : ℝ) 0 1 (Nat.cast_pos.2 (divisor_pos' A)) one_pos τ)

lemma hu_ptA {n : ℕ} (hn : 0 < n) (A : n.divisors) (j : ℕ) (w : ℍ) :
    ((n / A.1 : ℕ) : ℂ) * (ptA hn A j w : ℂ) = (A.1 : ℂ) * w + (j : ℂ) := by
  have hD0 : ((n / A.1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (quot_pos hn A).ne'
  rw [ptA, coe_affPt, coe_affPt]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_natCast, one_mul, add_zero, div_one]
  field_simp

/-! ### One coset term -/

variable {M : ℕ} [NeZero M]

lemma adjM_11 (g : Matrix (Fin 2) (Fin 2) ℤ) : adjM g 1 1 = g 0 0 := by simp [adjM]
lemma adjM_01 (g : Matrix (Fin 2) (Fin 2) ℤ) : adjM g 0 1 = -g 0 1 := by simp [adjM]

/-- The summand of the reproducing identity. -/
def cterm (k n : ℕ) (δ' : (ZMod M)ˣ) (f : ℍ → ℂ) (w : ℍ) (i : HNFIdx n) : ℂ :=
  ((((alphaHNF n δ' i 0 0 : ℤ) : ℂ) - ((alphaHNF n δ' i 1 0 : ℤ) : ℂ) * w) ^ k)⁻¹ *
    f (adjPt (alphaHNF n δ' i) w)

theorem term_HNF {k n : ℕ} (hn : 0 < n) (δ' : (ZMod M)ˣ) {χ : DirichletCharacter ℂ M} {f : S1 M k}
    (hf : f ∈ chiSubspace k χ) (i : HNFIdx n) (w u : ℍ)
    (hu : ((n / i.1.1 : ℕ) : ℂ) * (u : ℂ) = (i.1.1 : ℂ) * w + (i.2.1 : ℂ)) :
    cterm k n δ' f w i =
      χ ((δ' * (unitOf M (n / i.1.1))⁻¹ : (ZMod M)ˣ) : ZMod M) *
        ((((n / i.1.1 : ℕ) : ℂ) ^ k)⁻¹ * f u) := by
  have hdet : 0 < (alphaHNF n δ' i).det := by
    rw [alphaHNF, det_adjM, det_betaHNF]; exact_mod_cast hn
  have hJ : denom (sigmaD δ' (n / i.1.1)) u ≠ 0 := denom_ne_zero _ u
  have hJ' : ((sigmaD δ' (n / i.1.1) 1 0 : ℤ) : ℂ) * u + ((sigmaD δ' (n / i.1.1) 1 1 : ℤ) : ℂ) ≠ 0 := by
    rwa [← denom_SL]
  have h00 : alphaHNF n δ' i 0 0 =
      sigmaD δ' (n / i.1.1) 1 0 * (i.2.1 : ℤ) + sigmaD δ' (n / i.1.1) 1 1 * ((n / i.1.1 : ℕ) : ℤ) := by
    rw [alphaHNF, adjM_00, betaHNF, mul_Tmat_11]
  have h10 : alphaHNF n δ' i 1 0 = -(sigmaD δ' (n / i.1.1) 1 0 * (i.1.1 : ℤ)) := by
    rw [alphaHNF, adjM_10, betaHNF, mul_Tmat_10]
  have h11 : alphaHNF n δ' i 1 1 = sigmaD δ' (n / i.1.1) 0 0 * (i.1.1 : ℤ) := by
    rw [alphaHNF, adjM_11, betaHNF, mul_Tmat_00]
  have h01 : alphaHNF n δ' i 0 1 =
      -(sigmaD δ' (n / i.1.1) 0 0 * (i.2.1 : ℤ) + sigmaD δ' (n / i.1.1) 0 1 * ((n / i.1.1 : ℕ) : ℤ)) := by
    rw [alphaHNF, adjM_01, betaHNF, mul_Tmat_01]
  -- `a - c w = D j(σ, u)`
  have e1 : ((alphaHNF n δ' i 0 0 : ℤ) : ℂ) - ((alphaHNF n δ' i 1 0 : ℤ) : ℂ) * w =
      ((n / i.1.1 : ℕ) : ℂ) * denom (sigmaD δ' (n / i.1.1)) u := by
    rw [h00, h10, denom_SL]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_natCast]
    linear_combination (-((sigmaD δ' (n / i.1.1) 1 0 : ℤ) : ℂ)) * hu
  -- `adj α · w = σ · u`
  have e2 : adjPt (alphaHNF n δ' i) w = sigmaD δ' (n / i.1.1) • u := by
    apply UpperHalfPlane.coe_inj.1
    have hden : ((alphaHNF n δ' i 0 0 : ℤ) : ℂ) - ((alphaHNF n δ' i 1 0 : ℤ) : ℂ) * w ≠ 0 :=
      denom_adj_ne hdet w
    rw [coe_adjPt hdet, coe_smul_SL, div_eq_div_iff hden hJ', h00, h10, h11, h01]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_neg, Int.cast_natCast]
    linear_combination (((sigmaD δ' (n / i.1.1) 0 1 : ℤ) : ℂ) * ((sigmaD δ' (n / i.1.1) 1 0 : ℤ) : ℂ) -
      ((sigmaD δ' (n / i.1.1) 0 0 : ℤ) : ℂ) * ((sigmaD δ' (n / i.1.1) 1 1 : ℤ) : ℂ)) * hu
  -- the character relation at `u`
  have hs := congrFun (hf _ (sigmaD_mem δ' (n / i.1.1))) u
  rw [SL_slash_apply, Pi.smul_apply, smul_eq_mul, sigmaD_11, zpow_neg, zpow_natCast] at hs
  have hf' : f (sigmaD δ' (n / i.1.1) • u) =
      χ ((δ' * (unitOf M (n / i.1.1))⁻¹ : (ZMod M)ˣ) : ZMod M) * f u *
        denom (sigmaD δ' (n / i.1.1)) u ^ k := by
    rw [← hs, inv_mul_cancel_right₀ (pow_ne_zero _ hJ)]
  have hX : denom (sigmaD δ' (n / i.1.1)) u ^ k * (denom (sigmaD δ' (n / i.1.1)) u ^ k)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ hJ)
  rw [cterm, e1, e2, hf']
  linear_combination (χ ((δ' * (unitOf M (n / i.1.1))⁻¹ : (ZMod M)ˣ) : ZMod M) *
    ((((n / i.1.1 : ℕ) : ℂ) ^ k)⁻¹ * f u)) * hX

/-! ### `q`-expansion of the coset sum -/

/-- `D⁻¹ Σ_{j < D} f((A τ + j)/D)`, `D = n / A`. -/
def hFun (f : ℍ → ℂ) {n : ℕ} (hn : 0 < n) (A : n.divisors) (τ : ℍ) : ℂ :=
  (((n / A.1 : ℕ) : ℂ))⁻¹ * ∑ j ∈ Finset.range (n / A.1), f (ptA hn A j τ)

/-- The coefficient `[A ∣ m] a(D m / A)`. -/
def qcoef (a : ℕ → ℂ) (n A m : ℕ) : ℂ := if A ∣ m then a ((n / A) * (m / A)) else 0

lemma hasQExpansion_hFun {f : ℍ → ℂ} {a : ℕ → ℂ} (hf : QExp.HasQExpansion f a) {n : ℕ} (hn : 0 < n)
    (A : n.divisors) : QExp.HasQExpansion (hFun f hn A) (fun m => qcoef a n A.1 m) :=
  (hf.U (n / A.1) (quot_pos hn A)
    (fun j τ => affPt 1 j ((n / A.1 : ℕ) : ℝ) one_pos (Nat.cast_pos.2 (quot_pos hn A)) τ)
    (fun j τ => by
      rw [coe_affPt]
      simp only [Complex.ofReal_one, Complex.ofReal_natCast, one_mul])).comp_mul A.1 (divisor_pos' A)
    (fun τ => affPt (A.1 : ℝ) 0 1 (Nat.cast_pos.2 (divisor_pos' A)) one_pos τ)
    (fun τ => by
      rw [coe_affPt]
      simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.ofReal_natCast, add_zero, div_one])

lemma hasQExpansion_fsum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → ℍ → ℂ) (a : ι → ℕ → ℂ)
    (h : ∀ i ∈ s, QExp.HasQExpansion (F i) (a i)) :
    QExp.HasQExpansion (fun τ => ∑ i ∈ s, c i * F i τ) (fun m => ∑ i ∈ s, c i * a i m) := by
  intro τ
  have H := hasSum_sum (fun i hi => (h i hi τ).mul_left (c i))
  simp only [Finset.sum_mul, mul_assoc] at H ⊢
  exact H

/-- The per-divisor constant `χ(n δ / D) D^(1-k)`. -/
def cA (χ : DirichletCharacter ℂ M) (k n : ℕ) (δ : (ZMod M)ˣ) (A : ℕ) : ℂ :=
  χ ((unitOf M n * δ * (unitOf M (n / A))⁻¹ : (ZMod M)ˣ) : ZMod M) *
    ((((n / A : ℕ) : ℂ) ^ k)⁻¹ * ((n / A : ℕ) : ℂ))

omit [NeZero M] in
lemma coeff_match {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ)
    (χ : DirichletCharacter ℂ M) (a : ℕ → ℂ) (m : ℕ) :
    (n : ℂ) ^ (k - 1) * ∑ A ∈ n.divisors, cA χ k n δ A * qcoef a n A m =
      χ (δ : ZMod M) * ∑ d ∈ (Nat.gcd m n).divisors, χ d * (d : ℂ) ^ ((k : ℤ) - 1) * a (m * n / d ^ 2) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hfilter : n.divisors.filter (· ∣ m) = (Nat.gcd m n).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, h1⟩, (Nat.gcd_pos_of_pos_right m hn).ne'⟩
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, hn.ne'⟩, h1⟩
  rw [Finset.mul_sum, Finset.mul_sum, ← hfilter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun A hA => ?_
  have hAn : A ∣ n := Nat.dvd_of_mem_divisors hA
  have hApos : 0 < A := Nat.pos_of_mem_divisors hA
  have hDpos : 0 < n / A := Nat.div_pos (Nat.divisor_le hA) hApos
  have hDM : (n / A).Coprime M := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hAn) hnM
  unfold qcoef
  split_ifs with hAm
  · have hidx : n / A * (m / A) = m * n / A ^ 2 := by
      rw [Nat.div_mul_div_comm hAn hAm, mul_comm n m, sq]
    have hch : ((unitOf M n * δ * (unitOf M (n / A))⁻¹ : (ZMod M)ˣ) : ZMod M) = (A : ZMod M) * δ := by
      have h1 : (((unitOf M (n / A))⁻¹ : (ZMod M)ˣ) : ZMod M) * ((n / A : ℕ) : ZMod M) = 1 := by
        rw [← coe_unitOf hDM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hn' : (n : ZMod M) = (A : ZMod M) * ((n / A : ℕ) : ZMod M) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hAn]
      rw [Units.val_mul, Units.val_mul, coe_unitOf hnM, hn']
      linear_combination ((A : ZMod M) * δ) * h1
    have hnc : (n : ℂ) = (A : ℂ) * ((n / A : ℕ) : ℂ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hAn]
    have hD0 : ((n / A : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hDpos.ne'
    have hz : (A : ℂ) ^ (((k' + 1 : ℕ) : ℤ) - 1) = (A : ℂ) ^ k' := by
      rw [show (((k' + 1 : ℕ) : ℤ) - 1) = (k' : ℤ) by push_cast; ring, zpow_natCast]
    rw [cA, hch, map_mul, hidx, hz, Nat.add_sub_cancel, hnc]
    field_simp
    ring
  · simp

/-- **Identification on `S_k(M, χ)`.** -/
theorem cosetSum_chi {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ)
    {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : f ∈ chiSubspace k χ) (w : ℍ) :
    (n : ℂ) ^ (k - 1) * ∑ i : HNFIdx n, cterm k n (unitOf M n * δ) f w i =
      heckeTn (k : ℤ) n (diamond (k : ℤ) δ f) w := by
  have hfq : QExp.HasQExpansion f (fun m => (qExpansion 1 f).coeff m) :=
    QExp.hasQExpansion_cuspForm_Gamma1 (f := f)
  have hsum : ∑ i : HNFIdx n, cterm k n (unitOf M n * δ) f w i =
      ∑ A : n.divisors, cA χ k n δ A.1 * hFun f hn A w := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun A _ => ?_
    have hD0 : ((n / A.1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (quot_pos hn A).ne'
    have e : ∀ b : Fin (n / A.1), cterm k n (unitOf M n * δ) f w ⟨A, b⟩ =
        χ ((unitOf M n * δ * (unitOf M (n / A.1))⁻¹ : (ZMod M)ˣ) : ZMod M) *
          ((((n / A.1 : ℕ) : ℂ) ^ k)⁻¹ * f (ptA hn A b w)) :=
      fun b => term_HNF hn _ hf ⟨A, b⟩ w _ (hu_ptA hn A b w)
    rw [Finset.sum_congr rfl fun b _ => e b, ← Finset.mul_sum, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => f (ptA hn A j w))]
    simp only [cA, hFun, mul_assoc, mul_inv_cancel_left₀ hD0]
  have hL := hasQExpansion_fsum Finset.univ (fun A : n.divisors => cA χ k n δ A.1)
    (fun A => hFun f hn A) (fun A m => qcoef (fun m => (qExpansion 1 f).coeff m) n A.1 m)
    (fun A _ => hasQExpansion_hFun hfq hn A)
  have hT := QExp.hasQExpansion_cuspForm_Gamma1 (f := heckeTn (k : ℤ) n f)
  have hdiam : diamond (k : ℤ) δ f = χ (δ : ZMod M) • f :=
    (mem_chiSubspace_iff_diamond (k : ℤ) χ f).1 hf δ
  have hRw : heckeTn (k : ℤ) n (diamond (k : ℤ) δ f) w = χ (δ : ZMod M) * heckeTn (k : ℤ) n f w := by
    rw [hdiam, map_smul]; rfl
  have H1 := (hL w).mul_left ((n : ℂ) ^ (k - 1))
  have H2 := (hT w).mul_left (χ (δ : ZMod M))
  rw [hsum, hRw]
  refine H1.unique ?_
  convert H2 using 1
  funext m
  dsimp only
  rw [coeff_heckeTn_chi (k : ℤ) hf hn m,
    Finset.sum_coe_sort n.divisors (fun A => cA χ k n δ A * qcoef (fun m => (qExpansion 1 f).coeff m) n A m)]
  have hc := coeff_match hk hn hnM δ χ (fun m => (qExpansion 1 f).coeff m) m
  rw [← mul_assoc, hc, mul_assoc]

variable (M) in
/-- Evaluation at a point. -/
def evalL (k : ℤ) (z : ℍ) : S1 M k →ₗ[ℂ] ℂ where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero M] in
lemma sum_apply' {k : ℤ} {ι : Type*} (s : Finset ι) (g : ι → S1 M k) (z : ℍ) :
    (∑ i ∈ s, g i) z = ∑ i ∈ s, g i z :=
  map_sum (evalL M k z) g s

/-- **Identification**: `n^(k-1) Σ_i (a_i - c_i w)^(-k) f(adj α_i · w) = (T_n ⟨δ⟩ f)(w)`. -/
theorem cosetSum_eq {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ)
    (f : S1 M k) (w : ℍ) :
    (n : ℂ) ^ (k - 1) * ∑ i : HNFIdx n, cterm k n (unitOf M n * δ) f w i =
      heckeTn (k : ℤ) n (diamond (k : ℤ) δ f) w := by
  rw [← sum_proj (k : ℤ) f]
  simp only [cterm, sum_apply', map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [← cosetSum_chi hk hn hnM δ (proj_mem (k : ℤ) χ f) w, Finset.mul_sum]
  simp only [cterm]

end RamanujanPetersson.Kernel


