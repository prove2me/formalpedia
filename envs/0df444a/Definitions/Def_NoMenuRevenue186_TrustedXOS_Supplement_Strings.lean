-- Prove2me | Definitions.Def_NoMenuRevenue186_TrustedXOS_Supplement_Strings
-- name    : NoMenuRevenue186_TrustedXOS_Supplement_Strings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:03:52.146104+00:00
-- url     : https://prove2.me/theorems/8697f3d5-2292-4289-ba29-1d714413fee7
-- title:
--   Strings, valuations $v_{x,j}$, audit priors, the reference measure and noisy pairs
-- statement:
--   Section 5 works with $m=\lfloor n/2\rfloor$ item pairs. Item $(r,b)$, $r\in[m]$, $b\in\{0,1\}$, is the item with index $2r+b$ (with $r$ counted from $0$); a leftover item is ignored. A string $x\in\{0,1\}^m$ represents the $m$-item set $\hat x=\{(r,x_r):r\in[m]\}$, and for a color $j$
--
--   $$v_{x,j}(T)=2^j\,|T\cap\hat x|.$$
--
--   For strings, $|x|$ is the Hamming weight, $\mathrm{dist}_H$ the Hamming distance and $x\oplus y$ the coordinatewise exclusive or.
--
--   1. **Audit prior.** A local neighborhood has a center $C$ and perturbations $E_j$; its petal strings are $X_j=C\oplus E_j$. For a nonempty color set $J=\{j_1<\dots<j_t\}$ the audit $A_{i,J}$ puts probability $q_r$ on $v_{X_{j_r},j_r}$, where $q_r=2^{j_1-j_r}-2^{j_1-j_{r+1}}$ for $r<t$ and $q_t=2^{j_1-j_t}$.
--   2. **Reference measure.** $\mathcal V=\{0,1\}^m\times[K]$ with $[K]=\{1,\dots,K\}$, slices $\mathcal V_j=\{0,1\}^m\times\{j\}$, and $\nu$ the uniform measure on $\mathcal V$, so $\nu(P)=|P|/(K2^m)$ for $P\subseteq\mathcal V$.
--   3. **Noisy pair.** For $X$ uniform on $\{0,1\}^m$ and $Y$ obtained by flipping each coordinate of $X$ independently with probability $(1-\rho)/2$,
--
--   $$\Pr[X\in A,\,Y\in B]=\sum_{x\in A}\sum_{y\in B}2^{-m}\Bigl(\tfrac{1-\rho}2\Bigr)^{\mathrm{dist}_H(x,y)}\Bigl(\tfrac{1+\rho}2\Bigr)^{m-\mathrm{dist}_H(x,y)}.$$
--
--   4. **Weight-$d$ pair.** For $C$ uniform and $E,E'$ independent and uniform over the strings of weight exactly $d$, the law of $(C\oplus E,\,C\oplus E')$, written as a finite average.
--
--   These objects are the hard instance of the strategic-seller lower bound and the analytic tools of its collision bound.
--
--   **Formalization Note** The audit masses are entered as weights and normalized by their sum; the masses telescope to one, so normalization does not change them. Colors are natural numbers; the statements restrict them to $[K]=\{1,\dots,K\}$.
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed pp.22–24, PDF pp.24–26, Sections 5.1–5.2

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Auction

namespace NoMenuRevenue186.TrustedXOS.Supplement
open NoMenuRevenue186.TrustedXOS

/-! Section 5.1 (printed pp.22–24, PDF pp.24–26) and Section 5.2 (printed p.24). -/

/-- Binary strings `x ∈ {0,1}^m`. -/
abbrev BitString (m : ℕ) := Fin m → Bool

/-- Hamming weight: the number of coordinates equal to 1. -/
def hammingWeight {m : ℕ} (x : BitString m) : ℕ :=
  (Finset.univ.filter (fun r => x r = true)).card

/-- Hamming distance. -/
def hammingDist {m : ℕ} (x y : BitString m) : ℕ :=
  (Finset.univ.filter (fun r => x r ≠ y r)).card

/-- Coordinatewise exclusive or `x ⊕ y`. -/
def bxor {m : ℕ} (x y : BitString m) : BitString m := fun r => xor (x r) (y r)

/-- The strings of Hamming weight exactly `d`. -/
def weightStrings (m d : ℕ) : Finset (BitString m) :=
  Finset.univ.filter (fun e => hammingWeight e = d)

/-- `x̂ = {(r, x_r) : r ∈ [m]}` for `m = ⌊n/2⌋`, with item `(r,b)` at index `2r + b`
    (`r` zero-based, `b ∈ {0,1}`); a leftover item is ignored. -/
def itemSet (n : ℕ) (x : BitString (n / 2)) : Bundle n :=
  Finset.univ.filter (fun a : Fin n =>
    ∃ r : Fin (n / 2), a.val = 2 * r.val + (if x r then 1 else 0))

/-- `v_{x,j}(T) = 2^j · |T ∩ x̂|`: base value `2^j` on each item of `x̂`. -/
noncomputable def stringValuation (n : ℕ) (x : BitString (n / 2)) (j : ℕ) : Valuation n :=
  fun T => (2 : ℝ) ^ j * ((T ∩ itemSet n x).card : ℝ)

/-- The audit probability `q_r` of color `j = j_r ∈ J`, with `j_1 = min J`:
    `2^{j_1 - j_r} - 2^{j_1 - j_{r+1}}` if `j_r` is not the largest color of `J`,
    and `2^{j_1 - j_t}` for the largest color `j_t`. -/
noncomputable def auditMass (J : Finset ℕ) (hJ : J.Nonempty) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ (((J.min' hJ : ℕ) : ℤ) - (j : ℤ)) -
    (if hn : (J.filter (fun k => j < k)).Nonempty then
      (2 : ℝ) ^ (((J.min' hJ : ℕ) : ℤ) - (((J.filter (fun k => j < k)).min' hn : ℕ) : ℤ))
    else 0)

/-- Unnormalized audit weights on colors (zero outside `J`). -/
noncomputable def auditWeight (J : Finset ℕ) (hJ : J.Nonempty) (j : ℕ) : ENNReal :=
  if j ∈ J then ENNReal.ofReal (auditMass J hJ j) else 0

theorem auditWeight_tsum (J : Finset ℕ) (hJ : J.Nonempty) :
    ∑' j, auditWeight J hJ j = ∑ j ∈ J, auditWeight J hJ j :=
  tsum_eq_sum (fun j hj => by simp [auditWeight, hj])

theorem auditWeight_tsum_ne_top (J : Finset ℕ) (hJ : J.Nonempty) :
    ∑' j, auditWeight J hJ j ≠ ⊤ := by
  rw [auditWeight_tsum]
  exact ENNReal.sum_ne_top.mpr (fun j _ => by
    by_cases h : j ∈ J <;> simp [auditWeight, h])

theorem auditWeight_tsum_ne_zero (J : Finset ℕ) (hJ : J.Nonempty) :
    ∑' j, auditWeight J hJ j ≠ 0 := by
  intro h
  have h0 := (ENNReal.tsum_eq_zero.mp h) (J.max' hJ)
  have hmem : J.max' hJ ∈ J := J.max'_mem hJ
  have hempty : ¬ (J.filter (fun k => J.max' hJ < k)).Nonempty := by
    rintro ⟨k, hk⟩
    rw [Finset.mem_filter] at hk
    exact absurd (J.le_max' k hk.1) (not_le.mpr hk.2)
  simp only [auditWeight, hmem, if_true, auditMass, hempty, dif_neg, not_false_eq_true,
    sub_zero, ENNReal.ofReal_eq_zero] at h0
  exact absurd h0 (not_le.mpr (zpow_pos (by norm_num) _))

/-- The law of the audited color: mass proportional to `q_r` on `j_r ∈ J`. The masses
    `q_r` telescope to one (printed p.23), so normalization leaves them unchanged. -/
noncomputable def auditColorLaw (J : Finset ℕ) (hJ : J.Nonempty) : FiniteLaw ℕ :=
  ⟨PMF.normalize (auditWeight J hJ) (auditWeight_tsum_ne_zero J hJ)
      (auditWeight_tsum_ne_top J hJ), by
    rw [PMF.support_normalize]
    exact (J.finite_toSet).subset (fun j hj => by
      by_contra hjJ
      have hjJ' : j ∉ J := hjJ
      exact hj (by simp [auditWeight, hjJ']))⟩

/-- The audit prior `A_{F,i,J}` of a local neighborhood with center `C` and perturbations
    `E_j` (petal strings `X_j = C ⊕ E_j`): probability `q_r` on `v_{X_{j_r}, j_r}`. -/
noncomputable def auditPrior (n : ℕ) (C : BitString (n / 2)) (E : ℕ → BitString (n / 2))
    (J : Finset ℕ) (hJ : J.Nonempty) : Prior n :=
  (auditColorLaw J hJ).map (fun j => stringValuation n (bxor C (E j)) j)

/-- The reference type space `V = {0,1}^m × [K]`, colors `[K] = {1, …, K}`. -/
def refSpace (m K : ℕ) : Finset (BitString m × ℕ) := Finset.univ ×ˢ Finset.Icc 1 K

/-- The color-`j` slice `V_j = {0,1}^m × {j}`. -/
def slice (m j : ℕ) : Finset (BitString m × ℕ) := Finset.univ ×ˢ {j}

/-- The uniform measure `ν` on `V`: `ν(P) = |P| / (K · 2^m)` for `P ⊆ V`. -/
noncomputable def refMeasure (m K : ℕ) (P : Finset (BitString m × ℕ)) : ℝ :=
  ((P ∩ refSpace m K).card : ℝ) / ((K : ℝ) * 2 ^ m)

/-- The strings `x` with `(x, j) ∈ P`. -/
def fiber {m : ℕ} (P : Finset (BitString m × ℕ)) (j : ℕ) : Finset (BitString m) :=
  Finset.univ.filter (fun x => (x, j) ∈ P)

/-- `Pr[X ∈ A, Y ∈ B]` for `X` uniform on `{0,1}^m` and `Y` obtained from `X` by flipping
    each coordinate independently with probability `(1 - ρ)/2`. -/
noncomputable def noisyPairProb (m : ℕ) (ρ : ℝ) (A B : Finset (BitString m)) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ B, (1 / (2 : ℝ) ^ m) * ((1 - ρ) / 2) ^ hammingDist x y *
    ((1 + ρ) / 2) ^ (m - hammingDist x y)

/-- `Pr[X ∈ A, Y ∈ B]` for `X = C ⊕ E`, `Y = C ⊕ E'`, `C` uniform on `{0,1}^m` and
    `E, E'` independent and uniform over the strings of weight exactly `d`. -/
noncomputable def weightPairProb (m d : ℕ) (A B : Finset (BitString m)) : ℝ :=
  ∑ c : BitString m, ∑ e ∈ weightStrings m d, ∑ e' ∈ weightStrings m d,
    if bxor c e ∈ A ∧ bxor c e' ∈ B then
      (1 / (2 : ℝ) ^ m) * (1 / ((weightStrings m d).card : ℝ)) ^ 2
    else 0

end NoMenuRevenue186.TrustedXOS.Supplement


