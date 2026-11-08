-- Prove2me | Definitions.Def_CausalFailureRank_Qualifies
-- name    : CausalFailureRank_Qualifies
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:33.895193+00:00
-- url     : https://prove2.me/theorems/1f9666ae-648f-4172-b15a-e24f00aeb810
-- title:
--   Certificate for the given caps, eqs. (24), (25)
-- statement:
--   Let $C_N=6\cdot2^{N+1}$, $M_i=\max_y|\log(P_i^1(y)/P_i^0(y))|$, $L_i=|\log(\pi_i(1)/\pi_i(0))|$, $\underline d_i=2\,\mathrm{TV}(P_i^0,P_i^1)^2$ and $E_\delta=\min\{e\in\mathbb Z_{\ge1}:2^e\ge2NC_N/\delta\}$. For integers $\bar M_i\ge M_i$, $\bar L_i\ge L_i$,
--   $$\hat Q_i=\Big\lceil\max\Big\{\frac{2(E_\delta+\bar L_i)}{\underline d_i},\ \frac{8\bar M_i^2E_\delta}{\underline d_i^2}\Big\}\Big\rceil.$$
--   Caps **qualify** at $\delta$ when some such integers give $\hat Q_i\le Q_i$ for each stage and $H\ge H_0+\sum_i\hat Q_i+\min(N,q)$.
--
--   These are the explicit sufficient bounds that Theorem 3.1 assumes for its upper bound.
--
--   **Formalization Note** The paper does not name unique integers $\bar M_i,\bar L_i$, so they are existential: every printed choice qualifies. $H_0$ is the sum of the instance's normal calls.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.5, eqs. (24), (25), pp.18–19

import Mathlib
import Definitions.Def_CausalFailureRank_Event

namespace CausalFailureRank

variable {N q : ℕ}

/-- `C_N = 6 · 2^{N+1}`, App. B.5, p.18. -/
noncomputable def CN (N : ℕ) : ℝ := 6 * 2 ^ (N + 1)

/-- `M_i = max_y |log (P_i^1(y) / P_i^0(y))|`, App. B.5, p.18, as a supremum over the finite alphabet. -/
noncomputable def Mbound (I : Instance N q) (i : Fin N) : ℝ :=
  ⨆ y, |Real.log ((I.P i true y).toReal / (I.P i false y).toReal)|

/-- `L_i = |log (π_i(1) / π_i(0))|`, App. B.5, p.18. -/
noncomputable def Lbound (I : Instance N q) (i : Fin N) : ℝ :=
  |Real.log (I.prior i / (1 - I.prior i))|

/-- `d̲_i = 2 TV(P_i^0, P_i^1)²`, eq. (24), p.18, with `TV = ½ Σ_y |P_i^0(y) - P_i^1(y)|`. -/
noncomputable def dLow (I : Instance N q) (i : Fin N) : ℝ :=
  2 * ((1 / 2) * ∑ y, |(I.P i false y).toReal - (I.P i true y).toReal|) ^ 2

lemma exists_two_pow (x : ℝ) : ∃ e : ℕ, 1 ≤ e ∧ x ≤ 2 ^ e := by
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
  exact ⟨e + 1, by omega, he.le.trans (pow_le_pow_right₀ (by norm_num) (by omega))⟩

open scoped Classical in
/-- `E_δ = min {e ∈ ℤ_{≥1} : 2^e ≥ 2 N C_N / δ}`, eq. (24), p.18. -/
noncomputable def Edelta (N : ℕ) (δ : ℝ) : ℕ :=
  Nat.find (exists_two_pow (2 * N * CN N / δ))

/-- `Q̂_i = ⌈max {2 (E_δ + L̄_i) / d̲_i, 8 M̄_i² E_δ / d̲_i²}⌉`, eq. (24), p.18. -/
noncomputable def Qhat (I : Instance N q) (δ : ℝ) (Mbar Lbar : Fin N → ℕ) (i : Fin N) : ℕ :=
  ⌈max (2 * ((Edelta N δ : ℝ) + Lbar i) / dLow I i)
      (8 * (Mbar i : ℝ) ^ 2 * Edelta N δ / dLow I i ^ 2)⌉₊

/-- **The explicit sufficient bounds of App. B.5** (eqs. (24), (25), pp.18–19), which "the given
sampling and call limits" must satisfy in Theorem 3.1. Zang, Li, Jin, Xu, *Causal Failure Rank
Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256
721c8b0d…).

**Formalization Note.** "integers M̄_i ≥ M_i and L̄_i ≥ L_i are obtained by comparing the relevant
rational ratios … with integer powers of two" names no unique integers, so they are existential:
every printed choice qualifies. `H₀` is `∑ i, I.normalCalls i` (see `Instance`). -/
def Qualifies (I : Instance N q) (caps : Caps N) (δ : ℝ) : Prop :=
  ∃ Mbar Lbar : Fin N → ℕ,
    (∀ i, Mbound I i ≤ Mbar i ∧ Lbound I i ≤ Lbar i) ∧
    (∀ i, (Qhat I δ Mbar Lbar i : ℕ∞) ≤ caps.Q i) ∧
    (((∑ i, I.normalCalls i + ∑ i, Qhat I δ Mbar Lbar i + min N q : ℕ)) : ℕ∞) ≤ caps.H

end CausalFailureRank


