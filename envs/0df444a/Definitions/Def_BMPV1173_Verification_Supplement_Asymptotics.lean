-- Prove2me | Definitions.Def_BMPV1173_Verification_Supplement_Asymptotics
-- name    : BMPV1173_Verification_Supplement_Asymptotics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:50:52.510891+00:00
-- url     : https://prove2.me/theorems/a2425826-8714-43bf-a945-c7673713fd12
-- title:
--   Ordinary query bounds and real power rates
-- statement:
--   For a dimension-indexed family of Boolean decision problems in the published bit-query model, define ordinary upper and lower bounds by a positive coefficient and an eventual dimension threshold chosen before the dimension. For a rate $g(n)$, an upper bound supplies a successful $T$-query circuit with $T\le Cg(n)$, while a lower bound requires every successful $T$-query circuit to satisfy $cg(n)\le T$. Success is at least $2/3$ on every input in the domain. No logarithmic loss is hidden.
--
--   The rate functions are $n^p$ and $n^{3/2}/\sqrt{\log n}$. The latter is used only for $n\ge8$ or $n\ge27$, where its denominator is positive. These wrappers let the supplement use the source's ordinary asymptotic notation without converting an infinite extended-natural query complexity to zero.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, §2.1, printed p.13 = PDF p.13; ordinary bounds in Theorems 1.2–1.4, 3.4–3.5, 5.2 and Corollary 5.5.

import Definitions.Def_BMPV1173_Verification_QueryComplexity

/-! Ordinary asymptotic bounds for the published operational decision model.
Coefficients and thresholds precede the dimension; no logarithms are hidden. -/
namespace BMPV1173.Verification.Supplement

def OrdinaryDecisionUpper (ι : ℕ → Type) [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] (D : ∀ n, Set (ι n → Bool))
    (f : ∀ n, (ι n → Bool) → Bool) (rate : ℕ → ℝ) (minimum : ℕ) : Prop :=
  ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ n : ℕ, max minimum N ≤ n →
    ∃ T : ℕ, HasDecision (D n) (f n) (1 / 3) T ∧ (T : ℝ) ≤ C * rate n

def OrdinaryDecisionLower (ι : ℕ → Type) [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] (D : ∀ n, Set (ι n → Bool))
    (f : ∀ n, (ι n → Bool) → Bool) (rate : ℕ → ℝ) (minimum : ℕ) : Prop :=
  ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ n : ℕ, max minimum N ≤ n →
    ∀ T : ℕ, HasDecision (D n) (f n) (1 / 3) T → c * rate n ≤ (T : ℝ)

noncomputable def powerRate (p : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ p

/-- Used only above dimensions 8 (row search) or 27 (radius), so log n > 0. -/
noncomputable def rowLowerRate (n : ℕ) : ℝ :=
  (n : ℝ) ^ (3 / 2 : ℝ) / Real.sqrt (Real.log (n : ℝ))

end BMPV1173.Verification.Supplement


