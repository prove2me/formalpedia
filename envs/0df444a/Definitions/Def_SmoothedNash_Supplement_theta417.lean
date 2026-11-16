-- Prove2me | Definitions.Def_SmoothedNash_Supplement_theta417
-- name    : SmoothedNash_Supplement_theta417
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:08:11.4982+00:00
-- url     : https://prove2.me/theorems/e92501f9-0d51-43ca-98dc-6cb0c19629e6
-- title:
--   Row-gap bound $\theta = C^{-n}(a^{2n}P_d/n^n)^{-1}p/L_J$ (Lemma 4.2)
-- statement:
--   For a constant $C > 1$, dimension $n$, bounds $L_0, L_1, L_2$, density bound $P_d$ and failure probability $p$, the row-gap bound of Lemma 4.2 is
--   $$
--   \theta = C^{-n} \Bigl(\frac{a^{2n} P_d}{n^n}\Bigr)^{-1} \frac{p}{L_J}, \qquad a = L_0 + L_1 .
--   $$
--   The algorithm of Theorem 4.17 runs Algorithm 4 with this $\theta$, for the universal constant $C$ of Lemma 4.2.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 4.2, p.26, and proof of Theorem 4.17, p.41

import Mathlib
import Definitions.Def_SmoothedNash_Supplement_lipJK
open MeasureTheory

namespace SmoothedNash.Supplement

/-- The row-gap bound used by the algorithm of Theorem 4.17 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Lemma 4.2, p.26, and
the proof of Theorem 4.17, p.41): `θ = C^{−n} (a^{2n} Pd / n^n)^{−1} p / L_J` with `a = L0 + L1` and
`L_J = lipJK L0 L1 L2`, for the universal constant `C = Cθ` of Lemma 4.2. -/
noncomputable def theta417 (Cθ : ℝ) (n : ℕ) (L0 L1 L2 Pd p : ℝ) : ℝ :=
  (Cθ ^ n)⁻¹ * ((L0 + L1) ^ (2 * n) * Pd / (n : ℝ) ^ n)⁻¹ * p / lipJK L0 L1 L2

end SmoothedNash.Supplement


