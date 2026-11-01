-- Prove2me | Definitions.Def_BayesBAI_maxOthers
-- name    : BayesBAI_maxOthers
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:58.095268+00:00
-- url     : https://prove2.me/theorems/cddcbd19-a2fc-4823-8b39-8305b19fbc8d
-- title:
--   The maximum $\mu^*_{\setminus i}$ of the other arms
-- statement:
--   $\mu^*_{\setminus i}=\max_{j\ne i}\mu_j$, viewed as a function of $\mu_{\setminus i}$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, p.3, p.7

import Mathlib

namespace BayesBAI

/-- `μ*_\i = max_{j ≠ i} μ_j`, as a function of `μ_\i`, Komiyama, Ariu, Kato, Qin,
arXiv:2111.09885v3, p.3 and p.7.

**Formalization Note.** The maximum is `Finset.sup'` over the arms other than `i`, nonempty as `2 ≤ K`. -/
noncomputable def maxOthers {K : ℕ} (hK : 2 ≤ K) {i : Fin K} (ν : {j : Fin K // j ≠ i} → ℝ) : ℝ :=
  Finset.univ.sup'
    (by
      have : Nontrivial (Fin K) := Fin.nontrivial_iff_two_le.mpr hK
      obtain ⟨j, hj⟩ := exists_ne i
      exact ⟨⟨j, hj⟩, Finset.mem_univ _⟩)
    ν

end BayesBAI


