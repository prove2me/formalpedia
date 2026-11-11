-- Prove2me | Definitions.Def_SumReLU_probeLaw
-- name    : SumReLU_probeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:19.9002+00:00
-- url     : https://prove2.me/theorems/a2cf49be-a672-4b6e-9205-2a96e3683898
-- title:
--   The complex Gaussian probe $u=p+iq$ and the filter tensor $F_p(u)=u^{\otimes p}/\sqrt{p!}$
-- statement:
--   The probe distribution $\mathcal U$ is the law of $u=p+iq\in\mathbb C^d$ with $p,q$ independent standard Gaussians $N(0,I_d)$. The filter tensor is
--   $$
--   F_p(u)=\frac{u^{\otimes p}}{\sqrt{p!}},\qquad (F_p(u))_{i_1\dots i_p}=\frac{u_{i_1}\cdots u_{i_p}}{\sqrt{p!}} .
--   $$
--
--   **Formalization Note** The real and imaginary parts each have covariance $I_d$ (not the standard complex normal with variance $1/2$ per part).
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.13, p.34 (PDF p.36); Lemma 4.17, (21), p.36 (PDF p.38); Algorithm 7, line 13, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_SumReLU_CTensor

open MeasureTheory ProbabilityTheory

namespace SumReLU

/-- **The probe distribution** `U`: `u = p + iq` with `p, q` i.i.d. `N(0, I_d)` — the pushforward of
`N(0, I_d) ⊗ N(0, I_d)` under `(p, q) ↦ (p_j + i q_j)_j`.

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.13, p.34 (PDF p.36): "Let u = p + iq, where p, q iid∼ N(0, I_d)"; Algorithm 7, line 13,
p.33 (PDF p.35).

**Formalization Note.** Real and imaginary parts each have covariance `I_d` (not the
"standard complex normal" with variance `1/2` per part). The map is continuous, hence measurable. -/
noncomputable def probeLaw (d : ℕ) : Measure (Fin d → ℂ) :=
  ((stdGaussian (EuclideanSpace ℝ (Fin d))).prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map
    (fun pq => fun j => (⟨pq.1 j, pq.2 j⟩ : ℂ))

/-- The filter tensor `F_p(u) = u^{⊗p}/√(p!)` (Lemma 4.17, (21), p.36, PDF p.38; Claim 4.15). -/
noncomputable def Fp {d : ℕ} (p : ℕ) (u : Fin d → ℂ) : CTensor d p :=
  fun J => (∏ m, u (J m)) / ((Real.sqrt (p.factorial : ℝ) : ℝ) : ℂ)

end SumReLU


