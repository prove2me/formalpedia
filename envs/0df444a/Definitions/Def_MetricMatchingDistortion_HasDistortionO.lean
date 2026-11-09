-- Prove2me | Definitions.Def_MetricMatchingDistortion_HasDistortionO
-- name    : MetricMatchingDistortion_HasDistortionO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:20:57.353093+00:00
-- url     : https://prove2.me/theorems/2b4f9386-e24d-4d54-a3f7-b4752bd70fe0
-- title:
--   Metric distortion $O(f(n))$ of a matching mechanism
-- statement:
--   The **distortion** of a mechanism $\mathcal A$ on an instance $\sigma$ is
--   $$\mathrm{distortion}(\mathcal A,\sigma)=\sup_{d\in\rho(\sigma)}\frac{\mathbb E_{M\sim\mathcal A(\sigma)}[\mathrm{cost}(M,d)]}{\min_{M^*}\mathrm{cost}(M^*,d)},$$
--   with $0/0=1$ and $c/0=+\infty$ for $c>0$. The mechanism has distortion $O(f(n))$ when there is a constant $C$ such that for every $n\ge1$, every instance $\sigma$ with $n$ agents, every $d\in\rho(\sigma)$ and every perfect matching $\pi^*$,
--   $$\mathbb E_{M\sim\mathcal A(\sigma)}[\mathrm{cost}(M,d)]\le C\,f(n)\,\mathrm{cost}(\pi^*,d).$$
--
--   **Formalization Note** The ratio is written as an inequality against every perfect matching; with the page's conventions this is the same bound (a zero optimum forces zero expected cost). $C$ is chosen once, before $n$, the instance and the metric.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §2, p.10 (PDF p.12), footnote 10

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_Mechanism

namespace MetricMatchingDistortion

/-- **Distortion `O(f(n))`.** Charikar et al., *Sublinear Metric Distortion for Matching*,
arXiv:2611.05777 (held version, sha256 fdf3452b…), §2, p.10 (PDF p.12): "The worst-case distortion
of a mechanism M on an instance σ is given by distortion(M, σ) := sup_{d∈ρ(σ)}
E_{M∼M(σ)}[cost(M, d)] / min_{M∗} cost(M∗, d)", with footnote 10: "Throughout, we interpret 0/0 as
1 and c/0 as +∞ for c > 0."

`HasDistortionO A f` says there is one constant `C` such that for every `n ≥ 1`, every ranking
profile `rk` on `n` agents and items, every pseudometric `d` consistent with `rk` and every perfect
matching `π*`,
`E_{M∼A(rk)}[cost(M, d)] ≤ C · f(n) · cost(π*, d)`.

**Formalization Note.** The ratio is replaced by the inequality against every perfect matching;
this is the same as bounding the ratio to the minimum cost with the page's conventions: when the
optimum is `0` the bound forces the expected cost to be `0` (`c/0 = +∞`), and `0/0 = 1` is at most
`max C 1 · f(n)` whenever `f(n) ≥ 1`. `C` is chosen before `n`, the instance and the metric. -/
def HasDistortionO (A : Mechanism) (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ rk : Ranking n, ∀ d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ,
    IsConsistentPseudometric rk d → ∀ πstar : Equiv.Perm (Fin n),
      expectedCost A n rk d ≤ C * f n * matchingCost πstar d

end MetricMatchingDistortion


