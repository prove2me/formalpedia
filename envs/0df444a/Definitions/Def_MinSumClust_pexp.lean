-- Prove2me | Definitions.Def_MinSumClust_pexp
-- name    : MinSumClust_pexp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:46:38.194382+00:00
-- url     : https://prove2.me/theorems/a1808285-9bf9-4693-b161-428dcf7e1b14
-- title:
--   Uniform samples, expectations and probabilities of finite distributions
-- statement:
--   For a finite set $s$ and a default point $a$, $\mathrm{unif}(s)$ is the uniform distribution on $s$ (the point mass at $a$ if $s=\emptyset$, a case the algorithms never reach). For a distribution $\mu$ on a finite type and a real function $g$,
--
--   $$\mathbb E_\mu[g]=\sum_x \mu(x)\,g(x),$$
--
--   and $\Pr_\mu[E]$ is the $\mu$-mass of an event $E$. These are the probabilities and expectations of §5.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), §5, pp.43–57 (PDF pp.45–59)

import Mathlib

namespace MinSumClust

/-- The uniform distribution on a finite set `s`, or the point mass at `a` when `s` is empty.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), §5, pp.43–46 ("sample … uniformly at random").

**Formalization Note.** Every uniform sample of §5 is from a set the paper shows nonempty; the
point mass only makes the definition total. -/
noncomputable def unifOr {α : Type*} (s : Finset α) (a : α) : PMF α :=
  if h : s.Nonempty then PMF.uniformOfFinset s h else PMF.pure a

/-- **Expectation** `E_μ[g] = ∑_x μ(x) g(x)` of a real function under a distribution on a finite
type (a finite sum, so no integrability condition arises). -/
noncomputable def pexp {α : Type*} [Fintype α] (μ : PMF α) (g : α → ℝ) : ℝ :=
  ∑ x, (μ x).toReal * g x

/-- **Probability** `Pr_μ[p]` of an event under a distribution. -/
noncomputable def pprob {α : Type*} (μ : PMF α) (p : α → Prop) : ℝ :=
  (μ.toOuterMeasure {x | p x}).toReal

end MinSumClust


