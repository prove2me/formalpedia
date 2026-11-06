-- Prove2me | Definitions.Def_HMajConsensus_potential
-- name    : HMajConsensus_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:46.555907+00:00
-- url     : https://prove2.me/theorems/488fa986-f7da-4d78-938d-9b2934bafe72
-- title:
--   Smallest maximizing index $I$, potential $G_j=(p_{\max}-p_j)^2/(p_{\max}+p_j)$ and $\Phi_a(x)=1/(1+ax)$
-- statement:
--   For a configuration with densities $p_1,\dots,p_k$ and maximum $p_{\max}$:
--
--   1. $I=\min\{i\in[k]:p_i=p_{\max}\}$ is the index attaining the maximum, ties broken by the smallest index;
--   2. the potential of opinion $j$ is
--   $$G_j=\frac{(p_{\max}-p_j)^2}{p_{\max}+p_j};$$
--   3. for $a\ge0$ and $x\ge0$,
--   $$\Phi_a(x)=\frac{1}{1+ax}.$$
--
--   $G_j$ measures how far opinion $j$ is from the top, normalized by the scale of the two densities, and $\Phi_a$ turns it into a bounded potential whose expected one-round contraction (Lemma 7.4) drives symmetry breaking in §7.
--
--   **Formalization Note** "$i$ is the index $I$" is the predicate: $p_i=p_{\max}$ and every smaller index has density below $p_{\max}$. For $k\ge1$ exactly one index satisfies it, so "$j\ne I_t$" is its negation. The denominator of $G_j$ is positive since $p_{\max}\ge1/n>0$.
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, §7, p.40 (I_t); §7.1, p.41 (G_j(t), Φ_a(x))

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw

namespace HMajConsensus

/-- `i` is the index `I = min{i ∈ [k] : p_i = pmax}` attaining the maximum density, ties broken
by the smallest index (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, arXiv:2610.40562, §7, p.40:
`I_t = min{i ∈ [k] : p_i(t) = pmax(t)}`).

**Formalization Note** Stated as a predicate: `i` is a maximizer and every smaller index has a
smaller density. For `k ≥ 1` exactly one `i` satisfies it, so "`j ≠ I_t`" is `¬ IsTopIdx C j`.
Smaller index is the order of `Fin k`. -/
def IsTopIdx {n k : ℕ} (C : Config n k) (i : Fin k) : Prop :=
  density C i = pmax C ∧ ∀ i' : Fin k, i' < i → density C i' < pmax C

/-- The potential `G_j = (pmax − p_j)² / (pmax + p_j)` (arXiv:2610.40562, §7.1, p.41).

**Formalization Note** The denominator is positive for every configuration with `n ≥ 1`,
`k ≥ 1` (some opinion has density `≥ 1/n`). -/
noncomputable def potG {n k : ℕ} (C : Config n k) (j : Fin k) : ℝ :=
  (pmax C - density C j) ^ 2 / (pmax C + density C j)

/-- `Φ_a(x) = 1 / (1 + a x)` for `a ≥ 0`, `x ≥ 0` (arXiv:2610.40562, §7.1, p.41). -/
noncomputable def phiA (a x : ℝ) : ℝ :=
  1 / (1 + a * x)

end HMajConsensus


