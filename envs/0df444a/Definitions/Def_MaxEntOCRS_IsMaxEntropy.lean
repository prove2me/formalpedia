-- Prove2me | Definitions.Def_MaxEntOCRS_IsMaxEntropy
-- name    : MaxEntOCRS_IsMaxEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:19.853014+00:00
-- url     : https://prove2.me/theorems/2ea79bf4-6f81-4c9b-9296-a8ac0ec0f231
-- title:
--   Maximum-entropy distribution on matchings with marginals $q$
-- statement:
--   Let $G$ be a finite loopless multigraph and $q \in \mathbb R^E$. A distribution $\mu$ is **of maximum entropy among the distributions on $\mathcal M(G)$ with marginals $q$** if
--
--   1. $\mu$ is a distribution on the matchings of $G$,
--   2. $\Pr_\mu(e \in M) = q_e$ for every edge $e$, and
--   3. $H(\mu') \le H(\mu)$ for every distribution $\mu'$ on the matchings of $G$ with the same marginals $q$.
--
--   The maximum-entropy template of Aminian, Niazadeh and Nuti samples its initial matching from this distribution with $q = \alpha' x$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_IsMatchingDist
import Definitions.Def_MaxEntOCRS_edgeMarginal
import Definitions.Def_FuchsThesis_Types_entropy

namespace MaxEntOCRS

/-- `μ` is a distribution of maximum entropy among the distributions on `M(G)` with edge
marginals `q` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4: "the distribution µ* of maximum entropy among distributions on
M(G) with marginals α′x").

**Formalization Note** The entropy is the published `FuchsThesis.Types.entropy`,
`H(μ) = −∑_M μ(M) ln μ(M)` with `0 ln 0 = 0` (`Real.negMulLog`), applied to the weight function
`μ` on `Finset E`; the base of the logarithm does not change the maximizer. -/
def IsMaxEntropy {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (q : E → ℝ) (μ : Finset E → ℝ) : Prop :=
  IsMatchingDist G μ ∧ (∀ e, edgeMarginal μ e = q e) ∧
    ∀ μ' : Finset E → ℝ, IsMatchingDist G μ' → (∀ e, edgeMarginal μ' e = q e) →
      FuchsThesis.Types.entropy μ' ≤ FuchsThesis.Types.entropy μ

end MaxEntOCRS


