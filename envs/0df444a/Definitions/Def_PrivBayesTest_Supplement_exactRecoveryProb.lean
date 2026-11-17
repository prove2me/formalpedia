-- Prove2me | Definitions.Def_PrivBayesTest_Supplement_exactRecoveryProb
-- name    : PrivBayesTest_Supplement_exactRecoveryProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:10:42.852853+00:00
-- url     : https://prove2.me/theorems/fc64fab0-80ac-49db-b86d-10718b9c95d6
-- title:
--   $\varepsilon$-edge differential privacy and the probability of exact recovery up to a permutation of the communities
-- statement:
--   A randomized algorithm $\mathcal A$ on $n$ vertices maps a simple graph $G$ on $[n]$ to a random labelling $\tilde\sigma\in[k]^n$. It is **$\varepsilon$-edge differentially private** if for all graphs $G,G'$ that differ in the presence of a single edge and every set $S$ of labellings,
--
--   $$\Pr[\mathcal A(G)\in S]\le e^{\varepsilon}\Pr[\mathcal A(G')\in S].$$
--
--   A labelling $\tilde\sigma$ **recovers** $\sigma$ if there is a permutation $\pi$ of $[k]$ with $\tilde\sigma_v=\pi(\sigma_v)$ for every vertex $v$. The **exact-recovery probability** of $\mathcal A$ on $\mathrm{SBM}(n,p,W)$ is
--
--   $$\sum_{\sigma,G}\Pr_{\mathrm{SBM}}[(\sigma,G)]\cdot\Pr\big[\mathcal A(G)\text{ recovers }\sigma\big],$$
--
--   the probability over the model and the algorithm's randomness; the algorithm sees $G$ only.
--
--   These are the privacy notion and the success criterion of Theorems 1.7 and 4.8.
--
--   **Formalization Note** An algorithm is a map from `SimpleGraph (Fin n)` to probability mass functions on the finite set $[k]^n$, so every randomized algorithm, efficient or not, is covered and every set of labellings is an event. Edge adjacency is the published relation `LEDPCount.EdgeNeighbors` (the symmetric difference of the edge sets is a single edge).
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), Definition 1.1, p.2; ε-edge DP and exact recovery, §1.3.2, p.7; recovery up to a permutation, Theorem 1.7, p.8

import Mathlib
import Definitions.Def_LEDPCount_EdgeNeighbors
import Definitions.Def_PrivBayesTest_Supplement_sbmWeight

namespace PrivBayesTest

namespace Supplement

/-- **ε-edge differential privacy** (Jacobsen, *Optimal Error Exponents for Private Bayesian
Hypothesis Testing*, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), Definition 1.1,
p.2, with the edge adjacency of §1.3.2, p.7): a randomized algorithm `A` that maps a simple graph
on `[n]` to a random labelling `σ̃ ∈ [k]ⁿ` is ε-edge DP if
`Pr[A(G) ∈ S] ≤ e^ε Pr[A(G′) ∈ S]` for every set `S` of labellings and all graphs `G, G′` that
differ in the presence of a single edge.

**Formalization Note**
* An algorithm on `n` vertices is `A : SimpleGraph (Fin n) → PMF (Fin n → Fin k)`: the output
  law on each input graph. The output space is finite, so every randomized algorithm (deterministic
  or not, efficient or not) is of this form, and every subset of outputs is an event.
* Adjacency is the published `LEDPCount.EdgeNeighbors`: the symmetric difference of the edge sets
  is a single edge. -/
def IsEdgeDP {k n : ℕ} (ε : ℝ) (A : SimpleGraph (Fin n) → PMF (Fin n → Fin k)) : Prop :=
  ∀ G G' : SimpleGraph (Fin n), LEDPCount.EdgeNeighbors G G' →
    ∀ S : Set (Fin n → Fin k),
      (A G).toOuterMeasure S ≤ ENNReal.ofReal (Real.exp ε) * (A G').toOuterMeasure S

/-- The labellings that **recover** `σ` exactly up to a relabelling of the communities
(Jacobsen, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), Theorem 1.7, p.8):
`σ̃` such that some permutation `π` of `[k]` has `σ̃_v = π(σ_v)` for every vertex `v`. -/
def recovers {k n : ℕ} (σ : Fin n → Fin k) : Set (Fin n → Fin k) :=
  {τ | ∃ π : Equiv.Perm (Fin k), ∀ v, τ v = π (σ v)}

/-- The **exact-recovery probability** of an algorithm `A` on `(σ, G) ∼ SBM(n, p, W)`
(Jacobsen, STOC 2027 submission (manuscript sha256 abff2fdd…124ef), §1.3.2, pp.7–8): the
probability, over the model and the algorithm's randomness, that `A(G)` recovers `σ` up to a
permutation of `[k]`,

`∑_{σ, G} Pr_SBM[(σ, G)] · Pr[A(G) ∈ {σ̃ | ∃ π, ∀ v, σ̃_v = π(σ_v)}]`.

**Formalization Note** The algorithm sees the graph `G` only, not `σ`. The inner probability is
the real number `((A G).toOuterMeasure (recovers σ)).toReal ∈ [0, 1]`. -/
noncomputable def exactRecoveryProb {k n : ℕ} (p : Fin k → ℝ) (W : Matrix (Fin k) (Fin k) ℝ)
    (A : SimpleGraph (Fin n) → PMF (Fin n → Fin k)) : ℝ :=
  ∑ σ : Fin n → Fin k, ∑ G : SimpleGraph (Fin n),
    sbmWeight p W σ G * ((A G).toOuterMeasure (recovers σ)).toReal

end Supplement

end PrivBayesTest


