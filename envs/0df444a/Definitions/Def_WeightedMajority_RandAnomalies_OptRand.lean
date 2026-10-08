-- Prove2me | Definitions.Def_WeightedMajority_RandAnomalies_OptRand
-- name    : WeightedMajority_RandAnomalies_OptRand
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:17.018527+00:00
-- url     : https://prove2.me/theorems/546bf696-a14e-4f3d-af3c-5b5eaa043ad0
-- title:
--   The randomized optimum $\mathrm{opt}_{\mathrm{RAND}}(F,\eta)$ (Section 8)
-- statement:
--   Let $F$ be a pool of $\{0,1\}$-valued functions on a domain $X$ and let $S_\eta$ be the collection of finite sequences of trials $\mathcal S = ((x_1,y_1),\dots,(x_T,y_T))$ having at most $\eta$ anomalies with respect to $F$.
--
--   A **randomized prediction algorithm** is described by a map $A$ that assigns to the preceding trials $(x_1,y_1),\dots,(x_{t-1},y_{t-1})$ and the current instance $x_t$ a number
--   $$p_t = A\big((x_1,y_1),\dots,(x_{t-1},y_{t-1});\,x_t\big) \in [0,1],$$
--   the probability that the algorithm predicts $1$ at trial $t$. Its **expected number of mistakes** on $\mathcal S$ is
--   $$\mathbb E\,M_A(\mathcal S) = \sum_{t=1}^{T} |p_t - y_t|,$$
--   and the randomized optimum is
--   $$\mathrm{opt}_{\mathrm{RAND}}(F,\eta) = \inf_{A}\ \sup_{\mathcal S\in S_\eta}\ \sum_{t=1}^{T}|p_t - y_t| \in [0,\infty],$$
--   the infimum ranging over all such maps with values in $[0,1]$.
--
--   This is the paper's quantity "the minimum over all algorithms (including randomized algorithms) $A$ of the maximum over all sequences $\mathcal S \in S_\eta$ of the expected number of mistakes made by $A$ on $\mathcal S$", where the randomization of $A$ is independent of the choice of the sequence. Because the sequence is fixed in advance, the expected number of mistakes is by linearity the sum over trials of the probability of a wrong prediction, and that probability is $|p_t - y_t|$ with $p_t$ the probability of predicting $1$ given the preceding instances and labels (not conditioned on the algorithm's own earlier predictions). Conversely every map with values in $[0,1]$ is realized by the algorithm that predicts $1$ with probability $p_t$ using fresh independent coins at each trial. So the infimum over maps equals the infimum over randomized algorithms. Deterministic algorithms are the maps with values in $\{0,1\}$, so $\mathrm{opt}_{\mathrm{RAND}}(F,\eta) \le \mathrm{opt}(F,\eta)$.
--
--   **Formalization Note** The maps are `OnlineAlgR X` and the expected mistake count is `cumLoss` (with labels read as reals by `labelR`) from the published definition `UnderstandingML_Online`; the constraint $p_t \in [0,1]$ is the predicate `IsRandAlg`, without which `cumLoss` is not an expected mistake count. The value is taken in `ℝ≥0∞` (via `ENNReal.ofReal` of the nonnegative real `cumLoss`), so an unbounded supremum is $\infty$ rather than a junk real value. $S_\eta$ and $\mathrm{opt}$ are those of the definition `WeightedMajority.RandAnomalies.Anomalies`.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 250, Section 8 (definition of opt_RAND(F, η)); p. 252, proof of Theorem 8.2 (the probability of predicting 1)

import Definitions.Def_WeightedMajority_RandAnomalies_Anomalies

/-!
# Littlestone and Warmuth (1994), §8: the randomized optimum opt_RAND(F, η)

Littlestone, Warmuth, *The Weighted Majority Algorithm*, Inform. and Comput. 108 (1994),
p. 250, §8 and p. 252, proof of Theorem 8.2. The randomization of a randomized algorithm is
independent of the sequence, so on a fixed sequence its behaviour at trial `t` is summarized by
`pₜ ∈ [0,1]`, the probability that it predicts `1` given the preceding instances and labels and
the current instance (not conditioned on its own earlier predictions, p. 252). Its expected
number of mistakes on `S` is then `∑ₜ |pₜ − yₜ|`, which is `cumLoss` of `UnderstandingML_Online`.
Conversely every map `(history, x) ↦ p ∈ [0,1]` is realized by the randomized algorithm that
predicts `1` with probability `p` using fresh independent coins at each trial.
-/

open scoped ENNReal

namespace WeightedMajority.RandAnomalies

open UnderstandingML

variable {X : Type*}

/-- A real-valued online algorithm is a **randomized prediction algorithm** when each of its
outputs is a probability, `A hist x ∈ [0,1]`: the probability of predicting `1`. -/
def IsRandAlg (A : OnlineAlgR X) : Prop :=
  ∀ (hist : List (X × Bool)) (x : X), A hist x ∈ Set.Icc (0 : ℝ) 1

/-- `opt_RAND(F, η)` (p. 250): the infimum over all randomized algorithms `A` of the supremum,
over all finite sequences `S ∈ S_η`, of the expected number of mistakes `∑ₜ |pₜ − yₜ|` of `A`
on `S`, valued in `[0, ∞]`. -/
noncomputable def optRand (F : Set (X → Bool)) (η : ℕ) : ℝ≥0∞ :=
  ⨅ (A : OnlineAlgR X) (_ : IsRandAlg A),
    ⨆ (T : ℕ) (S : Fin T → X × Bool) (_ : InSEta F η S), ENNReal.ofReal (cumLoss A S)

end WeightedMajority.RandAnomalies


