-- Prove2me | Definitions.Def_RobustPrefLearn_MTP_Supplement_Dueling
-- name    : RobustPrefLearn_MTP_Supplement_Dueling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:12:55.163262+00:00
-- url     : https://prove2.me/theorems/f49a819d-f4a4-4908-aa96-15847c771b13
-- title:
--   Appendix B.5, pp. 48–49 — comparison matrices, Borda winners and pairwise information
-- statement:
--   For $K\ge2$, a comparison matrix $P=(p_{ij})$ gives the probability that item $i$ wins against item $j$. Its Borda score and strict winner condition are
--   $$s_i(P)=\frac1{K-1}\sum_{j\ne i}p_{ij},\qquad i_*(P)=i\ \Longleftrightarrow\ \forall j\ne i,\ s_j(P)<s_i(P).$$
--   The parameter class $\Theta^P$ consists of positive matrices satisfying $p_{ij}+p_{ji}=1$ for every $i,j$ and possessing a strict winner. Experiments are unordered pairs $\{i,j\}$; their outcome probabilities are $p_{ij}$ for $i$ and $p_{ji}$ for $j$. A $\delta$-PAC algorithm uses pair displays only, terminates almost surely and has nonwinner-selection probability at most $\delta$ under every matrix in $\Theta^P$.
--
--   For a probability distribution $\lambda$ on unordered pairs, write
--   $$D_\lambda(P\Vert Q)=\sum_i\sum_{j>i}\lambda(\{i,j\})\,\mathrm{kl}(p_{ij},q_{ij}),\qquad I_*^P(P)=\sup_\lambda\inf_{\substack{Q\in\Theta^P\\i_*(Q)\ne i_*(P)}}D_\lambda(P\Vert Q).$$
--   Here $\mathrm{kl}$ is the published Bernoulli divergence. These objects supply the precise sample-complexity bound for Borda identification.
--
--   **Formalization Note** The policy and product history law are the published ones. Pair distributions are extended by zero to the other display sets. The comparison preference is extended by zero to unused nonpair displays; pair-only policies assign these displays zero probability. A winner is represented by the strict-score predicate, avoiding arbitrary choices outside $\Theta^P$. The finite double sum counts each pair once via $i<j$. All matrix entries, including diagonal entries, are positive; reciprocity forces $p_{ii}=1/2$. Information and probabilities are extended nonnegative reals.
-- source:
--   Feng, Caldentey & Ryan, SSRN 3215614, Appendix B.5, pp. 48–49; theorem denominator, p. 49

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Policy

open scoped ENNReal

namespace RobustPrefLearn.MTP.Supplement

abbrev Comparison (K : ℕ) := Fin K → Fin K → ℝ

/-- Borda score, Appendix B.5, p.48. Theorems require K ≥ 2. -/
noncomputable def bordaScore {K : ℕ} (P : Comparison K) (i : Fin K) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, P i j) / ((K : ℝ) - 1)

def BordaWinner {K : ℕ} (P : Comparison K) (i : Fin K) : Prop :=
  ∀ j, j ≠ i → bordaScore P j < bordaScore P i

/-- Θ^P, p.49: positivity includes diagonal entries, which reciprocity
forces to 1/2. The unique winner is represented by its strict inequalities. -/
def ComparisonClass (K : ℕ) : Set (Comparison K) :=
  {P | (∀ i j, 0 < P i j ∧ P i j + P j i = 1) ∧ ∃ i, BordaWinner P i}

/-- On a pair {i,j}, the mass of i is p_ij, and all other votes have mass zero.
The zero extension to nonpairs is unused by pair-only policies. -/
noncomputable def duelingPref {K : ℕ} (P : Comparison K) : Pref K :=
  fun S i => if S.1.card = 2 ∧ i ∈ S.1 then ∑ j ∈ S.1.erase i, P i j else 0

/-- Admissible dueling policies use only pair displays after every history. -/
def PairPolicy {K : ℕ} (π : Policy K) : Prop :=
  Admissible π ∧ ∀ h S, S.1.card ≠ 2 → π.disp h S = 0

open Classical in
/-- Probability of selecting a nonwinner, using the published history law. -/
noncomputable def duelingProbWrong {K : ℕ} (π : Policy K) (P : Comparison K) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑ v : Fin t → Step K,
    if stopsAt π (toHist v) ∧ ¬ BordaWinner P (π.select (toHist v))
    then pathProb π (duelingPref P) (toHist v) else 0

/-- δ-PAC for the whole comparison class, not merely the tested P. -/
def DuelingPAC {K : ℕ} (δ : ℝ) (π : Policy K) : Prop :=
  PairPolicy π ∧ ∀ P ∈ ComparisonClass K,
    probStop π (duelingPref P) = 1 ∧ duelingProbWrong π P ≤ ENNReal.ofReal δ

/-- Distributions on unordered pairs, extended by zero to the other DS. -/
def pairSimplex (K : ℕ) : Set (DS K → ℝ) :=
  {lam | lam ∈ simplex K ∧ ∀ S, S.1.card ≠ 2 → lam S = 0}

/-- lam({i,j}); expressed without constructing a DS from a possibly repeated pair.
For i < j exactly one DS contributes. -/
noncomputable def pairWeight {K : ℕ} (lam : DS K → ℝ) (i j : Fin K) : ℝ :=
  ∑ S : DS K, if S.1 = {i, j} then lam S else 0

/-- The displayed double sum on p.49, one term per i < j. -/
noncomputable def duelingDiv {K : ℕ} (lam : DS K → ℝ) (P Q : Comparison K) : ℝ :=
  ∑ i, ∑ j, if i < j then pairWeight lam i j * kl (P i j) (Q i j) else 0

def duelingAlt {K : ℕ} (P : Comparison K) : Set (Comparison K) :=
  {Q | Q ∈ ComparisonClass K ∧ ∀ i, BordaWinner P i → ¬ BordaWinner Q i}

/-- Chernoff denominator of the theorem on p.49. For valid comparisons all
Bernoulli probabilities lie in (0,1) and all finite KL sums are nonnegative. -/
noncomputable def duelingInfo {K : ℕ} (P : Comparison K) : ℝ≥0∞ :=
  ⨆ lam ∈ pairSimplex K, ⨅ Q ∈ duelingAlt P, ENNReal.ofReal (duelingDiv lam P Q)

end RobustPrefLearn.MTP.Supplement


