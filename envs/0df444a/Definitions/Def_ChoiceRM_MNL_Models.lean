-- Prove2me | Definitions.Def_ChoiceRM_MNL_Models
-- name    : ChoiceRM_MNL_Models
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:51.350976+00:00
-- url     : https://prove2.me/theorems/9d272567-e28d-4819-b2a3-61b255988608
-- title:
--   (14), p. 23 and §3.3, p. 21 — the MNL and independent demand choice models
-- statement:
--   Two choice models on the fare products $N = \{1, \dots, n\}$.
--
--   1. **Multinomial logit (MNL).** Given preference weights $w_j = e^{u_j} > 0$ and the no-purchase weight $w_0 = 1$, the probability of buying $j$ from the offer set $S$ is
--   $$
--   P_j(S) = \frac{w_j}{\sum_{i \in S} w_i + 1}, \quad j \in S, \qquad (14)
--   $$
--   and $P_j(S) = 0$ for $j \notin S$.
--   2. **Independent demand.** Given $q_1, \dots, q_n$, an arriving customer chooses class $j$ with probability $q_j$ regardless of the offer set, and does not purchase if $j$ is not offered: $P_j(S) = q_j$ for $j \in S$ and $0$ otherwise.
--
--   The file also defines the **two-point convex weights** used in the proofs of Propositions 5 and 6: for an index $k$ and a number $\theta$,
--   $$
--   \alpha_i = \begin{cases} \theta & i = k, \\ 1 - \theta & i = k + 1, \\ 0 & \text{otherwise,} \end{cases} \qquad i = 0, \dots, n.
--   $$
--
--   The MNL model is the most widely used parametric choice model in travel demand and marketing; the independent model is the classical yield management model of Lee and Hersh.
--
--   **Formalization Note** The paper's weight parameter $\lambda$ is written $\theta$ because `λ` is a reserved word in Lean. The MNL formula (14) is defined for all real $w$; positivity $w_j > 0$ is a hypothesis of every theorem that uses it, and the independent model's $q_j \ge 0$, $\sum_j q_j \le 1$ likewise. The weights `twoPoint k θ` are indexed by `Fin (n + 1)`, matching the complete sets $A_0, \dots, A_n$.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 23, eq. (14); p. 21, §3.3; pp. 22 and 24, the convex weights α_k

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_MNL_FareOrder

namespace ChoiceRM.MNL

variable {n : ℕ}

/-- The MNL choice probabilities (14), p. 23, with no-purchase weight `w_0 = 1`:
`P_j(S) = w_j / (Σ_{i∈S} w_i + 1)` for `j ∈ S`, and `0` otherwise. -/
noncomputable def mnl (w : Fin n → ℝ) : Finset (Fin n) → Fin n → ℝ :=
  fun S j => if j ∈ S then w j / (∑ i ∈ S, w i + 1) else 0

/-- The independent demand model of §3.3, p. 21: `P_j(S) = q_j` for `j ∈ S`, and `0` otherwise. -/
def indep (q : Fin n → ℝ) : Finset (Fin n) → Fin n → ℝ :=
  fun S j => if j ∈ S then q j else 0

/-- The two-point convex weights of pp. 22 and 24 (the paper's `λ` is written `θ`, since `λ` is a
Lean keyword): `α_k = θ` at index `k`, `α_{k+1} = 1 − θ`, and `0` at every other index of
`{0, …, n}`. -/
def twoPoint (k : ℕ) (θ : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i.val = k then θ else if i.val = k + 1 then 1 - θ else 0

end ChoiceRM.MNL


