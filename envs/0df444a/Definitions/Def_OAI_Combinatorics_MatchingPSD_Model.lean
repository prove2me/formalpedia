-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
-- name    : OAI_Combinatorics_MatchingPSD_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:59:39.672403+00:00
-- url     : https://prove2.me/theorems/74ecb7fd-b905-4f8f-a8af-11ffb09c4639
-- title:
--   Slack matrix of the perfect matching polytope and its positive semidefinite rank
-- statement:
--   For $n\in\mathbb{N}$, an edge is a pair $(u,v)$ of vertices of $\{0,\dots,n-1\}$ with $u<v$, and a perfect matching $M$ is a set of edges in which every vertex lies in exactly one edge.
--
--   1. **Rows.** An odd cut is a set $U\subseteq\{0,\dots,n-1\}$ with $|U|$ odd. The rows of the slack matrix are the edges together with the odd cuts.
--   2. **Crossing.** An edge $(u,v)$ crosses $U$ if exactly one of $u,v$ lies in $U$. The crossing count of $U$ in $M$ is the number of edges of $M$ crossing $U$.
--   3. **Slack.** For a perfect matching $M$,
--   $$
--   \operatorname{slack}(e,M)=\begin{cases}1,&e\in M,\\0,&e\notin M,\end{cases}\qquad\operatorname{slack}(U,M)=\#\{e\in M:e\text{ crosses }U\}-1 .
--   $$
--   4. **Factorizations.** A real positive semidefinite factorization of order $r$ consists of positive semidefinite $r\times r$ matrices $A_i$ for the rows and $B_M$ for the perfect matchings such that $\operatorname{slack}(i,M)=\operatorname{tr}(A_iB_M)$ for all $i,M$.
--   5. **PSD rank.** $\operatorname{rk}_{\mathrm{psd}}(n)$ is the least $r>0$ admitting such a factorization (the infimum of the empty set is $0$ by convention).
--   6. **Main claim.** For every $C>0$ there is $n_0\ge4$ such that every even $n\ge n_0$ satisfies $n^C<\operatorname{rk}_{\mathrm{psd}}(n)$, with real powers.
--
--   The main claim says that the PSD rank of the perfect matching slack matrix grows faster than every polynomial. By the factorization theorem for lifts, this rules out small spectrahedral lifts of the perfect matching polytope.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingAffineLift mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation

namespace OAI

namespace PerfectMatchingPSD

abbrev OddCut (n : ℕ) := {U : Finset (Fin n) // Odd U.card}

abbrev Row (n : ℕ) := Edge n ⊕ OddCut n

def Crosses {n : ℕ} (U : Finset (Fin n)) (e : Edge n) : Prop :=
  (e.1.1 ∈ U ∧ e.1.2 ∉ U) ∨ (e.1.1 ∉ U ∧ e.1.2 ∈ U)

noncomputable def crossingCount {n : ℕ} (U : Finset (Fin n))
    (M : PerfectMatching n) : ℕ := by
  classical
  exact (M.1.filter (Crosses U)).card

noncomputable def slack {n : ℕ} (i : Row n) (M : PerfectMatching n) : ℝ := by
  classical
  exact match i with
  | Sum.inl e => if e ∈ M.1 then 1 else 0
  | Sum.inr U => (crossingCount U.1 M : ℝ) - 1

/-- Real PSD factors of order `r`, without equivariance or rank-one restrictions. -/
def HasFactorization (n r : ℕ) : Prop :=
  ∃ (A : Row n → Matrix (Fin r) (Fin r) ℝ)
    (B : PerfectMatching n → Matrix (Fin r) (Fin r) ℝ),
    (∀ i, (A i).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
    ∀ i M, slack i M = Matrix.trace (A i * B M)

/-- The least positive order of a real PSD factorization. -/
noncomputable def psdRank (n : ℕ) : ℕ :=
  sInf {r : ℕ | 0 < r ∧ HasFactorization n r}

/-- Every positive real power is eventually smaller than the PSD rank,
uniformly over all even vertex counts. The exponentiation is real `rpow`. -/
def MainClaim : Prop :=
  ∀ C : ℝ, 0 < C → ∃ n₀ : ℕ, 4 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n → Even n → (n : ℝ) ^ C < (psdRank n : ℝ)

end PerfectMatchingPSD

end OAI


