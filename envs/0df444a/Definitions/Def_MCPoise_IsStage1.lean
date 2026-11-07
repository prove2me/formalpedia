-- Prove2me | Definitions.Def_MCPoise_IsStage1
-- name    : MCPoise_IsStage1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:43.362778+00:00
-- url     : https://prove2.me/theorems/84125ddb-04e5-451f-8003-64e85d612650
-- title:
--   Stage 1 of MatchCenters for one group
-- statement:
--   For a nonempty group with root $r$ and terminals $S$:
--
--   1. the capacity is normalized, $\hat x_e = \max_{t \in S} \sum_{p \in P_t, e \in p} \hat f_p$;
--   2. $C$ is a positive integer with each $C \hat x_e$ an even integer, and the multigraph has $C \hat x_e$ parallel copies of $e$;
--   3. $Q$ is an $(S \cup \{r\})$-path-packing, and for each $t \in S$ a set $Q^t$ of exactly $C$ paths of $Q$ having $t$ as an endpoint is selected.
--
--   The **surviving** paths of $Q^t$ have length at most $4L'_d$. $S'$ is the set of terminals with $\sum_p y_p \ge 1$ for $y_p = 4/C$, and after scaling each surviving path of a terminal of $S'$ has the same weight, with total $1$.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §2.2.1, pp.17–18

import Mathlib
import Definitions.Def_MCPoise_IsPathIn
import Definitions.Def_MCPoise_MGraph

namespace MCPoise

variable {V : Type*} [DecidableEq V]

/-- **Stage 1 of MatchCenters for one nonempty group.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §2.2.1, p.17: "We may assume without loss of generality that x̂_{e,j} = max_{t∈S_j} Σ_{p∈P^j_t, e∈p} f̂_p for every
e ∈ E." Then:
"• Choose a positive integer C such that Cx̂_{e,j} is an even integer for every e ∈ E. Replace each edge e with Cx̂_{e,j}
parallel copies. ...
• ... Apply Theorem 2.8 on S⁺_j to obtain a S⁺_j-path-packing Q_j ...
• For each t ∈ S_j, choose a set Q^t_j of exactly C paths in Q_j having t as an endpoint."

Here `f t` holds the flow of the terminal `t`, `xh` the capacity of this group, `M` the multigraph, `Q` the packing and `Qt t`
the positions in `Q` of the selected paths.

**Formalization Note.** Lemmas 2.9 and 2.10 hold for any packing, so the size of `Q` is not part of this structure; the selection
`Qt` is a hypothesis, since the page proves it exists. -/
structure IsStage1 (G : SimpleGraph V) (r : V) (S : Finset V) (Lp : ℕ) (f : V → List V → ℝ)
    (xh : Sym2 V → ℝ) (C : ℕ) (M : MGraph V) (Q : List (MPath V))
    (Qt : V → Finset (Fin Q.length)) : Prop where
  nonempty : S.Nonempty
  normal : ∀ e ∈ G.edgeSet, (∀ t ∈ S, pathLoad (pathSet G r t Lp) (f t) e ≤ xh e) ∧
    ∃ t ∈ S, xh e = pathLoad (pathSet G r t Lp) (f t) e
  C_pos : 0 < C
  even : ∀ e ∈ G.edgeSet, ∃ m : ℕ, (C : ℝ) * xh e = 2 * (m : ℝ)
  copies : ∀ e, (e ∈ G.edgeSet → (M.edges.count e : ℝ) = (C : ℝ) * xh e) ∧
    (e ∉ G.edgeSet → M.edges.count e = 0)
  packing : IsSPacking M (insert r S) Q
  sel_card : ∀ t ∈ S, (Qt t).card = C
  sel_end : ∀ t ∈ S, ∀ q ∈ Qt t, Q[q].vs.head? = some t ∨ Q[q].vs.getLast? = some t

/-- The surviving paths of `Q^t_j`: "Remove all paths of length greater than 4L′_d from each collection Q^t_j" (p.17). -/
def surv (Lp : ℕ) (Q : List (MPath V)) (Qt : V → Finset (Fin Q.length)) (t : V) :
    Finset (Fin Q.length) :=
  (Qt t).filter fun q => Q[q].es.length ≤ 4 * Lp

/-- `S′_j`: the terminals with `Σ_{p∈Q^t_j} y^{j,t}_p ≥ 1` for `y^{j,t}_p = 4/C`, that is, `4 · |surviving paths| ≥ C` (p.18). -/
def Sprime (S : Finset V) (Lp C : ℕ) (Q : List (MPath V)) (Qt : V → Finset (Fin Q.length)) :
    Finset V :=
  S.filter fun t => C ≤ 4 * (surv Lp Q Qt t).card

/-- `y^{j,t}_p` after the scaling of p.18, "scale corresponding y values down so Σ_{p∈Q^t_j} y^{j,t}_p = 1": each of the `4/C`
is scaled by the same factor, so each surviving path has weight `1/|surviving paths|`. -/
noncomputable def yWeight (Lp : ℕ) (Q : List (MPath V)) (Qt : V → Finset (Fin Q.length)) (t : V) : ℝ :=
  1 / ((surv Lp Q Qt t).card : ℝ)

end MCPoise


