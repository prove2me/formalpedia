-- Prove2me | Definitions.Def_ReliableFacilityLoc_LevelOrder_Moves
-- name    : ReliableFacilityLoc_LevelOrder_Moves
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:56.507982+00:00
-- url     : https://prove2.me/theorems/24de7248-1377-4c8f-8eed-233160306e8d
-- title:
--   The probabilities recomputed from (1e)–(1f), and the two assignment changes of the proof of Proposition 2
-- statement:
--   These are the constructions of Appendix A.2 (pp. 34–35) of Cui, Ouyang and Shen, on top of the (RUFL) model.
--
--   1. **Recomputed probabilities.** For an assignment $Y$, the array $P = P(Y)$ is the unique solution of (1e)–(1f):
--   $$P_{ij0} = 1 - q_j,\qquad P_{ijr} = (1-q_j)\sum_{k=0}^{J-1}\frac{q_k}{1-q_k}P_{i,k,r-1}Y_{i,k,r-1}\quad(1 \le r \le R),$$
--   with $q_J = 0$. A triple $(X,Y,P)$ satisfies (1e)–(1f) exactly when $P = P(Y)$.
--   2. **The swap.** For a customer $i$, facilities $j, k$ and a level $r$ with $r+1 \le R$, the assignment $Y'$ that exchanges $j$ and $k$ between levels $r$ and $r+1$:
--   $$Y'_{h\ell s} = \begin{cases} 1 & h=i,\ \ell=k,\ s=r \text{ or } h=i,\ \ell=j,\ s=r+1,\\ 0 & h=i,\ \ell=j,\ s=r \text{ or } h=i,\ \ell=k,\ s=r+1,\\ Y_{h\ell s} & \text{otherwise.}\end{cases}$$
--   3. **Moving the emergency facility up.** For a customer $i$, a facility $j$ and a level $r$ with $r+1\le R$, the assignment $Y'$ with $Y'_{iJr} = 1$, $Y'_{ijr} = 0$, $Y'_{iJ,r+1} = 0$, $Y'_{ij,r+1} = 0$ and $Y' = Y$ elsewhere: the emergency facility replaces $j$ at level $r$ and $j$ is dropped.
--
--   They are the two improving moves by which the paper proves that optimal solutions order each customer's levels by distance.
--
--   **Formalization Note** The paper's $P'$ keeps $P'_{h\ell s} = P_{h\ell s}$ at the indices it does not list; that array violates (1e)–(1f) at unassigned entries, so the proof's $P'$ is taken here to be $P(Y')$, which coincides with the paper's $P'$ wherever $Y' = 1$. The level $r$ is an element of $\{0,\dots,R-1\}$, so that $r+1 \le R$.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 9 (PDF 11), (1e)–(1f); Appendix A.2, pp. 34–35 (PDF 36–37), the definitions of Y′ and P′

import Mathlib
import Definitions.Def_ReliableFacilityLoc_LevelOrder_RUFL

open Finset

namespace ReliableFacilityLoc.LevelOrder

namespace Instance

variable {I J R : ℕ} (D : Instance I J R)

/-- The transition probabilities determined by an assignment `Y` through (1e)–(1f) of Cui, Ouyang
and Shen, UCTC-FR-2010-02 (Feb. 2010), p. 9 (PDF 11): `P_ij0 = 1 - q_j` and, for `1 ≤ r ≤ R`,
`P_ijr = (1 - q_j) Σ_{k=0}^{J-1} q_k/(1-q_k) P_{i,k,r-1} Y_{i,k,r-1}` (with `q_J = 0`).

Formalization Note: the recursion runs over the level with `Fin.induction`; `transProb Y i j r` is
`P_ijr`. Constraints (1e)–(1f) say exactly that `P = transProb Y`. This is the `P′` "recomputed
by (1e)–(1f)" for a modified assignment `Y′` in the proof of Proposition 2 (A.2, pp. 34–35). -/
noncomputable def transProb (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) :
    Fin I → Fin (J + 1) → Fin (R + 1) → ℝ :=
  fun i j r =>
    (Fin.induction (motive := fun _ => Fin (J + 1) → ℝ)
      (fun j => 1 - D.qExt j)
      (fun r Pr j => (1 - D.qExt j) * ∑ k : Fin J,
        D.q k / (1 - D.q k) * Pr k.castSucc * Y i k.castSucc r.castSucc) r) j

end Instance

/-- The swap of A.2, p. 34 (PDF 36), of Cui, Ouyang and Shen, UCTC-FR-2010-02 (Feb. 2010):
for customer `i`, facilities `j`, `k` and a level `r` with `r + 1 ≤ R`,
`Y′_hℓs = 1` if `h = i, ℓ = k, s = r` or `h = i, ℓ = j, s = r+1`;
`Y′_hℓs = 0` if `h = i, ℓ = j, s = r` or `h = i, ℓ = k, s = r+1`; and `Y′_hℓs = Y_hℓs` otherwise.

Formalization Note: the level `r` is given as `r : Fin R`, so that `r.castSucc` is level `r` and
`r.succ` is level `r + 1 ≤ R`. -/
def swapY {I J R : ℕ} (i : Fin I) (j k : Fin (J + 1)) (r : Fin R)
    (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ :=
  fun h l s =>
    if h = i ∧ ((l = k ∧ s = r.castSucc) ∨ (l = j ∧ s = r.succ)) then 1
    else if h = i ∧ ((l = j ∧ s = r.castSucc) ∨ (l = k ∧ s = r.succ)) then 0
    else Y h l s

/-- The move of A.2, p. 35 (PDF 37), case `k = J`, of Cui, Ouyang and Shen, UCTC-FR-2010-02
(Feb. 2010): when customer `i` has facility `j` at level `r` and the emergency facility `J` at
level `r + 1`, the emergency facility is moved up to level `r` and `j` is dropped, so that
`Y′_iJr = 1`, `Y′_ijr = 0`, `Y′_{iJ,r+1} = 0`, `Y′_{ij,r+1} = 0`, and `Y′ = Y` elsewhere.

Formalization Note: the page says only that the case `k = J` is "similar, except that
`Y′_{ij,r+1} = P′_{ij,r+1} = 0`"; the swap of `j` and `J` with `j` then removed from level
`r + 1` is exactly this assignment. The level `r` is `r : Fin R`, as in `swapY`. -/
def emergencyUpY {I J R : ℕ} (i : Fin I) (j : Fin (J + 1)) (r : Fin R)
    (Y : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ) : Fin I → Fin (J + 1) → Fin (R + 1) → ℝ :=
  fun h l s =>
    if h = i ∧ l = Fin.last J ∧ s = r.castSucc then 1
    else if h = i ∧ ((l = j ∧ s = r.castSucc) ∨ (l = Fin.last J ∧ s = r.succ)) then 0
    else Y h l s

end ReliableFacilityLoc.LevelOrder


