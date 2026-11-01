-- Prove2me | Definitions.Def_NoRegretLastIterate_Game
-- name    : NoRegretLastIterate_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:27.754206+00:00
-- url     : https://prove2.me/theorems/49d8d0a5-5418-496c-b2ec-1a2624710109
-- title:
--   §2 and Definition 2.6 — $2\times2$ games, bilinear extension $X(p,q)$, competitive games, product distribution and CCE
-- statement:
--   A **$2\times2$ game** consists of two payoff matrices $G=(G(i,j))_{i,j\in\{0,1\}}$ and $H=(H(i,j))_{i,j\in\{0,1\}}$: if player 1 plays action $i$ and player 2 plays action $j$, player 1 receives $G(i,j)$ and player 2 receives $H(i,j)$; both maximize. A **mixed strategy** is the probability $p\in[0,1]$ (resp. $q$) of playing action $1$. This file defines:
--
--   1. the probability vector $(1-p,p)$ of a mixed strategy $p$;
--   2. the **bilinear extension** of $X\in\{G,H\}$ to mixed strategies,
--   $$
--   X(p,q):=(1-p)(1-q)X(0,0)+(1-p)qX(0,1)+p(1-q)X(1,0)+pqX(1,1);
--   $$
--   3. conditions (a) and (b) of Definition 2.6,
--   $$
--   \text{(a)}\ \ G(0,0)>G(1,0),\ G(0,1)<G(1,1),\ H(0,0)<H(0,1),\ H(1,0)>H(1,1),
--   $$
--   $$
--   \text{(b)}\ \ G(0,0)<G(1,0),\ G(0,1)>G(1,1),\ H(0,0)>H(0,1),\ H(1,0)<H(1,1),
--   $$
--   and the game is **competitive** if (a) or (b) holds;
--   4. the **product distribution** $p\times q$ on $\{0,1\}^2$, with $(i,j)$ entry $\Pr(I=i)\Pr(J=j)$ when $\Pr(I=1)=p$, $\Pr(J=1)=q$;
--   5. a **coarse correlated equilibrium** (payoff convention): a joint distribution $\mu$ on $\{0,1\}^2$ with
--   $$
--   \mathbb E_{(I,J)\sim\mu}[G(I,J)]\ge \mathbb E_{(I,J)\sim\mu}[G(i',J)]\quad\text{and}\quad \mathbb E_{(I,J)\sim\mu}[H(I,J)]\ge \mathbb E_{(I,J)\sim\mu}[H(I,j')]
--   $$
--   for every unilateral deviation $i'$, $j'\in\{0,1\}$.
--
--   Matching pennies ($G(0,0)=G(1,1)=1$, $G(0,1)=G(1,0)=-1$, $H=-G$) satisfies condition (a). These objects are the game-theoretic layer of every statement in the mission.
--
--   **Formalization Note** Actions are `Fin 2`, "action 1" being `1`. Payoffs are `Matrix (Fin 2) (Fin 2) ℝ`. Joint distributions use the published predicate `CalibratedCE.Convergence.IsJointDist`; the Nash equilibrium of the mission is the published `RankOneBimatrix.BinSearch.IsNE` applied to the vectors $(1-p,p)$, $(1-q,q)$.
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, §2 p.5 (bilinear extension), Definition 2.6 p.8 (competitive), App. B p.32 (CCE, µ = p∗ × q∗)

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game

namespace NoRegretLastIterate

open Matrix

/-- Muthukumar, Phade, Sahai, arXiv:2012.02125v3, §2, p.5: the mixed strategy that plays action
`1` with probability `p`, as the probability vector `(1 - p, p)` on `{0, 1}`.

**Formalization Note** Actions are `Fin 2`, with "action 1" `= (1 : Fin 2)`. This vector is only
used to feed a pair `(p, q)` to the published Nash-equilibrium predicate
`RankOneBimatrix.BinSearch.IsNE`, which takes probability vectors. -/
def mix (p : ℝ) : Fin 2 → ℝ := ![1 - p, p]

/-- arXiv:2012.02125v3, §2, p.5: the bilinear extension of a `2 × 2` payoff matrix `X`
(`X = G` or `X = H`) to mixed strategies `(p, q)`,
`X(p, q) := (1 − p)(1 − q)X(0, 0) + (1 − p)qX(0, 1) + p(1 − q)X(1, 0) + pqX(1, 1)`. -/
def ext (X : Matrix (Fin 2) (Fin 2) ℝ) (p q : ℝ) : ℝ :=
  (1 - p) * (1 - q) * X 0 0 + (1 - p) * q * X 0 1 + p * (1 - q) * X 1 0 + p * q * X 1 1

/-- arXiv:2012.02125v3, Definition 2.6 (a), p.8:
`G(0, 0) > G(1, 0), G(0, 1) < G(1, 1), H(0, 0) < H(0, 1), H(1, 0) > H(1, 1)`. -/
def CondA (G H : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  G 0 0 > G 1 0 ∧ G 0 1 < G 1 1 ∧ H 0 0 < H 0 1 ∧ H 1 0 > H 1 1

/-- arXiv:2012.02125v3, Definition 2.6 (b), p.8:
`G(0, 0) < G(1, 0), G(0, 1) > G(1, 1), H(0, 0) > H(0, 1), H(1, 0) < H(1, 1)`. -/
def CondB (G H : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  G 0 0 < G 1 0 ∧ G 0 1 > G 1 1 ∧ H 0 0 > H 0 1 ∧ H 1 0 < H 1 1

/-- arXiv:2012.02125v3, Definition 2.6, p.8: a `2 × 2` game `(G, H)` (payoffs of player 1 and
player 2, both maximized) is *competitive* if condition (a) or condition (b) holds. -/
def IsCompetitive (G H : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  CondA G H ∨ CondB G H

/-- arXiv:2012.02125v3, App. B, p.32 ("this distribution corresponds to the unique NE of this
game, i.e. µ = p∗ × q∗"): the product distribution `p × q` on `{0, 1}²`, whose `(i, j)` entry is
`P(I = i) P(J = j)` with `P(I = 1) = p`, `P(J = 1) = q`. -/
def prodDist (p q : ℝ) : Fin 2 → Fin 2 → ℝ := fun i j => mix p i * mix q j

/-- arXiv:2012.02125v3, App. B, p.32: a coarse correlated equilibrium of the `2 × 2` game
`(G, H)` in the payoff (maximization) convention: a joint distribution `D` on `{0, 1}²` such that
`E_{(I,J)∼D}[G(I, J)] ≥ E_{(I,J)∼D}[G(i′, J)]` for every `i′` and
`E_{(I,J)∼D}[H(I, J)] ≥ E_{(I,J)∼D}[H(I, j′)]` for every `j′`.

**Formalization Note** Joint distributions are matrices `D : Fin 2 → Fin 2 → ℝ` with the published
predicate `CalibratedCE.Convergence.IsJointDist` (nonnegative entries summing to one), the same
vocabulary as the published correlated-equilibrium predicate `CalibratedCE.Convergence.IsCE`. The
page prints these inequalities with `≤` (the cost convention); the theorem that uses this
definition states the printed `≤` system separately. -/
def IsCCE (G H : Matrix (Fin 2) (Fin 2) ℝ) (D : Fin 2 → Fin 2 → ℝ) : Prop :=
  CalibratedCE.Convergence.IsJointDist D ∧
  (∀ i' : Fin 2, ∑ i, ∑ j, D i j * G i' j ≤ ∑ i, ∑ j, D i j * G i j) ∧
  (∀ j' : Fin 2, ∑ i, ∑ j, D i j * H i j' ≤ ∑ i, ∑ j, D i j * H i j)

end NoRegretLastIterate


