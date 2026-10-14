-- Prove2me | Definitions.Def_BBDisclosure_Total_Stage2
-- name    : BBDisclosure_Total_Stage2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:55.474228+00:00
-- url     : https://prove2.me/theorems/baba08eb-6829-4d17-ac43-cf09d29ca80e
-- title:
--   §2–§4, pp. 8514–8519 — Hotelling duopoly with behavior-based pricing: turf price games, threshold disclosure (uniform and BBD), second-period equilibrium and ex ante profits
-- statement:
--   This file builds on the shared second-period model `BBDisclosure.Stage2.Model` of Zhang and Li, *Retention or Acquisition? Behavior-Based Quality Disclosure* (Management Science, 2025), §2–§4. That model fixes the Hotelling line $[0,1]$ with A at $0$ and B at $1$, transportation cost $t=1$, full coverage, independent $U[0,1]$ qualities, the belief map $\operatorname{bel}(\hat q,q)=q$ if $q>\hat q$ and $\hat q/2$ otherwise, the clamped turf price games, the second-period profiles and equilibria under uniform and behavior-based disclosure, the ex ante profits $E(\pi_{a2}),E(\pi_{b2})$, and the region-1 support windows. Every theorem of this mission uses those objects.
--
--   The file adds three auxiliary predicates:
--   - `IsNashNonneg fA fB p`: in a two-player game where both players choose a nonnegative number, $p$ is a Nash equilibrium of the payoffs $f_A$ (player 1) and $f_B$ (player 2), meaning both coordinates are $\ge 0$ and neither player gains from a unilateral deviation to another nonnegative number;
--   - `IsTurfNashA`, `IsTurfNashB`: its instances for the two turf price games of the shared model;
--   - `IsThresholdBR V cost thr`: for every $q\in[0,1]$, $V(\mathrm{thr}/2)\le V(q)-\mathrm{cost}$ when $q>\mathrm{thr}$, and $V(q)-\mathrm{cost}\le V(\mathrm{thr}/2)$ when $q<\mathrm{thr}$. This says that a disclosure threshold is a best response.
--
--   These predicates restate, in an unbundled form, the Nash and best-response clauses of the shared model's second-period equilibrium.
--
--   **Formalization Note.** The base value $v$ cancels from every profit and comparison and is omitted. Prices are nonnegative, reading the corner "$p^*_{bn}=0$" of Lemma 1/2.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, pp. 8514–8519, §2 Model Setup, §3.1–3.2, §4.1–4.2, (1), (10), Lemma 1, Lemma 2, Table 1 Notes

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace BBDisclosure.Total

/-!
# Zhang and Li, *Retention or Acquisition? Behavior-Based Quality Disclosure*, §2–§4 (pp. 8514–8519):
the second period

Two firms, A at `0` and B at `1`, on a Hotelling line `[0, 1]` of unit mass, transportation cost
`t = 1`, full coverage, marginal cost `0`. After the first period, A's old customers are `[0, x1]`
("A's turf") and B's old customers are `[x1, 1]` ("B's turf"). In the second period each firm `i`
sells a new product of quality `qᵢ ~ U[0,1]` (independent across firms), discloses it to a
segment at unit cost `c` per customer reached, and then prices behavior-based: own customers
`p_ao`, `p_bo`, competitor's customers `p_an`, `p_bn`.

The base value `v` cancels from every profit and every comparison and is omitted.
-/

/-- A two-player game in which both players choose a nonnegative number (a price): `p` is a Nash
equilibrium of the payoffs `fA` (player 1, chooses `p.1`) and `fB` (player 2, chooses `p.2`) when
both coordinates are `≥ 0` and neither player gains from a unilateral deviation to another
nonnegative price. -/
def IsNashNonneg (fA fB : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2 ∧ (∀ a : ℝ, 0 ≤ a → fA (a, p.2) ≤ fA p) ∧
    (∀ b : ℝ, 0 ≤ b → fB (p.1, b) ≤ fB p)

/-! ## The turf price games -/

/-- Nash equilibrium `p = (p_ao, p_bn)` of the price game on A's turf, beliefs `(u, w)`. -/
def IsTurfNashA (x1 u w : ℝ) (p : ℝ × ℝ) : Prop :=
  IsNashNonneg (BBDisclosure.Stage2.revAturfA x1 u w) (BBDisclosure.Stage2.revBturfA x1 u w) p

/-- Nash equilibrium `p = (p_an, p_bo)` of the price game on B's turf, beliefs `(u, w)`. -/
def IsTurfNashB (x1 u w : ℝ) (p : ℝ × ℝ) : Prop :=
  IsNashNonneg (BBDisclosure.Stage2.revAturfB x1 u w) (BBDisclosure.Stage2.revBturfB x1 u w) p

/-! ## Disclosure thresholds -/

/-- `thr` is a best-response disclosure threshold for a firm whose gross expected revenue on the
segment, when the segment's belief about its quality is `u`, is `V u`, and whose cost of
disclosing to the segment is `cost`: for every quality `q ∈ [0,1]`, disclosing (belief `q`, cost
paid) is weakly better than not disclosing (belief `thr / 2`) when `q > thr`, and weakly worse when
`q < thr`. -/
def IsThresholdBR (V : ℝ → ℝ) (cost thr : ℝ) : Prop :=
  ∀ q ∈ Set.Icc (0 : ℝ) 1,
    (thr < q → V (thr / 2) ≤ V q - cost) ∧ (q < thr → V q - cost ≤ V (thr / 2))

/-! ## Ex ante second-period profits -/

/-! ## "In region 1" -/

end BBDisclosure.Total


