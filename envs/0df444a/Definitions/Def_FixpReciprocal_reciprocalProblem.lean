-- Prove2me | Definitions.Def_FixpReciprocal_reciprocalProblem
-- name    : FixpReciprocal_reciprocalProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:49:29.716046+00:00
-- url     : https://prove2.me/theorems/48837085-2279-40f4-a40c-ae174ef4c448
-- title:
--   The search problems for gates of (1), with and without the nonconstant-gate assumption
-- statement:
--   For a fixed rational $\tau$, the search problem $\mathrm{Rec}_\tau$ takes a generalized circuit $\mathcal C$ with the gates of (1) and asks for a solution of $\mathcal C$. The problem $\mathrm{Rec}^{\mathrm{nc}}_\tau$ is the same problem restricted to circuits with at least one nonconstant gate.
--
--   The paper writes "We therefore assume that input circuits contain at least one nonconstant gate" (p.11). That sentence can be read as part of the problem or as a remark. Restricting instances makes membership easier and hardness harder, so neither reading is simply the stronger, and the goal theorem covers both problems.
--
--   **Formalization Note** $\tau$ is not part of the instance, so machines may depend on it, as "for every fixed rational $\tau>0$" says.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Theorem 1.1, p.2 (PDF p.4); Definition 3.3 and the paragraph on constant gates, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_FixpReciprocal_RealSearch
import Definitions.Def_FixpReciprocal_RGate

namespace FixpReciprocal

/-- **Finding a solution of a generalized circuit with the gates of (1)**, for a fixed `τ`: instances are all
valid circuits.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Theorem 1.1, p.2; Theorem 4.2, p.12; Definition 3.3, p.11.

**Formalization Note.** `τ` is a parameter of the problem, not of the instance ("for every fixed rational
`τ > 0`"), so machines may depend on it. -/
def reciprocalProblem (τ : ℚ) : RealSearch where
  Inst := {C : List RGate // RValid C}
  enc := fun I => encRGates I.1
  enc_injective := fun _ _ h => Subtype.ext (encRGates_injective h)
  dim := fun I => I.1.length
  Sol := fun I => RCircuitSol τ I.1

/-- **The same problem restricted to circuits with at least one nonconstant gate**: "We therefore assume that
input circuits contain at least one nonconstant gate" (p.11).

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.3 and the paragraph after it, p.11.

**Formalization Note.** That sentence can be read as a remark or as part of the problem. Restricting
instances makes membership easier and hardness harder, so the goal theorem states completeness for
both this problem and `reciprocalProblem`. -/
def reciprocalProblemNC (τ : ℚ) : RealSearch where
  Inst := {C : List RGate // RValid C ∧ ∃ g ∈ C, ¬ g.IsConstant}
  enc := fun I => encRGates I.1
  enc_injective := fun _ _ h => Subtype.ext (encRGates_injective h)
  dim := fun I => I.1.length
  Sol := fun I => RCircuitSol τ I.1

end FixpReciprocal


