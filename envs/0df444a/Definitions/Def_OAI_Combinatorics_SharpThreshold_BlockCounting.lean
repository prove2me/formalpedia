-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
-- name    : OAI_Combinatorics_SharpThreshold_BlockCounting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:10:58.162626+00:00
-- url     : https://prove2.me/theorems/24617891-40b7-49b0-be95-357198d88d01
-- title:
--   Probability over a uniformly random fixed-size subset
-- statement:
--   For a finite set $U$, an integer $m$ and a predicate $P$ on subsets, the probability that a uniformly random $m$-element subset of $U$ satisfies $P$ is
--   $$
--   \Pr_{A\in\binom Um}[P(A)]=\frac{|\{A\subseteq U:\ |A|=m,\ P(A)\}|}{\binom{|U|}m} .
--   $$
--   In particular the never-true predicate has probability $0$.
--
--   Random vertex blocks of a fixed size are chosen this way.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/BlockCounting.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockCounting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree

namespace OAI

universe u

noncomputable section

namespace Problem313

open Finset

variable {α : Type u} [DecidableEq α]

/-- Probability of an event for a uniformly chosen fixed-size subset. -/
def blockProbability (U : Finset α) (m : ℕ) (P : Finset α → Prop) : ℝ := by
  classical
  exact (((U.powersetCard m).filter P).card : ℝ) / (U.powersetCard m).card

omit [DecidableEq α] in
@[simp] theorem blockProbability_false (U : Finset α) (m : ℕ) :
    blockProbability U m (fun _ => False) = 0 := by
  simp [blockProbability]

end Problem313

end

end OAI


