-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
-- name    : OAI_InformationTheory_BooleanNoise_Statement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:10:11.74307+00:00
-- url     : https://prove2.me/theorems/3b605de6-4d61-4bcb-b4f2-571e55fbbdb0
-- title:
--   Endpoint values of $t\log t$ and of the binary entropy
-- statement:
--   With $\phi(t)=t\log t$ and $H(\varepsilon)=-\bigl(\phi(\varepsilon)+\phi(1-\varepsilon)\bigr)/\log2$ the binary entropy in bits,
--   $$
--   \phi(0)=0,\qquad H(0)=0,\qquad H(1)=0 .
--   $$
--
--   These are the boundary cases $\varepsilon\in\{0,1\}$ of the Courtade–Kumar bound $I\le1-H(\varepsilon)$: without noise the bound reads $I\le1$.
--
--   **Formalization Note** $\phi(0)=0$ holds because Lean sets $\log0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Statement.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Statement.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CourtadeKumar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

@[simp] theorem xlogx_zero : xlogx 0 = 0 := by simp [xlogx]

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, xlogx]

@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy, xlogx]

end LeanBlast.CourtadeKumar

end

end OAI


