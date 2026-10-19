-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
-- name    : OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:05:48.30998+00:00
-- url     : https://prove2.me/theorems/d33c51f9-bb67-4f1c-a6d0-0b9f7bfa9423
-- title:
--   Sign coordinates, coordinate flips and the threshold sign on the Boolean cube
-- statement:
--   The Boolean cube $\{0,1\}^n$ encodes the sign cube $\{-1,1\}^n$, with true representing $1$ and false representing $-1$.
--
--   1. **Sign coordinates.** For a vertex $x$ and a coordinate $i$, $x_i^{\pm}=1$ if $x_i$ is true and $-1$ otherwise.
--   2. **Flip.** $x^{\oplus i}$ is $x$ with coordinate $i$ negated.
--   3. **Threshold sign.**
--   $$
--   \operatorname{sgn}(t)=\begin{cases}1,&t\ge0,\\-1,&t<0,\end{cases}
--   $$
--   with the convention $\operatorname{sgn}(0)=1$.
--
--   These are the basic operations on the cube shared with the polynomial-threshold (Gotsman–Linial) development, reused here for Boolean functions under noise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CourtadeKumar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CourtadeKumar

namespace OAI

/-!
# Polynomial thresholds and average sensitivity

The Boolean cube encodes the sign cube `{−1,1}^n`:
`false` represents `−1` and `true` represents `1`. The public statement
quantifies directly over real multilinear polynomials and uses uniform counting
probability, the convention `sign(0) = 1`, and the exact constant `8`.

`GotsmanLinialStatement` is a proposition definition, not a proof of the bound.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

/-- Interpret a Boolean cube coordinate as the corresponding real sign. -/
def cubeCoord {n : ℕ} (x : Cube n) (i : Fin n) : ℝ :=
  if x i then 1 else -1

/-- Reverse one coordinate of a cube vertex. -/
def flip {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!(x i))

/-- The threshold convention assigns `1` at zero. -/
noncomputable def thresholdSign (t : ℝ) : ℝ :=
  if 0 ≤ t then 1 else -1

end LeanBlast.GotsmanLinial

end OAI


