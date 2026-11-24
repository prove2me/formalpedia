-- Prove2me | Definitions.Def_ValiantBorder_programWord
-- name    : ValiantBorder_programWord
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:02:23.791957+00:00
-- url     : https://prove2.me/theorems/d07ba8bb-c706-476f-8533-1c74753ee4e9
-- title:
--   Word encoding of a binary-tree program input
-- statement:
--   Encode a binary tree in preorder, writing a zero for an empty tree and a one for a node. The polynomial input is the one-hot encoding of the resulting word and its end marker.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Circuit.lean).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Circuit.lean.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_approxAccelerator
/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field* (2026),
`anthropics/formal-math`, revision 11b6c7e3c927df2658f513b6b68ea7f8929c62c5.
The compiler, universal grid projection, and Laurent approximation arguments appear
in `Paper/Circuit.lean`, `Paper/LowDeg.lean` and `Paper/ApproxScales.lean`. Apache-2.0. -/
namespace NS1
/-- The brackets of a tree, in preorder: 0 = empty, 1 = a node. -/
def tbits : Tree → List Bool
  | .nil => [false]
  | .cons a b => true :: (tbits a ++ tbits b)

/-- The one-hot code of a word, with one letter `none` at the end. -/
def codeB (R : Type) [CommRing R] (N : ℕ) (w : List Bool) : Fin N × Option Bool → R :=
  fun q => if (w.map some ++ [none])[(q.1 : ℕ)]? = some q.2 then 1 else 0

end NS1


