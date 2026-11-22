-- Prove2me | Definitions.Def_AvgPHETH_Supplement_Formula_IsLayeredAlt
-- name    : AvgPHETH_Supplement_Formula_IsLayeredAlt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:29:05.504464+00:00
-- url     : https://prove2.me/theorems/944f37c5-94bc-4758-a0a5-2ee08a93be87
-- title:
--   Layered alternating formulas of depth $d$
-- statement:
--   A formula $F$ is a **layered alternating formula of depth $d$**, AND-rooted or OR-rooted, if gate types alternate between consecutive levels, every root-to-leaf path contains exactly $d$ gates, and the root is an AND gate (respectively an OR gate). A formula of depth $0$ is a single leaf.
--
--   These are the hard formulas $F_{k,w}$ of Theorem 7.1.
--
--   **Formalization Note** Every internal node is required to have at least one child, as internal nodes of a tree do.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_Formula

namespace AvgPHETH.Supplement

/-- `F.IsLayeredAlt b d`: `F` is a layered alternating AND-OR formula of depth `d` whose root is an
AND gate if `b = true` and an OR gate if `b = false` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)): gate types
alternate between consecutive levels, every internal node has at least one child, and every
root-to-leaf path contains exactly `d` gates.

**Formalization Note** A formula of depth `0` is a single leaf (its root type is not used). -/
def Formula.IsLayeredAlt {V : Type} : Formula V → Bool → ℕ → Prop
  | .leaf _, _, 0 => True
  | .gate a m ch, b, d + 1 => a = b ∧ 1 ≤ m ∧ ∀ i, (ch i).IsLayeredAlt (!b) d
  | _, _, _ => False

end AvgPHETH.Supplement


