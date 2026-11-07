-- Prove2me | Definitions.Def_GeoQAC_IsInterval
-- name    : GeoQAC_IsInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:48.22672+00:00
-- url     : https://prove2.me/theorems/b20a6c8d-a00f-4677-b378-fa3fcb113e6b
-- title:
--   Interval supports in one row or one column
-- statement:
--   In a 2D-QAC circuit every multi-qubit gate has **contiguous support in one row or column**. A set $S\subseteq[w]\times[h]$ is an **interval support** when it is a horizontal interval $\{r\}\times[a,b]$ of some row $r$, or a vertical interval $[a,b]\times\{c\}$ of some column $c$, with $a\le b$.
--
--   Interval supports are nonempty, and a singleton is both horizontal and vertical. Their diameter is not bounded: "geometrically local" refers to connected interval support, not to bounded interaction range.
--
--   **Formalization Note** Rows and columns are indexed from $0$; the condition $a\le b$ makes every interval nonempty.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Definition 2.3, p.11

import Mathlib
import Definitions.Def_GeoQAC_Pos

namespace GeoQAC

/-!
# Interval supports: contiguous in one row or one column

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), Definition 2.3, p.11: "Each multi-qubit
gate has contiguous support in one row or column."

**Formalization Note.** A support is an interval `{r} × [a, b]` of a row or `[a, b] × {c}` of a
column, with `a ≤ b`, so it is nonempty. A singleton is both. The diameter is unrestricted (p.11:
"an allowed interval may have an arbitrarily large diameter").
-/

/-- `S` is a horizontal interval `{r} × [a, b]` or a vertical interval `[a, b] × {c}` of the grid,
with `a ≤ b` (arXiv:2604.07178, version of 2026-11-03, Definition 2.3, p.11). -/
def IsInterval {w h : ℕ} (S : Finset (Pos w h)) : Prop :=
  (∃ (r : Fin w) (a b : Fin h), a ≤ b ∧
      S = Finset.univ.filter (fun v : Pos w h => v.1 = r ∧ a ≤ v.2 ∧ v.2 ≤ b)) ∨
  (∃ (c : Fin h) (a b : Fin w), a ≤ b ∧
      S = Finset.univ.filter (fun v : Pos w h => v.2 = c ∧ a ≤ v.1 ∧ v.1 ≤ b))

instance {w h : ℕ} (S : Finset (Pos w h)) : Decidable (IsInterval S) := by
  unfold IsInterval; infer_instance

end GeoQAC


