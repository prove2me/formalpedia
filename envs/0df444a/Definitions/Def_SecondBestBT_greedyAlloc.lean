-- Prove2me | Definitions.Def_SecondBestBT_greedyAlloc
-- name    : SecondBestBT_greedyAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:40.119957+00:00
-- url     : https://prove2.me/theorems/ce30d9ec-a557-4159-ae0b-7f9c4e6532b4
-- title:
--   The allocation rule defined by Algorithm 1
-- statement:
--   The **allocation rule defined by Algorithm 1** assigns to $(s,b)$ the entry $x(s,b)$ produced when buyer value $b$ is processed.
--
--   **Formalization Note** If the run has failed by buyer value $b$, the column is set to $0$; the theorems use this rule only when the algorithm never fails.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Algorithm 1, p.14; Theorem 4.10, p.15

import Mathlib
import Definitions.Def_SecondBestBT_greedyRun

namespace SecondBestBT

/-- The allocation rule `x` defined by Algorithm 1 (Liu–Qin–Ren–Wang, arXiv:2606.03849, held
version sha256 17184930…, Section 4.5, Algorithm 1, p.14, and Theorem 4.10, p.15): `x(s, b)` is
the entry produced when buyer value `b` is processed.

**Formalization Note** If the run has failed by buyer value `b`, the column is set to `0`; the
theorems use this definition only under the hypothesis that the algorithm never fails. -/
noncomputable def greedyAlloc (α β : ℝ) (K : ℕ) (fS : ℕ → ℝ) (s b : ℕ) : ℝ :=
  match greedyRun α β K fS b with
  | some p => p.1 s b
  | none => 0

end SecondBestBT


