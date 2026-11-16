-- Prove2me | Definitions.Def_SmoothBerr_Supplement_IsAlternating
-- name    : SmoothBerr_Supplement_IsAlternating
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:53:27.837605+00:00
-- url     : https://prove2.me/theorems/332071b8-5f75-4e85-adb6-e3b67c23a03e
-- title:
--   Alternating matvec algorithm (Definition 6.3)
-- statement:
--   A deterministic matvec algorithm is **alternating** if at step $i$ it computes
--   $$
--   y_i=Ax_i\quad(i\text{ odd}),\qquad x_i=A^\top y_i\quad(i\text{ even}),
--   $$
--   that is, the kind of each query is fixed by the parity of its index and only the query vector is chosen adaptively. Alternating algorithms are the class of Theorems 6.4 and 6.7.
--
--   **Formalization Note** Step $i$ is the query issued after a transcript of $i-1$ entries. The parity condition is imposed on every transcript; changing an algorithm on transcripts that no run reaches changes no run, so this is the paper's class.
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Definition 6.3, p.17

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_DetMatvecAlg

namespace SmoothBerr.Supplement

/-- **Alternating matvec algorithm** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis
to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256
9575cd20…, Definition 6.3, p.17): at step `i` it computes `y_i = A x_i` for `i` odd and
`x_i = Aᵀ y_i` for `i` even.

**Formalization Note** Step `i` (1-indexed) is the query issued after a transcript of `i − 1`
entries, so the query kind is `mulA` when the transcript has even length and `mulAT` when it has
odd length. The condition is imposed on every transcript; changing an algorithm on transcripts
that no run reaches changes no run, so this is the paper's class. -/
def IsAlternating {n : ℕ} (Φ : DetMatvecAlg n) : Prop :=
  ∀ (b : Fin n → ℝ) (T : List (Entry n)) (s : Side) (v : Fin n → ℝ),
    Φ.next b T = some (s, v) → s = (if T.length % 2 = 0 then Side.mulA else Side.mulAT)

end SmoothBerr.Supplement


