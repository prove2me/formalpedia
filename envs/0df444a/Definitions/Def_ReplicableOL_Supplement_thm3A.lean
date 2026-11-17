-- Prove2me | Definitions.Def_ReplicableOL_Supplement_thm3A
-- name    : ReplicableOL_Supplement_thm3A
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:21:10.140118+00:00
-- url     : https://prove2.me/theorems/ad045463-ed49-46fd-952b-aa993efa5877
-- title:
--   Chain recursion of Theorem 3
-- statement:
--   The recursion defining Theorem 3's chain:
--
--   $$
--   A_0=T,\qquad A_i=2^{\lceil \log_2(\sqrt{A_{i-1}}/\kappa)\rceil}\quad(i\ge1).
--   $$
--
--   **Formalization Note** The exponent is the integer ceiling converted with `Int.toNat`, which clips negative values to $0$. Theorem 3 reads $A_i$ only for $i\le K$, where $\sqrt{A_{i-1}}/\kappa>1$ and the exponent is positive, so the clipping changes nothing there.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Theorem 3 (with parameters), p.20

import Mathlib
import Definitions.Def_ReplicableOL_Supplement_thm3kappa

namespace ReplicableOL.Supplement

/-- **Theorem 3's chain recursion.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Theorem 3 (with parameters), p.20. `A_0 = T` and "A_i := 2^{⌈log₂(√A_{i−1}/κ)⌉} (i ≥ 1)".

**Formalization Note.** The exponent is the integer ceiling taken through `Int.toNat`. Theorem 3 reads `A_i` only for `i ≤ K`, where every `A_{i-1}` with `i ≤ K` exceeds `8/κ²` and `κ ≤ 0.1`, so `√A_{i−1}/κ > 1` and the exponent is positive; `toNat` changes nothing there. -/
noncomputable def thm3A (ρ : ℝ) (T : ℕ) : ℕ → ℕ
  | 0 => T
  | i + 1 => 2 ^ (⌈Real.logb 2 (√(thm3A ρ T i : ℝ) / thm3kappa ρ T)⌉).toNat

end ReplicableOL.Supplement


