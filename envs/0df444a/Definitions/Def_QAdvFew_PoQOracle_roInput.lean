-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_roInput
-- name    : QAdvFew_PoQOracle_roInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:08.391284+00:00
-- url     : https://prove2.me/theorems/dc48e9c6-78c8-450a-986e-7a7fe2e8bbdf
-- title:
--   The random oracle as circuit inputs
-- statement:
--   The random oracle as circuit inputs indexed by strings: the input $s$ carries $\mathrm{RO}_{|s|}(s)$ if $|s|\le k$ and $0$ otherwise, with $k=\infty$ for every level.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Corollary 4.8, p. 24 (PDF p. 26); Lemma 4.11, p. 26 (PDF p. 28)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The random oracle as circuit inputs indexed by strings (Goldin, Lombardi, Morimae, *Quantum
Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Corollary 4.8, p. 24 (PDF p. 26):
input `(RO_1, …, RO_{t^{2d}−1})`; Lemma 4.11, p. 26 (PDF p. 28): input `RO`): the input `s` carries
`RO_{|s|}(s)` if `|s| ≤ k`, and `0` otherwise (`k = ⊤`: every level). -/
def roInput (ro : (Σ t : ℕ, Fin t → Bool) → Bool) (k : ℕ∞) : Str → Bool := fun s =>
  if (s.length : ℕ∞) ≤ k then ro ⟨s.length, fun i => s.get i⟩ else false

end QAdvFew.PoQOracle


