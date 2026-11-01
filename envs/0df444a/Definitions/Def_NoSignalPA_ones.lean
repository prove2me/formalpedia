-- Prove2me | Definitions.Def_NoSignalPA_ones
-- name    : NoSignalPA_ones
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:37.55119+00:00
-- url     : https://prove2.me/theorems/9205120b-3866-4a6b-92ab-4e218c5e4ff1
-- title:
--   Number of ones $\|\mathbf x\|$ of a bit string
-- statement:
--   For a bit string $\mathbf x\in\{0,1\}^n$, $\|\mathbf x\|$ is the number of indices $i$ with $x_i=1$ (the Hamming weight).
-- source:
--   Masanes, Universally-composable privacy amplification from causality constraints, arXiv:0807.2158v4, Appendix, proof of Lemma 2, p.4, item (iii)

import Mathlib
import Definitions.Def_NoSignalPA_Str

namespace NoSignalPA

/-- **The number of ones `‖v‖` of a bit string.**
Ll. Masanes, *Universally-composable privacy amplification from causality constraints*,
arXiv:0807.2158v4, Appendix, proof of Lemma 2, p. 4 (PDF p. 4): "(iii) the integer `‖x‖` is the number of ones
in x". -/
def ones {n : ℕ} (v : Str n) : ℕ :=
  (Finset.univ.filter fun i => v i = true).card

end NoSignalPA


