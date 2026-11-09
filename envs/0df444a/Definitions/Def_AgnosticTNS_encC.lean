-- Prove2me | Definitions.Def_AgnosticTNS_encC
-- name    : AgnosticTNS_encC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:28.884576+00:00
-- url     : https://prove2.me/theorems/3379cdd3-fb91-40b6-b5ca-d17c49ba78db
-- title:
--   Binary code of a Gaussian rational
-- statement:
--   A complex number $a+bi$ with $a,b\in\mathbb Q$ is written as the binary codes of $a$ and of $b$ (each a sign, a self-delimiting binary numerator and denominator). Other complex numbers get the empty string and are never decoded. Output descriptions use finite-precision numbers (Proposition 3.10: "rotation angles are specified to finite precision").
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.10 and its proof, pp.26–28

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace AgnosticTNS

/-- **A Gaussian rational in binary**, for the classical output descriptions of Proposition 3.10,
p.26 ("rotation angles are specified to finite precision") (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): a complex number `a + bi` with
`a, b ∈ ℚ` is written as the published codes `encRat a ++ encRat b`; any other complex number gets
the empty string (it is never decoded, see `decodeTTN`, `decodeMat`). -/
noncomputable def encC (z : ℂ) : QAlgorithms.Complexity.Str := by
  classical
  exact if h : ∃ q : ℚ × ℚ, z = ⟨q.1, q.2⟩ then
    QAlgorithms.LocalHamiltonian.encRat h.choose.1 ++ QAlgorithms.LocalHamiltonian.encRat h.choose.2
  else []

end AgnosticTNS


