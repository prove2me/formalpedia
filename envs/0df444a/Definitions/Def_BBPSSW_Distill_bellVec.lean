-- Prove2me | Definitions.Def_BBPSSW_Distill_bellVec
-- name    : BBPSSW_Distill_bellVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:36.482471+00:00
-- url     : https://prove2.me/theorems/f942ee99-1631-478f-a8bf-929979adab68
-- title:
--   The Bell states $\Psi^\pm=(\uparrow\downarrow\pm\downarrow\uparrow)/\sqrt2$, $\Phi^\pm=(\uparrow\uparrow\pm\downarrow\downarrow)/\sqrt2$
-- statement:
--   For two spin-$\tfrac12$ particles, the first held by Alice and the second by Bob, the four Bell states are
--
--   $$\Psi^\mp=\frac{|{\uparrow\downarrow}\rangle\mp|{\downarrow\uparrow}\rangle}{\sqrt2},\qquad \Phi^\pm=\frac{|{\uparrow\uparrow}\rangle\pm|{\downarrow\downarrow}\rangle}{\sqrt2}.$$
--
--   $\Psi^-$ is the singlet; $\Psi^+,\Phi^+,\Phi^-$ are the triplets. They form an orthonormal basis of $\mathbb C^2\otimes\mathbb C^2$.
--
--   **Formalization Note** A pair is indexed by $\{0,1\}\times\{0,1\}$ (Alice's spin, Bob's spin), with $0=\uparrow$ and $1=\downarrow$ in the $z$ basis. The vectors are normalized.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, p. 1 (Ψ− = (↑↓ − ↓↑)/√2) and p. 2, after Eq. (4) (Ψ+ = (↑↓ + ↓↑)/√2, Φ± = (↑↑ ± ↓↓)/√2)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_BBPSSW_Distill_BellLabel

open QAlgorithms.Papers.Independent.Information100.P21 (QQ)

namespace BBPSSW.Distill

/-- **The four Bell states.**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, p. 1 ("Ψ− = (↑↓ − ↓↑)/√2") and p. 2, after Eq. (4) ("the three triplet states
Ψ+ = (↑↓ + ↓↑)/√2 and Φ± = (↑↑ ± ↓↓)/√2"):

* `bellVec .psiMinus` = (|↑↓⟩ − |↓↑⟩)/√2, the singlet;
* `bellVec .psiPlus`  = (|↑↓⟩ + |↓↑⟩)/√2;
* `bellVec .phiPlus`  = (|↑↑⟩ + |↓↓⟩)/√2;
* `bellVec .phiMinus` = (|↑↑⟩ − |↓↓⟩)/√2.

**Formalization Note.** A pair of spins is indexed by `QQ = Fin 2 × Fin 2`
(`QAlgorithms.Papers.Independent.Information100.P21.QQ`), the first coordinate being Alice's
spin and the second Bob's, with `0` = ↑ and `1` = ↓ (the z basis). The vectors are
normalized. -/
noncomputable def bellVec : BellLabel → EuclideanSpace ℂ QQ
  | .psiMinus => WithLp.toLp 2 fun p =>
      if p = (0, 1) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
      else if p = (1, 0) then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0
  | .psiPlus => WithLp.toLp 2 fun p =>
      if p = (0, 1) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
      else if p = (1, 0) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0
  | .phiPlus => WithLp.toLp 2 fun p =>
      if p = (0, 0) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
      else if p = (1, 1) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0
  | .phiMinus => WithLp.toLp 2 fun p =>
      if p = (0, 0) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
      else if p = (1, 1) then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0

end BBPSSW.Distill


