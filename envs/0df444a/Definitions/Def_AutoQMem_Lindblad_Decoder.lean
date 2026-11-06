-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Decoder
-- name    : AutoQMem_Lindblad_Decoder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:51.578066+00:00
-- url     : https://prove2.me/theorems/3dae1206-e116-440f-b5dd-b2de4e77bfd8
-- title:
--   Readout decoder $\mathrm{Dec}$
-- statement:
--   An **X-readout decoder** is a map $\mathrm{Dec}_X:\Sigma_X\to\mathbb F_2^n$ with
--   $$H_X\,\mathrm{Dec}_X(s)=s\quad\text{for all }s\in\Sigma_X,\qquad \mathrm{Dec}_X(0)=0 .$$
--   A Z-readout decoder is the same notion for $H_Z$. No linearity and no locality are assumed. The decoded string of $x$ is $x\oplus\mathrm{Dec}_X(H_Xx)$, which is a codeword.
--
--   **Formalization Note** The decoder is a total function on $\mathbb F_2^{m}$; its values off $\Sigma=\operatorname{im}H$ are never used.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.5, eq. (9), p. 15 (PDF p. 17)

import Mathlib
open Matrix

namespace AutoQMem.Lindblad

/-- **Readout decoder.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.5, eq. (9), p. 15 (PDF 17): "An X-readout decoder is a
map Dec_X : Σ_X → Ω_X, H_X Dec_X(s) = s for all s ∈ Σ_X, Dec_X(0) = 0." "No linearity of Dec_X is
assumed." A Z-readout decoder is a `Decoder H_Z`.

**Formalization Note.** `dec` is a total function on `𝔽₂^m`; its values off `Σ = im H` are never
used by any definition of the mission (every sum is over `Σ` and every argument is a syndrome
`H x`). No linearity and no locality are assumed. -/
structure Decoder {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) : Type where
  /-- The decoder map `Dec : Σ → 𝔽₂ⁿ`. -/
  dec : (Fin m → ZMod 2) → (Fin n → ZMod 2)
  /-- `H Dec(s) = s` for every valid syndrome `s ∈ im H`. -/
  spec : ∀ s ∈ Set.range H.mulVec, H.mulVec (dec s) = s
  /-- `Dec(0) = 0`. -/
  zero : dec 0 = 0

end AutoQMem.Lindblad


