-- Prove2me | Definitions.Def_MayersBC_bb84Amp
-- name    : MayersBC_bb84Amp
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:43.653846+00:00
-- url     : https://prove2.me/theorems/c3b8e43c-7c9f-462e-9f9d-e1c795578405
-- title:
--   One-photon BB84 amplitudes $\langle x \mid c\rangle_t$
-- statement:
--   A photon carrying the bit $c \in \{0,1\}$ in the basis $t \in \{+,\times\}$ is in the state $|c\rangle_t$, where
--
--   $$
--   |c\rangle_+ = |c\rangle, \qquad |0\rangle_\times = \tfrac{1}{\sqrt2}\big(|0\rangle + |1\rangle\big), \qquad |1\rangle_\times = \tfrac{1}{\sqrt2}\big(|0\rangle - |1\rangle\big).
--   $$
--
--   This definition gives the amplitude of $|c\rangle_t$ at the computational basis vector $|x\rangle$: it is $\delta_{xc}$ in the rectilinear basis and $(-1)^{cx}/\sqrt2$ in the diagonal basis. These are the four BB84 states used in step 4 of the BCJL commitment.
--
--   **Formalization Note** `t = false` is the rectilinear basis; the sign exponent is the product $cx$ computed in $\mathbb Z/2$ and read as $0$ or $1$.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, p.3 (COMMIT step 4)

import Mathlib

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section b, p.3, step 4 of COMMIT: the amplitude
`⟨x | c⟩_t` of the one-photon state `|c⟩_t` (bit `c` encoded in basis `t`) at the computational
basis vector `|x⟩`. Rectilinear: `|c⟩_+ = |c⟩`. Diagonal: `|0⟩_× = (|0⟩ + |1⟩)/√2` and
`|1⟩_× = (|0⟩ − |1⟩)/√2`, so `⟨x|c⟩_× = (−1)^{c x}/√2`.

**Formalization Note.** `t = false` is `+`, `t = true` is `×`; bits are `ZMod 2` and the sign
exponent is `(c x).val ∈ {0, 1}`. -/
noncomputable def bb84Amp (t : Bool) (c x : ZMod 2) : ℂ :=
  if t then (-1 : ℂ) ^ (c * x).val / ((Real.sqrt 2 : ℝ) : ℂ) else if x = c then 1 else 0

end MayersBC


