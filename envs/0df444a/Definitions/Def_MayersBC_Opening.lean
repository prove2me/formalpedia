-- Prove2me | Definitions.Def_MayersBC_Opening
-- name    : MayersBC_Opening
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:40.234441+00:00
-- url     : https://prove2.me/theorems/66034598-340f-4ede-8e3b-d2c589f5642c
-- title:
--   Openings $(\theta, c) \in \{+,\times\}^n \times \{0,1\}^n$
-- statement:
--   In the BCJL commitment protocol on $n$ photons, Alice's secret choice is a pair $(\theta, c)$: a string of bases $\theta = \theta_1\dots\theta_n \in \{+, \times\}^n$ (rectilinear or diagonal for each photon) and a bit string $c = c_1\dots c_n \in \{0,1\}^n$. When she opens her commitment she announces $(\theta, c)$. Bob's measurement outcome $(\hat\theta, \hat c)$, a random basis string and the bits he observed, has the same shape.
--
--   This type is the index set of Alice's mixture, of her cheating measurement, and of Bob's measurement outcomes.
--
--   **Formalization Note** A basis is a Boolean: `false` is the rectilinear basis $+$ and `true` the diagonal basis $\times$. Bits are elements of $\mathbb Z/2$.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, pp.3–5 (COMMIT steps 3–5)

import Mathlib

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section b, pp.3–5: a pair `(θ, c)` with
`θ ∈ {+, ×}^n` (Alice's bases, step 3 of COMMIT) and `c ∈ {0, 1}^n` (her string); the same type
carries Bob's outcome `(θ̂, ĉ)` (step 5).

**Formalization Note.** A basis is a `Bool`: `false` is the rectilinear basis `+`, `true` the
diagonal basis `×`. Bits are `ZMod 2`. -/
abbrev Opening (n : ℕ) : Type := (Fin n → Bool) × (Fin n → ZMod 2)

end MayersBC


