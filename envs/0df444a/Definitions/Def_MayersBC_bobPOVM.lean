-- Prove2me | Definitions.Def_MayersBC_bobPOVM
-- name    : MayersBC_bobPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:58:02.881656+00:00
-- url     : https://prove2.me/theorems/0da15a0b-5e8c-4b28-ab2c-6af39d5c35c0
-- title:
--   Bob's random-basis measurement
-- statement:
--   In step 5 of the commitment Bob chooses a basis string $\hat\theta \in \{+,\times\}^n$ uniformly at random and measures each photon in the basis $\hat\theta_i$, obtaining $\hat c \in \{0,1\}^n$. As a single measurement with outcome $(\hat\theta, \hat c)$, it has the POVM elements
--
--   $$
--   E_{\hat\theta, \hat c} = 2^{-n}\, |\hat c\rangle_{\hat\theta}\langle \hat c|_{\hat\theta} .
--   $$
--
--   These elements are positive and sum to the identity, because for each $\hat\theta$ the states $|\hat c\rangle_{\hat\theta}$ form an orthonormal basis.
--
--   **Formalization Note** Outcomes are pairs $(\hat\theta, \hat c)$ of the same type as Alice's openings.
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, p.3 (COMMIT step 5)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_MayersBC_Opening
import Definitions.Def_MayersBC_bb84State
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section b, p.3, step 5 of COMMIT: "Bob measures the `n`
photons in a perfectly random basis `θ̂ ∈ {+, ×}^n` and obtains the classical outcome
`ĉ = ĉ_1 … ĉ_n`". As one measurement with outcome `(θ̂, ĉ)`, its POVM element is
`2^{-n} |ĉ⟩_θ̂⟨ĉ|`.

**Formalization Note.** Outcomes have type `Opening n`; the projector is
`QAlgorithms.pureDensity (bb84State θ̂ ĉ)`. -/
noncomputable def bobPOVM (n : ℕ) :
    Opening n → Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  fun y => (((1 : ℝ) / 2 ^ n : ℝ) : ℂ) • pureDensity (bb84State y.1 y.2)

end MayersBC


