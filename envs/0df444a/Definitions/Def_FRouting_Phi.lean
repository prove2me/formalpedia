-- Prove2me | Definitions.Def_FRouting_Phi
-- name    : FRouting_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:51.345347+00:00
-- url     : https://prove2.me/theorems/4b46f38c-e5af-483b-9fb3-1bb20b3c8a8f
-- title:
--   The EPR projector $\Phi$
-- statement:
--   For a dimension $d$, let
--   $$|\Phi\rangle=\frac1{\sqrt d}\sum_{i}|i\rangle|i\rangle$$
--   on two qudits, and let $\Phi=|\Phi\rangle\langle\Phi|$. The verifiers hold $\Phi$ on the reference $\bar Q$ and the challenge $Q$.
--
--   **Formalization Note** The reference is always the first factor. `phiVec` is the vector and `Phi` the projector.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), §3.1, p.14; §3.4, p.16

import Mathlib

set_option autoImplicit false

open Matrix

namespace FRouting

/-- The vector `|Φ⟩ = d^{-1/2} ∑ᵢ |i⟩|i⟩` on `Fin d × Fin d`. Renard, *Computational Bounds for
f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), §3.1 and §3.4, pp.14–16: the
`d`-dimensional EPR pair. -/
noncomputable def phiVec (d : ℕ) : Fin d × Fin d → ℂ :=
  fun p => if p.1 = p.2 then ((Real.sqrt d : ℝ) : ℂ)⁻¹ else 0

/-- **The EPR projector** `Φ = |Φ⟩⟨Φ|` on the reference and the challenge, written first the
reference `Q̄`, then the challenge. Renard, arXiv:2609.40278 (held copy, sha256 4a327f29…), §3.4,
p.16. -/
noncomputable def Phi (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.vecMulVec (phiVec d) (star (phiVec d))

end FRouting


