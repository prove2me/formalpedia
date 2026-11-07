-- Prove2me | Definitions.Def_MatrixSpencer_tiltExp
-- name    : MatrixSpencer_tiltExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:21.908932+00:00
-- url     : https://prove2.me/theorems/68c580f7-1681-4ea1-9e4b-5ac1facf7c70
-- title:
--   The expectation $\mathbb E_{\mu_t}$ under the tilted measure
-- statement:
--   The expectation of $f$ under the probability measure $d\mu_t\propto e^{-V(B_t)}d\gamma_n$:
--   $$\mathbb E_{\mu_t}f=\frac1{Z_t}\int f\,e^{-V(B_t)}\,d\gamma_n .$$
--
--   **Formalization Note** Statements using it also state that $Z_t>0$ and that the integrand is integrable.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Theorem 2.5, Step 2, p.9

import Mathlib
import Definitions.Def_MatrixSpencer_partition
open RBMSensitivity (E)

namespace MatrixSpencer

/-- **The expectation `E_{µ_t} f`, where `dµ_t ∝ e^{−V(B_t)} dγₙ`.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Step 2 of the proof of Theorem 2.5, p.9 ("F′(t) = −E_{µ_t} Tr(v′(B_t)Y)"), and p.3.

**Formalization Note.** `E_{µ_t} f = (∫ f e^{−V(B_t)} dγₙ) / Z_t`. Statements using it also state that
`f e^{−V(B_t)}` is integrable and that `Z_t > 0`, so neither Lean's junk integral nor the junk `x/0`
is read. -/
noncomputable def tiltExp {n d : ℕ} (α β : ℝ) (p : ℕ) (M : Fin n → Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (f : E n → ℝ) : ℝ :=
  (∫ g, f g * weight α β p (interp M t g) ∂(gam n)) / partition α β p M t

end MatrixSpencer


