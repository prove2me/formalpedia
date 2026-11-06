-- Prove2me | Definitions.Def_AutoQMem_Lindblad_decodedValue
-- name    : AutoQMem_Lindblad_decodedValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:35.569198+00:00
-- url     : https://prove2.me/theorems/17d545b0-0551-4cb0-b58c-9eae6b41b212
-- title:
--   Decoded logical value $b(x)=\ell\cdot(x\oplus\mathrm{Dec}(Hx))$
-- statement:
--   For a parity-check matrix $H$, a support vector $\ell\in\mathbb F_2^n$ of a bare logical operator and a readout decoder $\mathrm{Dec}$, the **decoded logical value** of a string $x\in\mathbb F_2^n$ is
--   $$b(x)=\ell\cdot\bigl(x\oplus\mathrm{Dec}(Hx)\bigr)\in\mathbb F_2 .$$
--   With $H=H_X$, $\ell=\ell_X$ this is $b_X(x)=\mu_X([x\oplus\mathrm{Dec}_X(H_Xx)]_X)$ for the logical value $\mu_X([c]_X)=\ell_X\cdot c$ of Definition 2.10; with $H=H_Z$, $\ell=\ell_Z$ it is $b_Z$. Evaluated on the sector error process it is the **logical-error indicator**.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.6, eq. (10), p. 15 (PDF p. 17); Definition 2.10, eq. (15), p. 16 (PDF p. 18)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Decoder
open Matrix

namespace AutoQMem.Lindblad

/-- **Decoded logical value `b(x)`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.6, eq. (10), p. 15 (PDF 17), with the
logical-value map of Definition 2.10, eq. (15), p. 16: `b_X(x) := μ_X([x ⊕ Dec_X(H_X x)]_X)` and
`μ_X([c]_X) := ℓ_X · c`, so `b_X(x) = ℓ_X · (x ⊕ Dec_X(H_X x))`.

**Formalization Note.** One definition serves both sectors: `b_X = decodedValue H_X ℓ_X Dec_X` and
`b_Z = decodedValue H_Z ℓ_Z Dec_Z`. The well-definedness of `μ_X` on cosets (Claim 2.11) is not
needed, since `μ_X` enters only through `c ↦ ℓ_X · c`. -/
def decodedValue {m n : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2)) (l : Fin n → ZMod 2)
    (D : Decoder H) (x : Fin n → ZMod 2) : ZMod 2 :=
  l ⬝ᵥ (x + D.dec (H *ᵥ x))

end AutoQMem.Lindblad


