-- Prove2me | Definitions.Def_AgnosticTNS_expVal
-- name    : AgnosticTNS_expVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:09.437357+00:00
-- url     : https://prove2.me/theorems/e0e7d7d1-91a8-4a3f-adfb-e272f450ef04
-- title:
--   Overlap $\langle\phi|\rho|\phi\rangle$
-- statement:
--   For an operator $\rho$ and a vector $|\phi\rangle$ on a finite-dimensional space with a fixed basis, the overlap
--   $$
--   \langle\phi|\rho|\phi\rangle=\sum_{x,y}\overline{\phi(x)}\,\rho_{xy}\,\phi(y).
--   $$
--
--   **Formalization Note** The real part is taken; for Hermitian $\rho$ (every use) the overlap is real.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Eqs. (3.1)–(3.2), p.15

import Mathlib
open Matrix

namespace AgnosticTNS

/-- **The overlap `⟨φ|ρ|φ⟩`**, Eqs. (3.1)–(3.2), p.15 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): the real number
`⟨φ|ρ|φ⟩ = Σ_{x,y} \overline{φ(x)} ρ_{xy} φ(y)` for a vector `φ` and an operator `ρ` on a finite
basis `ι`.

**Formalization Note** The real part is taken; for Hermitian `ρ` (every use) the number is real. -/
def expVal {ι : Type*} [Fintype ι] (ρ : Matrix ι ι ℂ) (φ : ι → ℂ) : ℝ :=
  (star φ ⬝ᵥ (ρ *ᵥ φ)).re

end AgnosticTNS


