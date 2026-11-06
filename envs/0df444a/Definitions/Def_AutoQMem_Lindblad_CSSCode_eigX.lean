-- Prove2me | Definitions.Def_AutoQMem_Lindblad_CSSCode_eigX
-- name    : AutoQMem_Lindblad_CSSCode_eigX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:27.122739+00:00
-- url     : https://prove2.me/theorems/1dbeefca-3e1b-440a-9a13-3d8accc757ac
-- title:
--   Syndrome eigenvalue functions $A(s)$
-- statement:
--   An operator $A\in\mathcal A_X$ acts as a scalar on every X-syndrome sector: for $s\in\Sigma_X$,
--   $$A\,\Pi^X_s=A(s)\,\Pi^X_s .$$
--   The scalar $A(s)$ is the **syndrome eigenvalue function** of $A$. It is computed here as
--   $$A(s)=\frac{\operatorname{Tr}(A\,\Pi^X_s)}{\operatorname{Tr}(\Pi^X_s)},$$
--   and analogously for $A\in\mathcal A_Z$ with $\Pi^Z_s$.
--
--   These functions give the transition rates of the induced sector processes and the classical representation maps $\Phi_X,\Phi_Z$.
--
--   **Formalization Note** The trace formula is defined for every matrix $A$ and every $s$; it equals the paper's $A(s)$ when $A\in\mathcal A_X$ and $s\in\Sigma_X$ (then $\Pi^X_s\neq0$), the only case in which it is used.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.3, eq. (6), p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_CSSCode_projX
open Matrix

namespace AutoQMem.Lindblad

namespace CSSCode

variable {n mX mZ : ℕ}

/-- **Syndrome eigenvalue function `A(s)` on the X sector.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.3, eq. (6), p. 14
(PDF 16): "for A_X ∈ A_X and s ∈ Σ_X, we can write A_X Π^X_s ≡ A_X(s) Π^X_s … with A_X(s) being the
scalar eigenvalue of A_X acting on the X-syndrome projector."

**Formalization Note.** `eigX A s := Tr(A Π^X_s) / Tr(Π^X_s)`. This is defined for every matrix
`A` and every `s`; it equals the paper's `A(s)` whenever `A ∈ A_X` and `s ∈ Σ_X` (then
`Π^X_s ≠ 0` and `A Π^X_s = A(s) Π^X_s`), which is the only case in which it is used. -/
noncomputable def eigX (C : CSSCode n mX mZ) (A : Op n) (s : Fin mX → ZMod 2) : ℂ :=
  (A * C.projX s).trace / (C.projX s).trace

/-- **Syndrome eigenvalue function on the Z sector** `A(s) = Tr(A Π^Z_s)/Tr(Π^Z_s)` for
`A ∈ A_Z`, `s ∈ Σ_Z` (Definition 2.3, "The Z version A_Z(s) for s ∈ Σ_Z is defined
accordingly"). -/
noncomputable def eigZ (C : CSSCode n mX mZ) (A : Op n) (s : Fin mZ → ZMod 2) : ℂ :=
  (A * C.projZ s).trace / (C.projZ s).trace

end CSSCode

end AutoQMem.Lindblad


