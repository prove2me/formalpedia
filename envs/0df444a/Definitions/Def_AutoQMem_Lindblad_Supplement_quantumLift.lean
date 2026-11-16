-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_quantumLift
-- name    : AutoQMem_Lindblad_Supplement_quantumLift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:41:54.880169+00:00
-- url     : https://prove2.me/theorems/617533cc-0235-4c7d-a8f3-d07fbd4ed9bf
-- title:
--   Quantum lift $\hat a^X_*$, $\hat a^Z_*$ of an SPCA update rule
-- statement:
--   For an X-sector update rule $a:\Sigma_X\to\Omega_X$ (a correction string for each valid X-syndrome), the **quantum lift** of $a$ is the channel
--   $$\hat a^X_*(\rho)=\sum_{s\in\Sigma_X}Z^{a(s)}\,\Pi^X_s\,\rho\,\Pi^X_s\,Z^{a(s)},$$
--   which measures the X-syndrome and applies the correction $Z^{a(s)}$. For $a:\Sigma_Z\to\Omega_Z$ the lift is $\hat a^Z_*(\rho)=\sum_{s\in\Sigma_Z}X^{a(s)}\Pi^Z_s\rho\,\Pi^Z_sX^{a(s)}$.
--
--   The 4D Toom channel of Theorem 3 is $N_*\circ\hat a^Z_*\circ\hat a^X_*$.
--
--   **Formalization Note** The rule is a total function on $\mathbb F_2^{m}$; only its values at valid syndromes enter, since the sum runs over $\Sigma=\operatorname{im}H$.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 5.4, eq. (165), p. 46 (PDF p. 48)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_CSSCode_projX
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

variable {n mX mZ : ℕ}

/-- **Quantum lift of an X-sector SPCA rule.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories
from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), Definition 5.4,
eq. (165), p. 46 (PDF 48): "For a : Σ_X → Ω_X, the quantum lift of a is the CPTP map
â^X_*(ρ) := Σ_{s∈Σ_X} Z^{a(s)} Π^X_s ρ Π^X_s Z^{a(s)}."

**Formalization Note.** `a` is total on `𝔽₂^{m_X}`; only its values on `Σ_X = im H_X` enter (the
sum runs over `C.synX`). -/
noncomputable def liftX (C : CSSCode n mX mZ) (a : (Fin mX → ZMod 2) → (Fin n → ZMod 2))
    (ρ : Op n) : Op n :=
  ∑ s ∈ C.synX, pauliZ (a s) * C.projX s * ρ * C.projX s * pauliZ (a s)

/-- **Quantum lift of a Z-sector SPCA rule** (Definition 5.4, "defined symmetrically, with X^{a(s)}
and Π^Z_s"): `â^Z_*(ρ) := Σ_{s∈Σ_Z} X^{a(s)} Π^Z_s ρ Π^Z_s X^{a(s)}`. -/
noncomputable def liftZ (C : CSSCode n mX mZ) (a : (Fin mZ → ZMod 2) → (Fin n → ZMod 2))
    (ρ : Op n) : Op n :=
  ∑ s ∈ C.synZ, pauliX (a s) * C.projZ s * ρ * C.projZ s * pauliX (a s)

end AutoQMem.Lindblad.Supplement


