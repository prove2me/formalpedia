-- Prove2me | Definitions.Def_AutoQMem_Lindblad_LogicalQubit_Fmin
-- name    : AutoQMem_Lindblad_LogicalQubit_Fmin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:00.025091+00:00
-- url     : https://prove2.me/theorems/75dc67d0-90b4-47cc-a664-abc53aa6de09
-- title:
--   Encoded fidelity $F(\psi;\mathcal W_*)$ and worst-case fidelity $F_{\min}[\mathcal W_*]$
-- statement:
--   For a physical evolution $\mathcal W_*$ and a pure carrier state $|\psi\rangle\in\mathbb C^2$, the **encoded fidelity** is
--   $$F(\psi;\mathcal W_*)=\langle\psi|\,\mathcal E_L[\mathcal W_*](|\psi\rangle\langle\psi|)\,|\psi\rangle,$$
--   and the **worst-case encoded fidelity** is
--   $$F_{\min}[\mathcal W_*]=\min_{\|\psi\|=1}F(\psi;\mathcal W_*).$$
--
--   **Formalization Note** The real part of $\langle\psi|\cdot|\psi\rangle$ is taken. The minimum is an infimum over unit vectors for the Euclidean norm $\sum_i|\psi_i|^2=1$ (not the sup norm); for a CPTP $\mathcal W_*$ it is attained.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.19, eqs. (26)–(27), p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_effective
open Matrix

namespace AutoQMem.Lindblad

namespace LogicalQubit

variable {n' mX mZ : ℕ} {C : CSSCode (n' + 1) mX mZ}

/-- **Encoded fidelity** `F(ψ; W_*) := ⟨ψ| E_L[W_*](|ψ⟩⟨ψ|) |ψ⟩`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.19, eq. (26),
p. 19 (PDF 21).

**Formalization Note.** `|ψ⟩⟨ψ|` is `vecMulVec ψ (star ψ)`; the real part is taken (the value is
real when `E_L[W_*]` preserves Hermiticity, e.g. for a CPTP `W_*`). -/
noncomputable def fidelity (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ)
    (W : Op (n' + 1) → Op (n' + 1)) (ψ : ZMod 2 → ℂ) : ℝ :=
  (star ψ ⬝ᵥ (Q.effective DX DZ W (Matrix.vecMulVec ψ (star ψ))) *ᵥ ψ).re

/-- **Worst-case encoded fidelity** `F_min[W_*] := min_{|ψ⟩ ∈ H_Q} F(ψ; W_*)`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03),
Definition 2.19, eq. (27), p. 19 (PDF 21).

**Formalization Note.** The minimum runs over unit vectors `ψ ∈ ℂ²`, `Σ_i |ψ_i|² = 1` (the
Euclidean norm, not the sup norm of `ZMod 2 → ℂ`), written as an infimum; for a CPTP `W_*` the
fidelity is continuous on this compact set, so the infimum is attained and equals the minimum. -/
noncomputable def Fmin (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ)
    (W : Op (n' + 1) → Op (n' + 1)) : ℝ :=
  ⨅ ψ : {ψ : ZMod 2 → ℂ // ∑ i, ‖ψ i‖ ^ 2 = 1}, Q.fidelity DX DZ W ψ.1

end LogicalQubit

end AutoQMem.Lindblad


