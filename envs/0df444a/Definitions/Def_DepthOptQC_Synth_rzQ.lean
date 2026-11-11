-- Prove2me | Definitions.Def_DepthOptQC_Synth_rzQ
-- name    : DepthOptQC_Synth_rzQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:11:58.967749+00:00
-- url     : https://prove2.me/theorems/3f394156-e2cf-426e-82ef-73e1a1ac26da
-- title:
--   The rotation $R_z(\theta)=\operatorname{diag}(e^{-i\theta/2},e^{i\theta/2})$ on the one-qubit register
-- statement:
--   For $\theta\in\mathbb R$, the single-qubit rotation about the $z$ axis is
--   $$
--   R_z(\theta)=\begin{pmatrix} e^{-i\theta/2} & 0\\ 0 & e^{i\theta/2}\end{pmatrix},
--   $$
--   written in the computational basis $|0\rangle,|1\rangle$. Every single-qubit unitary is, up to a global phase, a product of three such rotations and two Hadamard gates, so synthesizing $R_z(\theta)$ for all $\theta$ is the core of single-qubit synthesis.
--
--   **Formalization Note** The `Bool`-indexed matrix is the published `ShendeQSD.Synthesis.rz` (same matrix, $|0\rangle$ entry $e^{-i\theta/2}$); this definition transports it to the register type `Qubits 1` used by the circuits.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Eq. (17), p.14

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_ShendeQSD_Synthesis_rz

namespace DepthOptQC.Synth

open QAlgorithms

/-- **The rotation `R_z(θ)` on the one-qubit register** (Vasconcelos, *Depth-Optimal Quantum
Compilation*, arXiv:2609.34659, Eq. (17), p.14): `R_z(θ) = diag(e^{−iθ/2}, e^{iθ/2})`, transported
to `Qubits 1` via `Qubits 1 ≃ Bool`, `b ↦ b 0`.

**Formalization Note.** The `Bool`-indexed matrix is the published `ShendeQSD.Synthesis.rz` (same
matrix, same convention: `false` = `|0⟩` carries `e^{−iθ/2}`). -/
noncomputable def rzQ (θ : ℝ) : Matrix (Qubits 1) (Qubits 1) ℂ :=
  (ShendeQSD.Synthesis.rz θ).submatrix (fun b => b 0) (fun b => b 0)

end DepthOptQC.Synth


