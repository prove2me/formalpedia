-- Prove2me | Definitions.Def_ConstDepthUnitary_Supplement_encode
-- name    : ConstDepthUnitary_Supplement_encode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:22:49.000291+00:00
-- url     : https://prove2.me/theorems/15d5a19b-6f5d-48bf-a87e-0fa0897b7867
-- title:
--   The encoding isometry $E:\mathbb C^N\to L^2(\mathbb R^N)$
-- statement:
--   The **encoding isometry** maps $\mathbb C^N$ onto the single-excitation subspace of $L^2(\mathbb R^N)$:
--   $$
--   E=\sum_{x\in[N]}|\psi_x\rangle\langle x| ,\qquad\text{i.e.}\qquad (Ec)(v)=\sum_{x\in[N]}c_x\,\psi_x(v)\quad(c\in\mathbb C^N),
--   $$
--   where $\psi_x$ are the single-excitation states. In particular $E\,|x\rangle=\psi_x$. Since the $\psi_x$ are orthonormal, $E$ is an isometry.
--
--   **Formalization Note** A vector of $\mathbb C^N$ is a function `Fin N → ℂ`, and $Ec$ is a function `EuclideanSpace ℝ (Fin N) → ℂ` (a Schwartz function).
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §4.3, Eq. (26), p.20

import Mathlib
import Definitions.Def_ConstDepthUnitary_Supplement_excState

namespace ConstDepthUnitary

namespace Supplement

/-- The encoding isometry `E = ∑_{x ∈ [N]} |ψ_x⟩⟨x| : ℂ^N → L²(ℝ^N)`, so `E c = ∑ₓ c_x ψ_x`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §4.3, Eq. (26), p.20.

**Formalization Note** A vector of `ℂ^N` is a function `Fin N → ℂ`; the image is a function
`EuclideanSpace ℝ (Fin N) → ℂ` (a Schwartz function). -/
noncomputable def encode {N : ℕ} (c : Fin N → ℂ) (v : EuclideanSpace ℝ (Fin N)) : ℂ :=
  ∑ x, c x * excState x v

end Supplement

end ConstDepthUnitary


