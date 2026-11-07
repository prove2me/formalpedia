-- Prove2me | Definitions.Def_ConstDepthUnitary_EHat
-- name    : ConstDepthUnitary_EHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:06.634265+00:00
-- url     : https://prove2.me/theorems/c78c32ae-c8bb-47b1-8abf-461f4f7598cd
-- title:
--   The encoding isometry $\hat E$
-- statement:
--   For $b\in\{0,1\}$ let $Z_b=\sum_{a\in[K]}\alpha(a)^{2b}e^{-\alpha(a)^2}$ and
--   $$|\hat h_b\rangle=\frac1{\sqrt{Z_b}}\sum_{a\in[K]}\alpha(a)^b e^{-\alpha(a)^2/2}|a\rangle.$$
--   The encoded basis state $|\hat\psi_x\rangle$, $x\in[N]$, is the tensor product of $N$ registers with $|\hat h_1\rangle$ in register $x$ and $|\hat h_0\rangle$ in the others (Eq. (50)), and
--   $$\hat E=\sum_{x\in[N]}|\hat\psi_x\rangle\langle x|$$
--   is the encoding, a discretized single-excitation state of $N$ oscillators.
--
--   **Formalization Note** $\alpha^0=1$ also where $\alpha=0$. For even $K>0$, $\alpha$ never vanishes, so $Z_1>0$.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.1.2, Eq. (50), p.23; §6.1, p.37

import Mathlib
import Definitions.Def_ConstDepthUnitary_alpha

namespace ConstDepthUnitary

/-- The normalization `Z_b = Σ_a α(a)^{2b} e^{−α(a)²}`, for `b = 0, 1`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.1.2, p.23; §6.1, p.37. -/
noncomputable def Z (K b : ℕ) : ℝ :=
  ∑ a : Fin K, alpha K ((a : ℕ) : ℤ) ^ (2 * b) * Real.exp (-(alpha K ((a : ℕ) : ℤ)) ^ 2)

/-- The amplitude at `a` of `|ĥ_b⟩ = Z_b^{−1/2} Σ_a α(a)^b e^{−α(a)²/2} |a⟩`, for `b = 0, 1` (§5.1.2, p.23;
§6.1, p.37). -/
noncomputable def hHat (K b : ℕ) (a : Fin K) : ℝ :=
  alpha K ((a : ℕ) : ℤ) ^ b * Real.exp (-(alpha K ((a : ℕ) : ℤ)) ^ 2 / 2) / Real.sqrt (Z K b)

/-- The amplitude at `v` of `|ψ̂_x⟩ = |ĥ₀⟩ ⊗ ⋯ ⊗ |ĥ₁⟩_{V_x} ⊗ ⋯ ⊗ |ĥ₀⟩`, Eq. (50), p.23. -/
noncomputable def psiHat {N : ℕ} (K : ℕ) (x : Fin N) (v : Fin N → Fin K) : ℝ :=
  ∏ z : Fin N, hHat K (if z = x then 1 else 0) (v z)

/-- The encoding isometry `Ê = Σ_x |ψ̂_x⟩⟨x|` (§5.1.2, p.23). -/
noncomputable def EHat (N K : ℕ) : Matrix (Fin N → Fin K) (Fin N) ℂ :=
  Matrix.of fun v x => ((psiHat K x v : ℝ) : ℂ)

end ConstDepthUnitary


