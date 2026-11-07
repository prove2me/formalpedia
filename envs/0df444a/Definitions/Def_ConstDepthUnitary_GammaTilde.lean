-- Prove2me | Definitions.Def_ConstDepthUnitary_GammaTilde
-- name    : ConstDepthUnitary_GammaTilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:06.484321+00:00
-- url     : https://prove2.me/theorems/ed7a3ca3-3fdb-4f69-bbbf-cef2376268ba
-- title:
--   The ideal isometry $\tilde\Gamma_S$
-- statement:
--   The ideal half-algorithm has three parts. First $(-iS)^{1/2}=\frac1{\sqrt2}(S-iI)$. Second, the encoding $\tilde E=\sum_x|\tilde\psi_x\rangle\langle x|$ with a wider Gaussian, where $\tilde Z_b=\sum_a\alpha(a)^{2b}e^{-\alpha(a)^2/2}$, $|\tilde h_b\rangle=\tilde Z_b^{-1/2}\sum_a\alpha(a)^be^{-\alpha(a)^2/4}|a\rangle$, and $|\tilde\psi_x\rangle$ has $|\tilde h_1\rangle$ in register $x$ and $|\tilde h_0\rangle$ elsewhere. Third, $\hat Q_S^{-1/2}=\sum_v e^{-\frac14 i\alpha(v)^{\mathsf T}S\alpha(v)}|v\rangle\langle v|$. Then
--   $$\tilde\Gamma_S=\hat Q_S^{-1/2}\,\tilde E\,(-iS)^{1/2}.$$
--   It is a mathematical comparison object, not a part of the algorithm.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.2.2, p.26

import Mathlib
import Definitions.Def_ConstDepthUnitary_alpha
import Definitions.Def_ConstDepthUnitary_QHat

namespace ConstDepthUnitary

/-- The square root `(−i S)^{1/2} = (S − i I)/√2`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §5.2.2, step 1, p.26. -/
noncomputable def rootMinusIS {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (S.map Complex.ofReal - Complex.I • (1 : Matrix (Fin N) (Fin N) ℂ))

/-- The normalization `Z̃_b = Σ_a α(a)^{2b} e^{−α(a)²/2}` (§5.2.2, step 2, p.26). -/
noncomputable def ZTilde (K b : ℕ) : ℝ :=
  ∑ a : Fin K, alpha K ((a : ℕ) : ℤ) ^ (2 * b) * Real.exp (-(alpha K ((a : ℕ) : ℤ)) ^ 2 / 2)

/-- The amplitude at `a` of `|h̃_b⟩ = Z̃_b^{−1/2} Σ_a α(a)^b e^{−α(a)²/4} |a⟩` (§5.2.2, step 2, p.26). -/
noncomputable def hTilde (K b : ℕ) (a : Fin K) : ℝ :=
  alpha K ((a : ℕ) : ℤ) ^ b * Real.exp (-(alpha K ((a : ℕ) : ℤ)) ^ 2 / 4) / Real.sqrt (ZTilde K b)

/-- The modified encoding isometry `Ẽ = Σ_x |ψ̃_x⟩⟨x|`, with `|ψ̃_x⟩ = |h̃₀⟩ ⊗ ⋯ ⊗ |h̃₁⟩_{V_x} ⊗ ⋯ ⊗ |h̃₀⟩`
(§5.2.2, step 2, p.26). -/
noncomputable def ETilde (N K : ℕ) : Matrix (Fin N → Fin K) (Fin N) ℂ :=
  Matrix.of fun v x => ((∏ z : Fin N, hTilde K (if z = x then 1 else 0) (v z) : ℝ) : ℂ)

/-- The inverse square root `Q̂_S^{−1/2} = Σ_v e^{−¼ i α(v)ᵀSα(v)} |v⟩⟨v|` (§5.2.2, step 3, p.26). -/
noncomputable def QHatInvSqrt {N : ℕ} (K : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N → Fin K) (Fin N → Fin K) ℂ :=
  Matrix.diagonal fun v => Complex.exp (-(1 / 4 : ℂ) * Complex.I * (quadForm K S v : ℂ))

/-- The ideal isometry `Γ̃_S = Q̂_S^{−1/2} Ẽ (−i S)^{1/2}` (§5.2.2, p.26). -/
noncomputable def GammaTilde {N : ℕ} (K : ℕ) (S : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N → Fin K) (Fin N) ℂ :=
  QHatInvSqrt K S * ETilde N K * rootMinusIS S

end ConstDepthUnitary


