-- Prove2me | Definitions.Def_GL2QFT_AGamma
-- name    : GL2QFT_AGamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:38.333439+00:00
-- url     : https://prove2.me/theorems/c0c48082-47b5-486c-8f48-f4dc2f99d646
-- title:
--   The $q\times q$ block $A_\gamma=A_{\rho_\gamma,\rho_\gamma}$ of the A-matrix, eqs. (144)–(145)
-- statement:
--   The hard block of the A-matrix in the Mackey circuit for $B<\mathrm{GL}_2(\mathbb F_q)$. Its columns are the inputs $|c_\infty\rangle=|\rho_\gamma,e\rangle$ and $|c_\alpha\rangle=|\chi_{\alpha,\alpha^{-1}\gamma},w\rangle$, $\alpha\in X_q$ (143). Its rows are the irreps of $\mathrm{GL}_2(\mathbb F_q)$ in $\mathcal C_\gamma$ (cuspidal $\pi_\theta$ with $\theta|_{\mathbb F_q^*}=\chi_\gamma$), $\mathcal P_\gamma$ (principal series $I_{\delta,\eta}$, $\delta\eta=\gamma$, $\delta\neq\eta$) and $\mathcal S_\gamma$ (Steinberg $\mathrm{St}_\delta$, $\delta^2=\gamma$), (140)–(142). With $b=\alpha^{-1}\gamma$:
--   $$A_\gamma|c_\infty\rangle=\frac{1}{\sqrt{q+1}}\sum_{\mathcal C_\gamma}|\pi_\theta\rangle+\frac{1}{\sqrt{q-1}}\sum_{\mathcal P_\gamma}|I_{\delta,\eta}\rangle+\sqrt{\frac{q}{(q-1)(q+1)}}\sum_{\mathcal S_\gamma}|\mathrm{St}_\delta\rangle,$$
--   $$A_\gamma|c_\alpha\rangle=-\frac{\chi_b(-1)}{\sqrt{q(q^2-1)}}\sum_{\mathcal C_\gamma}g_{q^2}(\theta\cdot(\chi_{\alpha^{-1}}\circ N))|\pi_\theta\rangle+\frac{\chi_b(-1)}{(q-1)\sqrt q}\sum_{\mathcal P_\gamma}g_q(\alpha^{-1}\delta)g_q(\alpha^{-1}\eta)|I_{\delta,\eta}\rangle+\frac{\chi_b(-1)}{(q-1)\sqrt{q+1}}\sum_{\mathcal S_\gamma}g_q(\alpha^{-1}\delta)^2|\mathrm{St}_\delta\rangle.$$
--
--   This is the only block of the A-matrix whose size grows with $q$, and Theorem 6.34 implements it.
--
--   **Formalization Note** The block is defined by the displayed formulas (144)–(145), which the paper derives from (70). Its columns were checked to be orthonormal for every $\gamma$ at $q=2,3,5,7$. An unordered pair $\{\delta,\eta\}$ is represented by its $\prec$-ordered label and an orbit $\{\theta,\theta^q\}$ by its cuspidal label; the first sum of (145) does not depend on the representative (p.46). Rows outside $\mathcal C_\gamma\cup\mathcal P_\gamma\cup\mathcal S_\gamma$ are zero.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), §6.4.4 eqs. (140)–(145), p.46 (PDF p.47); Remark 6.15 p.48

import Definitions.Def_GL2QFT_Irreps

noncomputable section

open Classical

namespace GL2QFT

namespace FieldData

variable (D : FieldData)

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), §6.4.4, eqs. (140)–(145), p.46 (PDF p.47):
the `q × q` block `A_γ = A_{ρ_γ,ρ_γ}` of the A-matrix of the Mackey circuit for `B < GL₂(F_q)`.
Its columns are the input states (143) `|c_∞⟩ = |ρ_γ, e⟩` and `|c_α⟩ = |χ_{α,α⁻¹γ}, w⟩`,
`α ∈ X_q` (identified with the register `|0⟩` and `|α⟩`); its rows are irrep labels of `GL₂(F_q)`,
supported on `C_γ` (cuspidal `π_θ`, `θ|_{F*_q} = χ_γ`, (140)), `P_γ` (principal series `I_{δ,η}`,
`δη = γ`, `δ ≠ η`, (141)) and `S_γ` (Steinberg `St_δ`, `δ² = γ`, (142)):
* (144) `A_γ|c_∞⟩ = (q+1)^{−1/2} Σ_{C_γ} |π_θ⟩ + (q−1)^{−1/2} Σ_{P_γ} |I_{δ,η}⟩
  + √(q/((q−1)(q+1))) Σ_{S_γ} |St_δ⟩`;
* (145) with `b = α⁻¹γ`: `A_γ|c_α⟩ = −χ_b(−1)/√(q(q²−1)) Σ_{C_γ} g_{q²}(θ · (χ_{α⁻¹} ∘ N)) |π_θ⟩
  + χ_b(−1)/((q−1)√q) Σ_{P_γ} g_q(α⁻¹δ) g_q(α⁻¹η) |I_{δ,η}⟩
  + χ_b(−1)/((q−1)√(q+1)) Σ_{S_γ} g_q(α⁻¹δ)² |St_δ⟩`.

**Formalization Note** The block is defined by the displayed formulas (144)–(145), which the paper
derives from (70). Labels are exponents: `b = γ − α`, `α⁻¹δ = δ − α`, `δη = γ` is `δ + η = γ`,
`δ² = γ` is `2δ = γ`. An unordered pair `{δ, η}` is the label `ps (δ, η)` with `δ ≺ η`; an orbit
`{θ, θ^q}` is its cuspidal label `k` (the first sum does not depend on the representative, p.46).
Column `none` is `|c_∞⟩`, column `some α` is `|c_α⟩`. The rows `det δ` are zero. The columns are
orthonormal (checked numerically for `q = 2, 3, 5, 7`, `numerics/lean_defs_check.py`). -/
def AGamma (γ : D.Lab) : Matrix D.Irr (Option D.Lab) ℂ := fun μ c =>
  match c, μ with
  | none, .inl _ => 0
  | none, .inr (.inl δ) =>
      if 2 * δ = γ then ((Real.sqrt ((D.q : ℝ) / (((D.q : ℝ) - 1) * ((D.q : ℝ) + 1))) : ℝ) : ℂ) else 0
  | none, .inr (.inr (.inl ab)) => if ab.1.1 + ab.1.2 = γ then isqrt (D.q - 1) else 0
  | none, .inr (.inr (.inr k)) => if D.restrLab k.1 = γ then isqrt (D.q + 1) else 0
  | some _, .inl _ => 0
  | some α, .inr (.inl δ) =>
      if 2 * δ = γ then
        D.chi (γ - α) (-1) * (((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1)) * D.gauss (δ - α) ^ 2
      else 0
  | some α, .inr (.inr (.inl ab)) =>
      if ab.1.1 + ab.1.2 = γ then
        D.chi (γ - α) (-1) * (((D.q : ℂ) - 1)⁻¹ * isqrt D.q) *
          D.gauss (ab.1.1 - α) * D.gauss (ab.1.2 - α)
      else 0
  | some α, .inr (.inr (.inr k)) =>
      if D.restrLab k.1 = γ then
        -(D.chi (γ - α) (-1) * isqrt ((D.q : ℝ) * ((D.q : ℝ) ^ 2 - 1))) *
          D.gaussQ2 (fun z => D.theta k.1 z * D.chi (-α) (D.nrm z))
      else 0

end FieldData

end GL2QFT


