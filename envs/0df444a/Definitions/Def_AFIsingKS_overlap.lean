-- Prove2me | Definitions.Def_AFIsingKS_overlap
-- name    : AFIsingKS_overlap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:13:50.421769+00:00
-- url     : https://prove2.me/theorems/e51585ec-1c38-42bc-ac74-a863b16b664b
-- title:
--   Spins, the overlap $R$ and the balanced set $\Sigma_n(\varepsilon)$
-- statement:
--   Let $\Sigma_n=\{\pm1\}^n$. The **overlap** of $\tau,\sigma\in\Sigma_n$ is $R(\tau,\sigma)=\langle\tau,\sigma\rangle/n$. With $\mathbf 1=(1,\dots,1)$, the balanced configurations and their complement are
--   $$\Sigma_n(\varepsilon)=\{\sigma:|R(\sigma,\mathbf 1)|<\varepsilon\},\qquad \Sigma_n(\varepsilon)^c=\{\sigma:|R(\sigma,\mathbf 1)|\ge\varepsilon\}.$$
--   All truncated partition functions of the mission sum over these sets.
--
--   **Formalization Note** A spin is a Boolean, with `true` for $+1$ and `false` for $-1$. At $n=0$ the overlap is $0/0=0$; every statement takes $n$ large.
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), p.9 and eq. (5), p.11

import Mathlib

open scoped Classical

namespace AFIsingKS

/-- The spin configurations `Σ_n = {±1}^n` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9).

**Formalization Note.** A spin is a `Bool`, with `true` standing for `+1` and `false` for `−1`. -/
abbrev Spin (n : ℕ) : Type := Fin n → Bool

/-- The numerical value of a spin: `true ↦ +1`, `false ↦ −1`. -/
def spinVal (b : Bool) : ℝ := if b then 1 else -1

/-- The overlap `R(τ, σ) = ⟨τ, σ⟩ / n` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 2.2, p.9).

**Formalization Note.** At `n = 0` this is `0 / 0 = 0`; every statement takes `n` large. -/
noncomputable def overlap {n : ℕ} (τ σ : Spin n) : ℝ :=
  (∑ v, spinVal (τ v) * spinVal (σ v)) / (n : ℝ)

/-- The all-plus configuration `𝟏 = (1, …, 1)` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), Section 3.1, p.11). -/
def allOnes (n : ℕ) : Spin n := fun _ => true

/-- The balanced configurations `Σ_n(ε) = {σ : |R(σ, 𝟏)| < ε}` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (5), p.11). -/
noncomputable def balanced (n : ℕ) (ε : ℝ) : Finset (Spin n) :=
  Finset.univ.filter (fun σ => |overlap σ (allOnes n)| < ε)

/-- The complement `Σ_n(ε)^c = {σ : |R(σ, 𝟏)| ≥ ε}` (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), eq. (5), p.11). -/
noncomputable def unbalanced (n : ℕ) (ε : ℝ) : Finset (Spin n) :=
  Finset.univ.filter (fun σ => ε ≤ |overlap σ (allOnes n)|)

end AFIsingKS


