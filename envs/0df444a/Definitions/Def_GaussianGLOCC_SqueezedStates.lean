-- Prove2me | Definitions.Def_GaussianGLOCC_SqueezedStates
-- name    : GaussianGLOCC_SqueezedStates
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:40.327152+00:00
-- url     : https://prove2.me/theorems/c344aec7-6cba-4540-9cd8-57f02c8047b9
-- title:
--   Pure Gaussian states, the TMSS product and squeezing vectors
-- statement:
--   A **pure Gaussian state** of $n$ modes with covariance matrix (CM) $\gamma$ is a density operator $\rho=|u\rangle\langle u|$, $\|u\|=1$, on the full $n$-mode Fock space whose characteristic function $\chi_\rho(\xi)=\operatorname{tr}[\rho W_\xi]$ is $\exp(-\tfrac14\xi^T\gamma\xi+i d^T\xi)$ for some first moments $d$ (eqs. (1)–(2)).
--
--   The product of $n$ pure two-mode squeezed states with squeezing vector $r$ is $\bigotimes_k|\psi_{r_k}\rangle\langle\psi_{r_k}|$ with
--
--   $$
--   |\psi_r\rangle=\cosh^{-1}(r/2)\sum_{j=0}^{\infty}\tanh^{j}(r/2)\,|j\rangle_A|j\rangle_B ,
--   $$
--
--   $A$-mode $k$ paired with $B$-mode $k$ (eq. (28)); for $r\ge 0$ its CM is $\gamma_r$ of eq. (3).
--
--   A CM $\gamma$ of $n\times n$ modes is **characterized by the squeezing vector** $r$ if $r$ is ascending and nonnegative and some local symplectic $S_A\oplus S_B$ brings $\gamma$ to the normal form: $(S_A\oplus S_B)\gamma(S_A\oplus S_B)^T=\gamma_r$. This is the p.4 phrase "characterized by vectors $r$ and $r'$ of ascendingly ordered squeezing parameters".
--
--   **Formalization Note** The paper's $r$ enters the Fock expansion as $r/2$: it is twice the usual squeezing parameter, and the CM of $|\psi_r\rangle$ is $\cosh(r)\mathbb 1$ / $\sinh(r)\Lambda$. `IsPureGaussian` uses the published `Claimed50.P19.GaussianWithCovariance`. The squeezing vector is read at the level of CMs; Lemma 1 (milestone) ties it to the states.
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, §2, eqs. (1)–(3), p.3; Lemma 1 and the paragraph after it, p.4; eq. (28), p.8

import Mathlib
import Definitions.Def_GaussianGLOCC_PhaseSpace
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne)
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P08 (isSymplectic)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, pp.3–4: a *pure Gaussian state* of
`n` modes with covariance matrix (CM) `γ`. `ρ` is a density operator on the full (untruncated)
`n`-mode Fock space whose characteristic function `χ_ρ(ξ) = tr[ρ W_ξ]` is the Gaussian
`exp(−¼ ξᵀγξ + i dᵀξ)` for some first moments `d` (eqs. (1)–(2), p.3), and `ρ = |u⟩⟨u|` for a
unit vector `u`.

**Formalization Note.** `GaussianWithCovariance` is the published predicate of
`QAlgorithms.Papers.Independent.Claimed50.P19` (density, `γ` positive definite with
`γ + iσ ≥ 0`, finite mean energy, Gaussian characteristic function with some mean); for a
Gaussian state the extra positivity and energy clauses hold automatically. The vacuum CM is
`𝟙`. Purity is an actual norm-one vector representative on the full Fock space. -/
def IsPureGaussian {n : ℕ} (ρ : DensityKernel n) (γ : Cov n) : Prop :=
  GaussianWithCovariance ρ γ ∧ ∃ u : Hilbert (FockIndex n), ‖u‖ = 1 ∧ ρ = rankOne u

/-- arXiv:quant-ph/0301038v1, eq. (28), p.8: the Fock coefficients of
`⊗_k |ψ_{r_k}⟩`, `|ψ_r⟩ = cosh⁻¹(r/2) Σ_{j ≥ 0} tanh^j(r/2) |j⟩_A |j⟩_B`, with A-mode `k`
(index `Fin.castAdd n k`) paired with B-mode `k` (index `Fin.natAdd n k`).

**Formalization Note.** The paper's `r` enters as `r/2` in the Fock expansion (28): its CM is
`cosh(r)𝟙` / `sinh(r)Λ` (eq. (3)), i.e. `normalForm r`; `r` is twice the usual squeezing
parameter. The coefficient of a basis vector whose A and B occupations differ in some pair is
`0`. -/
noncomputable def tmssCoeff {n : ℕ} (r : Fin n → ℝ) (i : FockIndex (n + n)) : ℂ :=
  ∏ k : Fin n, if i (Fin.castAdd n k) = i (Fin.natAdd n k) then
    ((Real.tanh (r k / 2) ^ i (Fin.castAdd n k) / Real.cosh (r k / 2) : ℝ) : ℂ) else 0

/-- arXiv:quant-ph/0301038v1, Lemma 1, p.4, and eq. (28), p.8: the density kernel
`|ψ_r⟩⟨ψ_r|` of the product of `n` pure two-mode squeezed states with squeezing vector `r`,
on the full `(n + n)`-mode Fock space (A = first `n` modes, B = last `n`). For `r ≥ 0` it is a
pure Gaussian state with CM `normalForm r` and zero first moments. -/
noncomputable def tmssProduct {n : ℕ} (r : Fin n → ℝ) : DensityKernel (n + n) :=
  fun i j => tmssCoeff r i * star (tmssCoeff r j)

/-- arXiv:quant-ph/0301038v1, p.4: "we can consider them without loss of generality to be of
this normal form, characterized by vectors r and r′ of ascendingly ordered squeezing
parameters". `IsSqueezingVector γ r` says that the `(n + n)`-mode CM `γ` is brought to the
TMSS normal form `normalForm r` (eqs. (3), (22)) by a local symplectic transformation
`S_A ⊕ S_B`, and that `r` is ascending and nonnegative.

**Formalization Note.** Local Gaussian unitaries act on CMs by `γ ↦ SγSᵀ` with
`S = S_A ⊕ S_B` (eq. (5), p.3); `isSymplectic` is the published predicate (`SJSᵀ = J` for
`J = −σ`, the same group as for `σ`). The vector is ascending (`Monotone`), as on p.4; Lemma 1
prints the descending order, and either common order gives the same comparison `r ≥ r′`. The
vector is unique when it exists (it is determined by the symplectic spectrum of the A block). -/
def IsSqueezingVector {n : ℕ} (γ : Cov (n + n)) (r : Fin n → ℝ) : Prop :=
  Monotone r ∧ (∀ k, 0 ≤ r k) ∧ ∃ SA SB : Cov n, isSymplectic SA ∧ isSymplectic SB ∧
    localSymplectic SA SB * γ * (localSymplectic SA SB).transpose = normalForm r

end GaussianGLOCC


