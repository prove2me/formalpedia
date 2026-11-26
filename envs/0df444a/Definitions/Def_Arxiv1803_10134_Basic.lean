-- Prove2me | Definitions.Def_Arxiv1803_10134_Basic
-- name    : Arxiv1803_10134_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-26T13:08:14.015189+00:00
-- url     : https://prove2.me/theorems/ebde712c-c223-5005-844c-c0e2f0550f07
-- title:
--   Elastic Green's tensor, resonant point scatterers and quasi-modes
-- statement:
--   Objects of Section III A and Section III D of Skipetrov and Beltukov (2018).
--
--   1. **Medium.** A homogeneous isotropic elastic medium fills $\mathbb{R}^3$. Its mass density is $\rho_0>0$, and compressive and shear waves travel with speeds $c_p=[(\lambda_0+2\mu_0)/\rho_0]^{1/2}>0$ and $c_s=(\mu_0/\rho_0)^{1/2}>0$. At frequency $\omega$ the wave numbers are $k_{p,s}=\omega/c_{p,s}$.
--   2. **Green's tensor (eq. 8).** With $\hat F(\mathbf v)=\big[\mathbb 1-3\,\mathbf v\otimes\mathbf v/v^2\big]\big(1+3i/v-3/v^2\big)$, $v=|\mathbf v|$, and $\Delta\mathbf r=\mathbf r-\mathbf r'\neq0$,
--   $$\hat{\mathcal G}(\mathbf r,\mathbf r',\omega)=\frac{\omega}{12\pi\rho_0c_p^3}\Big\{\underbrace{\frac{e^{ik_p\Delta r}}{k_p\Delta r}\big[\mathbb 1-\hat F(k_p\Delta\mathbf r)\big]}_{\text{compressive part}}+2\Big(\frac{c_p}{c_s}\Big)^3\underbrace{\frac{e^{ik_s\Delta r}}{k_s\Delta r}\big[\mathbb 1+\tfrac12\hat F(k_s\Delta\mathbf r)\big]}_{\text{shear part}}\Big\}.$$
--   3. **Polarizability (eq. 10).** For a scatterer with resonance frequency $\omega_0$ and width $\Gamma_0>0$ and a real prefactor $b$, $\alpha(\omega)=b\,(-\Gamma_0/2)/(\omega-\omega_0+i\Gamma_0/2)$. The paper's prefactor is $B(\omega)=12\pi\rho_0c_p^3/\big(\omega[1+2(c_p/c_s)^3]\big)$, and $\alpha_0=\alpha$ with $b=B(\omega)$.
--   4. **Foldy–Lax equations (eq. 9).** Scatterers sit at positions $\mathbf r_1,\dots,\mathbf r_N$. Displacements $u_m^\alpha$ in an incident field $v_m^\alpha$ satisfy $u_m^\alpha=v_m^\alpha+\alpha_0(\omega)\sum_{n\neq m,\beta}\mathcal G^{\alpha\beta}(\mathbf r_m,\mathbf r_n,\omega)u_n^\beta$. Vectors $|u\rangle\in\mathbb C^{3N}$ are indexed by pairs (scatterer $m$, direction $\alpha$).
--   5. **Green's matrix (eq. 12).** $\hat G(\omega)$ is the $3N\times3N$ matrix with $3\times3$ blocks $\hat G_{mn}=i\delta_{mn}\mathbb 1+(1-\delta_{mn})B\,\hat{\mathcal G}(\mathbf r_m,\mathbf r_n,\omega)$.
--   6. **Biorthogonal eigensystem (eqs. 13–15).** $3N$ complex numbers $\Lambda_n$, column vectors $|R_n\rangle$ and row vectors $\langle L_n|$ with $\hat G(\omega_0)|R_n\rangle=\Lambda_n|R_n\rangle$, $\langle L_n|\hat G(\omega_0)=\Lambda_n\langle L_n|$, $\langle L_m|R_n\rangle=\delta_{mn}$.
--   7. **Quasi-modes (eq. 17).** $\omega_n=\omega_0-(\Gamma_0/2)\operatorname{Re}\Lambda_n$ and $\Gamma_n=\Gamma_0\operatorname{Im}\Lambda_n$.
--   8. **Near-field tensor (eq. 21).** $\dfrac{1}{8\pi\rho_0c_s^2\Delta r}\Big\{\big[1+(c_s/c_p)^2\big]\mathbb 1+\big[1-(c_s/c_p)^2\big]\dfrac{\Delta\mathbf r\otimes\Delta\mathbf r}{\Delta r^2}\Big\}$.
--
--   **Formalization Note** The medium is described by $\rho_0,c_p,c_s$. Every positive pair $(c_p,c_s)$ arises from Lamé parameters with $\mu_0>0$ and $\lambda_0+2\mu_0>0$. This also admits non-physical media (e.g. $c_p\le c_s$), where the statements remain true. The printed prefactor "$B=12\pi\rho_0c_p^3/\omega[1+2(c_p/c_s)^3]$" is read with the bracket in the denominator, the only reading compatible with the second line of eq. (12). The pairing $\langle L|R\rangle$ is the row-times-column product, without complex conjugation. At $\Delta\mathbf r=0$ the formulas divide by zero; they are only used at nonzero separations, or under limits that exclude $0$.
-- source:
--   Skipetrov and Beltukov, Anderson transition for elastic waves in three dimensions, arXiv:1803.10134v3 (2018), Section III A (eqs. (8)-(17), PDF pp. 4-5) and Section III D (eq. (21), PDF p. 8)

import Mathlib

/-!
Skipetrov and Beltukov, *Anderson transition for elastic waves in three dimensions*,
arXiv:1803.10134v3 (2018), Section III A: the elastic Green's tensor of a homogeneous isotropic
medium (eq. (8)), the polarizability of a resonant point scatterer (eq. (10)), the vector
Foldy-Lax equations (eq. (9)), the Green's matrix (eq. (12)), its biorthogonal eigensystem
(eqs. (13)-(15)), the quasi-mode frequencies and decay rates (eq. (17)), and the near-field
Green's tensor of Section III D (eq. (21)).

The medium enters only through its mass density `ρ0` and the speeds `cp`, `cs` of compressive and
shear waves, `cp = ((λ0 + 2 μ0) / ρ0)^{1/2}`, `cs = (μ0 / ρ0)^{1/2}`.
-/

open Complex

noncomputable section

namespace Arxiv1803_10134

/-- Physical space `ℝ³`, in which positions `r` and separations `Δr = r - r'` live
(Section III A). -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The `3N` Cartesian displacement components `u_m^α` of `N` scatterers, indexed by the scatterer
`m` and the direction `α ∈ {x, y, z}`; the vector `|u⟩` of Section III A, before eq. (11). -/
abbrev Idx (N : ℕ) := Fin N × Fin 3

/-- The dyadic `v ⊗ v` of a vector of `ℝ³`, as a complex `3 × 3` matrix (Section III A, after
eq. (8)). -/
def outerC (v : Space) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.vecMulVec (fun a => (v a : ℂ)) (fun a => (v a : ℂ))

/-- The auxiliary tensor function defined after eq. (8):
`F(v) = [1 - 3 (v ⊗ v) / v²] (1 + 3i/v - 3/v²)`, with `v = ‖v‖`. -/
def auxF (v : Space) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 + 3 * I / (‖v‖ : ℂ) - 3 / (‖v‖ : ℂ) ^ 2) •
    (1 - ((3 : ℂ) / (‖v‖ : ℂ) ^ 2) • outerC v)

/-- The compressive-wave term of eqs. (8) and (12) at separation `Δr`:
`e^{i k_p Δr} / (k_p Δr) [1 - F(k_p Δr)]`, with `k_p = ω / c_p`. -/
def compressivePart (cp om : ℝ) (x : Space) : Matrix (Fin 3) (Fin 3) ℂ :=
  (cexp (I * ((om / cp * ‖x‖ : ℝ) : ℂ)) / ((om / cp * ‖x‖ : ℝ) : ℂ)) •
    (1 - auxF ((om / cp) • x))

/-- The shear-wave term of eqs. (8) and (12) at separation `Δr`:
`e^{i k_s Δr} / (k_s Δr) [1 + F(k_s Δr) / 2]`, with `k_s = ω / c_s`. -/
def shearPart (cs om : ℝ) (x : Space) : Matrix (Fin 3) (Fin 3) ℂ :=
  (cexp (I * ((om / cs * ‖x‖ : ℝ) : ℂ)) / ((om / cs * ‖x‖ : ℝ) : ℂ)) •
    (1 + (1 / 2 : ℂ) • auxF ((om / cs) • x))

/-- Eq. (8): the elastic Green's tensor of a homogeneous isotropic medium of mass density `ρ0`
with compressive and shear wave speeds `cp`, `cs`, at frequency `ω`:
`𝒢(r, r', ω) = ω / (12 π ρ0 c_p³) {compressive part + 2 (c_p/c_s)³ shear part}` at `Δr = r - r'`. -/
def greenTensor (rho0 cp cs om : ℝ) (r r' : Space) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((om / (12 * Real.pi * rho0 * cp ^ 3) : ℝ) : ℂ) •
    (compressivePart cp om (r - r') + ((2 * (cp / cs) ^ 3 : ℝ) : ℂ) • shearPart cs om (r - r'))

/-- The prefactor `B` of eq. (10), read with the bracket in the denominator (as eq. (12)
requires): `B = 12 π ρ0 c_p³ / (ω [1 + 2 (c_p/c_s)³])`. -/
def prefactorB (rho0 cp cs om : ℝ) : ℝ :=
  12 * Real.pi * rho0 * cp ^ 3 / (om * (1 + 2 * (cp / cs) ^ 3))

/-- Eq. (10): the polarizability of an isotropic resonant scatterer with prefactor `B`, resonance
frequency `ω0` and resonance width `Γ0`: `α0(ω) = B (-Γ0/2) / (ω - ω0 + i Γ0/2)`. -/
def polarizability (B om0 gam0 om : ℝ) : ℂ :=
  (B : ℂ) * ((-gam0 / 2 : ℝ) : ℂ) / (((om - om0 : ℝ) : ℂ) + I * ((gam0 / 2 : ℝ) : ℂ))

/-- Eq. (9), the vector Foldy-Lax equations: the displacements `u` of scatterers at positions `r`
in the incident field `v` satisfy
`u_m^α = v_m^α + α0(ω) ∑_{n ≠ m, β} 𝒢^{αβ}(r_m, r_n, ω) u_n^β`, with `α0` of eq. (10) and the
prefactor `B` of eq. (10). -/
def IsFoldyLaxSolution {N : ℕ} (rho0 cp cs om0 gam0 om : ℝ) (r : Fin N → Space) (u v : Idx N → ℂ) :
    Prop :=
  ∀ (m : Fin N) (a : Fin 3),
    u (m, a) = v (m, a) + polarizability (prefactorB rho0 cp cs om) om0 gam0 om *
      ∑ n ∈ Finset.univ.filter (fun n => n ≠ m), ∑ b : Fin 3,
        greenTensor rho0 cp cs om (r m) (r n) a b * u (n, b)

/-- Eq. (12), first line: the `3N × 3N` Green's matrix with `3 × 3` blocks
`G_mn(ω) = i δ_mn 1 + (1 - δ_mn) B 𝒢(r_m, r_n, ω)`. -/
def greenMatrix {N : ℕ} (rho0 cp cs om : ℝ) (r : Fin N → Space) : Matrix (Idx N) (Idx N) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then (if p.2 = q.2 then I else 0)
    else (prefactorB rho0 cp cs om : ℂ) * greenTensor rho0 cp cs om (r p.1) (r q.1) p.2 q.2

/-- Eqs. (13)-(15): `lam n`, `R n` and `L n` (`n` ranging over `3N` indices) are eigenvalues, right
eigenvectors and left (row) eigenvectors of `G`, with `⟨L_m | R_n⟩ = δ_mn`. The pairing `⟨L|R⟩`
is the product of a row vector and a column vector, without complex conjugation. -/
def IsBiorthogonalEigensystem {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ)
    (lam : ι → ℂ) (R L : ι → ι → ℂ) : Prop :=
  (∀ n, G.mulVec (R n) = lam n • R n) ∧ (∀ n, Matrix.vecMul (L n) G = lam n • L n) ∧
    (∀ m n, L m ⬝ᵥ R n = if m = n then 1 else 0)

/-- Eq. (17): the frequency `ω_n = ω0 - (Γ0/2) Re Λ_n` of the quasi-mode with eigenvalue `Λ_n`. -/
def qmFreq (om0 gam0 : ℝ) (lam : ℂ) : ℝ := om0 - gam0 / 2 * lam.re

/-- Eq. (17): the decay rate `Γ_n = Γ0 Im Λ_n` of the quasi-mode with eigenvalue `Λ_n`. -/
def qmWidth (gam0 : ℝ) (lam : ℂ) : ℝ := gam0 * lam.im

/-- Eq. (21), Section III D: the near-field form of the elastic Green's tensor,
`1 / (8 π ρ0 c_s² Δr) {[1 + (c_s/c_p)²] 1 + [1 - (c_s/c_p)²] Δr ⊗ Δr / Δr²}` at `Δr = r - r'`. -/
def nearFieldTensor (rho0 cp cs : ℝ) (r r' : Space) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((1 / (8 * Real.pi * rho0 * cs ^ 2 * ‖r - r'‖) : ℝ) : ℂ) •
    (((1 + (cs / cp) ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) +
      (((1 - (cs / cp) ^ 2) / ‖r - r'‖ ^ 2 : ℝ) : ℂ) • outerC (r - r'))

end Arxiv1803_10134


