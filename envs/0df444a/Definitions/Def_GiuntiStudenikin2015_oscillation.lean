-- Prove2me | Definitions.Def_GiuntiStudenikin2015_oscillation
-- name    : GiuntiStudenikin2015_oscillation
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-24T13:00:06.345397+00:00
-- url     : https://prove2.me/theorems/ddbc9b58-af14-4b6e-87de-f2124be87314
-- title:
--   Neutrino oscillation, MSW, Majorana and spin-precession definitions (Giunti–Studenikin 2015)
-- statement:
--   Shared definitions for the mission, all in the namespace `GiuntiStudenikin2015`.
--
--   1. **Transition probability** (Eqs. (2.35)–(2.36)). For an $n\times n$ complex matrix $U$, masses $m=(m_k)$, distance $L$ and energy $E$,
--   $$P_{\ell\to\ell'}(L,E)=\Bigl|\sum_{k}\overline{U_{\ell k}}\;e^{-i m_k^2 L/(2E)}\;U_{\ell' k}\Bigr|^2 .$$
--   2. **Standard parametrization** $U^{\mathrm D}(\vartheta_{12},\vartheta_{13},\vartheta_{23},\delta_{13})$ of Eq. (2.27), with $c_{ab}=\cos\vartheta_{ab}$, $s_{ab}=\sin\vartheta_{ab}$:
--   $$U^{\mathrm D}=\begin{pmatrix}c_{12}c_{13}&s_{12}c_{13}&s_{13}e^{-i\delta_{13}}\\-s_{12}c_{23}-c_{12}s_{23}s_{13}e^{i\delta_{13}}&c_{12}c_{23}-s_{12}s_{23}s_{13}e^{i\delta_{13}}&s_{23}c_{13}\\s_{12}s_{23}-c_{12}c_{23}s_{13}e^{i\delta_{13}}&-c_{12}s_{23}-s_{12}c_{23}s_{13}e^{i\delta_{13}}&c_{23}c_{13}\end{pmatrix}.$$
--   3. **Majorana phases** $D^{\mathrm M}=\operatorname{diag}(1,e^{i\lambda_{21}},e^{i\lambda_{31}})$, Eq. (2.28).
--   4. **Two-neutrino mixing matrix** $\begin{pmatrix}\cos\vartheta&\sin\vartheta\\-\sin\vartheta&\cos\vartheta\end{pmatrix}$, Eqs. (2.38), (2.51).
--   5. **MSW Hamiltonian** (Eq. (2.46)) with $A_{\rm CC}=2EV_{\rm CC}$:
--   $$\mathrm H=\frac1{4E}\begin{pmatrix}-\Delta m^2\cos2\vartheta+2EV_{\rm CC}&\Delta m^2\sin2\vartheta\\\Delta m^2\sin2\vartheta&\Delta m^2\cos2\vartheta-2EV_{\rm CC}\end{pmatrix}.$$
--   6. **Effective squared-mass difference** $\Delta m^2_{\rm M}=\sqrt{(\Delta m^2\cos2\vartheta-2EV_{\rm CC})^2+(\Delta m^2\sin2\vartheta)^2}$, Eq. (2.53).
--   7. **Effective mixing angle** $\vartheta_{\rm M}=\tfrac12\arg\bigl((\Delta m^2\cos2\vartheta-2EV_{\rm CC})+i\,\Delta m^2\sin2\vartheta\bigr)$, so that $\Delta m^2_{\rm M}\cos2\vartheta_{\rm M}=\Delta m^2\cos2\vartheta-2EV_{\rm CC}$ and $\Delta m^2_{\rm M}\sin2\vartheta_{\rm M}=\Delta m^2\sin2\vartheta$, i.e. Eq. (2.54) wherever the quotient is defined.
--   8. **Levi-Civita symbol** $\epsilon^{abc}$ on $\{1,2,3\}$ with $\epsilon^{123}=1$ (Eq. (3.71)).
--   9. **Spin-flavor Hamiltonian** $\begin{pmatrix}V&\mu B\\\mu B&0\end{pmatrix}$ (Eqs. (6.23), (6.28)) and **energy splitting** $\Delta E_{\rm M}=\sqrt{V^2+(2\mu B)^2}$ (Eq. (6.31)).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Indices are `Fin n` starting at $0$ (so index $0$ is the paper's $1$). All functions are total: at $E=0$ the phase $m_k^2L/(2E)$ is $0$ by Lean's convention $x/0=0$, and $\arg 0=0$.
-- source:
--   C. Giunti and A. Studenikin, *Neutrino electromagnetic interactions: A window to new physics*, Rev. Mod. Phys. 87, 531 (2015), https://doi.org/10.1103/RevModPhys.87.531; Eqs. (2.27), (2.28), (2.35)–(2.36), (2.38), (2.46), (2.53)–(2.54), (3.71), (6.23), (6.28), (6.31)

import Mathlib

namespace GiuntiStudenikin2015

open Complex Matrix

/-- Plane-wave flavor transition probability, Eqs. (2.35)–(2.36):
`P(ℓ → ℓ') = |∑ₖ U*_{ℓk} exp(-i mₖ² L / (2E)) U_{ℓ'k}|²`,
for an `n × n` mixing matrix `U` (rows = flavors, columns = massive states),
masses `m k`, source–detector distance `L`, and neutrino energy `E`. -/
noncomputable def oscProb {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (m : Fin n → ℝ)
    (L E : ℝ) (l l' : Fin n) : ℝ :=
  Complex.normSq (∑ k, star (U l k) *
    Complex.exp (-(Complex.I * ((m k ^ 2 * L / (2 * E) : ℝ) : ℂ))) * U l' k)

/-- Standard parametrization of the Dirac mixing matrix `Uᴰ`, Eq. (2.27). -/
noncomputable def diracMixing (θ12 θ13 θ23 δ13 : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let c12 : ℂ := (Real.cos θ12 : ℂ)
  let s12 : ℂ := (Real.sin θ12 : ℂ)
  let c13 : ℂ := (Real.cos θ13 : ℂ)
  let s13 : ℂ := (Real.sin θ13 : ℂ)
  let c23 : ℂ := (Real.cos θ23 : ℂ)
  let s23 : ℂ := (Real.sin θ23 : ℂ)
  let e : ℂ := Complex.exp (Complex.I * (δ13 : ℂ))
  !![c12 * c13, s12 * c13, s13 * Complex.exp (-(Complex.I * (δ13 : ℂ)));
     -s12 * c23 - c12 * s23 * s13 * e, c12 * c23 - s12 * s23 * s13 * e, s23 * c13;
     s12 * s23 - c12 * c23 * s13 * e, -c12 * s23 - s12 * c23 * s13 * e, c23 * c13]

/-- Diagonal Majorana-phase matrix `Dᴹ = diag(1, e^{iλ₂₁}, e^{iλ₃₁})`, Eq. (2.28). -/
noncomputable def majoranaPhases (lam21 lam31 : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![1, Complex.exp (Complex.I * (lam21 : ℂ)),
    Complex.exp (Complex.I * (lam31 : ℂ))]

/-- Two-neutrino mixing matrix, Eq. (2.38) (also the matter mixing matrix of Eq. (2.51)). -/
noncomputable def twoFlavorMixing (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos θ : ℂ), (Real.sin θ : ℂ); -(Real.sin θ : ℂ), (Real.cos θ : ℂ)]

/-- Effective two-neutrino (`νₑ`–`νₐ`) Hamiltonian in matter, Eq. (2.46), with
`A_CC = 2 E V_CC`; `dm2` is the vacuum squared-mass difference `Δm²`. -/
noncomputable def mswHamiltonian (dm2 θ E Vcc : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((1 / (4 * E) : ℝ) : ℂ) •
    !![((-dm2 * Real.cos (2 * θ) + 2 * E * Vcc : ℝ) : ℂ), ((dm2 * Real.sin (2 * θ) : ℝ) : ℂ);
       ((dm2 * Real.sin (2 * θ) : ℝ) : ℂ), ((dm2 * Real.cos (2 * θ) - 2 * E * Vcc : ℝ) : ℂ)]

/-- Effective squared-mass difference in matter `Δm²_M`, Eq. (2.53). -/
noncomputable def mswDeltaM2 (dm2 θ E Vcc : ℝ) : ℝ :=
  Real.sqrt ((dm2 * Real.cos (2 * θ) - 2 * E * Vcc) ^ 2 + (dm2 * Real.sin (2 * θ)) ^ 2)

/-- Effective mixing angle in matter `ϑ_M`, Eq. (2.54): the angle with
`Δm²_M cos 2ϑ_M = Δm² cos 2ϑ − 2E V_CC` and `Δm²_M sin 2ϑ_M = Δm² sin 2ϑ`
(so `tan 2ϑ_M = tan 2ϑ / (1 − 2E V_CC / (Δm² cos 2ϑ))` whenever defined),
taken as half the argument of the complex number
`(Δm² cos 2ϑ − 2E V_CC) + i Δm² sin 2ϑ`. -/
noncomputable def mswMixingAngle (dm2 θ E Vcc : ℝ) : ℝ :=
  Complex.arg (⟨dm2 * Real.cos (2 * θ) - 2 * E * Vcc, dm2 * Real.sin (2 * θ)⟩ : ℂ) / 2

/-- Totally antisymmetric Levi-Civita symbol `ε^{abc}` on three indices (indices `0,1,2`
stand for the massive states `1,2,3`), with `ε^{012} = 1`; used in Eq. (3.71). -/
def leviCivita3 (a b c : Fin 3) : ℂ :=
  if (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) then 1
  else if (a = 0 ∧ b = 2 ∧ c = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 2) then -1
  else 0

/-- Effective Hamiltonian for the helicity amplitudes `(ψ_L, ψ_R)` of an ultrarelativistic
Dirac neutrino with magnetic moment `μ` in a transverse magnetic field `B_⊥ = B` and matter
potential `V`, Eq. (6.28) (Eq. (6.23) is the case `V = 0`):
`[[V, μB], [μB, 0]]`. -/
noncomputable def spinFlavorHamiltonian (V μ B : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(V : ℂ), ((μ * B : ℝ) : ℂ); ((μ * B : ℝ) : ℂ), 0]

/-- Effective energy splitting in matter `ΔE_M = √(V² + (2μB_⊥)²)`, Eq. (6.31). -/
noncomputable def spinFlavorEnergySplitting (V μ B : ℝ) : ℝ :=
  Real.sqrt (V ^ 2 + (2 * μ * B) ^ 2)

end GiuntiStudenikin2015


