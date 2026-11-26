-- Prove2me | Definitions.Def_Arxiv2405_00432_Basic
-- name    : Arxiv2405_00432_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-26T12:51:29.018787+00:00
-- url     : https://prove2.me/theorems/ae09412f-1ecc-4be8-a894-0fcaf8d0ebaf
-- title:
--   Tetrahedral POVM, Stokes vectors, instrumentation matrix, pseudo-inverse, retarders and Laguerre-Gaussian Poincaré beam
-- statement:
--   Objects of Sections 2-4 of McWilliam, Al Khafaji, Svensson, Pádua and Franke-Arnold (2024).
--
--   1. **Polarization states and Stokes vectors (Section 2.1).** A polarization state is $\psi=E_h|h\rangle+E_v|v\rangle$ with $(E_h,E_v)\in\mathbb{C}^2$. Its Stokes vector is $S_0=|E_h|^2+|E_v|^2$, $S_1=|E_h|^2-|E_v|^2$, $S_2=2\,\mathrm{Re}(\overline{E_h}E_v)$, $S_3=2\,\mathrm{Im}(E_h\overline{E_v})$, and the normalized Stokes vector is $S^{(N)}=S/S_0$.
--   2. **Tetrahedral POVM (eqs. 1-2).** With $a=\sqrt{\tfrac12+\tfrac1{2\sqrt3}}$ and $b=\sqrt{\tfrac12-\tfrac1{2\sqrt3}}$, the POVM states are $|\phi_1\rangle=a|h\rangle+b|v\rangle$, $|\phi_2\rangle=a|h\rangle-b|v\rangle$, $|\phi_3\rangle=b|h\rangle+ia|v\rangle$, $|\phi_4\rangle=b|h\rangle-ia|v\rangle$. The POVM operators are $\hat\pi_i=\tfrac12|\phi_i\rangle\langle\phi_i|$, the outcome probabilities are $P_i=\langle\psi|\hat\pi_i|\psi\rangle$, and the normalized intensity vector is $I^{(N)}=(P_1,\dots,P_4)/\sum_jP_j$.
--   3. **Ideal instrumentation matrix (eq. 4).** $\Pi=\tfrac14\begin{pmatrix}1&\sqrt{1/3}&\sqrt{2/3}&0\\1&\sqrt{1/3}&-\sqrt{2/3}&0\\1&-\sqrt{1/3}&0&-\sqrt{2/3}\\1&-\sqrt{1/3}&0&\sqrt{2/3}\end{pmatrix}$.
--   4. **Calibration states (eq. 8).** $|\bar\phi_1\rangle=b|h\rangle-a|v\rangle$, $|\bar\phi_2\rangle=b|h\rangle+a|v\rangle$, $|\bar\phi_3\rangle=a|h\rangle-ib|v\rangle$, $|\bar\phi_4\rangle=a|h\rangle+ib|v\rangle$.
--   5. **Pseudo-inverse (eq. 6).** For a real $4\times N$ matrix $\mathcal S$ whose columns are the Stokes vectors measured at $N$ pixels, $\mathcal S^\dagger=\mathcal S^T[\mathcal S\mathcal S^T]^{-1}$. The beam profile contains four linearly independent polarization states if four columns of $\mathcal S$ are linearly independent.
--   6. **Retarders (eqs. 11, 14, 15).** $M_T(\delta,\theta)$ is the Mueller matrix of eq. (11) of a retarder of retardance $\delta$ with fast axis at angle $\theta$. For a $4\times4$ matrix $m$ (indices $1$-$4$), $\delta_1=\tan^{-1}(-m_{34}/m_{33})$, $\delta_2=\tan^{-1}(-m_{34}/m_{44})$, $\delta_3=\tan^{-1}(m_{43}/m_{33})$, $\delta_4=\tan^{-1}(m_{43}/m_{44})$, with $\tan^{-1}$ the real arctangent with values in $(-\pi/2,\pi/2)$. The theoretical retardance of a waveplate of thickness $T$ at wavelength $\lambda$ is
--   $$\delta_T(\theta,\alpha)=\frac{2\pi T}{\lambda}\Big(\sqrt{n_e^2-\tfrac{n_e^2\cos^2\theta+n_o^2\sin^2\theta}{n_o^2}\sin^2\alpha}-\sqrt{n_o^2-\sin^2\alpha}\Big).$$
--   7. **Laguerre-Gaussian modes and the Poincaré beam (eq. 10).** For a Gaussian beam with waist $w_0$ at $z=0$ and wavelength $\lambda$: $z_R=\pi w_0^2/\lambda$, $w(z)=w_0\sqrt{1+(z/z_R)^2}$, $k=2\pi/\lambda$. The mode $\mathrm{LG}_p^\ell$ at polar coordinates $(r,\varphi)$ in the plane $z$ is
--   $$\frac{C_{p\ell}}{w}\Big(\frac{\sqrt2r}{w}\Big)^{|\ell|}L_p^{|\ell|}\Big(\frac{2r^2}{w^2}\Big)e^{-r^2/w^2}\,e^{-ikr^2z/(2(z^2+z_R^2))}\,e^{i\ell\varphi}\,e^{i(N+1)\arctan(z/z_R)},$$
--   with $C_{p\ell}=\sqrt{2p!/(\pi(p+|\ell|)!)}$, the generalized Laguerre polynomial $L_p^\alpha(x)=\sum_{i=0}^p(-1)^i\binom{p+\alpha}{p-i}x^i/i!$, and mode order $N=2p+|\ell|$; $(N+1)\arctan(z/z_R)$ is the Gouy phase. The Poincaré beam is $|\Psi\rangle=\mathrm{LG}_1^0|h\rangle+\mathrm{LG}_0^2|v\rangle$, both modes with the same $w_0$ and $\lambda$.
--
--   **Formalization Note** The paper does not state the sign convention of $S_3$. The one used, $S_3=2\,\mathrm{Im}(E_h\overline{E_v})$, is the unique sign for which the rows of eq. (4) are the Stokes vectors of the states of eq. (1), which the paper asserts. The paper does not write out the Laguerre-Gaussian modes; the standard paraxial form is used, with the factor $e^{-ikz}$ that is common to all modes omitted, and with both modes sharing waist and waist position. $P_i$ is taken as the real part of $\langle\psi|\hat\pi_i|\psi\rangle$, which is real.
-- source:
--   McWilliam, Al Khafaji, Svensson, Pádua and Franke-Arnold, Dynamic Mueller matrix polarimetry using generalized measurements, arXiv:2405.00432v1 (2024), Sections 2.1, 2.2, 3.2, 4, 4.1, 4.2; eqs. (1)-(4), (6), (8), (10), (11), (14), (15)

import Mathlib

/-!
McWilliam, Al Khafaji, Svensson, Pádua and Franke-Arnold, *Dynamic Mueller matrix polarimetry
using generalized measurements*, arXiv:2405.00432v1 (2024): the tetrahedral POVM states and the
ideal instrumentation matrix of Section 2.1, the pseudo-inverse reconstruction of Section 2.2, the
orthogonal calibration states of Section 3.2, the Laguerre-Gaussian Poincaré beam of Section 4, the
retarder Mueller matrices and retardance formulae of Sections 4.1 and 4.2.
-/

open Matrix

noncomputable section

namespace Arxiv2405_00432

/-- Eq. (2), Section 2.1: the coefficient `a = √(1/2 + 1/(2√3))`. -/
def coefA : ℝ := Real.sqrt (1 / 2 + 1 / (2 * Real.sqrt 3))

/-- Eq. (2), Section 2.1: the coefficient `b = √(1/2 - 1/(2√3))`. -/
def coefB : ℝ := Real.sqrt (1 / 2 - 1 / (2 * Real.sqrt 3))

/-- Section 2.1: a polarization state `E_h |h⟩ + E_v |v⟩`, stored as its coordinates
`(E_h, E_v)` in the horizontal/vertical basis. -/
abbrev Jones := Fin 2 → ℂ

/-- Eq. (1), Section 2.1: the four tetrahedral POVM states
`|φ₁⟩ = a|h⟩ + b|v⟩`, `|φ₂⟩ = a|h⟩ - b|v⟩`, `|φ₃⟩ = b|h⟩ + i a|v⟩`, `|φ₄⟩ = b|h⟩ - i a|v⟩`
(index `i : Fin 4` is the paper's `i + 1`). -/
def povmState : Fin 4 → Jones :=
  ![![(coefA : ℂ), (coefB : ℂ)], ![(coefA : ℂ), -(coefB : ℂ)],
    ![(coefB : ℂ), Complex.I * (coefA : ℂ)], ![(coefB : ℂ), -(Complex.I * (coefA : ℂ))]]

/-- Eq. (8), Section 3.2: the calibration states orthogonal to the POVM states,
`|φ̄₁⟩ = b|h⟩ - a|v⟩`, `|φ̄₂⟩ = b|h⟩ + a|v⟩`, `|φ̄₃⟩ = a|h⟩ - i b|v⟩`, `|φ̄₄⟩ = a|h⟩ + i b|v⟩`. -/
def orthState : Fin 4 → Jones :=
  ![![(coefB : ℂ), -(coefA : ℂ)], ![(coefB : ℂ), (coefA : ℂ)],
    ![(coefA : ℂ), -(Complex.I * (coefB : ℂ))], ![(coefA : ℂ), Complex.I * (coefB : ℂ)]]

/-- Section 2.1: the POVM operator `π̂_i = (1/d)|φ_i⟩⟨φ_i|` with `d = 2`. -/
def povmOp (i : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • Matrix.vecMulVec (povmState i) (star (povmState i))

/-- Section 2.1: the outcome probability (intensity) `P_i = ⟨ψ|π̂_i|ψ⟩` for a probe state `ψ`
(a real number; its real part is taken). -/
def outcomeProb (i : Fin 4) (ψ : Jones) : ℝ :=
  (star ψ ⬝ᵥ (povmOp i *ᵥ ψ)).re

/-- Section 2.1: the Stokes vector `(S₀, S₁, S₂, S₃)` of `E_h|h⟩ + E_v|v⟩`:
`S₀ = |E_h|² + |E_v|²`, `S₁ = |E_h|² - |E_v|²`, `S₂ = 2 Re(E_h* E_v)`, `S₃ = 2 Im(E_h E_v*)`.
The sign of `S₃` is not stated in the paper; it is the one for which the rows of eq. (4) are the
Stokes vectors of the states of eq. (1), as the paper says they are. -/
def stokes (ψ : Jones) : Fin 4 → ℝ :=
  ![Complex.normSq (ψ 0) + Complex.normSq (ψ 1), Complex.normSq (ψ 0) - Complex.normSq (ψ 1),
    2 * (starRingEnd ℂ (ψ 0) * ψ 1).re, 2 * (ψ 0 * starRingEnd ℂ (ψ 1)).im]

/-- Section 2.1: the normalized Stokes vector `S^(N) = (S₀, S₁, S₂, S₃) / S₀`. -/
def normStokes (ψ : Jones) : Fin 4 → ℝ :=
  fun j => stokes ψ j / stokes ψ 0

/-- Section 2.1: the normalized intensity four-vector `I^(N) = (I₁, I₂, I₃, I₄) / ∑ᵢ Iᵢ`, with
the intensity `I_i` of outcome `i` equal to `P_i`. -/
def normIntensity (ψ : Jones) : Fin 4 → ℝ :=
  fun i => outcomeProb i ψ / ∑ j, outcomeProb j ψ

/-- Eq. (4), Section 2.1: the instrumentation matrix of an ideal setup. -/
def instrMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  (1 / 4 : ℝ) • !![1, Real.sqrt (1 / 3), Real.sqrt (2 / 3), 0;
                   1, Real.sqrt (1 / 3), -Real.sqrt (2 / 3), 0;
                   1, -Real.sqrt (1 / 3), 0, -Real.sqrt (2 / 3);
                   1, -Real.sqrt (1 / 3), 0, Real.sqrt (2 / 3)]

/-- Eq. (6), Section 2.2: the right Moore-Penrose pseudo-inverse
`(𝒮_in)† = 𝒮_inᵀ [𝒮_in 𝒮_inᵀ]⁻¹` of a `4 × N` matrix of Stokes vectors (one column per pixel).
Statements use it only where `𝒮_in 𝒮_inᵀ` is invertible. -/
def rightPseudoInv {N : ℕ} (S : Matrix (Fin 4) (Fin N) ℝ) : Matrix (Fin N) (Fin 4) ℝ :=
  Sᵀ * (S * Sᵀ)⁻¹

/-- Section 2.2, last sentence: the beam profile (the columns of the `4 × N` Stokes matrix `S`)
contains 4 linearly independent polarization states. -/
def HasFourIndependentStates {N : ℕ} (S : Matrix (Fin 4) (Fin N) ℝ) : Prop :=
  ∃ c : Fin 4 → Fin N, LinearIndependent ℝ (fun k : Fin 4 => fun i : Fin 4 => S i (c k))

/-- Eq. (11), Section 4.1: the Mueller matrix `M_T(δ, θ)` of a retarder with retardance `δ` and
fast axis at angle `θ` to the horizontal. -/
def retarderMueller (δ θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, Real.cos (2 * θ) ^ 2 + Real.sin (2 * θ) ^ 2 * Real.cos δ,
       Real.cos (2 * θ) * Real.sin (2 * θ) * (1 - Real.cos δ), Real.sin (2 * θ) * Real.sin δ;
     0, Real.cos (2 * θ) * Real.sin (2 * θ) * (1 - Real.cos δ),
       Real.cos (2 * θ) ^ 2 * Real.cos δ + Real.sin (2 * θ) ^ 2, -(Real.cos (2 * θ) * Real.sin δ);
     0, -(Real.sin (2 * θ) * Real.sin δ), Real.cos (2 * θ) * Real.sin δ, Real.cos δ]

/-- Eq. (14), Section 4.2: the four retardance values computed from a Mueller matrix `m`,
`δ₁ = tan⁻¹(-m₃₄/m₃₃)`, `δ₂ = tan⁻¹(-m₃₄/m₄₄)`, `δ₃ = tan⁻¹(m₄₃/m₃₃)`, `δ₄ = tan⁻¹(m₄₃/m₄₄)`,
with `tan⁻¹` the real arctangent and the paper's 1-based indices (Lean index `k` is `δ_{k+1}`). -/
def retardanceEst (m : Matrix (Fin 4) (Fin 4) ℝ) : Fin 4 → ℝ :=
  ![Real.arctan (-(m 2 3) / m 2 2), Real.arctan (-(m 2 3) / m 3 3),
    Real.arctan (m 3 2 / m 2 2), Real.arctan (m 3 2 / m 3 3)]

/-- Eq. (15), Section 4.2: the theoretical retardance `δ_T(θ, α)` of a multi-order waveplate of
thickness `T` at vacuum wavelength `λ` (`lam`), with ordinary and extraordinary indices `n_o`,
`n_e`, fast axis at angle `θ` and angle of incidence `α`. -/
def theoryRetardance (T lam no ne θ α : ℝ) : ℝ :=
  2 * Real.pi * T / lam *
    (Real.sqrt (ne ^ 2 - (ne ^ 2 * Real.cos θ ^ 2 + no ^ 2 * Real.sin θ ^ 2) / no ^ 2 *
        Real.sin α ^ 2) -
      Real.sqrt (no ^ 2 - Real.sin α ^ 2))

/-- Section 4, eq. (10): the generalized Laguerre polynomial
`L_p^α(x) = ∑_{i=0}^{p} (-1)^i C(p+α, p-i) xⁱ / i!` that enters the mode `LG_p^ℓ` (with `α = |ℓ|`). -/
def genLaguerre (p α : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p + 1),
    (-1 : ℝ) ^ i * ((p + α).choose (p - i) : ℝ) * x ^ i / (i.factorial : ℝ)

/-- Section 4: the mode order `N = 2p + |ℓ|` of `LG_p^ℓ`. -/
def modeOrder (p : ℕ) (ℓ : ℤ) : ℕ := 2 * p + ℓ.natAbs

/-- Section 4: the Rayleigh range `z_R = π w₀² / λ` of a Gaussian beam of waist `w₀` (waist at
`z = 0`) and wavelength `λ`. -/
def rayleighRange (w0 lam : ℝ) : ℝ := Real.pi * w0 ^ 2 / lam

/-- Section 4: the beam radius `w(z) = w₀ √(1 + (z/z_R)²)`. -/
def beamWidth (w0 lam z : ℝ) : ℝ := w0 * Real.sqrt (1 + (z / rayleighRange w0 lam) ^ 2)

/-- Section 4, after eq. (10): the Gouy phase `(N + 1) arctan(z / z_R)` of `LG_p^ℓ`. -/
def gouyPhase (p : ℕ) (ℓ : ℤ) (w0 lam z : ℝ) : ℝ :=
  ((modeOrder p ℓ : ℝ) + 1) * Real.arctan (z / rayleighRange w0 lam)

/-- Section 4, eq. (10): the paraxial Laguerre-Gaussian mode `LG_p^ℓ` with waist `w₀` at `z = 0`
and wavelength `λ`, at polar coordinates `(r, φ)` in the plane `z`:
`C/w (√2 r/w)^{|ℓ|} L_p^{|ℓ|}(2r²/w²) e^{-r²/w²} e^{-i k r² z/(2(z² + z_R²))} e^{iℓφ} e^{i(N+1)ζ(z)}`,
with `k = 2π/λ`, `C = √(2 p! / (π (p+|ℓ|)!))`, `ζ(z) = arctan(z/z_R)` and the common factor `e^{-ikz}`
omitted. -/
def lgMode (p : ℕ) (ℓ : ℤ) (w0 lam r φ z : ℝ) : ℂ :=
  ((Real.sqrt (2 * (p.factorial : ℝ) / (Real.pi * ((p + ℓ.natAbs).factorial : ℝ))) /
      beamWidth w0 lam z *
      (Real.sqrt 2 * r / beamWidth w0 lam z) ^ ℓ.natAbs *
      genLaguerre p ℓ.natAbs (2 * r ^ 2 / beamWidth w0 lam z ^ 2) *
      Real.exp (-(r ^ 2 / beamWidth w0 lam z ^ 2)) : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * ((2 * Real.pi / lam * r ^ 2 * z /
      (2 * (z ^ 2 + rayleighRange w0 lam ^ 2)) : ℝ) : ℂ))) *
    Complex.exp (Complex.I * ((ℓ * φ : ℝ) : ℂ)) *
    Complex.exp (Complex.I * ((gouyPhase p ℓ w0 lam z : ℝ) : ℂ))

/-- Eq. (10), Section 4: the Poincaré probe beam `|Ψ⟩ = LG₁⁰|h⟩ + LG₀²|v⟩` at `(r, φ, z)`, both
modes having the same waist `w₀` at `z = 0` and the same wavelength `λ`. -/
def poincareBeam (w0 lam r φ z : ℝ) : Jones :=
  ![lgMode 1 0 w0 lam r φ z, lgMode 0 2 w0 lam r φ z]

end Arxiv2405_00432


