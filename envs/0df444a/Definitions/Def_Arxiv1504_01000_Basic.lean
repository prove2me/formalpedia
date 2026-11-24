-- Prove2me | Definitions.Def_Arxiv1504_01000_Basic
-- name    : Arxiv1504_01000_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T18:02:04.733305+00:00
-- url     : https://prove2.me/theorems/5b17fc92-d837-46a9-8eae-32766bd4c8e8
-- title:
--   Hellinger distance, rotated coherency matrix, OA estimator and SD-Y4O powers
-- statement:
--   Objects of Sections II-IV of Bhattacharya, Muhuri, De, Manickam and Frery (2015).
--
--   1. **Hellinger distance (Section II).** For distributions on $\mathbb{R}$ with densities $f_1,f_2$, $d_H=1-\int\sqrt{f_1f_2}$. This is the $(h,\phi)$ distance with $h(x)=x/2$, $\phi(x)=(\sqrt x-1)^2$.
--   2. **Multilook intensity law (Section II).** The Gamma distribution with shape $L>0$ (the number of looks) and mean $m=\sigma^2>0$. Its density is $f(x)=\frac{(L/m)^L}{\Gamma(L)}x^{L-1}e^{-Lx/m}$ for $x\ge0$ and $0$ for $x<0$.
--   3. **Rotated coherency matrix (eq. 7).** For a $3\times3$ coherency matrix $[T]$ and an angle $\theta$,
--   $$[U_3(\theta)]=\begin{pmatrix}1&0&0\\0&\cos2\theta&\sin2\theta\\0&-\sin2\theta&\cos2\theta\end{pmatrix},\qquad [T(\theta)]=[U_3(\theta)][T][U_3(\theta)]^{-1}.$$
--   The rotated diagonal elements are $\sigma_l^2(\theta)=T_{ll}(\theta)$, and $\sigma_l^2=T_{ll}$.
--   4. **Hellinger distance of the rotated elements (eq. 9).** For $a,b>0$ and $L>0$, $d_H(a,b)=1-\big[2\sqrt{ab}/(a+b)\big]^L$. The distance curves of the estimator are $\theta\mapsto d_H(\sigma_l^2,\sigma_l^2(\theta))$ for $l=2,3$.
--   5. **OA estimator (eqs. 9-10, Algorithm 1).** The search range is $[-\pi/4,\pi/4]$. A candidate angle is a point of $[-\pi/4,\pi/4]$ of the form $\phi_{3,2}$ or $\phi_{3,2}\pm\pi/4$, where $\phi_{3,2}$ is a maximiser over $[-\pi/4,\pi/4]$ of $d_H(\sigma_3^2,\sigma_3^2(\theta))$ (giving $\phi_3$) or of $d_H(\sigma_2^2,\sigma_2^2(\theta))$ (giving $\phi_2$). A candidate $\phi$ is selected when $d_H(\sigma_3^2,\sigma_3^2(\phi))>d_H(\sigma_2^2,\sigma_2^2(\phi))$. The final OA $\theta_0$ is $\phi+\pi/4$ if $\phi<-\pi/8$, $\phi-\pi/4$ if $\phi>\pi/8$, and $\phi$ otherwise.
--   6. **Relative Hellinger distance (eq. 12).** $\delta_H=d_H(\sigma_3^2,\sigma_3^2(\phi))-d_H(\sigma_2^2,\sigma_2^2(\phi))$ for $L$ looks, and $\delta_H^m=\sup_{L>0}\delta_H$.
--   7. **SD-Y4O (eqs. 13a-13d).** For Y4O powers $P_s,P_d,P_v,P_c$ and parameters $\delta,\alpha,\beta$: $P_v^n=P_v(1-\delta)$, $P_d^n=P_d+\alpha P_v\delta$, $P_s^n=P_s+\beta P_v\delta$ and $P_c^n=P_c$. The parameter $\alpha$ is the linear map $\alpha(\phi)=\tfrac12+2\phi/\pi$, which takes $[0,\pi/4]$ onto $[0.5,1]$.
--
--   **Formalization Note** The paper's indices $1,2,3$ are Lean's `Fin 3` indices $0,1,2$. The diagonal elements of $[T(\theta)]$ are complex numbers in Lean; their real parts are taken, and they are real when $[T]$ is Hermitian. The number of looks $L$ is a positive real number, as in Fig. 3, where $\delta_H$ is a function of $L$. The supremum defining $\delta_H^m$ is over all $L>0$. The paper states the linear map onto $[0.5,1]$ without saying which way it runs; it is taken increasing, $\alpha(0)=0.5$ and $\alpha(\pi/4)=1$.
-- source:
--   Bhattacharya, Muhuri, De, Manickam and Frery, Modifying the Yamaguchi Four-Component Decomposition Scattering Powers Using a Stochastic Distance, arXiv:1504.01000v1 (2015), Sec. II (Hellinger distance, Gamma intensity law), Sec. III (eqs. (7), (9), (10), Algorithm 1), Sec. IV (eqs. (12), (13a)-(13d))

import Mathlib

/-!
Bhattacharya, Muhuri, De, Manickam and Frery, *Modifying the Yamaguchi Four-Component
Decomposition Scattering Powers Using a Stochastic Distance*, arXiv:1504.01000v1 (2015):
the Hellinger distance and multilook intensity (Gamma) model of Section II, the rotated coherency
matrix and the orientation-angle (OA) estimator of Section III (eqs. (7), (9), (10), Algorithm 1),
and the relative Hellinger distance and SD-Y4O powers of Section IV (eqs. (12), (13a)-(13d)).

Indices: Lean's `Fin 3` indices `0, 1, 2` are the paper's indices `1, 2, 3`, so `T 1 1 = T₂₂`,
`T 2 2 = T₃₃` and `T 1 2 = T₂₃`.
-/

open MeasureTheory

noncomputable section

namespace Arxiv1504_01000

/-- Section II: the Hellinger distance `d_H(D₁, D₂) = 1 - ∫ √(f₁ f₂)` between two distributions on
`ℝ` with densities `f₁, f₂` (obtained from the `(h, φ)` divergence with `h(x) = x/2`,
`φ(x) = (√x - 1)²`). -/
def hellingerDist (f₁ f₂ : ℝ → ℝ) : ℝ :=
  1 - ∫ x, Real.sqrt (f₁ x * f₂ x)

/-- Section II, sentence after eq. (6): the multilook intensity law, the Gamma distribution with
shape `L` (number of looks) and expected value `m = σ²`, i.e. rate `L / m`. -/
def intensityPDF (L m : ℝ) (x : ℝ) : ℝ :=
  ProbabilityTheory.gammaPDFReal L (L / m) x

/-- Eq. (7): the real rotation matrix
`[U₃(θ)] = [[1, 0, 0], [0, cos 2θ, sin 2θ], [0, -sin 2θ, cos 2θ]]`. -/
def U3 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0;
     0, (Real.cos (2 * θ) : ℂ), (Real.sin (2 * θ) : ℂ);
     0, -(Real.sin (2 * θ) : ℂ), (Real.cos (2 * θ) : ℂ)]

/-- Eq. (7): the rotated coherency matrix `[T(θ)] = [U₃(θ)] [T] [U₃(θ)]⁻¹`. -/
def rotT (T : Matrix (Fin 3) (Fin 3) ℂ) (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  U3 θ * T * (U3 θ)⁻¹

/-- Eq. (7): the diagonal element `σ_l²(θ) = T_ll(θ)` of the rotated coherency matrix (a real
number for Hermitian `T`; its real part is taken). -/
def sigmaSq (T : Matrix (Fin 3) (Fin 3) ℂ) (l : Fin 3) (θ : ℝ) : ℝ :=
  (rotT T θ l l).re

/-- Eq. (9): the Hellinger distance between two Gamma laws of common shape `L` and means `a`,
`b`: `1 - [2 √(a b) / (a + b)]^L`. -/
def hellingerGamma (a b L : ℝ) : ℝ :=
  1 - (2 * Real.sqrt (a * b) / (a + b)) ^ L

/-- Eq. (9), Algorithm 1: `d_H(σ_l², σ_l²(θ))`, the Hellinger distance between the un-rotated
element `σ_l² = T_ll` and the rotated element `σ_l²(θ)`, as a function of `θ`. -/
def dH (T : Matrix (Fin 3) (Fin 3) ℂ) (L : ℝ) (l : Fin 3) (θ : ℝ) : ℝ :=
  hellingerGamma (T l l).re (sigmaSq T l θ) L

/-- Eq. (9): the search range `[-π/4, π/4]` of the OA estimator. -/
def oaRange : Set ℝ :=
  Set.Icc (-(Real.pi / 4)) (Real.pi / 4)

/-- Eq. (9) and the paragraph after it: `φ` is a candidate angle, i.e. it lies in `[-π/4, π/4]`
and equals `φ_{3,2}` or `φ_{3,2} ± π/4`, where `φ_{3,2}` is a maximiser over `[-π/4, π/4]` of
`d_H(σ₃², σ₃²(θ))` (that is `φ₃`) or of `d_H(σ₂², σ₂²(θ))` (that is `φ₂`). -/
def IsCandidateOA (T : Matrix (Fin 3) (Fin 3) ℂ) (L : ℝ) (φ : ℝ) : Prop :=
  φ ∈ oaRange ∧ ∃ p ∈ oaRange, (IsMaxOn (dH T L 2) oaRange p ∨ IsMaxOn (dH T L 1) oaRange p) ∧
    (φ = p ∨ φ = p + Real.pi / 4 ∨ φ = p - Real.pi / 4)

/-- Section III and Algorithm 1: the selection rule. The unwrapped OA `φ` is a candidate angle at
which the Hellinger distance of `σ₃²` exceeds that of `σ₂²`: `d_{Hφ₃} > d_{Hφ₂}`. -/
def IsSelectedOA (T : Matrix (Fin 3) (Fin 3) ℂ) (L : ℝ) (φ : ℝ) : Prop :=
  IsCandidateOA T L φ ∧ dH T L 1 φ < dH T L 2 φ

/-- Eq. (10): the final OA `θ₀`, obtained by wrapping `φ` into `[-π/8, π/8]`. -/
def wrapOA (φ : ℝ) : ℝ :=
  if φ < -(Real.pi / 8) then φ + Real.pi / 4
  else if Real.pi / 8 < φ then φ - Real.pi / 4
  else φ

/-- Eq. (12): the relative Hellinger distance
`δ_H = d_H(σ₃², σ₃²(φ)) - d_H(σ₂², σ₂²(φ))` at the angle `φ`, for `L` looks. -/
def deltaH (T : Matrix (Fin 3) (Fin 3) ℂ) (L : ℝ) (φ : ℝ) : ℝ :=
  dH T L 2 φ - dH T L 1 φ

/-- Section IV, paragraph after eq. (12): `δ_H^m`, the maximum over the number of looks `L > 0` of
the relative Hellinger distance at `φ`. -/
def deltaHm (T : Matrix (Fin 3) (Fin 3) ℂ) (φ : ℝ) : ℝ :=
  ⨆ L : Set.Ioi (0 : ℝ), deltaH T L φ

/-- Section IV, eqs. (13a)-(13d): the surface, double-bounce, volume and helix powers
`P_s, P_d, P_v, P_c` of a pixel. -/
structure Y4OPowers where
  /-- Surface power `P_s`. -/
  ps : ℝ
  /-- Double-bounce power `P_d`. -/
  pd : ℝ
  /-- Volume power `P_v`. -/
  pv : ℝ
  /-- Helix power `P_c`. -/
  pc : ℝ

/-- Eqs. (13a)-(13d): the SD-Y4O powers `P_v^n = P_v (1 - δ)`, `P_d^n = P_d + α P_v δ`,
`P_s^n = P_s + β P_v δ`, `P_c^n = P_c`, where `δ = δ_H^m`. -/
def sdY4O (P : Y4OPowers) (δ α β : ℝ) : Y4OPowers where
  ps := P.ps + β * P.pv * δ
  pd := P.pd + α * P.pv * δ
  pv := P.pv * (1 - δ)
  pc := P.pc

/-- Section IV, paragraph after eqs. (13a)-(13d): `α` is obtained by linearly mapping the estimated
OA `φ ∈ [0, π/4]` onto `[0.5, 1.0]`, i.e. `α = 1/2 + 2φ/π`. -/
def alphaOfOA (φ : ℝ) : ℝ :=
  1 / 2 + 2 * φ / Real.pi

end Arxiv1504_01000


