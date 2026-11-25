-- Prove2me | Definitions.Def_Arxiv2105_07250_Basic
-- name    : Arxiv2105_07250_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T09:28:20.8877+00:00
-- url     : https://prove2.me/theorems/e6460eff-5970-43d9-b7dc-4e5b0f3761ff
-- title:
--   Interferometric retrievals, random windowing and moving-source model
-- statement:
--   Objects of Sections 2-4 and Appendices A-B of Ayala-Garcia, Curtis and Branicki (2021). The straight source boundary $S$ is parametrised by arc length $x'\in\mathbb{R}$, and frequency-domain quantities are taken at one fixed angular frequency $\omega$, which is suppressed: $G_A(x')=\hat G(x_A,x',\omega)$, $G_B(x')=\hat G(x_B,x',\omega)$, $F(x')=\hat F(x',\omega)$.
--
--   1. **Retrievals (eqs. 1-3).** $\hat g=\frac{2}{\rho c}\int_{\mathbb{R}}\overline{G_A(x')}\,G_B(x')\,dx'$; for recordings $p_A,p_B$, $\hat h=\frac{2}{\rho c}\,\overline{p_A}\,p_B$.
--   2. **Stacking (eqs. 6-8).** The stacking-average kernel is $\langle \hat F^*\hat F\rangle(x',x'')=\mathbb{E}_P[\overline{F(x')}F(x'')]$ over noise realisations. For a kernel given as a measure $\kappa$ on $\mathbb{R}^2$, the stacked retrieval is $\frac{2}{\rho c}\int\overline{G_A(x')}G_B(x'')\,\kappa(dx',dx'')$. The delta kernel $\delta(x'-x'')|\hat s|^2$ is $|\hat s|^2$ times the image of Lebesgue measure under $x'\mapsto(x',x')$.
--   3. **Random windowing (eqs. 20-24, 27-28).** For a window density $f_T$ (a probability density vanishing outside a bounded interval), $\langle\gamma\rangle_T=\int\gamma(\tau)f_T(\tau)\,d\tau$. With $x_n=|v|t_n$, the windowed recording is $\int F(x')G(x')\chi_{\{|x'-x_n|\le T|v|\}}(x')\,dx'$, the windowed retrieval $\hat h(\cdot;T,t_n)$ applies (2) to two windowed recordings, $\hat h_T=\langle\hat h(\cdot;T,\cdot)\rangle_T$, and $\langle\chi\chi\rangle_T(x',x'')=\langle\chi_{\{|x'-x_n|\le T|v|\}}\chi_{\{|x''-x_n|\le T|v|\}}\rangle_T$. The uniform density is $f_T=\frac{1}{2T}\mathbf 1_{[t_0-T,t_0+T]}$. $\Theta(s)=1$ for $s\ge0$ and $0$ otherwise; the boxcar of width $w$ is $\mathbf 1_{[-w/2,w/2]}$; the tent of eq. (28) is $(d+L)\Theta(d+L)+(d-L)\Theta(d-L)-2d\,\Theta(d)$.
--   4. **Moving source (Appendix A).** In the plane, $q_1=\frac{c^2t-x\cdot v}{c^2-|v|^2}$, $q_2=q_1^2-\frac{c^2t^2-|x|^2}{c^2-|v|^2}$ and $\mathring t=q_1-\sqrt{q_2}$. $J_0$ and $Y_0$ are the Bessel functions of order zero given by their standard series (DLMF 10.2.2, 10.8.2), $\mathcal H_0^{(1)}=J_0+iY_0$ and $\mathcal H_1^{(1)}=-(\mathcal H_0^{(1)})'$. The potential (A12) is $\phi=\frac{i\,e^{-i\tilde\omega q_1}}{4c\sqrt{c^2-|v|^2}}\mathcal H_0^{(1)}(\tilde\omega\sqrt{q_2})$, and the pressure (A14) is the printed expression in $M=|v|/c$ and $t_x=|x|/c$.
--   5. **Doppler (eqs. 5, A21).** $\mathrm{ph}_x(t')=(\omega+\tilde\omega)t'+\frac{\omega}{c}|x-vt'|-\frac\pi4$; $\cos\theta_x(t')=\frac{(x-vt')\cdot v}{|x-vt'|\,|v|}$; $\breve\omega(x,t')=\tilde\omega/(1-\frac{|v|}{c}\cos\theta_x(t'))$.
--   6. **Broadband source (eq. A27, Appendix B).** $F(t';\theta)=\sum_i a_i\cos(w_it'+\theta_i)$; $\mathrm{Unif}(0,2\pi)$ is $\frac1{2\pi}$ times Lebesgue measure on $[0,2\pi)$; the band grid is $\tilde\omega_j=\tilde\omega_{\min}+j\frac{\tilde\omega_{\max}-\tilde\omega_{\min}}{N}$, $j=1,\dots,N$.
--
--   **Formalization Note** The boundary $S$ is the straight line of the paper's simulations, parametrised by arc length as on p. 12. The paper does not define the Bessel and Hankel functions; the standard series and the identity $\mathcal H_1^{(1)}=-(\mathcal H_0^{(1)})'$ (DLMF 10.6.2) are used. Eqs. (A12) and (A14) are encoded as printed, including the prefactor that REPORT.md shows to be inconsistent with (A7).
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), Sections 2-4 (eqs. (1)-(3), (6)-(8), (20)-(24), (27)-(28)), Appendix A (eqs. (A8)-(A14), (A21)-(A23), (A27)) and Appendix B

import Mathlib

/-!
D. Ayala-Garcia, A. Curtis and M. Branicki, *Seismic Interferometry from Correlated Noise Sources*,
arXiv:2105.07250v2 (2021): the interferometric retrievals of Sections 2 and 3, the random-windowing
quantities of Section 4, the moving point-source model and its Doppler phase in Appendix A, and the
random-phase source signature of Appendices A.2 and B.

Conventions. The straight source boundary `S` is parametrised by arc length, `x' = (x', 0)`
(Section 3, p. 12), so integrals over `S` are Lebesgue integrals over `ℝ`. Frequency-domain
quantities are taken at one fixed angular frequency `ω`, which is suppressed from the arguments:
`G x'` stands for `Ĝ(x, x', ω)` at a fixed receiver `x`, and `F x'` for `F̂(x', ω)`. Points of the
plane (Appendix A) are elements of `EuclideanSpace ℝ (Fin 2)`.
-/

open MeasureTheory

noncomputable section

namespace Arxiv2105_07250

/-- The plane `ℝ²` of Appendix A, with the Euclidean norm `|·|` and inner product `x · v`. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-! ### Sections 2 and 3: retrievals and stacking -/

/-- Eq. (1), Section 2, p. 4: the retrieval from individually recorded impulsive sources,
`ĝ(x_A,x_B,ω) = (2/(ρc)) ∫_S Ĝ*(x_A,x',ω) Ĝ(x_B,x',ω) dx'`, with `GA x' = Ĝ(x_A,x',ω)` and
`GB x' = Ĝ(x_B,x',ω)`. -/
def directRetrieval (ρ c : ℝ) (GA GB : ℝ → ℂ) : ℂ :=
  ((2 / (ρ * c) : ℝ) : ℂ) * ∫ x', starRingEnd ℂ (GA x') * GB x'

/-- Eq. (2), Section 2, p. 5: the ambient-noise retrieval
`ĥ(x_A,x_B,ω) = (2/(ρc)) p̂*(x_A,ω) p̂(x_B,ω)` from the recordings `pA = p̂(x_A,ω)`,
`pB = p̂(x_B,ω)`. -/
def ambientRetrieval (ρ c : ℝ) (pA pB : ℂ) : ℂ :=
  ((2 / (ρ * c) : ℝ) : ℂ) * (starRingEnd ℂ pA * pB)

/-- Eq. (7), Section 3, p. 10: the stacking-average kernel
`⟨F̂*F̂⟩(x',x'',ω) = ⟨F̂*(x',ω) F̂(x'',ω)⟩`, where the stacking average `⟨·⟩` is the expectation over
the noise realisations `r ∼ P` and `F r x' = F̂(x',ω)` in realisation `r`. -/
def stackKernel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → ℝ → ℂ)
    (x' x'' : ℝ) : ℂ :=
  ∫ r, starRingEnd ℂ (F r x') * F r x'' ∂P

/-- Eq. (6), Section 3, p. 10, for a stacking-average kernel given as a measure `κ` on `S × S`
(the measure `⟨F̂*F̂⟩(x',x'',ω) dx' dx''`; this is the form in which the δ-kernel of eq. (8) is a
kernel): `⟨ĥ(x_A,x_B,ω)⟩ = (2/(ρc)) ∫∫ Ĝ*(x_A,x',ω) Ĝ(x_B,x'',ω) κ(dx',dx'')`. -/
def stackedRetrievalOfKernel (ρ c : ℝ) (κ : Measure (ℝ × ℝ)) (GA GB : ℝ → ℂ) : ℂ :=
  ((2 / (ρ * c) : ℝ) : ℂ) * ∫ q, starRingEnd ℂ (GA q.1) * GB q.2 ∂κ

/-- Eq. (8), Section 3, p. 10: the delta-correlated kernel `δ(x' - x'') |ŝ(ω)|²` on `S × S`, i.e.
`|ŝ(ω)|²` times the image of arc length under the diagonal map `x' ↦ (x', x')`. -/
def deltaKernel (s : ℂ) : Measure (ℝ × ℝ) :=
  ENNReal.ofReal (Complex.normSq s) • (volume : Measure ℝ).map (fun x => (x, x))

/-! ### Section 4: random windowing -/

/-- Eq. (22), Section 4.1, p. 19: the random-windowing average `⟨γ⟩_T = ∫_ℝ γ(τ) f_T(τ) dτ` of a
function `γ` of the window centre, for the density `f_T` of the window centres. -/
def windowAvg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (fT : ℝ → ℝ) (γ : ℝ → E) : E :=
  ∫ τ, fT τ • γ τ

/-- Eq. (22) and Section 4.3, step (i), pp. 19 and 23: `f_T` is a probability density on `ℝ`
(measurable, non-negative, total mass one) that is non-zero only on a bounded interval. -/
def IsWindowDensity (fT : ℝ → ℝ) : Prop :=
  Measurable fT ∧ (∀ τ, 0 ≤ fT τ) ∧ (∫ τ, fT τ) = 1 ∧ ∃ a b : ℝ, ∀ τ, τ ∉ Set.Icc a b → fT τ = 0

/-- Eq. (20), Section 4.1, p. 19: the windowed recording
`p̂(x,ω;T,t_n) = ∫_S F̂(x',ω) Ĝ(x,x',ω) χ_{|x'-x_n| ≤ T|v|}(x') dx'`, with spatial window centre
`x_n = |v| t_n` (p. 19); `vabs = |v|`. -/
def windowedRecording (F G : ℝ → ℂ) (vabs T tn : ℝ) : ℂ :=
  ∫ x', Set.indicator {y : ℝ | |y - vabs * tn| ≤ T * vabs} (fun y => F y * G y) x'

/-- Eq. (21), Section 4.1, p. 19: the windowed retrieval
`ĥ(x_A,x_B,ω;T,t_n) = (2/(ρc)) p̂*(x_A,ω;T,t_n) p̂(x_B,ω;T,t_n)`. -/
def windowedRetrieval (ρ c : ℝ) (F GA GB : ℝ → ℂ) (vabs T tn : ℝ) : ℂ :=
  ambientRetrieval ρ c (windowedRecording F GA vabs T tn) (windowedRecording F GB vabs T tn)

/-- Eq. (23), Section 4.1, p. 20: the averaged retrieval for a time window of duration `T`,
`ĥ_T(x_A,x_B,ω) = ⟨ĥ(x_A,x_B,ω;T,·)⟩_T`. -/
def averagedRetrieval (ρ c : ℝ) (fT : ℝ → ℝ) (F GA GB : ℝ → ℂ) (vabs T : ℝ) : ℂ :=
  windowAvg fT (fun τ => windowedRetrieval ρ c F GA GB vabs T τ)

/-- Eq. (24), Section 4.1, p. 20: the random-windowing averaging kernel
`⟨χχ⟩_T(x',x'') = ⟨χ_{|x'-x_n| ≤ T|v|}(x') χ_{|x''-x_n| ≤ T|v|}(x'')⟩_T`, `x_n = |v| t_n`. -/
def windowKernel (fT : ℝ → ℝ) (vabs T x' x'' : ℝ) : ℝ :=
  windowAvg fT (fun τ => (if |x' - vabs * τ| ≤ T * vabs then (1 : ℝ) else 0) *
    (if |x'' - vabs * τ| ≤ T * vabs then (1 : ℝ) else 0))

/-- Eq. (27), Section 4.2, p. 21: the density `f_T = 1/(2T)` of window centres `t_n` uniformly
distributed on `D = [t₀ - T, t₀ + T]` (and `0` outside `D`). -/
def uniformWindowDensity (t0 T : ℝ) (τ : ℝ) : ℝ :=
  Set.indicator (Set.Icc (t0 - T) (t0 + T)) (fun _ => 1 / (2 * T)) τ

/-- The Heaviside function `Θ` of eqs. (28) and (A10): `Θ(s) = 1` for `s ≥ 0` and `0` for `s < 0`
(the convention of eq. (A10), p. 33). -/
def heaviside (s : ℝ) : ℝ := if 0 ≤ s then 1 else 0

/-- Section 4.2, p. 21: the boxcar function of height one and width `w`, centred at `0`. -/
def boxcar (w y : ℝ) : ℝ := Set.indicator (Set.Icc (-(w / 2)) (w / 2)) (fun _ => (1 : ℝ)) y

/-- The right-hand side of eq. (28), Section 4.2, p. 21, as a function of `L = T|v|` and of the
discrepancy `d = |x' - x''|`: `(d + L) Θ(d + L) + (d - L) Θ(d - L) - 2 d Θ(d)`. -/
def tentKernel (L d : ℝ) : ℝ :=
  (d + L) * heaviside (d + L) + (d - L) * heaviside (d - L) - 2 * d * heaviside d

/-! ### Appendix A: moving point source -/

/-- Eq. (A8), Appendix A, p. 33: `q₁(t,x,v) = (c² t - x·v)/(c² - |v|²)`. -/
def q1 (c t : ℝ) (x v : Plane) : ℝ := (c ^ 2 * t - inner ℝ x v) / (c ^ 2 - ‖v‖ ^ 2)

/-- Eq. (A9), Appendix A, p. 33: `q₂(t,x,v) = q₁(t,x,v)² - (c² t² - |x|²)/(c² - |v|²)`. -/
def q2 (c t : ℝ) (x v : Plane) : ℝ := q1 c t x v ^ 2 - (c ^ 2 * t ^ 2 - ‖x‖ ^ 2) / (c ^ 2 - ‖v‖ ^ 2)

/-- Eq. (A11), Appendix A, p. 33: the emission time `t̊ = q₁(t,x,v) - √q₂(t,x,v)` of the wave
recorded at `x` at time `t`, for a source at position `v t'` at time `t'`. -/
def emissionTime (c t : ℝ) (x v : Plane) : ℝ := q1 c t x v - Real.sqrt (q2 c t x v)

/-- The Bessel function of the first kind of order zero,
`J₀(z) = ∑_{k ≥ 0} (-1)^k (z/2)^{2k} / (k!)²` (DLMF 10.2.2). The paper uses it through the Hankel
function `𝓗₀⁽¹⁾` of eq. (A12), p. 33, without defining it. -/
def besselJ0 (z : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k * (z / 2) ^ (2 * k) / ((Nat.factorial k : ℝ) ^ 2)

/-- The Bessel function of the second kind of order zero, for `z > 0`,
`Y₀(z) = (2/π)(ln(z/2) + γ) J₀(z) + (2/π) ∑_{k ≥ 1} (-1)^{k+1} H_k (z²/4)^k / (k!)²`, with `H_k` the
harmonic numbers and `γ` the Euler–Mascheroni constant (DLMF 10.8.2). Used through eq. (A12). -/
def besselY0 (z : ℝ) : ℝ :=
  2 / Real.pi * (Real.log (z / 2) + Real.eulerMascheroniConstant) * besselJ0 z +
    2 / Real.pi * ∑' k : ℕ, (-1 : ℝ) ^ k * (harmonic (k + 1) : ℝ) * (z ^ 2 / 4) ^ (k + 1) /
      ((Nat.factorial (k + 1) : ℝ) ^ 2)

/-- The Hankel function of the first kind of order zero, `𝓗₀⁽¹⁾(z) = J₀(z) + i Y₀(z)` for real
`z > 0` (DLMF 10.4.3), as in eq. (A12), Appendix A, p. 33. -/
def hankel1Zero (z : ℝ) : ℂ := (besselJ0 z : ℂ) + Complex.I * (besselY0 z : ℂ)

/-- The Hankel function of the first kind of order one, `𝓗₁⁽¹⁾ = -(𝓗₀⁽¹⁾)'` (DLMF 10.6.2), as in
eq. (A14), Appendix A, p. 34. -/
def hankel1One (z : ℝ) : ℂ := -deriv hankel1Zero z

/-- Eq. (A12), Appendix A, p. 33, as printed: the complex potential of a monochromatic point source
of angular frequency `ω̃` moving with velocity `v`,
`φ(t,x,v) = i e^{-i ω̃ q₁(t,x,v)} 𝓗₀⁽¹⁾(ω̃ √q₂(t,x,v)) / (4 c √(c² - |v|²))`. -/
def potentialA12 (c wt t : ℝ) (x v : Plane) : ℂ :=
  Complex.I * Complex.exp (-(Complex.I * ((wt * q1 c t x v : ℝ) : ℂ))) /
      ((4 * c * Real.sqrt (c ^ 2 - ‖v‖ ^ 2) : ℝ) : ℂ) *
    hankel1Zero (wt * Real.sqrt (q2 c t x v))

/-- Eq. (A14), Appendix A, p. 34, as printed, with `M = |v|/c` and `t_x = |x|/c` (eq. (A13)):
`p(t,x,M) = Re{ -(i ρ ω̃)/(4 c² (1-M²)^{3/2}) e^{-i ω̃ t/(1-M²)}
  [ M² t/R 𝓗₁⁽¹⁾(ω̃ R/(1-M²)) + i 𝓗₀⁽¹⁾(ω̃ R/(1-M²)) ] }`, `R = √(M² t² + (1-M²) t_x²)`. -/
def pressureA14 (ρ c wt M tx t : ℝ) : ℝ :=
  let R := Real.sqrt (M ^ 2 * t ^ 2 + (1 - M ^ 2) * tx ^ 2)
  (-(Complex.I * ((ρ * wt / (4 * c ^ 2 * (1 - M ^ 2) ^ ((3 : ℝ) / 2)) : ℝ) : ℂ)) *
      Complex.exp (-(Complex.I * ((wt / (1 - M ^ 2) * t : ℝ) : ℂ))) *
      (((M ^ 2 * t / R : ℝ) : ℂ) * hankel1One (wt / (1 - M ^ 2) * R) +
        Complex.I * hankel1Zero (wt / (1 - M ^ 2) * R))).re

/-- Eq. (A21), Appendix A.1, p. 36: the instantaneous phase
`ph_x(t') = (ω + ω̃) t' + (ω/c) |x - v t'| - π/4` of the integrand of eq. (A20). -/
def dopplerPhase (c ω wt : ℝ) (x v : Plane) (t' : ℝ) : ℝ :=
  (ω + wt) * t' + ω / c * ‖x - t' • v‖ - Real.pi / 4

/-- Eq. (5), Section 2, p. 7, and eq. (A23): `cos θ_x(t')`, where `θ_x(t')` is the angle between
the line from the instantaneous source position `v t'` to the receiver `x` and the source line `S`,
oriented by the direction of motion `v` (as in eq. (A22): `(x - v t')/|x - v t'| · v = |v| cos θ`). -/
def cosTheta (x v : Plane) (t' : ℝ) : ℝ := inner ℝ (x - t' • v) v / (‖x - t' • v‖ * ‖v‖)

/-- Eq. (5), Section 2, p. 7 (= eq. (A23), p. 36): the recorded instantaneous frequency
`ω̆(x,t') = ω̃ / (1 - (|v|/c) cos θ_x(t'))`. -/
def recordedFrequency (c wt : ℝ) (x v : Plane) (t' : ℝ) : ℝ :=
  wt / (1 - ‖v‖ / c * cosTheta x v t')

/-! ### Appendices A.2 and B: random-phase broadband source -/

/-- Eq. (A27), Appendix A.2, p. 37: the source signature
`F(t'; θ) = ∑_{ω̃ ∈ Ω̃} c_ω̃ cos(ω̃ t' + θ_ω̃)` of a broadband source emitting the frequencies
`w i` with coefficients `a i` and phases `θ i`. -/
def sourceSignature {ι : Type*} [Fintype ι] (w a θ : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, a i * Real.cos (w i * t + θ i)

/-- Section 3, p. 12, and Appendix B, p. 38: the law `Unif(0, 2π)` of a random phase. -/
def uniformPhase : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume.restrict (Set.Ico 0 (2 * Real.pi))

/-- Appendix B, p. 38: the regular partition `Ω̃ = {ω̃_j}_{j=1}^{N}` of the band
`[ω̃_min, ω̃_max]` with spacing `Δ_ω̃ = (ω̃_max - ω̃_min)/N`, `ω̃_j = ω̃_min + j Δ_ω̃` (here
`j = 0, …, N-1` stands for the paper's `j = 1, …, N`). -/
def bandGrid (wmin wmax : ℝ) (N : ℕ) (j : Fin N) : ℝ :=
  wmin + ((j : ℕ) + 1 : ℝ) * (wmax - wmin) / N

end Arxiv2105_07250


