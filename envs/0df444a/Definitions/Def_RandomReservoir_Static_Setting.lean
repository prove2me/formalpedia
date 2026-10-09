-- Prove2me | Definitions.Def_RandomReservoir_Static_Setting
-- name    : RandomReservoir_Static_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:50.022777+00:00
-- url     : https://prove2.me/theorems/e2290df3-e6f6-45cc-9c94-82d4cc4dbebf
-- title:
--   Notation (p. 30), §4.1 and Theorem 1 (pp. 36–38), proof (pp. 39–40) — ReLU network (14), sampling law π, F_π, conditions (i)/(ii), g_j, C*_j, h̄ and the densities of α
-- statement:
--   This file fixes the objects of Section 4.1 and Theorem 1. Throughout, $\mathcal X$ is a separable real Hilbert space with inner product $\langle\cdot,\cdot\rangle$ and its Borel $\sigma$-algebra.
--
--   1. **Rectifier.** $\sigma(x)=\max(x,0)$ for $x\in\mathbb R$.
--   2. **Random ReLU network (14).** For inner weights $\theta_i=(A_i,\zeta_i)\in\mathcal X\times\mathbb R$, $i=1,\dots,N$, and a readout matrix $W\in\mathbb M_{m,N}$,
--   $$H_W^{A,\zeta}(z)_j=\sum_{i=1}^N W_{ji}\,\sigma\big(\langle A_i,z\rangle+\zeta_i\big),\qquad z\in\mathcal X,\ j=1,\dots,m,$$
--   that is, $H_W^{A,\zeta}(z)=W\sigma(Az+\zeta)$ with $Az=(\langle A_1,z\rangle,\dots,\langle A_N,z\rangle)$.
--   3. **Squared error.** $\|y-y'\|^2=\sum_{j=1}^m (y_j-y'_j)^2$, the squared Euclidean norm on $\mathbb R^m$.
--   4. **Sampling law.** $\pi=\pi_{\mathcal X}\otimes(\pi_{\mathbb R}(x)\,dx)$ on $\mathcal X\times\mathbb R$, for a measure $\pi_{\mathcal X}$ on $\mathcal X$ and a density $\pi_{\mathbb R}$ on $\mathbb R$.
--   5. **The function $F_\pi$.** $F_\pi(x)=2\int_{-x}^{0}\frac{1}{\pi_{\mathbb R}(u)}\,du$, an oriented integral, so $F_\pi(x)\le 0$ for $x<0$.
--   6. **Conditions (i) or (ii) of Theorem 1.** Either (i) $\pi_{\mathbb R}>0$ everywhere and $|F_\pi(x)|<\infty$ for all $x$, or (ii) for some $R>0$, $\pi_{\mathcal X}(\{\|w\|>R\})=0$ and $\pi_{\mathbb R}(x)>0$, $|F_\pi(x)|<\infty$ for $|x|\le\max(MR,1)$. Here $|F_\pi(x)|<\infty$ means that $1/\pi_{\mathbb R}$ is integrable on the interval between $-x$ and $0$.
--   7. **The density $g$.** For a finite measure $\nu$ (in Theorem 1, $\nu=|\hat\mu_j|$ is the total variation of a complex measure) and $\nu^-(\cdot)=\nu(-\cdot)$, $g=\frac{d(\nu+\nu^-)}{d\pi_{\mathcal X}}$.
--   8. **The constant.**
--   $$C^*_j=M^2\int_{\mathcal X}F_\pi(M\|w\|)\|w\|^2g_j(w)^2\,\pi_{\mathcal X}(dw)+32\max(M^2,1)\big(F_\pi(1)-F_\pi(-1)\big)\int_{\mathcal X}\max(\|w\|^2,1)g_j(w)^2\,\pi_{\mathcal X}(dw).$$
--   9. **The signed measure $\alpha$ of the proof.** For $h:\mathcal X\to\mathbb C$ with $|h|=1$, $\bar h(w)=2\operatorname{Re}h(w)-\operatorname{Im}h(w)$, and $\alpha=\alpha_1+\alpha_2$ is the signed measure with density
--   $$k_+(w,u)=-\mathbb 1_{(-M\|w\|,0]}(u)\operatorname{Re}[e^{-iu}h(w)]+\mathbb 1_{[0,1]}(u)\bar h(w)$$
--   with respect to $\nu(dw)\,du$ plus density
--   $$k_-(w,u)=-\mathbb 1_{(-M\|w\|,0]}(u)\operatorname{Re}[e^{iu}h(-w)]-\mathbb 1_{[-1,0]}(u)\bar h(-w)$$
--   with respect to $\nu^-(dw)\,du$.
--
--   These are the objects in terms of which Theorem 1 and the steps of its proof are stated.
--
--   **Formalization Note.** The constant uses $32\max(M^2,1)$ instead of the printed $32M^2$. Read literally, the printed constant is false for small $M$: the proof's estimate (26) produces $16(M^2\|w\|^2+1)(F_\pi(1)-F_\pi(-1))$, which is bounded by $32M^2\max(\|w\|^2,1)(\dots)$ only when $M\ge1$. The two constants agree for $M\ge 1$. A complex measure $\hat\mu$ is represented in polar form, $\hat\mu(dw)=h(w)\,|\hat\mu|(dw)$ with $|h|=1$ (Rudin, *Real and Complex Analysis*, Thm 6.12, quoted on p. 39). Every finite measure $\nu$ and measurable unimodular $h$ give a complex measure with $|\hat\mu|=\nu$, so this loses no generality. The network's readout is a `Matrix (Fin m) (Fin N) ℝ`; the inner weights are pairs $(A_i,\zeta_i)$.
-- source:
--   Gonon, Grigoryeva & Ortega, Ann. Appl. Probab. 33 (2023), Notation, p. 30; §4.1, (14), pp. 36–37; Theorem 1, pp. 37–38; Proof of Theorem 1, Step 1, pp. 39–40

import Mathlib

namespace RandomReservoir.Static

open MeasureTheory

variable {𝒳 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [CompleteSpace 𝒳]
  [TopologicalSpace.SeparableSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]

/-- The rectifier (ReLU) `σ(x) = max(x, 0)`, p. 38. -/
noncomputable def relu (x : ℝ) : ℝ := max x 0

/-- The random-feature network (14), `H_W^{A,ζ}(z) = W σ(A z + ζ)`, with the inner weights
`θ i = (A_i, ζ_i) ∈ 𝒳 × ℝ`, so that `(A z + ζ)_i = ⟨A_i, z⟩ + ζ_i`, and `σ` applied componentwise. -/
noncomputable def network {m N : ℕ} (W : Matrix (Fin m) (Fin N) ℝ) (θ : Fin N → 𝒳 × ℝ) (z : 𝒳) :
    Fin m → ℝ :=
  fun j => ∑ i, W j i * relu (inner ℝ (θ i).1 z + (θ i).2)

/-- The squared Euclidean distance `‖y − y'‖²` in `ℝ^m` (not the sup norm of `Fin m → ℝ`). -/
def sqErr {m : ℕ} (y y' : Fin m → ℝ) : ℝ := ∑ j, (y j - y' j) ^ 2

/-- The sampling law `π = π_𝒳 ⊗ (π_ℝ(x) dx)` of one row `(A_i, ζ_i)`, Theorem 1, p. 37. -/
noncomputable def samplingLaw (πX : Measure 𝒳) (πR : ℝ → ℝ) : Measure (𝒳 × ℝ) :=
  πX.prod (volume.withDensity (fun x => ENNReal.ofReal (πR x)))

/-- `F_π(x) = 2 ∫_{−x}^{0} 1/π_ℝ(u) du`, Theorem 1, p. 37 (an oriented interval integral, so
`F_π(x) < 0` for `x < 0`). -/
noncomputable def Fπ (πR : ℝ → ℝ) (x : ℝ) : ℝ := 2 * ∫ u in (-x)..0, 1 / πR u

/-- The conditions (i) or (ii) of Theorem 1, p. 37, on the sampling law `π = π_𝒳 ⊗ (π_ℝ(x) dx)`.
"`|F_π(x)| < ∞`" is the interval integrability of the nonnegative function `1/π_ℝ` on `[−x, 0]`. -/
def SamplingCondition (M : ℝ) (πX : Measure 𝒳) (πR : ℝ → ℝ) : Prop :=
  ((∀ x, 0 < πR x) ∧ ∀ x, IntervalIntegrable (fun u => 1 / πR u) volume (-x) 0) ∨
  (∃ R : ℝ, 0 < R ∧ πX {w | R < ‖w‖} = 0 ∧
    ∀ x : ℝ, |x| ≤ max (M * R) 1 →
      0 < πR x ∧ IntervalIntegrable (fun u => 1 / πR u) volume (-x) 0)

/-- `g = d(|μ̂| + |μ̂|⁻)/dπ_𝒳`, Theorem 1, p. 37, where `ν = |μ̂|` is the total variation measure
of the complex measure `μ̂` and `ν⁻(·) = ν(−·)` is its image under `w ↦ −w`. -/
noncomputable def gdens (ν πX : Measure 𝒳) (w : 𝒳) : ℝ :=
  ((ν + ν.map (fun w => -w)).rnDeriv πX w).toReal

/-- The constant `C*_j` of Theorem 1, p. 38, with the coefficient `32·max(M², 1)` in place of the
printed `32 M²` (the two agree for `M ≥ 1`; see the Formalization Note). -/
noncomputable def CstarJ (M : ℝ) (πX : Measure 𝒳) (πR : ℝ → ℝ) (g : 𝒳 → ℝ) : ℝ :=
  M ^ 2 * ∫ w, Fπ πR (M * ‖w‖) * ‖w‖ ^ 2 * g w ^ 2 ∂πX
    + 32 * max (M ^ 2) 1 * (Fπ πR 1 - Fπ πR (-1)) * ∫ w, max (‖w‖ ^ 2) 1 * g w ^ 2 ∂πX

/-- `h̄(w) = 2 Re[h(w)] − Im[h(w)]`, Proof of Theorem 1, Step 1, p. 39. -/
def hbar (h : 𝒳 → ℂ) (w : 𝒳) : ℝ := 2 * (h w).re - (h w).im

/-- The density of `α₁ + α₂` (Proof of Theorem 1, p. 40) with respect to `|μ̂|(dw) du`:
`−𝟙_{(−M‖w‖,0]}(u) Re[e^{−iu} h(w)] + 𝟙_{[0,1]}(u) h̄(w)`. -/
noncomputable def kPlus (M : ℝ) (h : 𝒳 → ℂ) (p : 𝒳 × ℝ) : ℝ :=
  -(Set.indicator (Set.Ioc (-(M * ‖p.1‖)) 0) (fun _ => (1 : ℝ)) p.2) *
      (Complex.exp (-(Complex.I * (p.2 : ℂ))) * h p.1).re
    + Set.indicator (Set.Icc 0 1) (fun _ => (1 : ℝ)) p.2 * hbar h p.1

/-- The density of `α₁ + α₂` (Proof of Theorem 1, p. 40) with respect to `|μ̂|⁻(dw) du`:
`−𝟙_{(−M‖w‖,0]}(u) Re[e^{iu} h(−w)] − 𝟙_{[−1,0]}(u) h̄(−w)`. -/
noncomputable def kMinus (M : ℝ) (h : 𝒳 → ℂ) (p : 𝒳 × ℝ) : ℝ :=
  -(Set.indicator (Set.Ioc (-(M * ‖p.1‖)) 0) (fun _ => (1 : ℝ)) p.2) *
      (Complex.exp (Complex.I * (p.2 : ℂ)) * h (-p.1)).re
    - Set.indicator (Set.Icc (-1) 0) (fun _ => (1 : ℝ)) p.2 * hbar h (-p.1)

end RandomReservoir.Static


