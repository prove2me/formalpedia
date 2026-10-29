-- Prove2me | Definitions.Def_PeskirShiryaev_SequentialTesting_BoundaryClass
-- name    : PeskirShiryaev_SequentialTesting_BoundaryClass
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:54.08226+00:00
-- url     : https://prove2.me/theorems/6dd8e3b2-347b-439a-9b30-84ddba8042a0
-- title:
--   Infinite-horizon roots, boundary class and Gaussian kernels
-- statement:
--   Let $\psi(p)=(1-2p)\log(p/(1-p))$ and
--   $$v_A(p)=\frac{2\sigma^2}{\mu^2}[\psi(p)-\psi(A)]+\left[a-\frac{2\sigma^2}{\mu^2}\psi'(A)\right](p-A)+aA.$$
--   The threshold pair solves $0<A<c<B<1$, $v_A(B)=b(1-B)$ and $v_A'(B)=-b$. The lower and upper threshold definitions take the infimum and supremum of the corresponding root coordinates; existence and uniqueness are theorem conclusions.
--
--   A pair $g=(g_0,g_1)$ belongs to the boundary class if both functions are continuous on $[0,T]$, $g_0$ is nondecreasing, $g_1$ is nonincreasing, $A_*\le g_0(t)<c<g_1(t)\le B_*$ for $t<T$, and $g_0(T)=g_1(T)=c$. Write $M(p,u)=E_pH(\Pi^p_u)$ and $K(p,u,q)=P_p(\Pi^p_u\le q)$. The coupled equations are
--   $$M(g_i(t),T-t)=H(g_i(t))+\int_0^{T-t}[K(g_i(t),u,g_0(t+u))-K(g_i(t),u,g_1(t+u))]\,du.$$
--   The module also defines the two standard-normal integrals of (21.2.47). If $\Phi$ is the standard normal distribution function, its positive-time Gaussian transition expression with coefficient $r$ is
--   $$Q_r(p,u,q)=p\Phi\!\left(\frac{\log\frac{q(1-p)}{p(1-q)}}{r\sqrt u}-\frac{r\sqrt u}{2}\right)+(1-p)\Phi\!\left(\frac{\log\frac{q(1-p)}{p(1-q)}}{r\sqrt u}+\frac{r\sqrt u}{2}\right).$$
--   These definitions separate the actual transition probabilities from the claimed formulas and separate solving an integral system from optimality.
--
--   **Formalization Note** Gaussian integrals use the standard normal probability measure, equivalently $\varphi(z)\,dz$. At $u=0$, $Q_r(p,0,q)=\mathbf1_{\{p\le q\}}$ is the deterministic transition, avoiding division by zero. Uniqueness of boundaries is only on $[0,T]$. The faithful formula uses $r=\mu/\sigma$ and the corrected variant uses $r=|\mu/\sigma|$.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 290–291, 299–301 / PDF pp. 307–308, 316–318, Eqs. (21.1.11)–(21.1.15), (21.2.34)–(21.2.37), (21.2.46)–(21.2.48)

import Definitions.Def_PeskirShiryaev_SequentialTesting_value

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace PeskirShiryaev.SequentialTesting

noncomputable def psi (p : ℝ) : ℝ := (1 - 2 * p) * Real.log (p / (1 - p))

noncomputable def infiniteCandidate (C : Parameters) (A p : ℝ) : ℝ :=
  2 * C.σ ^ 2 / C.μ ^ 2 * (psi p - psi A) +
    (C.a - 2 * C.σ ^ 2 / C.μ ^ 2 * deriv psi A) * (p - A) + C.a * A

/-- The transcendental system (21.1.14)-(21.1.15), with its strict domains. -/
def ThresholdPair (C : Parameters) (A B : ℝ) : Prop :=
  0 < A ∧ A < cutoff C ∧ cutoff C < B ∧ B < 1 ∧
    infiniteCandidate C A B = C.b * (1 - B) ∧
    HasDerivAt (infiniteCandidate C A) (-C.b) B

noncomputable def lowerThreshold (C : Parameters) : ℝ :=
  sInf {A : ℝ | ∃ B, ThresholdPair C A B}

noncomputable def upperThreshold (C : Parameters) : ℝ :=
  sSup {B : ℝ | ∃ A, ThresholdPair C A B}

/-- Exactly the continuous monotone class (21.2.34)-(21.2.37). Its bounds
are determined by the infinite-horizon root system, not arbitrary constants. -/
def BoundaryClass (C : Parameters) (g : Fin 2 → ℝ → ℝ) : Prop :=
  (∀ i, ContinuousOn (g i) (Icc 0 C.T)) ∧
  MonotoneOn (g 0) (Icc 0 C.T) ∧ AntitoneOn (g 1) (Icc 0 C.T) ∧
  (∀ t ∈ Ico 0 C.T, lowerThreshold C ≤ g 0 t ∧ g 0 t < cutoff C ∧
    cutoff C < g 1 t ∧ g 1 t ≤ upperThreshold C) ∧
  (∀ i, g i C.T = cutoff C) ∧
  (∀ i, ∀ t ∈ Icc 0 C.T, g i t ∈ Icc 0 1)

noncomputable def terminalMean {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (p u : ℝ) : ℝ :=
  ∫ ω, terminalLoss C (posterior E C p u.toNNReal ω) ∂prior E p

noncomputable def transitionCDF {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (p u q : ℝ) : ℝ :=
  (prior E p).real {ω | posterior E C p u.toNNReal ω ≤ q}

/-- The coupled equations (21.2.46). The two summands are lower CDF minus
upper CDF, not their sum. -/
def SolvesIntegralEquations {Ω : Type*} [MeasurableSpace Ω] (E : Model Ω)
    (C : Parameters) (g : Fin 2 → ℝ → ℝ) : Prop :=
  ∀ t ∈ Icc 0 C.T, ∀ i : Fin 2,
    terminalMean E C (g i t) (C.T - t) = terminalLoss C (g i t) +
      ∫ u in (0 : ℝ)..(C.T - t),
        transitionCDF E C (g i t) u (g 0 (t + u)) -
        transitionCDF E C (g i t) u (g 1 (t + u))

noncomputable def normalCDF (z : ℝ) : ℝ := (gaussianReal 0 1).real (Iic z)

/-- The two Gaussian integrals in (21.2.47), with the standard normal
measure replacing the density φ(z) dz. -/
noncomputable def gaussianTerminalMean (C : Parameters) (p u : ℝ) : ℝ :=
  p * (∫ z : ℝ,
    let e := Real.exp (C.μ / C.σ * z * Real.sqrt u + C.μ ^ 2 / (2 * C.σ ^ 2) * u)
    min (C.a * p * e) (C.b * (1 - p)) / (1 - p + p * e) ∂gaussianReal 0 1) +
  (1 - p) * (∫ z : ℝ,
    let e := Real.exp (C.μ / C.σ * z * Real.sqrt u - C.μ ^ 2 / (2 * C.σ ^ 2) * u)
    min (C.a * p * e) (C.b * (1 - p)) / (1 - p + p * e) ∂gaussianReal 0 1)

/-- The positive-time expression in (21.2.48), with ratio r = μ/σ in the
faithful item and |μ/σ| in the corrected variant. At zero elapsed time the
transition is a point mass, specified explicitly rather than using 1/0. -/
noncomputable def gaussianTransitionCDF (r p u q : ℝ) : ℝ :=
  if u = 0 then (if p ≤ q then 1 else 0) else
    p * normalCDF (Real.log (q / (1 - q) * ((1 - p) / p)) /
      (r * Real.sqrt u) - r * Real.sqrt u / 2) +
    (1 - p) * normalCDF (Real.log (q / (1 - q) * ((1 - p) / p)) /
      (r * Real.sqrt u) + r * Real.sqrt u / 2)

end PeskirShiryaev.SequentialTesting


