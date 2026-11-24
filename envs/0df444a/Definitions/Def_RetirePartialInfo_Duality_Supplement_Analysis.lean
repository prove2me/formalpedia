-- Prove2me | Definitions.Def_RetirePartialInfo_Duality_Supplement_Analysis
-- name    : RetirePartialInfo_Duality_Supplement_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:18:34.08293+00:00
-- url     : https://prove2.me/theorems/85cb4141-79ad-458d-b745-75ecdd9fc5d2
-- title:
--   §3.1, pp.16–17 — HMM coefficients, CRRA utility, weak derivatives, global/local Sobolev spaces and PDE/VI
-- statement:
--   Let $a=(T,T_1,r,\sigma,\xi,\beta,\ell,\mu_1,\mu_2,\lambda_1,\lambda_2,\gamma)$ contain the financial and hidden-regime parameters. The standing restrictions are $\mu_1>\mu_2$, $\lambda_i>0$, $\gamma>0$, $\gamma\ne1$, together with the immutable base financial parameters, which permit either sign of $r\ne0$ and $\xi=0$. The utilities are $U_i(c)=c^{1-\gamma}/(1-\gamma)$; their conjugates use the published supremum definition, not a stipulated formula.
--
--   For $\mathcal M_h=[0,h)\times(0,\infty)\times(0,1)$, define genuine global unweighted and local $W_q^{1,2,2}$ spaces using the published distributional weak derivatives and the seven orders $0,t,y,p,yy,pp,yp$. Global membership includes integrability of the function itself. The continuous classes include one-sided time endpoint regularity.
--
--   $$\widehat\theta(p)=\frac{\mu_1-r}{\sigma}p+\frac{\mu_2-r}{\sigma}(1-p),\qquad g(t,y)=yb(t)+\frac\ell\beta(1-e^{\beta(t-T_1)}).$$
--
--   The file defines the full rank-one generator, PDE (30), weak VI (32), and Appendix A's homogeneous profile. These are equations to solve, not predicates containing solvability or the desired estimates.
--
--   **Formalization Note** All finite real $q\ge1$ are retained. The stray $p$ exponent and absent $1/q$ norm root on p.16 are read with the conventional common exponent $q$; no global-to-local change is made in the counterexample targets.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), pp. 15–20, (22)–(23), (29)–(32), Theorems 3.1–3.2

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_HunterPDE_Shared_WeakDeriv

open MeasureTheory Set Filter
open scoped Topology ENNReal

set_option autoImplicit false

namespace RetirePartialInfo.Duality.Supplement

/-- Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553
(version of June 8, 2021), pp. 15–20, (22)–(23), (29)–(32), §3.2.
HMM and CRRA data. All restrictions are in `Admissible`, not assumptions of solvability.
**Formalization Note.** Both signs of the risk premia and both CRRA regimes are allowed;
the immutable base `Params` supplies the financial parameters. -/
structure Data where
  par : Params
  μ1 : ℝ
  μ2 : ℝ
  rate1 : ℝ
  rate2 : ℝ
  γ : ℝ

def Data.Admissible (a : Data) : Prop :=
  a.μ2 < a.μ1 ∧ 0 < a.rate1 ∧ 0 < a.rate2 ∧ 0 < a.γ ∧ a.γ ≠ 1

noncomputable def theta1 (a : Data) : ℝ := (a.μ1 - a.par.r) / a.par.σ
noncomputable def theta2 (a : Data) : ℝ := (a.μ2 - a.par.r) / a.par.σ
noncomputable def thetaHat (a : Data) (p : ℝ) : ℝ := (theta1 a - theta2 a) * p + theta2 a
noncomputable def beliefVol (a : Data) (p : ℝ) : ℝ := (theta1 a - theta2 a) * p * (1 - p)
noncomputable def beliefDrift (a : Data) (p : ℝ) : ℝ := a.rate2 - (a.rate1 + a.rate2) * p
noncomputable def phi (a : Data) : ℝ := 1 - 1 / a.γ
noncomputable def crra (a : Data) (_t c : ℝ) : ℝ := c ^ (1 - a.γ) / (1 - a.γ)

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Value := ℝ → ℝ → ℝ → ℝ

def flatten (v : Value) (z : Space) : ℝ := v (z 0) (z 1) (z 2)
def state (t y p : ℝ) : Space := WithLp.toLp 2 ![t, y, p]

/-- The time face at zero is included as on p.16. It has zero Lebesgue measure.
The time closure does not include y=0 or p=0,1. -/
def domain (h : ℝ) : Set Space := {z | z 0 ∈ Ico 0 h ∧ 0 < z 1 ∧ z 2 ∈ Ioo 0 1}
def timeClosure (h : ℝ) : Set Space := {z | z 0 ∈ Icc 0 h ∧ 0 < z 1 ∧ z 2 ∈ Ioo 0 1}

noncomputable def dt (h : ℝ) (v : Value) (t y p : ℝ) : ℝ :=
  derivWithin (fun s => v s y p) (Icc 0 h) t
noncomputable def dy (v : Value) (t y p : ℝ) : ℝ := deriv (fun z => v t z p) y
noncomputable def dp (v : Value) (t y p : ℝ) : ℝ := deriv (fun z => v t y z) p
noncomputable def dyy (v : Value) : Value := dy (dy v)
noncomputable def dpp (v : Value) : Value := dp (dp v)
noncomputable def dyp (v : Value) : Value := dy (dp v)

def C1 (h : ℝ) (v : Value) : Prop := ContDiffOn ℝ 1 (flatten v) (timeClosure h)

/-- Genuine C^{1,2,2} regularity, including one-sided time endpoint regularity.
Spatial second and mixed derivatives exist and extend continuously to the time faces.
No differentiability of a spatial derivative with respect to time is imposed. -/
def C122 (h : ℝ) (v : Value) : Prop :=
  C1 h v ∧
  (∀ z ∈ timeClosure h,
    DifferentiableAt ℝ (fun y => dy v (z 0) y (z 2)) (z 1) ∧
    DifferentiableAt ℝ (fun p => dp v (z 0) (z 1) p) (z 2) ∧
    DifferentiableAt ℝ (fun y => dp v (z 0) y (z 2)) (z 1)) ∧
  ContinuousOn (flatten (dyy v)) (timeClosure h) ∧
  ContinuousOn (flatten (dpp v)) (timeClosure h) ∧
  ContinuousOn (flatten (dyp v)) (timeClosure h)

def orders : Finset (Fin 3 → ℕ) :=
  {![0,0,0], ![1,0,0], ![0,1,0], ![0,0,1], ![0,2,0], ![0,0,2], ![0,1,1]}

/-- Chen–Jeon–Wong, p.16: global unweighted W_q^{1,2,2}.
**Formalization Note.** Weak derivatives use the published Hunter distributional definition
with smooth compactly supported tests; the space includes the zeroth-order L^q term.
The isolated p exponent on |∂y V| and missing 1/q norm root on p.16 are read as typography:
all seven terms have exponent q. This does not change the global integrability requirement.
`q` is finite real, as in the source. No local/weighted replacement is made. -/
def GlobalW (h q : ℝ) (v : Value) : Prop :=
  1 ≤ q ∧ ∀ α ∈ orders, ∃ g : Space → ℝ,
    HunterPDE.Shared.HasWeakDeriv (domain h) α (flatten v) g ∧
    MemLp g (ENNReal.ofReal q) (volume.restrict (domain h))

def LocalW (h q : ℝ) (v : Value) : Prop :=
  1 ≤ q ∧ ∀ K : Set Space, IsCompact K → K ⊆ domain h →
    ∀ α ∈ orders, ∃ g : Space → ℝ,
      HunterPDE.Shared.HasWeakDeriv (domain h) α (flatten v) g ∧
      MemLp g (ENNReal.ofReal q) (volume.restrict K)

/-- The rank-one degenerate generator (29), p.16; the negative mixed and killing
terms are retained. There is no ellipticity assumption. -/
noncomputable def generator (a : Data) (v : Value) (t y p : ℝ) : ℝ :=
  1/2 * thetaHat a p ^ 2 * y ^ 2 * dyy v t y p +
  1/2 * beliefVol a p ^ 2 * dpp v t y p -
  thetaHat a p * beliefVol a p * y * dyp v t y p +
  (a.par.β - a.par.r) * y * dy v t y p +
  beliefDrift a p * dp v t y p - a.par.β * v t y p

def Growth (h : ℝ) (v : Value) : Prop :=
  ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ z ∈ domain h,
    |dy v (z 0) (z 1) (z 2)| + |dp v (z 0) (z 1) (z 2)| ≤ C * (1 + (z 1) ^ (-κ))

/-- PDE (30), p.17. The forcing/terminal data are the published supremum conjugate
of the actual CRRA utility, not an assumed conjugacy identity. -/
def PDE30 (a : Data) (v : Value) : Prop :=
  (∀ z ∈ domain a.par.T,
    -dt a.par.T v (z 0) (z 1) (z 2) - generator a v (z 0) (z 1) (z 2) =
      Utilde (crra a) (z 0) (z 1)) ∧
  ∀ y > 0, ∀ p ∈ Ioo (0 : ℝ) 1, v a.par.T y p = Utilde (crra a) a.par.T y

noncomputable def laborCost (a : Data) (t : ℝ) : ℝ :=
  (1 - Real.exp (a.par.β * (t - a.par.T1))) * a.par.ℓ / a.par.β
noncomputable def obstacle (a : Data) (t y : ℝ) : ℝ := y * b a.par t + laborCost a t

noncomputable def weakJet (h : ℝ) (v : Value) (α : Fin 3 → ℕ) (z : Space) : ℝ :=
  HunterPDE.Shared.weakDeriv (domain h) α (flatten v) z

noncomputable def weakGenerator (a : Data) (f : Value) (z : Space) : ℝ :=
  1/2 * thetaHat a (z 2) ^ 2 * (z 1)^2 * weakJet a.par.T1 f ![0,2,0] z +
  1/2 * beliefVol a (z 2)^2 * weakJet a.par.T1 f ![0,0,2] z -
  thetaHat a (z 2) * beliefVol a (z 2) * z 1 * weakJet a.par.T1 f ![0,1,1] z +
  (a.par.β - a.par.r) * z 1 * weakJet a.par.T1 f ![0,1,0] z +
  beliefDrift a (z 2) * weakJet a.par.T1 f ![0,0,1] z - a.par.β * flatten f z

/-- VI (32), p.17. Local weak derivatives must exist separately; the a.e. equation
does not establish that existence. No estimates or solvability are part of this predicate. -/
def VI32 (a : Data) (f : Value) : Prop :=
  (∀ᵐ z ∂volume.restrict (domain a.par.T1),
    min (-weakJet a.par.T1 f ![1,0,0] z - weakGenerator a f z)
      (flatten f z - obstacle a (z 0) (z 1)) = 0) ∧
  ∀ y > 0, ∀ p ∈ Ioo (0 : ℝ) 1, f a.par.T1 y p = 0

/-- The CRRA homogeneous profile used in Appendix A, p.35. -/
noncomputable def powerProfile (a : Data) (w : ℝ → ℝ → ℝ) : Value :=
  fun t y p => -(y ^ phi a) * w t p / phi a

end RetirePartialInfo.Duality.Supplement


