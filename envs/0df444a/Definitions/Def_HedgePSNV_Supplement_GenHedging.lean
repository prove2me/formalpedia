-- Prove2me | Definitions.Def_HedgePSNV_Supplement_GenHedging
-- name    : HedgePSNV_Supplement_GenHedging
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:53:13.05006+00:00
-- url     : https://prove2.me/theorems/bf1c6d8d-0495-5045-b19c-38c1f8b8502f
-- title:
--   Hedging problem (EC.5.4) in the general model: $\mathcal A_X$, $B(m,q)$, unhedgeable risk and Assumption EC.2
-- statement:
--   Throughout, the general model of §EC.5 holds: the asset model of §3.1 ($B$, $X$, $\mu$, $\sigma$, $\mathcal F\supseteq\mathcal G$, $Z$, $\mathbb P^M$) with a $K$-dimensional Brownian motion $\tilde B$ independent of $B$, $J$ operational factors $A_T=C_T+\tilde\Sigma\tilde B_T$ (EC.5.1) with $C$ adapted to $\mathcal G$ and increments driven by $X$, decisions $q\in\mathbb R^n$ with $q\ge0$, and an operational payoff $H_T(q,a)$.
--
--   **Admissible strategies and minimal variance.** $\mathcal M_X$ and $\mathcal A_X$ are as in (EC.7.13), (EC.7.15): $(\theta,\chi)\in\mathcal A_X$ when $\theta$ is progressive, $\chi=\int\theta\,dX$ on $[0,T]$, $\chi_T\in L^2(\mathbb P)$ and $\chi$ is a martingale under every $\bar{\mathbb P}^M\in\mathcal M_X$. The hedging problem (EC.5.4) has value
--   $$
--   B(m,q)=\inf\big\{\mathrm{Var}[H_T(q,A_T)+\chi_T]:(\theta,\chi)\in\mathcal A_X,\ \mathbb E[H_T(q,A_T)+\chi_T]=m\big\}\in[0,\infty].
--   $$
--
--   **Unhedgeable risk.** If $V_t(q)=V_0(q)+\int_0^t\xi_s\,dX_s+\int_0^t\delta_s\cdot d\tilde B_s$ (EC.10.2), with $\xi,\delta$ progressive, then $\delta$ is a $d\tilde B$-integrand of $V(q)$, and its squared unhedgeable risk is
--   $$
--   \Psi(q)=\int_0^T\mathbb E\Big[\frac{Z_t}{Z^M_t}\|\delta_t\|^2\Big]dt ,
--   $$
--   the second term of (EC.10.6), with $\|\cdot\|$ the Euclidean norm.
--
--   **Assumption EC.2** (strict reading). For a family $\delta(q)$ of $d\tilde B$-integrands, $0\le q\le q'$ and $q\ne q'$ imply $\Psi(q)<\Psi(q')$.
--
--   **Formalization Note** $B$ and $\Psi$ take values in $[0,\infty]$. The integrands of a representation are unique up to null sets, so $\Psi$ does not depend on the representation; the gradient formula (EC.10.3) is not used. Assumption EC.2 is read strictly, as the paper says of the newsvendor's unhedgeable risk (“strictly increases”, p.ec48). Under the weak reading Theorem EC.1 fails: $H_T(q,a)=h(q)+a_1$ with $h$ concave and flat on $[q^*,q^*+1]$ has constant $\Psi$, and when $\mathbb E[C_{1,T}]>\mathbb E^M[C_{1,T}]$ the point $q^*+1$ minimizes $B(m,\cdot)$. The square root is increasing, so the squared risk is compared.
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, (EC.5.4), p.ec15; Assumption EC.2, p.ec16; (EC.10.2), (EC.10.6), p.ec59; (EC.7.13), (EC.7.15), p.ec29

import Mathlib
import Definitions.Def_HedgePSNV_Supplement_GenModel

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV.Supplement

open HedgePSNV

namespace GenModel

variable {n J K : ℕ} {g : GenParams n J K} {Ω : Type*} [m : MeasurableSpace Ω]

/-- The set `M_X` of equivalent martingale measures with square-integrable density,
arXiv:2201.01026v4, (EC.7.13), p.ec29, in the general model (same asset model, p.ec61):
`M_X := {P̄^M ∼ P : dP̄^M/dP ∈ L²(P), X_t is a P̄^M-martingale}` on `[0, T]`, with respect to `F`. -/
def MX (M : GenModel g Ω) : Set (Measure Ω) :=
  {Q | IsProbabilityMeasure Q ∧ Q ≪ M.P ∧ M.P ≪ Q ∧
    MemLp (fun ω => (Q.rnDeriv M.P ω).toReal) 2 M.P ∧ IsMartingaleOn g.T M.F Q M.X}

/-- The admissible hedging strategies `A_X` of (EC.5.3)–(EC.5.4), arXiv:2201.01026v4, p.ec15
(defined in (EC.7.15), p.ec29), with the gains process attached: `(θ, χ) ∈ A_X` when `θ` is
progressively measurable with respect to `F`, `χ = ∫_0^· θ dX` on `[0, T]`, `χ_T ∈ L²(P)`, and `χ`
is a `P̄^M`-martingale on `[0, T]` for every `P̄^M ∈ M_X`.

**Formalization Note** Field by field the published `HedgePSNV.Model.AX`. -/
def AX (M : GenModel g Ω) : Set ((ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) :=
  {θχ | IsStronglyProgressive M.F θχ.1 ∧ StronglyAdapted M.F θχ.2 ∧ M.IsXGains θχ.1 θχ.2 ∧
    MemLp (θχ.2 g.T) 2 M.P ∧
    ∀ Q ∈ M.MX, IsMartingaleOn g.T M.F Q θχ.2}

/-- The optimal value of the hedging problem (EC.5.4), arXiv:2201.01026v4, p.ec15:
`B(m,q) := min_{ϑ ∈ A_X} Var[H_T(q, A_T) + χ_T(ϑ)]` s.t. `E[H_T(q, A_T) + χ_T(ϑ)] = m`.

**Formalization Note** As the published `HedgePSNV.Model.Bval`: an infimum in `ℝ≥0∞` of the
extended variance, so that an empty feasible set gives `⊤`; attainment is part of Theorem
EC.2. -/
noncomputable def Bval (M : GenModel g Ω) (mean : ℝ) (q : Fin n → ℝ) : ℝ≥0∞ :=
  ⨅ θχ ∈ M.AX, ⨅ (_ : ∫ ω, (M.Hq q ω + θχ.2 g.T ω) ∂M.P = mean),
    evariance (fun ω => M.Hq q ω + θχ.2 g.T ω) M.P

/-- `δ` is the `dB̃`-integrand of a martingale representation (EC.10.2) of `V(q)`,
arXiv:2201.01026v4, Lemma EC.11, p.ec59: there are an `F`-progressive `ξ` with gains process
`χξ = ∫ ξ dX` and the Itô integral `L = ∫ δ · dB̃` such that, for every `t ≤ T`,
`V_t(q) = V_0(q) + ∫_0^t ξ_s dX_s + ∫_0^t δ_s · dB̃_s` almost surely, with `δ` `F`-progressive.

**Formalization Note** The integrands of the representation are unique up to
`dt ⊗ dP`-null sets, so every quantity built from `δ` below (the unhedgeable risk) does not
depend on the representation chosen. The paper's gradient formula (EC.10.3) for `δ` is not
used. -/
def IsBtIntegrand (M : GenModel g Ω) (q : Fin n → ℝ) (δ : ℝ≥0 → Ω → (Fin K → ℝ)) : Prop :=
  IsStronglyProgressive M.F δ ∧
    ∃ ξ χξ L : ℝ≥0 → Ω → ℝ, IsStronglyProgressive M.F ξ ∧ M.IsXGains ξ χξ ∧
      M.IsBtIntegral δ L ∧
      ∀ t : ℝ≥0, t ≤ g.T → M.V q t =ᵐ[M.P] fun ω => M.V0 q + χξ t ω + L t ω

/-- The squared unhedgeable risk `∫_0^T E[(Z_t/Z^M_t) ‖δ_t‖²] dt`, the second term of (EC.10.6),
arXiv:2201.01026v4, p.ec59 (and p.ec16: "the unhedgeable risk is a function of the operational
decision q"), for the `dB̃`-integrand `δ` of the representation of `V(q)`; `‖·‖` is the Euclidean
norm on `ℝᴷ`.

**Formalization Note** A lower Lebesgue integral in `ℝ≥0∞` of `ofReal` of the integrand (which
is almost surely nonnegative, Theorem EC.2). The squared Euclidean norm is written as
`Σ_k δ_k²`, since the default norm on `Fin K → ℝ` is the sup norm. -/
noncomputable def unhedgeableRiskSq (M : GenModel g Ω) (δ : ℝ≥0 → Ω → (Fin K → ℝ)) : ℝ≥0∞ :=
  ∫⁻ u in Set.Icc (0 : ℝ) (g.T : ℝ), ∫⁻ ω,
    ENNReal.ofReal (M.Z u.toNNReal ω / M.ZM u.toNNReal ω * ∑ k : Fin K, δ u.toNNReal ω k ^ 2)
      ∂M.P

/-- Assumption EC.2, arXiv:2201.01026v4, p.ec16: "The unhedgeable risk increases in each
component of q", for a family `δ q` of `dB̃`-integrands of the representations of `V(q)`: read
strictly, for decisions `0 ≤ q ≤ q'` with `q ≠ q'` the (squared) unhedgeable risk of `q` is
strictly smaller than that of `q'`.

**Formalization Note** Strict reading. The paper's model case is the newsvendor's unhedgeable
risk, which "strictly increases in both P and R" (proof of Proposition 7, p.ec48). Under the
weak reading Theorem EC.1 is false: `H_T(q,a) = h(q) + a_1` with `h` concave and constant on
`[q*, q* + 1]` satisfies Assumption EC.1 and has a constant unhedgeable risk, and when
`E[C_{1,T}] > E^M[C_{1,T}]` every point of the flat arg max of `h`, including `q* + 1 > q*`,
minimizes `B(m, ·)`. Increasing in each component separately and strictly is equivalent to this
order form. The square root is increasing, so the squared risk is used. -/
def AssumptionEC2 (M : GenModel g Ω) (δ : (Fin n → ℝ) → ℝ≥0 → Ω → (Fin K → ℝ)) : Prop :=
  ∀ q q' : Fin n → ℝ, 0 ≤ q → q ≤ q' → q ≠ q' →
    M.unhedgeableRiskSq (δ q) < M.unhedgeableRiskSq (δ q')

end GenModel

end HedgePSNV.Supplement


