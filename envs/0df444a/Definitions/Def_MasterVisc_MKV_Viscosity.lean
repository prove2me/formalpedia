-- Prove2me | Definitions.Def_MasterVisc_MKV_Viscosity
-- name    : MasterVisc_MKV_Viscosity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:34:48.893983+00:00
-- url     : https://prove2.me/theorems/4d0dad85-c7ff-481b-b1d4-aeb518dc691a
-- title:
--   Definitions 4.2 and 4.4, (4.2) — test functions C_b^{1,1,1}, test sets 𝒜̲^L V, 𝒜̄^L V, viscosity solutions of (3.1)
-- statement:
--   This file encodes the viscosity notion of §4.1 for the master equation (3.1), $\mathbb L V(t,\mu)=0$ on $\Theta$, where
--   $$\mathbb L\varphi(t,\mu)=\partial_t\varphi(t,\mu)+G\big(t,\mu,\varphi(t,\mu),\partial_\mu\varphi(t,\mu,\cdot),\partial_\omega\partial_\mu\varphi(t,\mu,\cdot)\big).$$
--
--   1. **$C_b^{1,1,1}([t_1,t_2]\times\mathcal P)$ (Definition 4.2).** A function $\varphi$ with derivatives $\partial_t\varphi$, $\partial_\mu\varphi(s,P,\omega)\in\mathbb R^d$, $\partial_\omega\partial_\mu\varphi(s,P,\omega)\in\mathbb R^{d\times d}$ such that $\varphi,\partial_t\varphi$ are continuous on $[t_1,t_2]\times\mathcal P$ for the pseudometric (2.5); $\partial_\mu\varphi,\partial_\omega\partial_\mu\varphi$ are continuous on $[t_1,t_2]\times\mathcal P\times\Omega$ and $\mathcal F_s$-measurable in $\omega$; $\partial_t\varphi$ is bounded; $|\partial_\mu\varphi(s,P,\omega)|+|\partial_\omega\partial_\mu\varphi(s,P,\omega)|\le C(1+\|\omega\|)$ for $P$-a.e. $\omega$; and the functional Itô formula holds under every $P\in\mathcal P$: for every representation $(\tilde X,\tilde b,\tilde\sigma)$ of $P$ from $t_1$ and $t_1\le s\le t_2$,
--   $$\varphi(s,P)-\varphi(t_1,P)=\int_{t_1}^s\partial_t\varphi(r,P)\,dr+\mathbb E^{\tilde{\mathbb P}}\Big[\int_{t_1}^s\Big(\partial_\mu\varphi(r,P,\tilde X)\cdot\tilde b_r+\tfrac12\,\partial_\omega\partial_\mu\varphi(r,P,\tilde X):\tilde\sigma_r\tilde\sigma_r^\top\Big)dr\Big].$$
--   2. **Test sets (4.2).** For $V:\Theta\to\mathbb R$, $\varphi\in\underline{\mathcal A}^LV(t,\mu)$ if for some $0<\delta\le T-t$, $\varphi\in C_b^{1,1,1}([t,t+\delta]\times\mathcal P_L(t,\mu))$, $(\varphi-V)(t,\mu)=0$ and $\inf_{(s,P)\in[t,t+\delta]\times\mathcal P_L(t,\mu)}(\varphi-V)(s,P)=0$. $\overline{\mathcal A}^LV(t,\mu)$ is the same with $\sup$.
--   3. **Viscosity solutions (Definition 4.4).** $V\in C^0(\Theta)$ is an $L$-viscosity subsolution (supersolution) if $\mathbb L\varphi(t,\mu)\ge0$ ($\le0$) for all $(t,\mu)\in\Theta$ and $\varphi\in\underline{\mathcal A}^LV(t,\mu)$ ($\overline{\mathcal A}^LV(t,\mu)$); an $L$-viscosity solution if both; and a viscosity solution if it is an $L$-viscosity solution for some $L>0$.
--
--   **Formalization Note.** The derivatives are witnesses carried with $\varphi$ and tied to it by the predicate, never chosen. The Itô formula is in drift form: since $dX=\tilde b\,dr+\tilde\sigma\,d\tilde B$ and $d\langle X\rangle=\tilde\sigma\tilde\sigma^\top dr$, the term $\mathbb E\int\partial_\mu\varphi\cdot\tilde\sigma\,d\tilde B$ has zero expectation (square-integrable integrand: linear growth of $\partial_\mu\varphi$, bounded $\tilde\sigma$, $P\in\mathcal P_2$), so this is the paper's (2.25); the left side depends only on $P$, so it is required for every representation. The inner integrands are integrable for the same reason, so the Bochner integrals are not default values. "$\inf(\varphi-V)=0$" is read as "$\varphi-V\ge0$ on $[t,t+\delta]\times\mathcal P_L(t,\mu)$ and $=0$ at $(t,\mu)$" ("$\le0$" for the sup). Since a test function is defined on $[t,t+\delta]\times\mathcal P_L(t,\mu)$ only and $\mu$ itself need not belong to $\mathcal P_L(t,\mu)$, the values $\varphi(t,\mu)$, $\partial_t\varphi(t,\mu)$, $\partial_\mu\varphi(t,\mu,\cdot)$, $\partial_\omega\partial_\mu\varphi(t,\mu,\cdot)$ used in $\mathbb L\varphi(t,\mu)$ are required to equal those at $(t,P)$ for every $P\in\mathcal P_L(t,\mu)$; all such $P$ have $P_{[0,t]}=\mu_{[0,t]}$, so (by continuity for the pseudometric) these values coincide, and this is the paper's reading of $\varphi(t,\mu)$. The hypothesis "X is a semimartingale on $[t_1,t_2]$ under each $P\in\mathcal P$" is carried by the set: every use has $\mathcal P=\mathcal P_L(t,\mu)$. One $L$ serves both halves of a viscosity solution.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), (3.1) p. 947, Definition 4.2, (4.2) and Definition 4.4, p. 959

import Mathlib
import Definitions.Def_MasterVisc_MKV_Setting
import Definitions.Def_MasterVisc_Comparison_Viscosity

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.MKV

open EthierKurtz

variable {d : ℕ} {T : ℝ≥0}

/-- `Φ ∈ C_b^{1,1,1}([t₁, t₂] × 𝒫)` (Definition 4.2, p. 959), for a set `𝒫` of laws each of which
carries a semimartingale representation from `t₁` on:
(a) `φ`, `∂_tφ` are continuous on `[t₁, t₂] × 𝒫` for the pseudometric (2.5);
(b) `∂_μφ`, `∂_ω∂_μφ` are continuous on `[t₁, t₂] × 𝒫 × Ω`;
(c) `∂_μφ(s, P, ·)`, `∂_ω∂_μφ(s, P, ·)` are `F_s`-measurable;
(d) the functional Itô formula (2.25) holds on `[t₁, t₂]` under every `P ∈ 𝒫`, in drift form, for
every representation of `P`;
(e) `∂_tφ` is bounded; (f) `|∂_μφ| + |∂_ω∂_μφ| ≤ C(1 + ‖ω‖)`, `P`-a.e., for all `P ∈ 𝒫`. -/
def IsC111b (t₁ t₂ : ℝ≥0) (Pset : Measure (MasterVisc.Comparison.Path d T) → Prop) (Φ : MasterVisc.Comparison.C111Data d T) : Prop :=
  (∀ s P, t₁ ≤ s → s ≤ t₂ → Pset P → ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ s' P', t₁ ≤ s' → s' ≤ t₂ →
    Pset P' → MasterVisc.Comparison.W2Θ s P s' P' < δ →
      |Φ.fn s' P' - Φ.fn s P| < ε ∧ |Φ.dt s' P' - Φ.dt s P| < ε) ∧
  (∀ s P ω, t₁ ≤ s → s ≤ t₂ → Pset P → ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ s' P' ω', t₁ ≤ s' →
    s' ≤ t₂ → Pset P' → MasterVisc.Comparison.W2Θ s P s' P' + ‖ω' - ω‖ < δ →
      ‖Φ.dmu s' P' ω' - Φ.dmu s P ω‖ < ε ∧
      Real.sqrt (MasterVisc.Comparison.frob2 (Φ.dwdmu s' P' ω' - Φ.dwdmu s P ω)) < ε) ∧
  (∀ s P, t₁ ≤ s → s ≤ t₂ → Pset P →
    Measurable[MasterVisc.Comparison.filt s] (Φ.dmu s P) ∧ ∀ i j, Measurable[MasterVisc.Comparison.filt s] (fun ω => Φ.dwdmu s P ω i j)) ∧
  (∀ P, Pset P → ∀ R : Rep d T, IsRepFrom t₁ P R → ∀ s, t₁ ≤ s → s ≤ t₂ →
    Φ.fn s P - Φ.fn t₁ P =
      (∫ r in (t₁ : ℝ)..(s : ℝ), Φ.dt r.toNNReal P) +
      ∫ ω, (∫ r in (t₁ : ℝ)..(s : ℝ),
        (inner ℝ (Φ.dmu r.toNNReal P (R.Y ω)) (R.b r.toNNReal ω) +
          MasterVisc.Comparison.fdot (Φ.dwdmu r.toNNReal P (R.Y ω))
            (R.σ r.toNNReal ω * (R.σ r.toNNReal ω).transpose) / 2)) ∂(R.P)) ∧
  (∃ C : ℝ, ∀ s P, t₁ ≤ s → s ≤ t₂ → Pset P → |Φ.dt s P| ≤ C) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ s P, t₁ ≤ s → s ≤ t₂ → Pset P →
    ∀ᵐ ω ∂(P), ‖Φ.dmu s P ω‖ + Real.sqrt (MasterVisc.Comparison.frob2 (Φ.dwdmu s P ω)) ≤ C * (1 + ‖ω‖))

/-- The data of `Φ` at `(t, μ)` are those at `(t, P)` for every `P ∈ 𝒫_L(t, μ)`. Since
`P_{[0,t]} = μ_{[0,t]}`, this is how the page reads `φ(t, μ)`, `∂_tφ(t, μ)`, … for a test function
defined on `[t, t + δ] × 𝒫_L(t, μ)` only (the law `μ` itself need not lie in `𝒫_L(t, μ)`). -/
def AnchoredAt (L : ℝ) (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T)) (Φ : MasterVisc.Comparison.C111Data d T) : Prop :=
  ∀ P, InPL L t μ P →
    Φ.fn t P = Φ.fn t μ ∧ Φ.dt t P = Φ.dt t μ ∧ Φ.dmu t P = Φ.dmu t μ ∧
      Φ.dwdmu t P = Φ.dwdmu t μ

/-- `Φ ∈ 𝒜̲^L V(t, μ)` (4.2): for some `0 < δ ≤ T − t`, `Φ ∈ C_b^{1,1,1}([t, t + δ] × 𝒫_L(t, μ))`,
`(φ − V)(t, μ) = 0` and `inf_{(s,P) ∈ [t,t+δ] × 𝒫_L(t,μ)} (φ − V)(s, P) = 0`, read as
`φ − V ≥ 0` on that set. -/
def InAsub (L : ℝ) (V : ℝ≥0 → Measure (MasterVisc.Comparison.Path d T) → ℝ) (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T))
    (Φ : MasterVisc.Comparison.C111Data d T) : Prop :=
  ∃ δ : ℝ≥0, 0 < δ ∧ t + δ ≤ T ∧ IsC111b t (t + δ) (InPL L t μ) Φ ∧ AnchoredAt L t μ Φ ∧
    Φ.fn t μ = V t μ ∧
    ∀ s P, t ≤ s → s ≤ t + δ → InPL L t μ P → 0 ≤ Φ.fn s P - V s P

/-- `Φ ∈ 𝒜̄^L V(t, μ)` (4.2): as `InAsub`, with `sup (φ − V) = 0` read as `φ − V ≤ 0` on the set. -/
def InAsup (L : ℝ) (V : ℝ≥0 → Measure (MasterVisc.Comparison.Path d T) → ℝ) (t : ℝ≥0) (μ : Measure (MasterVisc.Comparison.Path d T))
    (Φ : MasterVisc.Comparison.C111Data d T) : Prop :=
  ∃ δ : ℝ≥0, 0 < δ ∧ t + δ ≤ T ∧ IsC111b t (t + δ) (InPL L t μ) Φ ∧ AnchoredAt L t μ Φ ∧
    Φ.fn t μ = V t μ ∧
    ∀ s P, t ≤ s → s ≤ t + δ → InPL L t μ P → Φ.fn s P - V s P ≤ 0

/-- `V` is an `L`-viscosity subsolution of (3.1) (Definition 4.4(i)). -/
def IsLViscSub (L : ℝ) (G : MasterVisc.Comparison.Gen d T) (V : ℝ≥0 → Measure (MasterVisc.Comparison.Path d T) → ℝ) : Prop :=
  IsC0Θ V ∧ ∀ t μ Φ, t ≤ T → MasterVisc.Comparison.IsP2 μ → InAsub L V t μ Φ → 0 ≤ MasterVisc.Comparison.Lop G Φ t μ

/-- `V` is an `L`-viscosity supersolution of (3.1) (Definition 4.4(i)). -/
def IsLViscSuper (L : ℝ) (G : MasterVisc.Comparison.Gen d T) (V : ℝ≥0 → Measure (MasterVisc.Comparison.Path d T) → ℝ) : Prop :=
  IsC0Θ V ∧ ∀ t μ Φ, t ≤ T → MasterVisc.Comparison.IsP2 μ → InAsup L V t μ Φ → MasterVisc.Comparison.Lop G Φ t μ ≤ 0

/-- `V` is an `L`-viscosity solution of (3.1) (Definition 4.4(ii)). -/
def IsLViscSol (L : ℝ) (G : MasterVisc.Comparison.Gen d T) (V : ℝ≥0 → Measure (MasterVisc.Comparison.Path d T) → ℝ) : Prop :=
  IsLViscSub L G V ∧ IsLViscSuper L G V

/-- `V` is a viscosity solution of (3.1): an `L`-viscosity solution for some `L > 0`
(Definition 4.4(ii)), with one `L` for both halves. -/
def IsViscSol (G : MasterVisc.Comparison.Gen d T) (V : ℝ≥0 → Measure (MasterVisc.Comparison.Path d T) → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ IsLViscSol L G V

end MasterVisc.MKV


