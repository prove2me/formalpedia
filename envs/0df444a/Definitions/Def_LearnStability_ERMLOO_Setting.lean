-- Prove2me | Definitions.Def_LearnStability_ERMLOO_Setting
-- name    : LearnStability_ERMLOO_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:19:33.552261+00:00
-- url     : https://prove2.me/theorems/d8d09d1d-ed32-487b-9a1b-db62eac2dcdc
-- title:
--   The General Learning Setting: risks, the ERM value, learning rules, ERMs and rates
-- statement:
--   This file fixes the objects of the **General Learning Setting** of Shalev-Shwartz, Shamir, Srebro and Sridharan (§2).
--
--   A learning problem consists of an instance space $\mathcal Z$ with a $\sigma$-algebra, a nonempty hypothesis class $\mathcal H$, and an objective $f:\mathcal H\times\mathcal Z\to\mathbb R$. For a probability measure $\mathcal D$ on $\mathcal Z$ and a sample $S=(z_1,\dots,z_m)\in\mathcal Z^m$:
--
--   1. $\mathcal D^m$ is the law of an i.i.d. sample of size $m$ (the product measure);
--   2. the **risk** of $h$ is $F(h)=\mathbb E_{z\sim\mathcal D}[f(h;z)]$ and the **optimal risk** is $F^*=\inf_{h\in\mathcal H}F(h)$;
--   3. the **empirical risk** is $F_S(h)=\frac1m\sum_{i=1}^m f(h;z_i)$ and the **minimal empirical risk** (the ERM value) is $F_S(\hat h_S)=\inf_{h\in\mathcal H}F_S(h)$;
--   4. a **learning rule** $A$ assigns to every sample of size $m\ge1$ a hypothesis $A(S)\in\mathcal H$;
--   5. $A$ is an **ERM** if $F_S(A(S))=\inf_{h\in\mathcal H}F_S(h)$ for every sample $S$ of every size $m\ge 1$;
--   6. a **rate** is a sequence $\varepsilon(m)$ that is non-increasing in $m\ge1$ and tends to $0$.
--
--   The **standing assumptions** are the paper's bound $|f(h;z)|\le B$ for all $h,z$, together with measurability of each $z\mapsto f(h;z)$.
--
--   These are the objects in terms of which consistency, generalization and leave-one-out stability are defined in the companion definition file.
--
--   **Formalization Note.** The paper does not discuss measurability. A rule is called *measurable* when $(S,z)\mapsto f(A(S);z)$ is jointly measurable for every $m$; the ERM value is called measurable when $S\mapsto\inf_h F_S(h)$ is measurable for every $m$. Without such assumptions Lean's Bochner integral of a non-measurable function is $0$ and the expectation bounds would hold trivially. For a measurable ERM rule the ERM value is automatically measurable. The ERM value is the infimum itself; no minimiser is chosen. The paper's $B$ is $\sup_{h,z}|f(h;z)|$; any bound $B$ may be used, since every rate in the paper is increasing in $B$. Rates are required to be monotone only for $m\ge1$, because the value of a rule at $m=0$ is never used.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), pp. 2637–2639, §2 (definitions of F, F*, F_S, ĥ_S, learning rule, ERM, rate; Table 1)

import Mathlib

open MeasureTheory Filter Topology

namespace LearnStability.ERMLOO

variable {H Z : Type*} [MeasurableSpace Z]

/-- The law `D^m` of an i.i.d. sample `S = (z_1, …, z_m)` of size `m` drawn from `D`
(Shalev-Shwartz et al. 2010, §2, p. 2637). -/
noncomputable def sampleLaw (D : Measure Z) (m : ℕ) : Measure (Fin m → Z) :=
  Measure.pi fun _ : Fin m => D

/-- The risk `F(h) = E_{z∼D}[f(h; z)]` of a hypothesis `h` (p. 2637). -/
noncomputable def risk (f : H → Z → ℝ) (D : Measure Z) (h : H) : ℝ :=
  ∫ z, f h z ∂D

/-- The empirical risk `F_S(h) = (1/m) ∑_{i=1}^m f(h; z_i)` on a sample `S` of size `m`
(p. 2638). -/
noncomputable def empRisk (f : H → Z → ℝ) {m : ℕ} (S : Fin m → Z) (h : H) : ℝ :=
  (∑ i, f h (S i)) / m

/-- The optimal risk `F* = inf_{h ∈ H} F(h)` (p. 2638). -/
noncomputable def optRisk (f : H → Z → ℝ) (D : Measure Z) : ℝ :=
  ⨅ h, risk f D h

/-- The minimal empirical risk `F_S(ĥ_S) = inf_{h ∈ H} F_S(h)` (p. 2639). No minimiser is
chosen: only the value of the infimum is used, as in the paper. -/
noncomputable def ermValue (f : H → Z → ℝ) {m : ℕ} (S : Fin m → Z) : ℝ :=
  ⨅ h, empRisk f S h

/-- The standing assumptions on a learning problem `(H, Z, f)`:
* `bounded`: `|f(h; z)| ≤ B` for all `h, z` (the paper's standing assumption, p. 2637);
* `measurable`: each loss `z ↦ f(h; z)` is measurable (not in the paper; the minimal
  assumption under which the risk `F(h)` is meaningful). -/
structure StandingAssumptions (f : H → Z → ℝ) (B : ℝ) : Prop where
  bounded : ∀ h z, |f h z| ≤ B
  measurable : ∀ h, Measurable (f h)

/-- The minimal empirical risk `S ↦ inf_h F_S(h)` is, for every sample size `m`, a measurable
function of the sample. (Not in the paper; needed for `E[F_S(ĥ_S)]` to be meaningful. For a
measurable ERM rule it holds automatically.) -/
def MeasurableERMValue (f : H → Z → ℝ) : Prop :=
  ∀ m : ℕ, Measurable (fun S : Fin m → Z => ermValue f S)

/-- A (deterministic) learning rule: for every sample size `m`, a map from samples
`S ∈ Z^m` to hypotheses (p. 2637). The value at `m = 0` is never used. -/
abbrev Rule (H Z : Type*) := (m : ℕ) → (Fin m → Z) → H

/-- A learning rule is measurable if, for every `m`, the map `(S, z) ↦ f(A(S); z)` is jointly
measurable. (Not in the paper; the minimal assumption under which the expectations of the
paper are meaningful.) -/
def MeasurableRule (f : H → Z → ℝ) (A : Rule H Z) : Prop :=
  ∀ m : ℕ, Measurable (fun p : (Fin m → Z) × Z => f (A m p.1) p.2)

/-- `A` is an ERM (p. 2639): on every sample of size `m ≥ 1` it attains the minimal empirical
risk, `F_S(A(S)) = inf_{h ∈ H} F_S(h)`. -/
def IsERMRule (f : H → Z → ℝ) (A : Rule H Z) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ S : Fin m → Z, empRisk f S (A m S) = ermValue f S

/-- A rate `ε(m)`: monotonically non-increasing (for `m ≥ 1`) and tending to `0` (p. 2638). -/
def IsRate (ε : ℕ → ℝ) : Prop :=
  (∀ m n : ℕ, 1 ≤ m → m ≤ n → ε n ≤ ε m) ∧ Tendsto ε atTop (𝓝 0)

end LearnStability.ERMLOO


