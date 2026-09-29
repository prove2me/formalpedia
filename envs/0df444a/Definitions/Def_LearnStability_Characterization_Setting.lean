-- Prove2me | Definitions.Def_LearnStability_Characterization_Setting
-- name    : LearnStability_Characterization_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:06:46.847132+00:00
-- url     : https://prove2.me/theorems/1167fc83-addc-4655-bd8b-8fbb11e308bc
-- title:
--   The General Learning Setting: risks, empirical risks, learning rules and rates (§2)
-- statement:
--   This file fixes the objects of the General Learning Setting of Vapnik, as used by Shalev-Shwartz, Shamir, Srebro and Sridharan.
--
--   A **learning problem** consists of a hypothesis class $\mathcal H$, an instance set $\mathcal Z$ carrying a $\sigma$-algebra, and an objective function $f:\mathcal H\times\mathcal Z\to\mathbb R$. For a probability distribution $\mathcal D$ on $\mathcal Z$ and a sample $S=(z_1,\dots,z_m)$ the following quantities are defined:
--
--   1. the law $\mathcal D^m$ of an i.i.d. sample of size $m$;
--   2. the **risk** $F(h)=\mathbb E_{z\sim\mathcal D}[f(h;z)]$;
--   3. the **empirical risk** $F_S(h)=\frac1m\sum_{i=1}^m f(h;z_i)$;
--   4. the **optimal risk** $F^*=\inf_{h\in\mathcal H}F(h)$;
--   5. the **minimal empirical risk** $F_S(\hat h_S)=\inf_{h\in\mathcal H}F_S(h)$ (no minimiser is chosen; only the value is used).
--
--   The **standing assumptions** on the problem, with a constant $B$, are
--   $$|f(h;z)|\le B\quad\text{for all } h\in\mathcal H,\ z\in\mathcal Z,$$
--   that each $z\mapsto f(h;z)$ is measurable, and that for every $m$ the map $S\mapsto\inf_h F_S(h)$ is measurable on $\mathcal Z^m$.
--
--   A **learning rule** $A$ maps each sample of each size $m$ to a hypothesis $A(S)\in\mathcal H$. It is **measurable** if for every $m$ the map $(S,z)\mapsto f(A(S);z)$ is jointly measurable on $\mathcal Z^m\times\mathcal Z$. A **rate** is a sequence $\varepsilon(m)$ that is non-increasing for $m\ge1$ and tends to $0$.
--
--   These objects underlie every consistency, AERM, generalization and stability notion of the paper.
--
--   **Formalization Note.** Samples are functions `Fin m → Z` and $\mathcal D^m$ is `Measure.pi`. The paper's bound $B=\sup_{h,z}|f(h;z)|$ is replaced by any bound $B$; every rate in the paper is increasing in $B$, so the statements are equivalent. The two measurability clauses and the measurability of learning rules are not in the paper, which never discusses measurability; without them the Bochner integrals of the paper could silently be $0$. They hold, for instance, when $\mathcal H$ is countable. Rates are required to be monotone only on $m\ge1$, because the value at $m=0$ is never used and constructed rates such as $8B/\sqrt m$ take junk values at $m=0$ in Lean.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), pp. 2637–2639, §2 (standing assumption |f| ≤ B, p. 2637; risk, rules and rates, p. 2638; Table 1 and ERM, p. 2639)

import Mathlib

open MeasureTheory Filter Topology

namespace LearnStability.Characterization

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
* `measurable`: each loss `z ↦ f(h; z)` is measurable;
* `measurable_ermValue`: for every `m`, the minimal empirical risk `S ↦ inf_h F_S(h)` is a
  measurable function of the sample.
The two measurability clauses are not in the paper; they are the minimal assumptions under
which the expectations of the paper are meaningful. -/
structure StandingAssumptions (f : H → Z → ℝ) (B : ℝ) : Prop where
  bounded : ∀ h z, |f h z| ≤ B
  measurable : ∀ h, Measurable (f h)
  measurable_ermValue : ∀ m : ℕ, Measurable (fun S : Fin m → Z => ermValue f S)

/-- A (deterministic) learning rule: for every sample size `m`, a map from samples
`S ∈ Z^m` to hypotheses (p. 2637). The value at `m = 0` is never used. -/
abbrev Rule (H Z : Type*) := (m : ℕ) → (Fin m → Z) → H

/-- A learning rule is measurable if, for every `m`, the map `(S, z) ↦ f(A(S); z)` is jointly
measurable. (Not in the paper; see `StandingAssumptions`.) -/
def MeasurableRule (f : H → Z → ℝ) (A : Rule H Z) : Prop :=
  ∀ m : ℕ, Measurable (fun p : (Fin m → Z) × Z => f (A m p.1) p.2)

/-- A rate `ε(m)`: monotonically non-increasing (for `m ≥ 1`) and tending to `0` (p. 2638). -/
def IsRate (ε : ℕ → ℝ) : Prop :=
  (∀ m n : ℕ, 1 ≤ m → m ≤ n → ε n ≤ ε m) ∧ Tendsto ε atTop (𝓝 0)

end LearnStability.Characterization


