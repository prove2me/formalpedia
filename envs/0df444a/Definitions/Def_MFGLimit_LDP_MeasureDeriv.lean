-- Prove2me | Definitions.Def_MFGLimit_LDP_MeasureDeriv
-- name    : MFGLimit_LDP_MeasureDeriv
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:21.463339+00:00
-- url     : https://prove2.me/theorems/f2322df5-a3dc-4b28-b710-9f1561be4622
-- title:
--   §2.2, pp. 5–6 — flat derivative δV/δm on P_q(ℝ^d), W_q-compact sets, joint continuity on [0,T] × ℝ^d × P_q
-- statement:
--   Derivatives of functions of probability measures (§2.2).
--
--   Fix $q\ge1$. A function $V:\mathcal P^q(\mathbb R^d)\to\mathbb R$ is $\mathscr C^1$ if there is a continuous map $\frac{\delta V}{\delta m}:\mathcal P^q(\mathbb R^d)\times\mathbb R^d\to\mathbb R$ (with $\mathcal W_q$ on the measure argument) such that
--
--   1. for every $\mathcal W_q$-compact $K\subset\mathcal P^q(\mathbb R^d)$ there is $c<\infty$ with $\sup_{m\in K}|\frac{\delta V}{\delta m}(m,v)|\le c(1+|v|^q)$ for all $v$;
--   2. for all $m,m'\in\mathcal P^q(\mathbb R^d)$,
--   $$V(m')-V(m)=\int_0^1\int_{\mathbb R^d}\frac{\delta V}{\delta m}\big((1-t)m+tm',v\big)\,(m'-m)(dv)\,dt; \qquad (2.2)$$
--   3. the normalization $\int\frac{\delta V}{\delta m}(m,v)\,m(dv)=0$ holds.
--
--   The intrinsic derivative is $D_mV(m,v)=D_v\frac{\delta V}{\delta m}(m,v)$; $V$ is $\mathscr C^2$ if each $m\mapsto\frac{\delta V}{\delta m}(m,v)$ is $\mathscr C^1$. The file also defines $\mathcal W_q$-compactness of a set of measures and joint continuity of a function of $(t,x,m,w)\in[0,T]\times\mathbb R^d\times\mathcal P^q(\mathbb R^d)\times V$, used to state Assumption A(5).
--
--   **Formalization Note** The flat derivative is a witness function (`IsFlatDeriv q V dV`); the normalization makes it unique. Compactness in $(\mathcal P^q,\mathcal W_q)$ is sequential compactness, and continuity is the $\varepsilon$–$\delta$ form for the metric $\mathcal W_q$.
-- source:
--   Delarue, Lacker & Ramanan, From the master equation to mean field game limit theory: large deviations and concentration of measure, arXiv:1804.08550v1, pp. 5–6, §2.2, (2.2)

import Mathlib
import Definitions.Def_MFGLimit_LDP_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLimit.LDP

variable {d : ℕ}

/-- `K ⊂ P_q(ℝ^d)` is `W_q`-compact: `K ⊆ P_q(ℝ^d)` and every sequence of `K` has a subsequence
converging in `W_q` to a point of `K` (sequential compactness of the metric space `(P_q, W_q)`). -/
def IsWCompact (q : ℝ) (K : Set (Measure (MFGLimit.Conc.E d))) : Prop :=
  (∀ m ∈ K, MFGLimit.Conc.IsPp q m) ∧
    ∀ u : ℕ → Measure (MFGLimit.Conc.E d), (∀ k, u k ∈ K) →
      ∃ m ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => Wp q (u (φ k)) m) atTop (𝓝 0)

/-- The mixture `(1 − t) m + t m'` of two measures, `t ∈ [0, 1]`. -/
noncomputable def mix (t : ℝ) (m m' : Measure (MFGLimit.Conc.E d)) : Measure (MFGLimit.Conc.E d) :=
  ENNReal.ofReal (1 - t) • m + ENNReal.ofReal t • m'

/-- §2.2, p. 5: `dV = δV/δm` is the (normalized) flat derivative of `V : P_q(ℝ^d) → ℝ`, so that
`V` is `C¹`:
* `dV` is continuous on `P_q(ℝ^d) × ℝ^d` (metric `W_q` in the measure);
* (i) on every `W_q`-compact `K ⊂ P_q(ℝ^d)` there is `c < ∞` with
  `sup_{m ∈ K} |dV(m, v)| ≤ c (1 + |v|^q)` for all `v`;
* (ii) (2.2): `V(m') − V(m) = ∫₀¹ ∫ dV((1 − t)m + t m', v) (m' − m)(dv) dt` for `m, m' ∈ P_q`;
* the normalization `∫ dV(m, v) m(dv) = 0` for `m ∈ P_q`. -/
def IsFlatDeriv (q : ℝ) (V : Measure (MFGLimit.Conc.E d) → ℝ) (dV : Measure (MFGLimit.Conc.E d) → MFGLimit.Conc.E d → ℝ) : Prop :=
  (∀ m v, MFGLimit.Conc.IsPp q m → ∀ ε > 0, ∃ δ > 0, ∀ m' v', MFGLimit.Conc.IsPp q m' →
      Wp q m m' < ENNReal.ofReal δ → dist v v' < δ → |dV m' v' - dV m v| < ε) ∧
    (∀ K, IsWCompact q K → ∃ c : ℝ, ∀ m ∈ K, ∀ v, |dV m v| ≤ c * (1 + ‖v‖ ^ q)) ∧
    (∀ m m', MFGLimit.Conc.IsPp q m → MFGLimit.Conc.IsPp q m' →
      V m' - V m = ∫ t in (0 : ℝ)..1,
        ((∫ v, dV (mix t m m') v ∂m') - ∫ v, dV (mix t m m') v ∂m)) ∧
    (∀ m, MFGLimit.Conc.IsPp q m → ∫ v, dV m v ∂m = 0)

/-- Joint continuity of `F(t, x, m, w)` on `[0, T] × ℝ^d × P_q(ℝ^d) × V`, with the metric `W_q`
in the measure argument. -/
def ContOnPq (q : ℝ) (T : ℝ≥0) {V β : Type*} [PseudoMetricSpace V] [SeminormedAddCommGroup β]
    (F : ℝ≥0 → MFGLimit.Conc.E d → Measure (MFGLimit.Conc.E d) → V → β) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ≥0) T, ∀ x m w, MFGLimit.Conc.IsPp q m → ∀ ε > 0, ∃ δ > 0,
    ∀ t' ∈ Set.Icc (0 : ℝ≥0) T, ∀ x' m' w', MFGLimit.Conc.IsPp q m' →
      dist t t' < δ → dist x x' < δ → Wp q m m' < ENNReal.ofReal δ → dist w w' < δ →
        ‖F t' x' m' w' - F t x m w‖ < ε

end MFGLimit.LDP


