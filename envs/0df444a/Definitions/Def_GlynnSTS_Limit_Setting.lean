-- Prove2me | Definitions.Def_GlynnSTS_Limit_Setting
-- name    : GlynnSTS_Limit_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:02:15.2017+00:00
-- url     : https://prove2.me/theorems/79c5b329-9753-4cf5-966c-52e2ede2683e
-- title:
--   §2 — C[0,1], the Brownian motion B, D(g), the class 𝓜 of (2.3), Assumption (2.1), and the map h of the proof of Theorem 2.4
-- statement:
--   This file fixes the objects of §2 of Glynn and Iglehart (1990), *Simulation output analysis using standardized time series*.
--
--   1. **The path space.** $C[0,1]$ is the space of continuous real functions on $[0,1]$ with the uniform norm $\|x\| = \sup_{0\le t\le 1}|x(t)|$, equipped with its Borel $\sigma$-algebra. The function $k \in C[0,1]$ is $k(t) = t$.
--
--   2. **Discontinuity sets.** For $g : C[0,1] \to \mathbb R$, $D(g)$ is the set of points $x \in C[0,1]$ at which $g$ is not continuous.
--
--   3. **Brownian motion.** A map $B : \Omega \to C[0,1]$ on a probability space $(\Omega, \mathcal F, P)$ is a *standard Brownian motion* if it is measurable and its coordinates $B(\omega)(t)$, $t \in [0,1]$, agree for every $\omega$ with a real Brownian motion $W$ (Gaussian finite-dimensional laws with $\operatorname{Cov}(W(s),W(t)) = \min(s,t)$, almost surely continuous paths).
--
--   4. **The class $\mathcal M$ of (2.3).** Relative to such a $B$, $\mathcal M$ is the class of measurable $g : C[0,1] \to \mathbb R$ with
--      - (i) $g(\alpha x) = \alpha g(x)$ for $\alpha > 0$, $x \in C[0,1]$;
--      - (ii) $g(x - \beta k) = g(x)$ for $\beta \in \mathbb R$, $x \in C[0,1]$;
--      - (iii) $P\{g(B) > 0\} = 1$;
--      - (iv) $P\{B \in D(g)\} = 0$.
--
--   5. **Assumption (2.1).** $Y = \{Y(t) : t \ge 0\}$ is a real-valued measurable process (the simulation output), and
--   $$\bar Y_n(t) = \frac1n\int_0^{nt} Y(s)\,ds,\qquad X_n(t) = n^{1/2}\bigl(\bar Y_n(t) - \mu t\bigr),\qquad 0 \le t \le 1.$$
--   Assumption (2.1) states that there are finite constants $\mu$ and $\sigma > 0$ such that $X_n \Rightarrow \sigma B$ as $n \to \infty$, weak convergence in $C[0,1]$.
--
--   6. **The map $h$.** Given $g$, $h(x) = x(1)/g(x)$ if $g(x) \ne 0$ and $h(x) = 0$ otherwise. It is the auxiliary map of the proof of Theorem 2.4.
--
--   These objects are the standing setting of the standardized-time-series method: $\bar Y_n(1)$ is the time average of the first $n$ time units of output, and a function $g \in \mathcal M$ is the "standardization" that cancels the unknown $\sigma$.
--
--   **Formalization Note** $C[0,1]$ is `C(unitInterval, ℝ)`, and its Borel instance is declared here because Mathlib has none. The Brownian motion is a $C[0,1]$-valued map whose coordinates match Mathlib's `IsBrownianReal` process pointwise (a continuous modification). $\bar Y_n$ is a parameter pinned pointwise by its defining integral, so it is determined by $Y$. Assumption (2.1) also requires local integrability of each path of $Y$; the paper uses it implicitly, since it makes $\bar Y_n$ defined. $n$ ranges over $\mathbb N$; at $n = 0$, $\bar Y_0 = X_0 = 0$. Weak convergence is Mathlib's `TendstoInDistribution`. Condition (iii) is printed "$P\{g(b) > 0\} = 1$" in the paper, a misprint for $g(B)$.
-- source:
--   Glynn & Iglehart, Simulation output analysis using standardized time series, Math. Oper. Res. 15 (1990), pp. 2–3, §2, (2.1), (2.3), and proof of Theorem 2.4, p. 3

import Mathlib

namespace GlynnSTS.Limit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- The Borel σ-algebra on `C[0,1]` (sup-norm topology). Mathlib has no `MeasurableSpace`
instance on `C(unitInterval, ℝ)` at this commit; "measurable" in the paper means Borel. -/
noncomputable instance instMeasurableSpaceC : MeasurableSpace C(unitInterval, ℝ) := borel _

instance instBorelSpaceC : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

/-- The identity path `k(t) = t` of (2.3ii). -/
def kfun : C(unitInterval, ℝ) := ⟨fun t => (t : ℝ), continuous_subtype_val⟩

/-- `D(g)`: the set of points of `C[0,1]` at which `g` is not continuous. -/
def D (g : C(unitInterval, ℝ) → ℝ) : Set C(unitInterval, ℝ) := {x | ¬ ContinuousAt g x}

/-- `B` is a standard Brownian motion on `[0,1]`, viewed as a random element of `C[0,1]`:
`B` is measurable, and its coordinates agree with a real Brownian motion `W` (Mathlib's
`IsBrownianReal`) for every `ω` and every `t ∈ [0,1]`. -/
def IsStdBMC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : Ω → C(unitInterval, ℝ)) :
    Prop :=
  Measurable B ∧ ∃ W : ℝ≥0 → Ω → ℝ, IsBrownianReal W P ∧
    ∀ ω (t : unitInterval), B ω t = W ⟨t, t.2.1⟩ ω

/-- The class `𝓜` of (2.3), relative to the Brownian motion `B` on `(Ω, P)`:
measurable `g : C[0,1] → ℝ` with (i) positive homogeneity, (ii) invariance under adding
multiples of `k`, (iii) `g(B) > 0` almost surely, (iv) `P{B ∈ D(g)} = 0`. -/
def ClassM {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : Ω → C(unitInterval, ℝ))
    (g : C(unitInterval, ℝ) → ℝ) : Prop :=
  Measurable g ∧
  (∀ a : ℝ, 0 < a → ∀ x, g (a • x) = a * g x) ∧
  (∀ β : ℝ, ∀ x, g (x - β • kfun) = g x) ∧
  (∀ᵐ ω ∂P, 0 < g (B ω)) ∧
  P {ω | B ω ∈ D g} = 0

/-- `Xₙ(t) = n^{1/2}(Ȳₙ(t) − μt)`. -/
noncomputable def Xn {Ω : Type*} (Ybar : ℕ → Ω → C(unitInterval, ℝ)) (μ : ℝ) (n : ℕ) (ω : Ω) :
    C(unitInterval, ℝ) :=
  Real.sqrt n • (Ybar n ω - μ • kfun)

/-- Assumption (2.1): `Y` is a jointly measurable real process with locally integrable paths,
`Ȳₙ(t) = ∫₀^{nt} Y(s) ds / n` for `t ∈ [0,1]`, `σ > 0`, and `Xₙ ⇒ σB` in `C[0,1]`. -/
structure Assumption21 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ)) (μ σ : ℝ)
    (B : Ω → C(unitInterval, ℝ)) : Prop where
  measurable : Measurable (fun p : ℝ × Ω => Y p.1 p.2)
  integrable : ∀ ω (T : ℝ), IntervalIntegrable (fun s => Y s ω) volume 0 T
  ybar_eq : ∀ (n : ℕ) ω (t : unitInterval),
    Ybar n ω t = (∫ s in (0:ℝ)..((n : ℝ) * t), Y s ω) / n
  sigma_pos : 0 < σ
  fclt : TendstoInDistribution (Xn Ybar μ) atTop (fun ω => σ • B ω) (fun _ => P) P

/-- The auxiliary map of the proof of Theorem 2.4: `h(x) = x(1)/g(x)` for `g(x) ≠ 0`, and `0`
elsewhere. -/
noncomputable def hmap (g : C(unitInterval, ℝ) → ℝ) (x : C(unitInterval, ℝ)) : ℝ :=
  if g x ≠ 0 then x 1 / g x else 0

end GlynnSTS.Limit


