-- Prove2me | Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
-- name    : AntonelliBFSDE_BackwardForward_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:36.66749+00:00
-- url     : https://prove2.me/theorems/68fd0f71-a0ec-4a0f-8cb6-295497da7d16
-- title:
--   The filtered space, the usual hypotheses, càdlàg paths, bounded-variation integrators and conditional-expectation versions (§§1–2)
-- statement:
--   This file fixes the setting shared by §§1–3 of Antonelli's paper on backward-forward stochastic differential equations.
--
--   **Filtered space.** Time is $t \in \mathbb R_{\ge 0}$ with a fixed horizon $T > 0$; only $[0,T]$ matters. $(\Omega, \mathcal F, P)$ is a probability space and $(\mathcal F_t)_{t \ge 0}$ a filtration. It satisfies the **usual hypotheses** when it is right-continuous, $\mathcal F_t = \bigcap_{s > t} \mathcal F_s$, and $\mathcal F_0$ contains every $P$-null set (every subset of a set of outer measure zero).
--
--   **Càdlàg paths.** A path $x : \mathbb R_{\ge0} \to \mathbb R$ is càdlàg on $[0,T]$ if it is right-continuous at every $t < T$ and has a finite left limit at every $0 < t \le T$.
--
--   **Bounded-variation integrators.** A bounded-variation integrator with bound $\beta$ is an adapted process $A$ together with its minimal (Jordan) decomposition
--   $$A_t = A^+_t - A^-_t,$$
--   where $A^\pm$ are adapted, have nondecreasing right-continuous paths, vanish at $0$, are constant on $[T,\infty)$, satisfy
--   $$A^+_t + A^-_t = |A|_t := \operatorname{Var}_{[0,t]}(A), \qquad 0 \le t \le T,$$
--   and $|A|_T \le \beta$. The pathwise measures $dA^\pm(\omega)$ are the Stieltjes measures of the paths, $|dA|(\omega) = dA^+(\omega) + dA^-(\omega)$, and
--   $$\int_s^t h_r\,dA_r := \int_{(s,t]} h_r\,dA^+_r - \int_{(s,t]} h_r\,dA^-_r, \qquad \int_s^t |h_r|\,|dA_r| \in [0,\infty].$$
--
--   **Conditional-expectation versions.** For processes $\xi, W$, $W$ is a version of $t \mapsto E(\xi_t \mid \mathcal F_t)$ on $[0,T]$ if $(t,\omega) \mapsto W_t(\omega)$ is jointly measurable on the horizon, each $\xi_t$ is integrable, and, for each $t \le T$, $W_t = E(\xi_t \mid \mathcal F_t)$ $P$-a.s.
--
--   These are the objects the paper takes from Protter (1990) (p. 778: "we refer to Protter (1990) for notation and definitions") and from the opening of §2 (pp. 778–779).
--
--   **Formalization Note** The Jordan decomposition is carried as data, and the field `minimal` ties $A^+ + A^-$ to Mathlib's `eVariationOn`, so that $|dA|$ is the paper's total-variation measure and not a larger one. Integrals are over $(s,t]$ (Protter's Lebesgue–Stieltjes convention); because $A_0 = 0$ and the path is extended by $0$ to $(-\infty,0]$, there is no atom at $0$. Every integrand is evaluated at $r^+ = \max(r,0)$ to pass from $\mathbb R$ to $\mathbb R_{\ge0}$.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), pp. 777–779, §1 (usual hypotheses) and §2 ((2.3)–(2.4), the total variation |A|)

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The "usual hypotheses" on a filtered probability space (Antonelli 1993, p. 777):
the filtration is right-continuous, and `𝓕 0` contains every `P`-null set
(`P s` is the outer measure, so subsets of null sets are included). -/
def UsualHypotheses (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) : Prop :=
  𝓕.rightCont ≤ 𝓕 ∧ ∀ s : Set Ω, P s = 0 → MeasurableSet[𝓕 0] s

/-- An adapted process of bounded variation on `[0, T]` (the integrators `A`, `C` of §§2–3),
carried together with its minimal (Jordan) decomposition `A = A⁺ - A⁻`:
`A⁺`, `A⁻` are adapted, nondecreasing, right-continuous, vanish at `0`, are frozen after `T`,
`A⁺_t + A⁻_t` is the total variation `|A|_t` of `A` on `[0, t]`, and `|A|_T ≤ β`. -/
structure BVIntegrator (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) where
  /-- The process `A`. -/
  A : ℝ≥0 → Ω → ℝ
  /-- The positive variation `A⁺`. -/
  Apos : ℝ≥0 → Ω → ℝ
  /-- The negative variation `A⁻`. -/
  Aneg : ℝ≥0 → Ω → ℝ
  adapted : StronglyAdapted 𝓕 A
  adapted_pos : StronglyAdapted 𝓕 Apos
  adapted_neg : StronglyAdapted 𝓕 Aneg
  decomp : ∀ t ω, A t ω = Apos t ω - Aneg t ω
  mono_pos : ∀ ω, Monotone (fun t => Apos t ω)
  mono_neg : ∀ ω, Monotone (fun t => Aneg t ω)
  rc_pos : ∀ ω t, ContinuousWithinAt (fun s => Apos s ω) (Set.Ici t) t
  rc_neg : ∀ ω t, ContinuousWithinAt (fun s => Aneg s ω) (Set.Ici t) t
  zero : ∀ ω, Apos 0 ω = 0 ∧ Aneg 0 ω = 0
  frozen : ∀ ω t, T ≤ t → Apos t ω = Apos T ω ∧ Aneg t ω = Aneg T ω
  minimal : ∀ ω, ∀ t ≤ T,
    ENNReal.ofReal (Apos t ω + Aneg t ω) = eVariationOn (fun s => A s ω) (Set.Icc 0 t)
  bound : ∀ ω, Apos T ω + Aneg T ω ≤ β

namespace BVIntegrator

variable {𝓕 : Filtration ℝ≥0 mΩ} {T : ℝ≥0} {β : ℝ}

/-- The total variation process `|A|_t = A⁺_t + A⁻_t`. -/
def totVar (I : BVIntegrator 𝓕 T β) (t : ℝ≥0) (ω : Ω) : ℝ := I.Apos t ω + I.Aneg t ω

/-- The Stieltjes measure `dA⁺(ω)` on `ℝ` of the path `x ↦ A⁺_{x⁺}(ω)`. -/
noncomputable def posMeasure (I : BVIntegrator 𝓕 T β) (ω : Ω) : Measure ℝ :=
  (show Monotone (fun x : ℝ => I.Apos x.toNNReal ω) from
    fun _ _ h => I.mono_pos ω (Real.toNNReal_le_toNNReal h)).stieltjesFunction.measure

/-- The Stieltjes measure `dA⁻(ω)` on `ℝ` of the path `x ↦ A⁻_{x⁺}(ω)`. -/
noncomputable def negMeasure (I : BVIntegrator 𝓕 T β) (ω : Ω) : Measure ℝ :=
  (show Monotone (fun x : ℝ => I.Aneg x.toNNReal ω) from
    fun _ _ h => I.mono_neg ω (Real.toNNReal_le_toNNReal h)).stieltjesFunction.measure

/-- The variation measure `|dA|(ω) = dA⁺(ω) + dA⁻(ω)`. -/
noncomputable def varMeasure (I : BVIntegrator 𝓕 T β) (ω : Ω) : Measure ℝ :=
  I.posMeasure ω + I.negMeasure ω

/-- The pathwise Lebesgue–Stieltjes integral `∫_s^t h_r dA_r` over `(s, t]`. -/
noncomputable def integral (I : BVIntegrator 𝓕 T β) (h : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0)
    (ω : Ω) : ℝ :=
  (∫ r in Set.Ioc (s : ℝ) (t : ℝ), h r.toNNReal ω ∂I.posMeasure ω) -
    ∫ r in Set.Ioc (s : ℝ) (t : ℝ), h r.toNNReal ω ∂I.negMeasure ω

/-- The pathwise integral `∫_s^t |h_r| |dA_r|` over `(s, t]`, in `[0, ∞]`. -/
noncomputable def absLIntegral (I : BVIntegrator 𝓕 T β) (h : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioc (s : ℝ) (t : ℝ), ‖h r.toNNReal ω‖ₑ ∂I.varMeasure ω

end BVIntegrator

end AntonelliBFSDE.BackwardForward


