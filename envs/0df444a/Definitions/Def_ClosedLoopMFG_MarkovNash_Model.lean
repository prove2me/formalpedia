-- Prove2me | Definitions.Def_ClosedLoopMFG_MarkovNash_Model
-- name    : ClosedLoopMFG_MarkovNash_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:29:57.255123+00:00
-- url     : https://prove2.me/theorems/c09a440c-5f5f-4489-9f9c-21603cb53d9d
-- title:
--   $\mathcal P(\mathbb R^d)$, paths, measure flows, empirical measures, $\mathbb F$-Brownian motion, Assumptions A and B (Section 2)
-- statement:
--   This file fixes the setting of Section 2 of Lacker's paper, shared by every statement of the mission.
--
--   Fix a dimension $d\in\mathbb N$ and a horizon $T>0$. The state space is $\mathbb R^d$ with its Euclidean norm. $\mathcal P(\mathbb R^d)$ is the set of Borel probability measures on $\mathbb R^d$, with the topology of weak convergence and the corresponding Borel $\sigma$-field. The path space is
--   $$\mathcal C^d = C([0,T];\mathbb R^d),$$
--   with the topology of uniform convergence and its Borel $\sigma$-field, and $C([0,T];\mathcal P(\mathbb R^d))$ is the space of continuous measure flows, also with its Borel $\sigma$-field. For $n\ge 1$ and $\boldsymbol x=(x_1,\dots,x_n)\in(\mathbb R^d)^n$ the **empirical measure** is
--   $$L_n(\boldsymbol x)=\frac1n\sum_{k=1}^n\delta_{x_k}\in\mathcal P(\mathbb R^d).$$
--
--   On a filtered probability space $(\Omega,\mathcal F,\mathbb F,\mathbb P)$, an **$\mathbb F$-Brownian motion** in $\mathbb R^d$ is a standard $d$-dimensional Brownian motion $W$ that is $\mathbb F$-adapted and whose increments $(W_r-W_t)_{r\ge t}$ are independent of $\mathcal F_t$ for every $t$.
--
--   The data of the game are a control space $A$ (a subset of a real normed space), bounded functions $b:[0,T]\times\mathbb R^d\times\mathcal P(\mathbb R^d)\times A\to\mathbb R^d$, $f:[0,T]\times\mathbb R^d\times\mathcal P(\mathbb R^d)\times A\to\mathbb R$ and $g:\mathbb R^d\times\mathcal P(\mathbb R^d)\to\mathbb R$.
--
--   **Assumption A.** (A.1) $A$ is a compact convex subset of a normed vector space. (A.2) $b$, $f$ and $g$ are bounded and jointly continuous.
--
--   **Assumption B.** For each $(t,x,m)\in[0,T]\times\mathbb R^d\times\mathcal P(\mathbb R^d)$ the set
--   $$K(t,x,m)=\{(b(t,x,m,a),z): a\in A,\ z\le f(t,x,m,a)\}\subset\mathbb R^d\times\mathbb R$$
--   is convex. It holds, for example, when $b$ is affine and $f$ concave in $a$.
--
--   **Formalization Note** $\mathbb R^d$ is the platform's `EthierKurtz.SDEState d`. $\mathcal P(\mathbb R^d)$, $\mathcal C^d$ and the flow space are type synonyms carrying the weak (resp. compact-open) topology and its Borel $\sigma$-field; on maps from the compact interval $[0,T]$ into a metric space the compact-open topology is the topology of the sup-metric, so this is the paper's topology. Coefficients take a real time argument; boundedness and continuity are required only on $[0,T]\times\mathbb R^d\times\mathcal P(\mathbb R^d)\times A$, and values outside that domain are never used. The empirical measure is the image of the uniform law on $\{1,\dots,n\}$ under $k\mapsto x_k$, which is $\frac1n\sum_k\delta_{x_k}$. Paths are read at real times through the clamp $s\mapsto \min(\max(s,0),T)$, which is the identity on $[0,T]$.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, pp. 5–6, Section 2 (Assumptions A and B)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ClosedLoopMFG.MarkovNash

/-- The state space `ℝ^d` of Lacker, arXiv:1808.02745v1, §2 (p. 5), as the platform's Euclidean
`EthierKurtz.SDEState d`. -/
abbrev E (d : ℕ) : Type := EthierKurtz.SDEState d

/-- `𝒫(ℝ^d)`: Borel probability measures on `ℝ^d`, with the topology of weak convergence and its
Borel σ-field (p. 5: "We always endow P(E) with the topology of weak convergence and its
corresponding Borel σ-field"). A type synonym, so that the Borel σ-field is the one used. -/
def PR (d : ℕ) : Type := ProbabilityMeasure (E d)

instance (d : ℕ) : TopologicalSpace (PR d) :=
  inferInstanceAs (TopologicalSpace (ProbabilityMeasure (E d)))

instance (d : ℕ) : MeasurableSpace (PR d) := borel (PR d)

instance (d : ℕ) : BorelSpace (PR d) := ⟨rfl⟩

/-- The underlying measure of an element of `𝒫(ℝ^d)`. -/
def PR.toMeasure {d : ℕ} (m : PR d) : Measure (E d) :=
  ProbabilityMeasure.toMeasure (show ProbabilityMeasure (E d) from m)

/-- `𝒞^d = C([0, T]; ℝ^d)` (p. 5), with the compact-open topology (= uniform convergence, since
`[0, T]` is compact) and its Borel σ-field. -/
def Path (d : ℕ) (T : ℝ≥0) : Type := C(Set.Icc (0 : ℝ) T, E d)

instance (d : ℕ) (T : ℝ≥0) : TopologicalSpace (Path d T) :=
  inferInstanceAs (TopologicalSpace C(Set.Icc (0 : ℝ) T, E d))

instance (d : ℕ) (T : ℝ≥0) : FunLike (Path d T) (Set.Icc (0 : ℝ) T) (E d) :=
  inferInstanceAs (FunLike C(Set.Icc (0 : ℝ) T, E d) (Set.Icc (0 : ℝ) T) (E d))

instance (d : ℕ) (T : ℝ≥0) : MeasurableSpace (Path d T) := borel (Path d T)

instance (d : ℕ) (T : ℝ≥0) : BorelSpace (Path d T) := ⟨rfl⟩

/-- `C([0, T]; 𝒫(ℝ^d))`, measure flows (p. 5), with the Borel σ-field. -/
def Flow (d : ℕ) (T : ℝ≥0) : Type := C(Set.Icc (0 : ℝ) T, PR d)

instance (d : ℕ) (T : ℝ≥0) : TopologicalSpace (Flow d T) :=
  inferInstanceAs (TopologicalSpace C(Set.Icc (0 : ℝ) T, PR d))

instance (d : ℕ) (T : ℝ≥0) : FunLike (Flow d T) (Set.Icc (0 : ℝ) T) (PR d) :=
  inferInstanceAs (FunLike C(Set.Icc (0 : ℝ) T, PR d) (Set.Icc (0 : ℝ) T) (PR d))

instance (d : ℕ) (T : ℝ≥0) : MeasurableSpace (Flow d T) := borel (Flow d T)

instance (d : ℕ) (T : ℝ≥0) : BorelSpace (Flow d T) := ⟨rfl⟩

/-- The initial time `0 ∈ [0, T]`. -/
def t0 (T : ℝ≥0) : Set.Icc (0 : ℝ) T := ⟨0, le_refl 0, T.2⟩

/-- The terminal time `T ∈ [0, T]`. -/
def tT (T : ℝ≥0) : Set.Icc (0 : ℝ) T := ⟨T, T.2, le_refl _⟩

/-- Clamp a real time into `[0, T]`. -/
noncomputable def clampT (T : ℝ≥0) (s : ℝ) : Set.Icc (0 : ℝ) T := Set.projIcc (0 : ℝ) (T : ℝ) T.2 s

/-- A path read at a real time `s` (clamped into `[0, T]`); equals `x s` for `s ∈ [0, T]`. -/
noncomputable def ev {d : ℕ} {T : ℝ≥0} (x : Path d T) (s : ℝ) : E d := x (clampT T s)

/-- A flow read at a real time `s` (clamped into `[0, T]`). -/
noncomputable def evF {d : ℕ} {T : ℝ≥0} (m : Flow d T) (s : ℝ) : PR d := m (clampT T s)

/-- The empirical measure `L_n(x) = (1/n) ∑_{k=1}^n δ_{x_k}` of `x ∈ (ℝ^d)^n`, `n ≥ 1`
(p. 6 and p. 20): the image of the uniform law on `{1, …, n}` under `k ↦ x_k`. -/
noncomputable def empirical {n d : ℕ} [NeZero n] (x : Fin n → E d) : PR d :=
  (⟨(PMF.uniformOfFintype (Fin n)).toMeasure.map x,
    Measure.isProbabilityMeasure_map (measurable_of_countable x).aemeasurable⟩ :
      ProbabilityMeasure (E d))

/-- An `𝔽`-Brownian motion in `ℝ^d`: a standard `d`-dimensional Brownian motion (platform
`EthierKurtz.IsStandardBrownian`) that is `𝔽`-adapted and whose increments after `t` are
independent of `𝓕_t`. -/
def IsFBrownian {d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (W : ℝ≥0 → Ω → E d) : Prop :=
  EthierKurtz.IsStandardBrownian P W ∧
  (∀ t, Measurable[𝓕 t] (W t)) ∧
  ∀ t, Indep (𝓕 t)
    (MeasurableSpace.comap (fun ω (r : Set.Ici t) => W r ω - W t ω) inferInstance) P

/-- **Assumption A** (p. 6): (A.1) `A` is a compact convex subset of a real normed space;
(A.2) `b`, `f`, `g` are bounded and jointly continuous on their domains
`[0, T] × ℝ^d × 𝒫(ℝ^d) × A` and `ℝ^d × 𝒫(ℝ^d)`. Values of `b`, `f` at times outside `[0, T]`
or at controls outside `A` are irrelevant and unconstrained. -/
structure AssumptionA {d : ℕ} (T : ℝ≥0) {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA]
    (A : Set EA) (b : ℝ → E d → PR d → EA → E d) (f : ℝ → E d → PR d → EA → ℝ)
    (g : E d → PR d → ℝ) : Prop where
  compact : IsCompact A
  convex : Convex ℝ A
  b_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x m, ∀ a ∈ A, ‖b t x m a‖ ≤ C
  f_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x m, ∀ a ∈ A, |f t x m a| ≤ C
  g_bdd : ∃ C : ℝ, ∀ x m, |g x m| ≤ C
  b_cont : ContinuousOn (fun p : ℝ × E d × PR d × EA => b p.1 p.2.1 p.2.2.1 p.2.2.2)
    (Set.Icc (0 : ℝ) T ×ˢ Set.univ ×ˢ Set.univ ×ˢ A)
  f_cont : ContinuousOn (fun p : ℝ × E d × PR d × EA => f p.1 p.2.1 p.2.2.1 p.2.2.2)
    (Set.Icc (0 : ℝ) T ×ˢ Set.univ ×ˢ Set.univ ×ˢ A)
  g_cont : Continuous (fun p : E d × PR d => g p.1 p.2)

/-- **Assumption B** (p. 6): for each `(t, x, m) ∈ [0, T] × ℝ^d × 𝒫(ℝ^d)` the set
`K(t, x, m) = {(b(t, x, m, a), z) : a ∈ A, z ≤ f(t, x, m, a)} ⊂ ℝ^d × ℝ` is convex. -/
def KSet {d : ℕ} {EA : Type*} (A : Set EA) (b : ℝ → E d → PR d → EA → E d)
    (f : ℝ → E d → PR d → EA → ℝ) (t : ℝ) (x : E d) (m : PR d) : Set (E d × ℝ) :=
  {p | ∃ a ∈ A, p.1 = b t x m a ∧ p.2 ≤ f t x m a}

/-- **Assumption B** (p. 6): every `K(t, x, m)`, `t ∈ [0, T]`, is convex. -/
def AssumptionB {d : ℕ} (T : ℝ≥0) {EA : Type*} [AddCommGroup EA] [Module ℝ EA] (A : Set EA)
    (b : ℝ → E d → PR d → EA → E d) (f : ℝ → E d → PR d → EA → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x m, Convex ℝ (KSet A b f t x m)

end ClosedLoopMFG.MarkovNash


