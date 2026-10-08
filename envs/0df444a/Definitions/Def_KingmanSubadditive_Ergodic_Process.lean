-- Prove2me | Definitions.Def_KingmanSubadditive_Ergodic_Process
-- name    : KingmanSubadditive_Ergodic_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:23:48.128643+00:00
-- url     : https://prove2.me/theorems/81aad21b-d31b-48f9-b4b0-e242fd4e5cfc
-- title:
--   Subadditive processes: S₁, S₂, S₃, gₜ, γ, and the invariant σ-field
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space. A two-parameter family of real random variables $x_{st}$ is indexed by nonnegative integers $s<t$. It is a **subadditive process** when the following hold:
--
--   1. Each $x_{st}$, $s<t$, is a random variable (measurable).
--   2. $x_{su}\le x_{st}+x_{tu}$ whenever $s<t<u$ (condition S₁, (1.1.1)).
--   3. The entire shifted family $(x_{s+1,t+1})_{s<t}$ has the same joint distribution as $(x_{st})_{s<t}$ (condition S₂). This is stronger than S₂′, which asks only that the law of each single $x_{st}$ depend on $t-s$.
--   4. Every $x_{0t}$, $t\ge1$, is integrable, and for some real constant $A$ its mean $g_t=E(x_{0t})$ satisfies $g_t\ge-At$ for all $t\ge1$ (condition S₃, (1.1.2)–(1.1.3)).
--
--   An **additive process** has equality $x_{su}=x_{st}+x_{tu}$ in S₁ (1.1.6), together with the same measurability, S₂ and S₃. The constant associated with a subadditive process $x$ is
--   $$\gamma(x)=\inf_{t\ge1}\frac{g_t}{t},$$
--   which S₃ makes finite (1.1.5). The **invariant σ-field** $\mathcal I$ of (1.2.3)–(1.2.4) consists of the events defined in terms of the whole path of $x$ and invariant under the shift $x\mapsto x'$, $x'_{st}=x_{s+1,t+1}$.
--
--   These objects are the common model of Kingman's Theorem 1, its auxiliary statements (1.1.4), (1.2.4)–(1.2.6), and the applications to products of positive random matrices (Theorem 5) and to Theorem 2.
--
--   **Formalization Note** The family is a total function $x:\mathbb N\to\mathbb N\to\Omega\to\mathbb R$, but only pairs $s<t$ enter any definition. S₁ is required for every sample point (an almost-sure version gives an equivalent Theorem 1 after changing $x$ on a null set). S₂ is equality of the laws of the full path $(x_{st})_{s<t}$ and of the shifted path on the countable product space. The paper prints (1.1.3) "for all $t>1$"; with $g_1$ finite this is equivalent to the bound for all $t\ge1$ used here. The mean $g_t$ and the infimum $\gamma$ are meaningful only under S₃; without it Lean returns default values, so every theorem using them assumes S₃. The invariant σ-field consists of the preimages under the path map of the strictly shift-invariant measurable sets of path space.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, pp. 883–885, §1.1, (1.1.1)–(1.1.6), (1.2.3)

import Mathlib

namespace KingmanSubadditive.Ergodic

open MeasureTheory

/-- The valid index pairs `s < t` of §1.1 (pp. 883–884). Values outside this
type play no role in the process. -/
abbrev Interval := {p : ℕ × ℕ // p.1 < p.2}

/-- The full two-parameter sample path, indexed only by valid pairs. -/
def path {Ω : Type*} (x : ℕ → ℕ → Ω → ℝ) (ω : Ω) : Interval → ℝ :=
  fun p => x p.1.1 p.1.2 ω

/-- The shift `x'_{st} = x_{s+1,t+1}` of (1.2.3), p. 885, on path space. -/
def shift (φ : Interval → ℝ) : Interval → ℝ :=
  fun p => φ ⟨(p.1.1 + 1, p.1.2 + 1), by omega⟩

/-- The shift of a two-parameter sample path. -/
def shiftedPath {Ω : Type*} (x : ℕ → ℕ → Ω → ℝ) (ω : Ω) : Interval → ℝ :=
  shift (path x ω)

/-- `g_t = E(x_{0t})`, (1.1.2), p. 883. The integrability condition is
carried by `S3` wherever this quantity is used in a theorem. -/
noncomputable def mean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) (t : ℕ) : ℝ := ∫ ω, x 0 t ω ∂P

/-- Condition S₁, (1.1.1), p. 883. We use the pointwise version of the
displayed inequality for every valid triple. -/
def S1 {Ω : Type*} (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ (s t u : ℕ) (ω : Ω), s < t → t < u → x s u ω ≤ x s t ω + x t u ω

/-- Condition S₂, p. 884: equality of the laws of the *whole paths* before
and after shifting both indices by one. This is stronger than S₂′, which
requires equality only for individual coordinates. -/
def S2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  Measure.map (shiftedPath x) P = Measure.map (path x) P

/-- Condition S₃, (1.1.2)–(1.1.3), p. 883: each positive-time mean is finite
and the means have a common linear lower bound. -/
def S3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ t : ℕ, 1 ≤ t → Integrable (x 0 t) P) ∧
  ∃ A : ℝ, ∀ t : ℕ, 1 ≤ t → -A * (t : ℝ) ≤ mean P x t

/-- Kingman's subadditive process (§1.1, pp. 883–884): measurable random
variables on valid index pairs satisfying S₁, joint-law stationarity S₂,
and S₃. -/
def IsSubadditiveProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ s t : ℕ, s < t → Measurable (x s t)) ∧ S1 x ∧ S2 P x ∧ S3 P x

/-- An additive process, (1.1.6), p. 884: equality in S₁ along with the
same measurability, S₂ and S₃ requirements. -/
def IsAdditiveProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ s t : ℕ, s < t → Measurable (x s t)) ∧
  (∀ (s t u : ℕ) (ω : Ω), s < t → t < u →
    x s u ω = x s t ω + x t u ω) ∧ S2 P x ∧ S3 P x

/-- The finite constant `γ(x) = inf_{t≥1} g_t/t`, (1.1.5), p. 883.
Theorems using it assume S₃, which bounds the infimum below. -/
noncomputable def gamma {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : ℝ :=
  ⨅ t : {t : ℕ // 1 ≤ t}, mean P x t / (t : ℝ)

/-- The invariant σ-field `𝓘` of (1.2.3)–(1.2.4), p. 885: the pullback
under the full path map of the shift-invariant measurable sets of path space.
For a measurable process this is a sub-σ-field of the ambient one. -/
noncomputable def invariantSigma {Ω : Type*} [MeasurableSpace Ω]
    (x : ℕ → ℕ → Ω → ℝ) : MeasurableSpace Ω :=
  (MeasurableSpace.invariants shift).comap (path x)

end KingmanSubadditive.Ergodic


