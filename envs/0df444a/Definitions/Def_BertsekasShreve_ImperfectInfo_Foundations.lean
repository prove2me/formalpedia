-- Prove2me | Definitions.Def_BertsekasShreve_ImperfectInfo_Foundations
-- name    : BertsekasShreve_ImperfectInfo_Foundations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T05:28:08.14993+00:00
-- url     : https://prove2.me/theorems/22512bc3-122e-4ef7-b0c8-173c18adf394
-- title:
--   Borel spaces, universal measurability, lower semianalytic functions, the extended integral, and history measures
-- statement:
--   This file collects the measure-theoretic vocabulary of Chapter 7 that the imperfect state information model of Chapter 10 is built on, together with a generic construction of the distribution of the histories of a controlled process.
--
--   1. **Borel space** (Definition 7.7). A topological space $X$ is a Borel space if it is homeomorphic to a Borel subset of a complete separable metric space; the empty space counts as a Borel space.
--   2. **Universally measurable maps** (Definitions 7.18, 7.20). The universal $\sigma$-algebra of $X$ is the intersection, over all probability measures $p$ on $X$, of the $p$-completions of the Borel $\sigma$-algebra. A map $f:X\to Y$ is universally measurable if $f^{-1}(B)$ is universally measurable for every Borel $B\subseteq Y$, equivalently if $f$ is measurable for the completion of every probability measure on $X$.
--   3. **Lower semianalytic functions** (Definition 7.21). For $D\subseteq X$ and $f:D\to R^*=[-\infty,\infty]$, $f$ is lower semianalytic if $D$ is analytic and $\{x\in D\mid f(x)<c\}$ is analytic for every $c\in\mathbb R$.
--   4. **Extended arithmetic and integral** (p. 26; eqs. (42)–(43) of Chapter 7). In $R^*$ the convention $\infty-\infty=-\infty+\infty=+\infty$ is used, and for $f:X\to R^*$ and a probability measure $p$,
--   $$\int f\,dp=\int f^+\,dp-\int f^-\,dp,\qquad f^+=\max(f,0),\ f^-=\max(-f,0).$$
--   $f$ is called quasi-integrable if $\int f^+dp<\infty$ or $\int f^-dp<\infty$ (p. 246).
--   5. **History measures** (Proposition 7.45; eqs. (16) and (28) of Chapter 10). Consider a process with state space $X_j$ at stage $j$ and a control space $C$, an initial distribution $q$ of $y_0$, Borel transition kernels $t_j(dy_{j+1}\mid y_j,u_j)$ and control kernels $\mu_n(du_n\mid y_0,u_0,\dots,u_{n-1},y_n)$. The distribution $P_n$ of the history $(y_0,u_0,\dots,y_n,u_n)$ is the unique probability measure with
--   $$P_0(A\times D)=\int_A\mu_0(D\mid y_0)\,q(dy_0),\qquad P_{n+1}(E\times A\times D)=\int_E\int_A\mu_{n+1}(D\mid h,y)\,t_n(dy\mid y_n,u_n)\,P_n(dh)$$
--   for Borel sets $E$ of histories, $A\subseteq X_{n+1}$ and $D\subseteq C$.
--
--   These objects are used to state the imperfect state information model and its reduction to a perfect state information model.
--
--   **Formalization Note** Spaces live in `Type`. Integrals of $[0,\infty]$-valued functions are Mathlib lower Lebesgue integrals, which agree with the completion integral for the universally measurable integrands that occur. The extended integral is written out with the book's convention $\infty-\infty=+\infty$, which differs from Mathlib's `EReal` subtraction ($\top-\top=\bot$); `badd`/`bsum` implement the book's addition. The history measure is selected by its defining property on measurable rectangles (existence and uniqueness are Proposition 7.45); histories are stored as a tuple of states and a tuple of controls.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 118, Definition 7.7; p. 171, Definitions 7.18, 7.20; p. 177, Definition 7.21; p. 26 and p. 139, Eqs. (42)–(43) of Chapter 7; p. 246; Proposition 7.45; p. 249, Eq. (16) of Chapter 10; p. 252, Eq. (28) of Chapter 10

import Mathlib
import Definitions.Def_BertsekasShreve_BorelFinite_Policy
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.ImperfectInfo

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

/-- Definition 7.7 (p. 118): a topological space `X` is a *Borel space* if it is homeomorphic
to a Borel subset of a complete separable metric (Polish) space. The empty space qualifies. -/
def IsBorelSpace (X : Type) [TopologicalSpace X] : Prop :=
  ∃ (Y : Type) (_ : TopologicalSpace Y), PolishSpace Y ∧
    ∃ e : X → Y, Topology.IsEmbedding e ∧ MeasurableSet[borel Y] (Set.range e)

/-- Definitions 7.18 and 7.20 (p. 171): `f` is *universally measurable* if the preimage of every
measurable set lies in the completion of every probability measure on the domain. -/
def UnivMeasurable {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ν : Measure α, IsProbabilityMeasure ν → NullMeasurable f ν

/-- Definition 7.21 (p. 177): `f : D → R*` is *lower semianalytic* if `D` is analytic and every
strict lower level set `{x ∈ D | f x < c}`, `c ∈ ℝ`, is analytic. Values of `f` outside `D` are
irrelevant. -/
def LowerSemianalyticOn {α : Type} [TopologicalSpace α] (f : α → EReal) (D : Set α) : Prop :=
  MeasureTheory.AnalyticSet D ∧ ∀ c : ℝ, MeasureTheory.AnalyticSet {x | x ∈ D ∧ f x < (c : EReal)}

/-- Positive part `x⁺ = max(x, 0)` of an extended real, as an element of `[0, ∞]`. -/
noncomputable def posPart (x : EReal) : ℝ≥0∞ := x.toENNReal

/-- Negative part `x⁻ = max(-x, 0)` of an extended real, as an element of `[0, ∞]`. -/
noncomputable def negPart (x : EReal) : ℝ≥0∞ := (-x).toENNReal

/-- The book's extended integral, eq. (43) of Chapter 7 (p. 139):
`∫ f dp = ∫ f⁺ dp − ∫ f⁻ dp` with the convention `∞ − ∞ = +∞` (eq. (42)). -/
noncomputable def extIntegral {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → EReal) :
    EReal :=
  if ∫⁻ a, posPart (f a) ∂μ = ∞ then ⊤
  else ((∫⁻ a, posPart (f a) ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ a, negPart (f a) ∂μ : ℝ≥0∞) : EReal)

/-- `f` is *quasi-integrable* for `μ`: `∫ f⁺ dμ < ∞` or `∫ f⁻ dμ < ∞` (p. 246). -/
def QuasiIntegrable {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α → EReal) : Prop :=
  ∫⁻ a, posPart (f a) ∂μ < ∞ ∨ ∫⁻ a, negPart (f a) ∂μ < ∞

/-! ### Histories of a controlled process with stage-dependent state spaces

A process has state space `X j` at stage `j` and a fixed control space `C`. -/

/-- States `y₀, …, yₙ` of stages `0, …, n`. -/
abbrev StateSeq (X : ℕ → Type) (n : ℕ) := (m : Fin (n + 1)) → X m

/-- What the controller has seen at stage `n`: `(y₀, u₀, …, u_{n−1}, yₙ)`. -/
abbrev Obs (X : ℕ → Type) (C : Type) (n : ℕ) := StateSeq X n × (Fin n → C)

/-- A history `(y₀, u₀, …, yₙ, uₙ)` up to and including the control of stage `n`. -/
abbrev Hist (X : ℕ → Type) (C : Type) (n : ℕ) := StateSeq X n × (Fin (n + 1) → C)

variable {X : ℕ → Type} {C : Type}

/-- The state `yₙ` of the last stage of a history. -/
def Hist.state {n : ℕ} (h : Hist X C n) : X n := h.1 (Fin.last n)

/-- The control `uₙ` of the last stage of a history. -/
def Hist.control {n : ℕ} (h : Hist X C n) : C := h.2 (Fin.last n)

/-- The observation `(y₀, u₀, …, yₙ)` contained in a history (drop the last control). -/
def Hist.obs {n : ℕ} (h : Hist X C n) : Obs X C n := (h.1, fun j => h.2 j.castSucc)

/-- The history of stages `0, …, n` contained in a history of stages `0, …, n+1`. -/
def Hist.prefix {n : ℕ} (h : Hist X C (n + 1)) : Hist X C n :=
  (fun m => h.1 m.castSucc, fun j => h.2 j.castSucc)

/-- Extend a history of stages `0, …, n` by the next state `y_{n+1}`. -/
def Hist.extend {n : ℕ} (h : Hist X C n) (y : X (n + 1)) : Obs X C (n + 1) :=
  (Fin.snoc (α := fun m : Fin (n + 2) => X m) h.1 y, h.2)

/-- The stage-0 observation `(y₀)`. -/
def Obs.init (y : X 0) : Obs X C 0 :=
  (Fin.snoc (α := fun m : Fin 1 => X m) (fun i => Fin.elim0 i) y, fun i => Fin.elim0 i)

variable [∀ j, MeasurableSpace (X j)] [MeasurableSpace C]

/-- The distributions of the histories (Proposition 7.45 and eqs. (16), (28) of Chapter 10):
for an initial distribution `q` of `y₀`, Borel transition kernels `t j (dy_{j+1} | y_j, u_j)`
and control kernels `μ n (du_n | y₀, u₀, …, yₙ)` (possibly only universally measurable),
`histLaw q t μ n` is the probability measure on `Hist X C n` characterized on measurable
rectangles by
* `P₀(A × D) = ∫_A μ₀(D | y₀) q(dy₀)`,
* `P_{n+1}(E × A × D) = ∫_E ∫_A μ_{n+1}(D | h, y) t_n(dy | yₙ, uₙ) P_n(dh)`.
Such a measure exists and is unique (Proposition 7.45); the `else 0` branch is never used. -/
noncomputable def histLaw (q : Measure (X 0)) (t : (j : ℕ) → Kernel (X j × C) (X (j + 1)))
    (μ : (n : ℕ) → Obs X C n → Measure C) : (n : ℕ) → Measure (Hist X C n)
  | 0 =>
    if h : ∃ P : Measure (Hist X C 0), IsProbabilityMeasure P ∧
        ∀ (A : Set (X 0)) (D : Set C), MeasurableSet A → MeasurableSet D →
          P {h | h.state ∈ A ∧ h.control ∈ D} = ∫⁻ y in A, μ 0 (Obs.init y) D ∂q
    then h.choose else 0
  | n + 1 =>
    if h : ∃ P : Measure (Hist X C (n + 1)), IsProbabilityMeasure P ∧
        ∀ (E : Set (Hist X C n)) (A : Set (X (n + 1))) (D : Set C),
          MeasurableSet E → MeasurableSet A → MeasurableSet D →
          P {h | h.prefix ∈ E ∧ h.state ∈ A ∧ h.control ∈ D} =
            ∫⁻ h in E, (∫⁻ y in A, μ (n + 1) (h.extend y) D ∂(t n (h.state, h.control)))
              ∂(histLaw q t μ n)
    then h.choose else 0

end BertsekasShreve.ImperfectInfo


