-- Prove2me | Definitions.Def_BertsekasShreve_BorelFinite_Model
-- name    : BertsekasShreve_BorelFinite_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:20:14.990095+00:00
-- url     : https://prove2.me/theorems/021ca59e-5be2-4831-ae52-e236a65ff78e
-- title:
--   The finite horizon Borel model (S, C, U, W, p, f, α, g, N) of Definition 8.1, with universal measurability and lower semianalyticity
-- statement:
--   This file fixes the measure-theoretic vocabulary of Chapter 8 and the model itself.
--
--   A **Borel space** is a topological space homeomorphic to a Borel subset of a complete separable metric space; it carries its Borel $\sigma$-algebra. For a Borel space $X$, the **universal $\sigma$-algebra** is
--   $$\mathcal U_X=\bigcap_{p\in P(X)}\mathcal B_X(p),$$
--   the intersection over all Borel probability measures $p$ of the $p$-completions of the Borel $\sigma$-algebra. A function into a measurable space is **universally measurable** if the preimage of every Borel set lies in $\mathcal U_X$. A function $f:D\to R^*=[-\infty,\infty]$ on an analytic set $D\subseteq X$ is **lower semianalytic** if $\{x\in D\mid f(x)<c\}$ is analytic for every real $c$. A **universally measurable stochastic kernel** $q(dy\mid x)$ on $Y$ given $X$ assigns a Borel probability measure $q(\cdot\mid x)$ to each $x$ so that $x\mapsto q(B\mid x)$ is universally measurable for every Borel $B\subseteq Y$.
--
--   A **finite horizon stochastic optimal control model** is a nine-tuple $(S,C,U,W,p,f,\alpha,g,N)$:
--   1. $S$ (states), $C$ (controls), $W$ (disturbances) are nonempty Borel spaces;
--   2. $U(x)\subseteq C$ is nonempty for each $x\in S$, and $\Gamma=\{(x,u)\mid x\in S,\ u\in U(x)\}$ is analytic in $S\times C$;
--   3. $p(dw\mid x,u)$ is a Borel-measurable stochastic kernel on $W$ given $S\times C$;
--   4. $f:S\times C\times W\to S$ is Borel-measurable;
--   5. $\alpha>0$ is the discount factor;
--   6. $g:\Gamma\to R^*$ is lower semianalytic;
--   7. $N\ge 1$ is the horizon.
--
--   The state transition kernel is
--   $$t(B\mid x,u)=p(\{w\mid f(x,u,w)\in B\}\mid x,u).$$
--
--   Every result of Chapter 8 is stated for this model.
--
--   **Formalization Note** Universally measurable sets are those that are $p$-null-measurable for every probability measure $p$; `universalSigma X` is that $\sigma$-algebra, and `UMeasurable f` is measurability with respect to it. Kernels are taken in the form of Lemma 7.28(b): a universally measurable stochastic kernel is a family of probability measures whose evaluation at each Borel set is universally measurable. The cost $g$ is stored as a function on all of $S\times C$; only its restriction to $\Gamma$ is constrained and only its values on $\Gamma$ enter the cost. The Borel-space and nonemptiness assumptions on $S$, $C$, $W$ are type-class hypotheses of each theorem (`[BorelSpace X] [IsBorelSpace X] [Nonempty X]`). Analytic sets are Mathlib's `AnalyticSet` (empty or a continuous image of $\mathbb N^{\mathbb N}$).
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 188–190, Definition 8.1 and Eq. (3) of Chapter 8; p. 118, Definition 7.7; p. 167, Definition 7.18; p. 171, Definition 7.20; p. 174, Lemma 7.28; p. 177, Definition 7.21

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace

namespace BertsekasShreve.BorelFinite

open MeasureTheory

universe u

set_option warn.classDefReducibility false in
/-- **Definition 7.18** (p. 167). The *universal σ-algebra* `𝒰_X = ⋂_{p ∈ P(X)} 𝓑_X(p)`: a set is
universally measurable if it lies in the completion of the Borel σ-algebra with respect to every
probability measure `p` on `X`, i.e. it is `p`-null-measurable for every such `p`. -/
def universalSigma (X : Type*) [MeasurableSpace X] : MeasurableSpace X where
  MeasurableSet' E := ∀ p : Measure X, IsProbabilityMeasure p → NullMeasurableSet E p
  measurableSet_empty := fun _ _ => nullMeasurableSet_empty
  measurableSet_compl := fun _ h p hp => (h p hp).compl
  measurableSet_iUnion := fun _ h p hp => NullMeasurableSet.iUnion (fun i => h i p hp)

/-- **Definition 7.20** (p. 171), for functions defined on the whole space: `f : X → Y` is
*universally measurable* if `f⁻¹(B) ∈ 𝒰_X` for every Borel set `B ⊆ Y`. -/
def UMeasurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y) : Prop :=
  Measurable[universalSigma X] f

/-- **Definition 7.21** (p. 177), for the restriction to `D` of a function `f : X → R*`: `f` is
*lower semianalytic on `D`* if `D` is analytic and `{x ∈ D | f(x) < c}` is analytic for every real
`c`. Values of `f` outside `D` play no role. -/
def IsLowerSemianalyticOn {X : Type*} [TopologicalSpace X] (D : Set X) (f : X → EReal) : Prop :=
  AnalyticSet D ∧ ∀ c : ℝ, AnalyticSet {x | x ∈ D ∧ f x < (c : EReal)}

/-- **Definitions 7.12, 7.20 and Lemma 7.28(b)** (pp. 134, 171, 174). A *universally measurable
stochastic kernel* `q(dy|x)` on `Y` given `X`: for every `x` a probability measure `q(·|x)` on the
Borel sets of `Y`, such that `x ↦ q(B|x)` is universally measurable for every Borel `B ⊆ Y`. -/
structure UMKernel (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y] where
  /-- the probability measure `q(·|x)` -/
  toFun : X → Measure Y
  isProb : ∀ x, IsProbabilityMeasure (toFun x)
  /-- `x ↦ q(B|x)` is universally measurable for every Borel set `B` -/
  um : ∀ B : Set Y, MeasurableSet B → UMeasurable (fun x => toFun x B)

/-- **Definition 8.1** (pp. 188–189). A finite horizon stochastic optimal control model
`(S, C, U, W, p, f, α, g, N)`. The spaces `S` (states), `C` (controls) and `W` (disturbances) are
nonempty Borel spaces; these standing assumptions are type-class hypotheses of every statement.
The one-stage cost `g` is stored as a function on all of `S × C`; only its values on
`Γ = {(x,u) | u ∈ U(x)}` matter, and only those are constrained. -/
structure Model (S C W : Type*) [TopologicalSpace S] [MeasurableSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W] where
  /-- control constraint `U(x) ⊆ C` -/
  U : S → Set C
  U_nonempty : ∀ x, (U x).Nonempty
  /-- `Γ = {(x,u) | x ∈ S, u ∈ U(x)}` is analytic in `SC`, Eq. (1) of Chapter 8 -/
  Γ_analytic : AnalyticSet {z : S × C | z.2 ∈ U z.1}
  /-- disturbance kernel `p(dw|x,u)`: a Borel-measurable stochastic kernel on `W` given `SC` -/
  p : ProbabilityTheory.Kernel (S × C) W
  p_markov : ProbabilityTheory.IsMarkovKernel p
  /-- system function `f : SCW → S`, Borel-measurable -/
  f : S × C × W → S
  f_measurable : Measurable f
  /-- discount factor, a positive real number -/
  α : ℝ
  α_pos : 0 < α
  /-- one-stage cost `g : Γ → R*` (extended to `S × C`; the values off `Γ` are irrelevant) -/
  g : S × C → EReal
  g_lsa : IsLowerSemianalyticOn {z : S × C | z.2 ∈ U z.1} g
  /-- horizon, a positive integer -/
  N : ℕ
  N_pos : 0 < N

namespace Model

variable {S C W : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W]

/-- The set `Γ = {(x,u) | x ∈ S, u ∈ U(x)}`, Eq. (1) of Chapter 8. -/
def Γ (M : Model S C W) : Set (S × C) := {z | z.2 ∈ M.U z.1}

/-- The state transition stochastic kernel, Eq. (3) of Chapter 8:
`t(B|x,u) = p({w | f(x,u,w) ∈ B}|x,u)`, the image of `p(·|x,u)` under `w ↦ f(x,u,w)`. -/
noncomputable def t (M : Model S C W) (z : S × C) : Measure S :=
  (M.p z).map (fun w => M.f (z.1, z.2, w))

end Model

end BertsekasShreve.BorelFinite


