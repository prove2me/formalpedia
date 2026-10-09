-- Prove2me | Definitions.Def_FeinbergPOMDP_WStar_Model
-- name    : FeinbergPOMDP_WStar_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:52.819841+00:00
-- url     : https://prove2.me/theorems/f73e0b81-81e5-4f7f-9041-7e210921df12
-- title:
--   §2–§3, pp. 4–11 and (5.14) — kernel continuity notions, R (3.1), R′ (3.2), filters H (3.3), q (3.5), c̄ (3.8), Assumption (H), 𝓡_B
-- statement:
--   This file fixes the objects of Feinberg, Kasyanov and Zgurovsky's reduction of a partially observable Markov decision process (POMDP) to its belief MDP (the COMDP), and the continuity notions in which the paper's results are stated.
--
--   **Convergence of probability measures** (p. 4). For a measurable space $\mathbb S$, let $\mathbb P(\mathbb S)$ be the set of probability measures on $\mathbb S$. A sequence $\mu^{(n)} \in \mathbb P(\mathbb S)$ converges
--
--   1. *weakly* to $\mu$ if $\int f\,d\mu^{(n)} \to \int f\,d\mu$ for every bounded continuous $f$;
--   2. *setwise* to $\mu$ if $\mu^{(n)}(C) \to \mu(C)$ for every Borel set $C$;
--   3. *in the total variation* to $\mu$ if
--   $$\sup\Big\{\Big|\int f\,d\mu^{(n)} - \int f\,d\mu\Big| : f : \mathbb S \to [-1,1] \text{ Borel}\Big\} \to 0 .$$
--
--   A stochastic kernel $R(dt \mid s)$ is *weakly continuous* (*setwise continuous*, *continuous in the total variation*) if $R(\cdot \mid s^{(n)})$ converges weakly (setwise, in the total variation) to $R(\cdot \mid s)$ whenever $s^{(n)} \to s$.
--
--   **The POMDP** (p. 4). The state space $\mathbb X$, observation space $\mathbb Y$ and action space $\mathbb A$ are Borel subsets of Polish spaces. $P(dx' \mid x, a)$ is the transition kernel on $\mathbb X$ given $\mathbb X \times \mathbb A$, and $Q(dy \mid a, x)$ the observation kernel on $\mathbb Y$ given $\mathbb A \times \mathbb X$. For a belief $z \in \mathbb P(\mathbb X)$ and an action $a$, the joint law of the next state and the next observation is (3.1)
--   $$R(B \times C \mid z, a) = \int_{\mathbb X}\int_B Q(C \mid a, x')\,P(dx' \mid x, a)\,z(dx),$$
--   and its observation marginal is $R'(C \mid z, a) = R(\mathbb X \times C \mid z, a)$ (3.2).
--
--   **Filters.** A *filter* is a stochastic kernel $H(dx \mid z, a, y)$ on $\mathbb X$ given $\mathbb P(\mathbb X) \times \mathbb A \times \mathbb Y$ such that (3.3)
--   $$R(B \times C \mid z, a) = \int_C H(B \mid z, a, y)\,R'(dy \mid z, a)\qquad\text{for all Borel } B \subseteq \mathbb X,\ C \subseteq \mathbb Y;$$
--   $H(z, a, y)$ is the posterior distribution of the state after observing $y$. The belief transition (3.5) is the law of the posterior,
--   $$q(D \mid z, a) = \int_{\mathbb Y} \mathbf 1\{H(z, a, y) \in D\}\,R'(dy \mid z, a),$$
--   a probability measure on $\mathbb P(\mathbb X)$ with the Borel σ-algebra of the weak topology. It is *weakly continuous* if $q(\cdot \mid z^{(n)}, a^{(n)}) \to q(\cdot \mid z, a)$ weakly whenever $z^{(n)} \to z$ weakly and $a^{(n)} \to a$.
--
--   **Assumption (H)** (p. 11): there is a filter $H$ such that whenever $z^{(n)} \to z$ weakly and $a^{(n)} \to a$, some subsequence $(z^{(n_k)}, a^{(n_k)})$ and some Borel $C \subseteq \mathbb Y$ with $R'(C \mid z, a) = 1$ satisfy $H(z^{(n_k)}, a^{(n_k)}, y) \to H(z, a, y)$ weakly for every $y \in C$.
--
--   **Costs.** For a cost $c(x, a) = \ell + f(x, a)$ with $\ell \in \mathbb R$ and $f$ taking values in $[0, \infty]$, the COMDP cost (3.8) is $\bar c(z, a) = \int c(x, a)\,z(dx) = \ell + \int f(x, a)\,z(dx)$.
--
--   **The family $\mathcal R_B$** (5.14). For a Borel $B \subseteq \mathbb X$, $\mathcal R_B = \{(z, a) \mapsto R(B \times C \mid z, a) : C \text{ Borel in } \mathbb Y\}$. It is *equicontinuous at all the points* of $\mathbb P(\mathbb X) \times \mathbb A$ in the sense of (5.15):
--   $$\sup_{C}\big|R(B \times C \mid z^{(n)}, a^{(n)}) - R(B \times C \mid z, a)\big| \to 0\quad\text{whenever } z^{(n)} \to z \text{ weakly},\ a^{(n)} \to a .$$
--
--   These objects are shared by every statement of the mission: Lemma 6.1, Theorems 3.4–3.7, 5.2, 5.5, Lemmas 5.3, 5.6 and Corollary 5.4.
--
--   **Formalization Note.** Weak convergence is convergence in Mathlib's topology on `ProbabilityMeasure`. All continuity notions are the paper's sequential ones. Total variation is written without a real supremum: for every $\varepsilon > 0$ there is $N$ such that $|\int f\,d\mu^{(n)} - \int f\,d\mu| \le \varepsilon$ for all $n \ge N$ and all Borel $f$ with $|f| \le 1$; the same is done for the supremum over $C$ in (5.15). A Markov kernel $\kappa$ is turned into the map $s \mapsto \kappa(\cdot \mid s)$ by `kernelPM`. A filter is a map $H : \mathbb P(\mathbb X) \to \mathbb A \to \mathbb Y \to \mathbb P(\mathbb X)$ that is jointly Borel measurable in $(z,a,y)$, as the paper requires for a stochastic kernel on $\mathbb P(\mathbb X) \times \mathbb A \times \mathbb Y$. Its $y$-sections are also required measurable for Mathlib's σ-algebra on `ProbabilityMeasure`, so $y \mapsto H(B \mid z,a,y)$ is measurable in (3.3). The belief transition $q$ is the image of $R'(\cdot \mid z, a)$ under $H(z, a, \cdot)$ for the Borel σ-algebra, so integrals of bounded continuous functions against $q$ are genuine. `beliefCost f z a` is $\int f(x, a)\,z(dx)$ in $[0, \infty]$; this is exact also when $c = +\infty$ on a set of positive $z$-measure. `RFamily` is $\mathcal R_B$ as real-valued functions indexed by the Borel sets $C$.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, §2 p. 4 (convergence notions, kernel continuity, the POMDP), §3 pp. 7–9 ((3.1), (3.2), (3.3), (3.5), (3.8)), p. 11 (Assumption (H)), §5 p. 19 ((5.14), (5.15))

import Mathlib

open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter

namespace FeinbergPOMDP.WStar

/-! Feinberg, Kasyanov, Zgurovsky, *Partially Observable Total-Cost Markov Decision Processes with
Weakly Continuous Transition Probabilities*, arXiv:1401.2168v2, §2 (pp. 3–4) and §3 (pp. 7–11):
convergence of probability measures, continuity of stochastic kernels, the kernels `R` (3.1) and
`R′` (3.2), filters `H` (3.3), the belief transition `q` (3.5), the belief cost `c̄` (3.8),
Assumption (H) (p. 11) and the family `𝓡_B` (5.14). -/

section Convergence

variable {T : Type*} [MeasurableSpace T]

/-- Setwise convergence (p. 4): `μ n (C) → μ(C)` for every Borel set `C`. -/
def TendstoSetwise (μs : ℕ → ProbabilityMeasure T) (μ : ProbabilityMeasure T) : Prop :=
  ∀ C : Set T, MeasurableSet C →
    Tendsto (fun n => (μs n : Measure T) C) atTop (𝓝 ((μ : Measure T) C))

/-- Convergence in the total variation (p. 4):
`sup { |∫ f dμₙ − ∫ f dμ| : f : T → [−1, 1] Borel } → 0`, written without a real supremum as
"for every `ε > 0` there is `N` such that for `n ≥ N` every Borel `f` with `|f| ≤ 1` has
`|∫ f dμₙ − ∫ f dμ| ≤ ε`". Bounded Borel functions are integrable against probability measures,
so no integral here takes Lean's default value. -/
def TendstoTV (μs : ℕ → ProbabilityMeasure T) (μ : ProbabilityMeasure T) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ f : T → ℝ, Measurable f → (∀ t, |f t| ≤ 1) →
    |∫ t, f t ∂(μs n : Measure T) - ∫ t, f t ∂(μ : Measure T)| ≤ ε

end Convergence

section KernelContinuity

variable {S T : Type*} [TopologicalSpace S] [MeasurableSpace T]

/-- A stochastic kernel `R(dt|s)`, given as the map `s ↦ R(·|s)` into `ℙ(T)`, is **weakly
continuous** (p. 4) if `R(·|s⁽ⁿ⁾)` converges weakly to `R(·|s)` whenever `s⁽ⁿ⁾ → s`. Weak
convergence is convergence in Mathlib's topology on `ProbabilityMeasure T` (integrals of bounded
continuous functions converge). -/
def IsWeaklyContinuous [TopologicalSpace T] [OpensMeasurableSpace T]
    (R : S → ProbabilityMeasure T) : Prop :=
  ∀ (s : S) (ss : ℕ → S), Tendsto ss atTop (𝓝 s) → Tendsto (fun n => R (ss n)) atTop (𝓝 (R s))

/-- A stochastic kernel is **setwise continuous** (p. 4) if `R(·|s⁽ⁿ⁾)` converges setwise to
`R(·|s)` whenever `s⁽ⁿ⁾ → s`. -/
def IsSetwiseContinuous (R : S → ProbabilityMeasure T) : Prop :=
  ∀ (s : S) (ss : ℕ → S), Tendsto ss atTop (𝓝 s) → TendstoSetwise (fun n => R (ss n)) (R s)

/-- A stochastic kernel is **continuous in the total variation** (p. 4) if `R(·|s⁽ⁿ⁾)` converges
in the total variation to `R(·|s)` whenever `s⁽ⁿ⁾ → s`. -/
def IsTVContinuous (R : S → ProbabilityMeasure T) : Prop :=
  ∀ (s : S) (ss : ℕ → S), Tendsto ss atTop (𝓝 s) → TendstoTV (fun n => R (ss n)) (R s)

end KernelContinuity

/-- A Markov kernel `κ` from `α` to `β`, seen as the map `a ↦ κ(·|a)` into `ℙ(β)`. -/
noncomputable def kernelPM {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] : α → ProbabilityMeasure β :=
  fun a => ⟨κ a, inferInstance⟩

section POMDP

variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]

/-- The kernel `R(· | z, a)` on `𝕏 × 𝕐` of (3.1):
`R(B × C | z, a) = ∫_𝕏 ∫_B Q(C | a, x′) P(dx′ | x, a) z(dx)`,
the law of `(x′, y)` when `x ∼ z`, `x′ ∼ P(· | x, a)` and `y ∼ Q(· | a, x′)`. -/
noncomputable def jointLaw (P : Kernel (X × A) X) [IsMarkovKernel P]
    (Q : Kernel (A × X) Y) [IsMarkovKernel Q] (z : ProbabilityMeasure X) (a : A) :
    ProbabilityMeasure (X × Y) :=
  ⟨((P.comap (fun x => (x, a)) measurable_prodMk_right) ∘ₘ (z : Measure X)) ⊗ₘ
      (Q.comap (fun x' => (a, x')) measurable_prodMk_left), inferInstance⟩

/-- The observation kernel `R′(C | z, a) = R(𝕏 × C | z, a)` of (3.2), the second marginal of
`R(· | z, a)`. -/
noncomputable def obsLaw (P : Kernel (X × A) X) [IsMarkovKernel P]
    (Q : Kernel (A × X) Y) [IsMarkovKernel Q] (z : ProbabilityMeasure X) (a : A) :
    ProbabilityMeasure Y :=
  (jointLaw P Q z a).map measurable_snd.aemeasurable

/-- `H` is a **filter** for the POMDP, i.e. a stochastic kernel `H(dx | z, a, y)` on `𝕏` given
`ℙ(𝕏) × 𝔸 × 𝕐` satisfying (3.3):
`R(B × C | z, a) = ∫_C H(B | z, a, y) R′(dy | z, a)` for all Borel `B ⊆ 𝕏`, `C ⊆ 𝕐`.

Formalization Note. `H z a y` is the posterior `H(· | z, a, y)`. For each `(z, a)`, `y ↦ H z a y`
is required to be measurable both for Mathlib's σ-algebra on `ProbabilityMeasure X` (generated by
`μ ↦ μ(B)`, so `y ↦ H(B | z, a, y)` is measurable) and for the Borel σ-algebra of the weak
topology (the paper's `ℬ(ℙ(𝕏))`). The Borel measurability is required jointly in `(z,a,y)`,
as it is for the stochastic kernel on `ℙ(𝕏) × 𝔸 × 𝕐` on p. 8. -/
structure IsFilter [TopologicalSpace X] [OpensMeasurableSpace X]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) : Prop where
  measurable : ∀ z a, Measurable (H z a)
  measurable_joint_borel :
    @Measurable _ _
      ((borel (ProbabilityMeasure X)).prod (inferInstance : MeasurableSpace A) |>.prod
        (inferInstance : MeasurableSpace Y))
      (borel (ProbabilityMeasure X))
      (fun p : (ProbabilityMeasure X × A) × Y => H p.1.1 p.1.2 p.2)
  disintegration : ∀ (z : ProbabilityMeasure X) (a : A) (B : Set X) (C : Set Y),
    MeasurableSet B → MeasurableSet C →
      (jointLaw P Q z a : Measure (X × Y)) (B ×ˢ C) =
        ∫⁻ y in C, (H z a y : Measure X) B ∂(obsLaw P Q z a : Measure Y)

/-- The transition probability `q(· | z, a)` of the belief MDP (COMDP), (3.5):
`q(D | z, a) = ∫_𝕐 I{H(z, a, y) ∈ D} R′(dy | z, a)`, the law of the posterior `H(z, a, y)` when
`y ∼ R′(· | z, a)`. It is a measure on `ℙ(𝕏)` with the Borel σ-algebra of the weak topology. -/
noncomputable def beliefTransition [TopologicalSpace X] [OpensMeasurableSpace X]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) (z : ProbabilityMeasure X) (a : A) :
    @Measure (ProbabilityMeasure X) (borel (ProbabilityMeasure X)) :=
  @Measure.map Y (ProbabilityMeasure X) _ (borel (ProbabilityMeasure X)) (H z a)
    (obsLaw P Q z a : Measure Y)

/-- (W*)(ii) for the COMDP (p. 9): `q(· | z, a)` is weakly continuous in `(z, a) ∈ ℙ(𝕏) × 𝔸`,
i.e. whenever `z⁽ⁿ⁾ → z` weakly and `a⁽ⁿ⁾ → a`, `∫ g dq(· | z⁽ⁿ⁾, a⁽ⁿ⁾) → ∫ g dq(· | z, a)` for
every bounded continuous `g : ℙ(𝕏) → ℝ`. Under `IsFilter`, `g ∘ H(z, a, ·)` is Borel and bounded,
so these integrals are the integrals `∫ g(H(z, a, y)) R′(dy | z, a)`. -/
def BeliefTransitionWeaklyContinuous [TopologicalSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) : Prop :=
  ∀ (z : ProbabilityMeasure X) (a : A) (zs : ℕ → ProbabilityMeasure X) (as : ℕ → A),
    Tendsto zs atTop (𝓝 z) → Tendsto as atTop (𝓝 a) →
      ∀ g : ProbabilityMeasure X →ᵇ ℝ,
        Tendsto (fun n => ∫ p, g p ∂(beliefTransition P Q H (zs n) (as n))) atTop
          (𝓝 (∫ p, g p ∂(beliefTransition P Q H z a)))

/-- Assumption (H) (p. 11): there is a filter `H` satisfying (3.3) such that whenever
`z⁽ⁿ⁾ → z` weakly and `a⁽ⁿ⁾ → a`, some subsequence `(z⁽ⁿᵏ⁾, a⁽ⁿᵏ⁾)` and some Borel `C ⊆ 𝕐` with
`R′(C | z, a) = 1` satisfy `H(z⁽ⁿᵏ⁾, a⁽ⁿᵏ⁾, y) → H(z, a, y)` weakly for all `y ∈ C` (3.12). -/
def AssumptionH [TopologicalSpace X] [OpensMeasurableSpace X] [TopologicalSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q] : Prop :=
  ∃ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H ∧
    ∀ (z : ProbabilityMeasure X) (a : A) (zs : ℕ → ProbabilityMeasure X) (as : ℕ → A),
      Tendsto zs atTop (𝓝 z) → Tendsto as atTop (𝓝 a) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ C : Set Y, MeasurableSet C ∧
          (obsLaw P Q z a : Measure Y) C = 1 ∧
          ∀ y ∈ C, Tendsto (fun k => H (zs (φ k)) (as (φ k)) y) atTop (𝓝 (H z a y))

/-- The `[0, ∞]`-valued part of the COMDP one-step cost (3.8). With the POMDP cost written
`c(x, a) = lower + f x a` (`lower : ℝ`, `f : 𝕏 → 𝔸 → [0, ∞]`), the COMDP cost is
`c̄(z, a) = ∫ c(x, a) z(dx) = lower + beliefCost f z a`, with `beliefCost f z a = ∫ f(x, a) z(dx)`.
This is exact also when `c` is `+∞` on a `z`-positive set: both sides are then `+∞`. -/
noncomputable def beliefCost (f : X → A → ℝ≥0∞) (z : ProbabilityMeasure X) (a : A) : ℝ≥0∞ :=
  ∫⁻ x, f x a ∂(z : Measure X)

/-- The family `𝓡_B = {(z, a) ↦ R(B × C | z, a) : C ∈ ℬ(𝕐)}` of (5.14), indexed by the Borel
sets `C ⊆ 𝕐`, as real-valued functions on `ℙ(𝕏) × 𝔸`. -/
noncomputable def RFamily (P : Kernel (X × A) X) [IsMarkovKernel P]
    (Q : Kernel (A × X) Y) [IsMarkovKernel Q] (B : Set X) :
    {C : Set Y // MeasurableSet C} → ProbabilityMeasure X × A → ℝ :=
  fun C p => (jointLaw P Q p.1 p.2 (B ×ˢ C.1) : ℝ)

/-- `𝓡_B` is **equicontinuous at all the points** `(z, a) ∈ ℙ(𝕏) × 𝔸`, in the sequential form
the paper writes out in (5.15): whenever `z⁽ⁿ⁾ → z` weakly and `a⁽ⁿ⁾ → a`,
`sup_{C ∈ ℬ(𝕐)} |R(B × C | z⁽ⁿ⁾, a⁽ⁿ⁾) − R(B × C | z, a)| → 0`, written without a real supremum
(for every `ε > 0` there is `N` with the difference `≤ ε` for all `n ≥ N` and all Borel `C`). -/
def REquicontinuous [TopologicalSpace X] [OpensMeasurableSpace X] [TopologicalSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (B : Set X) : Prop :=
  ∀ (z : ProbabilityMeasure X) (a : A) (zs : ℕ → ProbabilityMeasure X) (as : ℕ → A),
    Tendsto zs atTop (𝓝 z) → Tendsto as atTop (𝓝 a) →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ C : {C : Set Y // MeasurableSet C},
        |RFamily P Q B C (zs n, as n) - RFamily P Q B C (z, a)| ≤ ε

end POMDP

end FeinbergPOMDP.WStar


