-- Prove2me | Definitions.Def_FeinbergPOMDP_Setwise_Model
-- name    : FeinbergPOMDP_Setwise_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:56.062183+00:00
-- url     : https://prove2.me/theorems/02334f2a-8be4-48bd-b610-8221cbe95cde
-- title:
--   Example 4.1 model and belief transition
-- statement:
--   The model uses hidden states $X=\{1,2\}$, observations $Y=[0,1]$, and actions $A=\{0\}\cup\{1/n:n\ge1\}$ with the topology inherited from $\mathbb R$. State 1 and state 2 are encoded by `0` and `1` of `Fin 2`. The state transition $P$ leaves the state unchanged. Write $m$ for Lebesgue probability measure on $Y$. For each $n\ge1$, equation (4.1) defines a density $f^{(n)}$ that is zero on the open intervals $(2k/2^n,(2k+1)/2^n)$, $0\le k<2^{n-1}$, and is two elsewhere. The measure $m^{(n)}$ is $f^{(n)}m$. The observation law is $Q(\cdot\mid a,1)=Q(\cdot\mid0,2)=m$ and $Q(\cdot\mid1/n,2)=m^{(n)}$.
--
--   For general transition and observation kernels $P$ and $Q$, the definitions also provide the next-state and observation joint law $R$ of (3.1), its observation marginal $R'$ of (3.2), the predicate that a filter $H$ satisfies the disintegration identity (3.3), and the posterior transition
--
--   $$
--   q_H(D\mid z,a)=\int_Y \mathbf 1_{\{H(z,a,y)\in D\}}\,R'(dy\mid z,a)
--   $$
--
--   of (3.5). Sequential weak, setwise, and total-variation continuity use the tests specified on page 4. The fixed belief $z$ is $(1/2,1/2)$, and the two later posterior points are $(1/3,2/3)$ and $(1,0)$.
--
--   These shared objects let every statement about the example refer to the same model and the same version-independent belief transition.
--
--   **Formalization Note** Lean indexes the paper's positive $n$ with a subtype of positive natural numbers. The action space is a real subtype, so $1/n\to0$ in its subspace topology. The Borel σ-algebra of the weak topology is used for $q_H$; Mathlib's default measurable structure on probability measures is Giry's. The filter predicate asks for measurability in the observation variable for each fixed belief and action, as needed for (3.3) and (3.5). The example involves no cost, initial observation kernel, initial prior, or discount factor.
-- source:
--   Feinberg, Kasyanov, Zgurovsky, Partially Observable Total-Cost Markov Decision Processes with Weakly Continuous Transition Probabilities, arXiv:1401.2168v2, §2 p. 4, (3.1)–(3.5) pp. 7–8, Example 4.1 pp. 13–14

import Mathlib

namespace FeinbergPOMDP.Setwise

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology BoundedContinuousFunction

/-- Feinberg–Kasyanov–Zgurovsky, arXiv:1401.2168v2, §2, p. 4.
Sequential setwise convergence: probabilities of every measurable set converge. -/
def SetwiseConverges {T : Type*} [MeasurableSpace T]
    (μ : ℕ → Measure T) (ν : Measure T) : Prop :=
  (∀ n, IsProbabilityMeasure (μ n)) ∧ IsProbabilityMeasure ν ∧
    ∀ C : Set T, MeasurableSet C → Tendsto (fun n => μ n C) atTop (𝓝 (ν C))

/-- §2, p. 4. Sequential total-variation convergence, tested on all measurable
real functions with values in `[-1,1]`. -/
def TVConverges {T : Type*} [MeasurableSpace T]
    (μ : ℕ → Measure T) (ν : Measure T) : Prop :=
  (∀ n, IsProbabilityMeasure (μ n)) ∧ IsProbabilityMeasure ν ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ f : T → ℝ,
      Measurable f → (∀ t, |f t| ≤ 1) →
        |(∫ t, f t ∂(μ n)) - (∫ t, f t ∂ν)| ≤ ε

/-- §2, p. 4. Sequential weak convergence, using bounded continuous tests. -/
def WeakConverges {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    [OpensMeasurableSpace T]
    (μ : ℕ → Measure T) (ν : Measure T) : Prop :=
  (∀ n, IsProbabilityMeasure (μ n)) ∧ IsProbabilityMeasure ν ∧
    ∀ g : T →ᵇ ℝ,
      Tendsto (fun n => ∫ t, g t ∂(μ n)) atTop (𝓝 (∫ t, g t ∂ν))

/-- §2, p. 4. Sequential weak continuity of a measure-valued kernel. -/
def WeaklyContinuous {S T : Type*} [TopologicalSpace S]
    [TopologicalSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    (K : S → Measure T) : Prop :=
  ∀ (s : S) (ss : ℕ → S), Tendsto ss atTop (𝓝 s) →
    WeakConverges (fun n => K (ss n)) (K s)

/-- §2, p. 4. Sequential setwise continuity of a measure-valued kernel. -/
def SetwiseContinuous {S T : Type*} [TopologicalSpace S]
    [MeasurableSpace T] (K : S → Measure T) : Prop :=
  ∀ (s : S) (ss : ℕ → S), Tendsto ss atTop (𝓝 s) →
    SetwiseConverges (fun n => K (ss n)) (K s)

/-- §2, p. 4. Sequential continuity in total variation. -/
def TVContinuous {S T : Type*} [TopologicalSpace S]
    [MeasurableSpace T] (K : S → Measure T) : Prop :=
  ∀ (s : S) (ss : ℕ → S), Tendsto ss atTop (𝓝 s) →
    TVConverges (fun n => K (ss n)) (K s)

/-- (3.1), p. 7: the joint law of the next state and observation. The input
`z` is the prior belief; `P` and `Q` have the paper's argument order. -/
noncomputable def R {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] (P : Kernel (X × A) X) (Q : Kernel (A × X) Y)
    (z : ProbabilityMeasure X) (a : A) : Measure (X × Y) :=
  (((z : Measure X).bind (fun x => P (x, a))) ⊗ₘ
    (Q.comap (fun x' => (a, x')) (by fun_prop)))

/-- (3.2), p. 8: the observation marginal of `R`. -/
noncomputable def Rprime {X Y A : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace A] (P : Kernel (X × A) X)
    (Q : Kernel (A × X) Y) (z : ProbabilityMeasure X) (a : A) : Measure Y :=
  (R P Q z a).map Prod.snd

/-- (3.3), p. 8: `H` is a version of the conditional next-state law.
The two measurability clauses use Mathlib's Giry σ-algebra and the paper's Borel
σ-algebra on probability measures. Measurability is stated in `y` for fixed
`(z,a)`; the paper also describes a jointly measurable version. -/
def IsFilter {X Y A : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace A]
    (P : Kernel (X × A) X) (Q : Kernel (A × X) Y)
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) : Prop :=
  (∀ z a, Measurable (H z a)) ∧
  (∀ z a, @Measurable Y (ProbabilityMeasure X) _ (borel (ProbabilityMeasure X)) (H z a)) ∧
  ∀ z a (B : Set X) (C : Set Y), MeasurableSet B → MeasurableSet C →
    R P Q z a (B ×ˢ C) =
      ∫⁻ y in C, (H z a y : Measure X) B ∂(Rprime P Q z a)

/-- (3.5), p. 8: the law of the posterior under the observation marginal.
Its target σ-algebra is the Borel σ-algebra of the weak topology. -/
noncomputable def beliefTransition {X Y A : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace A]
    (P : Kernel (X × A) X) (Q : Kernel (A × X) Y)
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X)
    (z : ProbabilityMeasure X) (a : A) :
    @Measure (ProbabilityMeasure X) (borel (ProbabilityMeasure X)) :=
  @Measure.map Y (ProbabilityMeasure X) _ (borel (ProbabilityMeasure X))
    (H z a) (Rprime P Q z a)

/-- Example 4.1, p. 13: the two hidden states, with paper state 1 at `0`
and paper state 2 at `1`. -/
abbrev State := Fin 2

/-- Example 4.1, p. 13: observations in `[0,1]`. -/
abbrev Observation := unitInterval

/-- Example 4.1, p. 13: the literal action subspace of the real line. -/
abbrev Action := {a : ℝ // a = 0 ∨ ∃ n : ℕ, 1 ≤ n ∧ a = 1 / (n : ℝ)}

instance : Countable Action := by
  have hs : Set.Countable
      ({a : ℝ | a = 0 ∨ ∃ n : ℕ, 1 ≤ n ∧ a = 1 / (n : ℝ)}) := by
    apply ((Set.countable_singleton (0 : ℝ)).union
      (Set.countable_range (fun n : ℕ => 1 / (n : ℝ)))).mono
    intro a ha
    rcases ha with h | ⟨n, _, h⟩
    · exact Or.inl (by simpa [h])
    · exact Or.inr ⟨n, h.symm⟩
  exact hs.to_subtype

/-- The paper indexes its dyadic densities by the positive integers. -/
abbrev PositiveNat := {n : ℕ // 1 ≤ n}

/-- Example 4.1, p. 13: action `1/n`, `n ≥ 1`. -/
noncomputable def reciprocalAction (n : PositiveNat) : Action :=
  ⟨1 / (n.1 : ℝ), Or.inr ⟨n.1, n.2, rfl⟩⟩

/-- Example 4.1, p. 13: action zero. -/
def zeroAction : Action := ⟨0, Or.inl rfl⟩

/-- Example 4.1, equation (4.1), p. 13. The zero intervals are open;
dyadic endpoints therefore get density 2, as printed. -/
noncomputable def density (n : PositiveNat) (y : Observation) : ℝ≥0∞ :=
  if ∃ k : ℕ, k < 2 ^ (n.1 - 1) ∧
      (2 * (k : ℝ)) / (2 ^ n.1 : ℝ) < (y : ℝ) ∧
      (y : ℝ) < (2 * (k : ℝ) + 1) / (2 ^ n.1 : ℝ)
  then 0 else 2

/-- Example 4.1, pp. 13–14: `m^(n) = f^(n) m` with Lebesgue
probability measure `m` on `[0,1]`. -/
noncomputable def dyadicLaw (n : PositiveNat) : Measure Observation :=
  (volume : Measure Observation).withDensity (density n)

/-- A nonzero action has an index `n ≥ 1` with value `1/n`. -/
noncomputable def actionIndex (a : Action) (ha : a.1 ≠ 0) : PositiveNat := by
  let h : ∃ n : ℕ, 1 ≤ n ∧ a.1 = 1 / (n : ℝ) := a.2.resolve_left ha
  exact ⟨Classical.choose h, (Classical.choose_spec h).1⟩

/-- Example 4.1, p. 13: the state does not move. -/
noncomputable def transition : Kernel (State × Action) State :=
  Kernel.deterministic Prod.fst (by fun_prop)

instance : IsMarkovKernel transition := by
  unfold transition
  infer_instance

/-- Example 4.1, p. 13: observation law. At state 1 and at action 0 it
is Lebesgue measure; at state 2 and action `1/n` it is `m^(n)`. -/
noncomputable def observationKernel : Kernel (Action × State) Observation where
  toFun p :=
    if hs : p.2 = 0 then volume
    else if ha : p.1.1 = 0 then volume
    else dyadicLaw (actionIndex p.1 ha)
  measurable' := by
    exact measurable_of_countable _

/-- Example 4.1, p. 14: the prior belief `(1/2,1/2)`. -/
noncomputable def prior : ProbabilityMeasure State :=
  ⟨ProbabilityTheory.bernoulliMeasure (0 : State) 1 ⟨1 / 2, by norm_num⟩,
    inferInstance⟩

/-- Example 4.1, p. 14: posterior `(1/3,2/3)` on the high-density event. -/
noncomputable def posteriorHigh : ProbabilityMeasure State :=
  ⟨ProbabilityTheory.bernoulliMeasure (0 : State) 1 ⟨1 / 3, by norm_num⟩,
    inferInstance⟩

/-- Example 4.1, p. 14: posterior `(1,0)` on the zero-density event. -/
noncomputable def posteriorLow : ProbabilityMeasure State :=
  ⟨Measure.dirac (0 : State), inferInstance⟩

end FeinbergPOMDP.Setwise


