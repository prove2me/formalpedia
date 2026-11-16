-- Prove2me | Definitions.Def_GMRDiversity_Supplement_GMRFramework
-- name    : GMRDiversity_Supplement_GMRFramework
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:07:12.786879+00:00
-- url     : https://prove2.me/theorems/37d1e316-7adc-4af2-baf3-d9f7eaf2961a
-- title:
--   GMR frameworks with one generation, one mutation and one recombination rule
-- statement:
--   A **generation–mutation–recombination (GMR) framework** (Definition 1) is a tuple $\mathcal G=(X,U,\mathcal D,c,\mathrm{Obs})$: a space $X$ of candidate solutions, a hidden objective $U:X\to\mathbb R$, families $\mathcal D_k$ of $k$-input distribution rules and inference costs $c:\mathcal D\to\mathbb N_{>0}$. This definition is the subclass to which Theorems 1 and 2 of the paper belong:
--
--   1. $\mathcal D_0=\{\text{generation}\}$, a probability distribution on $X$;
--   2. $\mathcal D_1=\{\text{mutation}\}$, a distribution $\text{mutation}(x)$ on $X$ for every $x\in X$;
--   3. $\mathcal D_2=\{\text{recombination}\}$, a distribution $\text{recombination}(x_1,x_2)$ on $X$ for every ordered pair of parents;
--   4. $\mathcal D_k=\emptyset$ for $k\ge3$;
--   5. costs $c_G,c_M,c_R\in\mathbb N_{>0}$ for generation, mutation and recombination;
--   6. full feedback: after producing $z_t$ the policy observes $o_t=(z_t,U(z_t))$.
--
--   The definition also fixes the action alphabet of a policy: in each round it either generates, mutates the candidate of an earlier round, or recombines the candidates of two earlier rounds (not necessarily distinct), and each action carries the cost of its operator.
--
--   **Formalization Note** $X$ is a measurable space, $U$ is measurable, generation is a probability measure and mutation and recombination are Markov kernels, so that the run of an adaptive policy is a probability measure (the paper assumes all expectations are well-defined). An action names earlier rounds by $0$-based indices; an index that names no earlier round is read as the latest earlier round, which reparametrizes the legal actions without changing any policy. Full feedback is built into the policy type `GMRDiversity.Supplement.Policy`.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), Definition 1, p.3, and §2 'Feedback model', 'Policies', p.4

import Mathlib

namespace GMRDiversity.Supplement

open MeasureTheory ProbabilityTheory

/-- **The operator called in one round** of a three-operator GMR framework (Brandenberger,
Doron-Arad, Mossel, *Genetic Algorithms with Optimization Guided Operators*, STOC 2027 submission,
manuscript sha256 f89f4f77…, §2 "Policies", p.4): `generate` is a call of the generation rule
(`k = 0`), `mutate i` a call of the mutation rule on the candidate of round `i + 1` (`k = 1`), and
`recombine i j` a call of the recombination rule on the candidates of rounds `i + 1` and `j + 1`
(`k = 2`, the two indices not necessarily distinct).

**Formalization Note.** Indices are `0`-based (index `i` names round `i + 1`). An index that does
not name an earlier round is read as the latest earlier round (see `GMRDiversity.Supplement.cand`),
so every value of `Op` is a legal action: this reparametrizes the actions "previous indices
`i₁, …, i_k < t`" of p.4 and changes no policy. -/
inductive Op where
  | generate
  | mutate (i : ℕ)
  | recombine (i j : ℕ)
  deriving DecidableEq

instance : Countable Op := by
  have : Function.Injective (fun o : Op => match o with
    | .generate => (0, 0, 0) | .mutate i => (1, i, 0) | .recombine i j => (2, i, j)) := by
    intro a b h; cases a <;> cases b <;> simp_all
  exact this.countable

/-- Every set of actions is measurable (a countable discrete space). -/
instance : MeasurableSpace Op := ⊤

instance : DiscreteMeasurableSpace Op := ⟨fun _ => trivial⟩

/-- **A GMR framework with one generation, one mutation and one recombination rule and full
feedback** (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with Optimization Guided
Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, Definition 1, p.3, and the feedback
model, p.4): a candidate space `X`, a hidden objective `U : X → ℝ`, `D = D₀ ∪ D₁ ∪ D₂` with
`D₀ = {generation}` (a distribution on `X`), `D₁ = {mutation}` (a distribution `mutation(x)` for
every `x ∈ X`), `D₂ = {recombination}` (a distribution `recombination(x₁, x₂)` for every pair) and
`D_k = ∅` for `k ≥ 3`, with inference costs `c_G, c_M, c_R ∈ ℕ_{>0}`. Feedback is full,
`o_t = (z_t, U(z_t))`.

This is the subclass of Definition 1 to which both Theorem 1 (§4, p.6) and Theorem 2 (§5, p.7)
belong.

**Formalization Note.** `X` is a measurable space, `U` is measurable, the generation law is a
probability measure and mutation and recombination are Markov kernels (measurable families of
probability measures), so that the run of an adaptive policy is a well-defined probability measure
("all expectations below are assumed to be well-defined", p.3). Full feedback is encoded in
`GMRDiversity.Supplement.Policy`: a policy observes every queried candidate `z_t`, from which
`U(z_t)` is determined. -/
structure GMRFramework (X : Type) [MeasurableSpace X] where
  /-- The hidden objective `U`. -/
  U : X → ℝ
  measurable_U : Measurable U
  /-- The generation rule `D ∈ D₀`. -/
  generation : Measure X
  generation_prob : IsProbabilityMeasure generation
  /-- The mutation rule `D ∈ D₁`. -/
  mutation : Kernel X X
  mutation_markov : IsMarkovKernel mutation
  /-- The recombination rule `D ∈ D₂` (ordered parents). -/
  recombination : Kernel (X × X) X
  recombination_markov : IsMarkovKernel recombination
  /-- The cost `c_G` of a generation. -/
  cG : ℕ
  /-- The cost `c_M` of a mutation. -/
  cM : ℕ
  /-- The cost `c_R` of a recombination. -/
  cR : ℕ
  cG_pos : 0 < cG
  cM_pos : 0 < cM
  cR_pos : 0 < cR

/-- The inference cost `c(D_t)` of an action. -/
def Op.cost {X : Type} [MeasurableSpace X] (F : GMRFramework X) : Op → ℕ
  | .generate => F.cG
  | .mutate _ => F.cM
  | .recombine _ _ => F.cR

/-- The action is a generation. -/
def Op.isGen : Op → Bool
  | .generate => true
  | _ => false

/-- The action is a mutation. -/
def Op.isMut : Op → Bool
  | .mutate _ => true
  | _ => false

/-- The action is a recombination. -/
def Op.isRec : Op → Bool
  | .recombine _ _ => true
  | _ => false

end GMRDiversity.Supplement


