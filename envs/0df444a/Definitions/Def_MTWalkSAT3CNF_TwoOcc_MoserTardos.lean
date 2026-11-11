-- Prove2me | Definitions.Def_MTWalkSAT3CNF_TwoOcc_MoserTardos
-- name    : MTWalkSAT3CNF_TwoOcc_MoserTardos
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:25:29.911191+00:00
-- url     : https://prove2.me/theorems/8cef0410-ba8c-4364-b37f-043f1fe67b60
-- title:
--   The Moser–Tardos resampling algorithm in the variable setting and on 3-CNF formulas
-- statement:
--   **Variable setting.** Let $V$ be a finite set of mutually independent variables, $x_v$ taking values in a measurable space $\mathcal X_v$ with law $\nu_v$. Events are indexed by a finite set $I$: event $i$ is a measurable set $A_i$ of joint values determined by the coordinates in a set $\mathrm{vbl}(i)\subseteq V$. Distinct events $i\ne j$ are **adjacent** in the dependency graph $G$ when $\mathrm{vbl}(i)\cap \mathrm{vbl}(j)\neq\emptyset$; $\bar\Gamma(i)$ is $i$ together with its neighbours, a set of events is **independent** when no two of its members are adjacent (the empty set is independent), and
--
--   $$\Psi_i(\mu)=\sum_{J\subseteq\bar\Gamma(i),\ J \text{ independent}}\ \prod_{j\in J}\mu_j .$$
--
--   **Algorithm.** Sample all variables from the product law $\pi=\bigotimes_v \nu_v$. While some event occurs, the rule chooses an occurring event $i$ and the coordinates in $\mathrm{vbl}(i)$ are replaced by fresh independent samples from the $\nu_v$, the others being kept. $T_{MT}$ is the first time no event occurs, $N_i$ the number of steps that resampled event $i$, and their expectations are taken over the trajectory law.
--
--   **On a 3-CNF formula** $F$ with $m$ clauses: all variables are unbiased bits, the events are indexed by the clause indices, $\mathrm{vbl}(i)=\mathrm{var}(C_i)$ and $A_i=\{\sigma: C_i \text{ is false under }\sigma\}$. A step replaces the three variables of the chosen unsatisfied clause by fresh independent unbiased bits and counts even if no value changes. The uniform rule chooses each index of $\mathrm{Bad}_F(X_t)$ with probability $1/|\mathrm{Bad}_F(X_t)|$, and the uniform distribution on assignments is the product of fair bits.
--
--   **Formalization Note** The trajectory law is `ProbabilityTheory.Kernel.trajMeasure` (Ionescu–Tulcea) of history-dependent step kernels; the state is the joint value and the record of the last chosen event. $T_{MT}$ and $N_i$ are `ℕ∞`-valued and expectations are `lintegral`s in `ℝ≥0∞`, so no integrability assumption is involved.
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), Definition 2.2 and Algorithm 2, pp. 9–10; Theorem 3.2, p. 11; proof of Theorem 3.1, pp. 11–12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Formula
import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Process

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Moser–Tardos resampling algorithm in the variable setting, and on a 3-CNF formula

Gao–He–Jiang, STOC 2027 submission #914 (October 2026), Definition 2.2 and Algorithm 2
(pp. 9–10), Theorem 3.2 (p. 11) and the proof of Theorem 3.1 (pp. 11–12).

Conventions.
* Variable setting: a finite set `V` of variables, the variable `v` taking values in a measurable
  space `X v` with law `ν v`, the variables mutually independent (product law
  `Measure.pi ν`). Events are indexed by a finite type `I` (two indices may carry the same set):
  event `i` is a measurable set `A i` of joint values, determined by the coordinates in
  `vbl i`. Two distinct events are adjacent when their `vbl` sets meet; the empty set of events
  is independent.
* The algorithm samples all variables from the product law. While some event occurs, the rule
  chooses an occurring event `i` and replaces the coordinates in `vbl i` by fresh independent
  samples from the `ν v`, leaving the others unchanged. The state records the last choice;
  once no event occurs the assignment is frozen and the record is `none`.
* `T_MT` is the hitting time of the set where no event occurs, `N_i` the number of steps that
  chose event `i`, and expectations are `lintegral`s in `ℝ≥0∞` of these `ℕ∞`-valued times.
* On a 3-CNF formula `F`: variables `V`, every `X v = Bool` with the fair-coin law, events
  indexed by the clause indices `Fin m`, `vbl i` the three variables of `C_i` and `A i` the
  event that `C_i` is false. Resampling `vbl i` replaces the three variables of `C_i` by fresh
  independent unbiased bits; the step counts even if no value changes.
-/

namespace MTWalkSAT3CNF.TwoOcc

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A finite family of events, indexed by `I`, determined by mutually independent variables
`(x_v)_{v ∈ V}` with laws `ν v`. -/
structure EventSystem (V : Type*) (X : V → Type*) [∀ v, MeasurableSpace (X v)] (I : Type*) where
  /-- the law of each variable -/
  ν : ∀ v, Measure (X v)
  /-- each law is a probability measure -/
  isProb : ∀ v, IsProbabilityMeasure (ν v)
  /-- the variables the event `i` depends on (and that the algorithm resamples) -/
  vbl : I → Finset V
  /-- the event `i`, a set of joint values -/
  A : I → Set (∀ v, X v)
  /-- every event is measurable -/
  measurableSet_A : ∀ i, MeasurableSet (A i)
  /-- the event `i` is determined by the coordinates in `vbl i` -/
  determined : ∀ (i : I) (x y : ∀ v, X v), (∀ v ∈ vbl i, x v = y v) → (x ∈ A i ↔ y ∈ A i)

attribute [instance] EventSystem.isProb

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, MeasurableSpace (X v)]
  {I : Type*} [Fintype I] [DecidableEq I]

namespace EventSystem

variable (E : EventSystem V X I)

/-- Adjacency in the dependency graph `G`: distinct events sharing a variable. -/
def Adj (i j : I) : Prop := i ≠ j ∧ (E.vbl i ∩ E.vbl j).Nonempty

instance (i j : I) : Decidable (E.Adj i j) := by unfold Adj; infer_instance

/-- `Γ̄(A_i)`: the event `i` together with all its neighbours in `G`. -/
def closedNbhd (i : I) : Finset I := Finset.univ.filter (fun j => j = i ∨ E.Adj i j)

/-- A set of events is independent in `G` (no two of its members are adjacent). -/
def IsIndep (J : Finset I) : Prop := ∀ j ∈ J, ∀ k ∈ J, ¬ E.Adj j k

instance (J : Finset I) : Decidable (E.IsIndep J) := by unfold IsIndep; infer_instance

/-- `Σ_{J ⊆ Γ̄(A_i), J independent} Π_{j ∈ J} μ_j` (the empty set contributes `1`). -/
def clusterSum (μ : I → ℝ) (i : I) : ℝ :=
  ∑ J ∈ (E.closedNbhd i).powerset.filter E.IsIndep, ∏ j ∈ J, μ j

/-- `P(A_i)` under the product law. -/
noncomputable def prob (i : I) : ℝ := (Measure.pi E.ν (E.A i)).toReal

/-- The events occurring at the joint value `x`. -/
def occurring (x : ∀ v, X v) : Set I := {i | x ∈ E.A i}

end EventSystem

/-- A state of the Moser–Tardos process: the current joint value and the record of the last
resampled event. -/
abbrev MTState (X : V → Type*) (I : Type*) : Type _ := (∀ v, X v) × Choice I

/-- An adaptive rule for Moser–Tardos on `E`: it selects a currently occurring event. -/
abbrev MTRule (E : EventSystem V X I) : Type _ :=
  AdaptiveRule (MTState X I) I (fun s => E.occurring s.1)

/-- The frozen step: keep the joint value, record no choice. -/
noncomputable def mtFrozenKernel (t : ℕ) : Kernel (Hist (MTState X I) t) (MTState X I) :=
  Kernel.deterministic (fun h => (h.cur.1, Choice.none))
    ((measurable_fst.comp (measurable_pi_apply _)).prodMk measurable_const)

/-- `N_i`: the number of steps that resampled the event `i`. -/
noncomputable def resampleCount (i : I) (ω : ℕ → MTState X I) : ℕ∞ :=
  {t : ℕ | (ω (t + 1)).2 = Choice.some i}.encard

namespace EventSystem

variable (E : EventSystem V X I)

/-- Whether the variable `v` belongs to the event recorded in `c`. -/
def inChosen (c : Choice I) (v : V) : Bool := c.elim false (fun i => decide (v ∈ E.vbl i))

/-- The new state after a choice `c` from the joint value `x`, given fresh samples `z` of all
variables: the coordinates in `vbl i` are taken from `z` when `c = some i`, the others are kept;
the choice is recorded. -/
def resampleMap (p : ((∀ v, X v) × Choice I) × (∀ v, X v)) : MTState X I :=
  (fun v => if E.inChosen p.1.2 v = true then p.2 v else p.1.1 v, p.1.2)

lemma measurable_resampleMap : Measurable E.resampleMap := by
  refine Measurable.prodMk (measurable_pi_lambda _ fun v => ?_) (measurable_snd.comp measurable_fst)
  refine Measurable.ite ?_ ((measurable_pi_apply v).comp measurable_snd)
    ((measurable_pi_apply v).comp (measurable_fst.comp measurable_fst))
  exact (measurable_snd.comp measurable_fst) (MeasurableSet.of_discrete
    (s := {c : Choice I | E.inChosen c v = true}))

/-- The resampling kernel: from `(x, c)`, resample the variables of the chosen event with fresh
independent samples from the product law. -/
noncomputable def resampleKernel : Kernel ((∀ v, X v) × Choice I) (MTState X I) :=
  (Kernel.id ×ₖ Kernel.const _ (Measure.pi E.ν)).map E.resampleMap

instance : IsMarkovKernel E.resampleKernel :=
  Kernel.IsMarkovKernel.map _ E.measurable_resampleMap

omit [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] in
lemma measurable_cur_fst (t : ℕ) :
    Measurable (fun h : Hist (MTState X I) t => h.cur.1) :=
  measurable_fst.comp (measurable_pi_apply _)

lemma measurableSet_someOccurs (t : ℕ) :
    MeasurableSet {h : Hist (MTState X I) t | ∃ i, h.cur.1 ∈ E.A i} := by
  have : {h : Hist (MTState X I) t | ∃ i, h.cur.1 ∈ E.A i} =
      ⋃ i, (fun h : Hist (MTState X I) t => h.cur.1) ⁻¹' E.A i := by
    ext h; simp
  rw [this]
  exact MeasurableSet.iUnion fun i => measurable_cur_fst t (E.measurableSet_A i)

open Classical in
/-- The `t`-th step kernel of Moser–Tardos under the rule `R`: if some event occurs at the
current state, the rule chooses one and its variables are resampled; otherwise the state is
frozen. -/
noncomputable def mtStep (R : MTRule E) (t : ℕ) :
    Kernel (Hist (MTState X I) t) (MTState X I) :=
  Kernel.piecewise (E.measurableSet_someOccurs t)
    (E.resampleKernel ∘ₖ (Kernel.deterministic (fun h => h.cur.1) (measurable_cur_fst t) ×ₖ
      R.pick t))
    (mtFrozenKernel t)

instance (R : MTRule E) (t : ℕ) : IsMarkovKernel (E.mtStep R t) := by
  unfold mtStep mtFrozenKernel; infer_instance

/-- The initial law: all variables sampled from the product law, no choice recorded. -/
noncomputable def mtInit : Measure (MTState X I) :=
  (Measure.pi E.ν).map (fun x => (x, Choice.none))

/-- The law of the Moser–Tardos trajectory `(X_t)_{t ∈ ℕ}` under the rule `R`. -/
noncomputable def mtLaw (R : MTRule E) : Measure (ℕ → MTState X I) :=
  Kernel.trajMeasure E.mtInit (E.mtStep R)

/-- `T_MT`: the first time at which no event occurs (`⊤` if never). -/
noncomputable def mtTimeOf (ω : ℕ → MTState X I) : ℕ∞ :=
  hitTime (fun s : MTState X I => ∀ i, s.1 ∉ E.A i) ω

/-- `E[T_MT]` under the rule `R`. -/
noncomputable def expectedTime (R : MTRule E) : ℝ≥0∞ :=
  ∫⁻ ω, (E.mtTimeOf ω : ℝ≥0∞) ∂(E.mtLaw R)

/-- `E[N_i]` under the rule `R`. -/
noncomputable def expectedResamples (R : MTRule E) (i : I) : ℝ≥0∞ :=
  ∫⁻ ω, (resampleCount i ω : ℝ≥0∞) ∂(E.mtLaw R)

end EventSystem

/-! ### Moser–Tardos on a 3-CNF formula -/

/-- The law of an unbiased bit. -/
noncomputable def bitLaw : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure bitLaw := by unfold bitLaw; infer_instance

/-- The uniform distribution on assignments `{0,1}^V` (independent unbiased bits). -/
noncomputable def uniformAssignment (V : Type*) [Fintype V] : Measure (V → Bool) :=
  Measure.pi (fun _ : V => bitLaw)

variable {m : ℕ}

/-- The variable setting of a 3-CNF formula `F`: unbiased bits, one bad event per clause index,
`A_i = {σ : C_i is false under σ}`, determined by the three variables of `C_i`. -/
noncomputable def cnfSystem (F : Formula V m) : EventSystem V (fun _ => Bool) (Fin m) where
  ν := fun _ => bitLaw
  isProb := fun _ => inferInstance
  vbl i := Finset.univ.image (F i).var
  A i := {σ | ∀ p : Fin 3, ¬ LitTrue σ (F i) p}
  measurableSet_A i := (Set.to_countable _).measurableSet
  determined i x y hxy := by
    have h : ∀ p : Fin 3, x ((F i).var p) = y ((F i).var p) := fun p =>
      hxy _ (Finset.mem_image.2 ⟨p, Finset.mem_univ _, rfl⟩)
    show (∀ p : Fin 3, ¬ LitTrue x (F i) p) ↔ ∀ p : Fin 3, ¬ LitTrue y (F i) p
    simp only [LitTrue, h]

/-- The uniform clause-selection rule for Moser–Tardos on `F`: each index of
`Bad_F(X_t)` with probability `1/|Bad_F(X_t)|`. -/
noncomputable def uniformRuleMT (F : Formula V m) : MTRule (cnfSystem F) :=
  uniformRule (fun s : MTState (fun _ : V => Bool) (Fin m) => (cnfSystem F).occurring s.1)
    (fun s => bad F s.1) (fun s => by
    ext i; simp [bad, EventSystem.occurring, cnfSystem])

end MTWalkSAT3CNF.TwoOcc


