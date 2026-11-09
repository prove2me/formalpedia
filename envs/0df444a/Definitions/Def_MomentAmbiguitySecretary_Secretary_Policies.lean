-- Prove2me | Definitions.Def_MomentAmbiguitySecretary_Secretary_Policies
-- name    : MomentAmbiguitySecretary_Secretary_Policies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:53:06.548852+00:00
-- url     : https://prove2.me/theorems/ae71f260-78a3-41a5-b3d0-79d0becd4f6f
-- title:
--   Labeled measurable randomized cardinal secretary policies
-- statement:
--   For a horizon $m$, a path contains a uniform permutation $\sigma$ of $m$ labels and the independent labeled values $(X_i)$. At time $t$ the observation is $(\sigma(t),X_{\sigma(t)})$. A policy is a measurable probability kernel from its disclosure and path to an arrival time or no selection, with each stopping probability depending only on the observed prefix. Independent-model policies receive one realizable moment sequence per label; i.i.d. policies receive the common sequence. A cardinal policy with fixed auxiliary information is a section at that information.
--
--   The experiment uses the independent product of the uniform permutation and the product value measure, followed by the policy kernel. Success is the measurable event
--
--   $$\exists t:\ \text{selection}=t\ \text{and}\ \forall i,\ X_i\le X_{\sigma(t)}.$$
--
--   No selection fails. Every tied or zero maximizer counts. The success probability is proved to lie in $[0,1]$.
--
--   This extensional kernel representation retains arbitrary measurable private randomization; the finite-horizon correspondence with sequential stopping rules is explained in the local moderation notes.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, Definition 2.2 and §2.2, PDF/printed p.4–5, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Laws

open scoped NNReal

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MomentAmbiguitySecretary.Secretary

noncomputable section

instance finMeasurable (m : ℕ) : MeasurableSpace (Fin m) := ⊤
instance finSingleton (m : ℕ) : MeasurableSingletonClass (Fin m) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
instance optionFinMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
instance optionFinSingleton (m : ℕ) : MeasurableSingletonClass (Option (Fin m)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
instance permMeasurable (m : ℕ) : MeasurableSpace (Equiv.Perm (Fin m)) := ⊤
instance permSingleton (m : ℕ) : MeasurableSingletonClass (Equiv.Perm (Fin m)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

abbrev Path (m : ℕ) := Equiv.Perm (Fin m) × (Fin m → ℝ≥0)

def observation {m : ℕ} (p : Path m) (t : Fin m) : Fin m × ℝ≥0 :=
  (p.1 t, p.2 (p.1 t))

def AgreeThrough {m : ℕ} (t : Fin m) (p q : Path m) : Prop :=
  ∀ i : Fin m, i ≤ t → observation p i = observation q i

/-- A randomized stopping kernel. Prefix causality is imposed on every stopping mass;
the remaining probability is no selection. No law or future observation is disclosed.
This is the extensional single-choice representation used in the authors' OnlinePolicy file. -/
structure Policy (D : Type*) [MeasurableSpace D] (m : ℕ) where
  kernel : Kernel (D × Path m) (Option (Fin m))
  markov : IsMarkovKernel kernel
  causal : ∀ (d : D) (p q : Path m) (t : Fin m), AgreeThrough t p q →
    kernel (d, p) {some t} = kernel (d, q) {some t}

attribute [instance] Policy.markov

def rejectPolicy (D : Type*) [MeasurableSpace D] (m : ℕ) : Policy D m where
  kernel := Kernel.const _ (Measure.dirac none)
  markov := by infer_instance
  causal := by intros; rfl

instance (D : Type*) [MeasurableSpace D] (m : ℕ) : Nonempty (Policy D m) :=
  ⟨rejectPolicy D m⟩

abbrev IndependentPolicy (m : ℕ) := Policy (Fin m → Disclosure) m
abbrev IIDPolicy (m : ℕ) := Policy Disclosure m
abbrev CardinalPolicy (m : ℕ) := Policy Unit m

def uniformPermutation (m : ℕ) : ProbabilityMeasure (Equiv.Perm (Fin m)) :=
  ⟨(PMF.uniformOfFintype (Equiv.Perm (Fin m))).toMeasure, by infer_instance⟩

def experiment {m : ℕ} (μ : Fin m → Distribution) : ProbabilityMeasure (Path m) :=
  (uniformPermutation m).prod (ProbabilityMeasure.pi μ)

def fixedKernel {D : Type*} [MeasurableSpace D] {m : ℕ}
    (π : Policy D m) (d : D) : Kernel (Path m) (Option (Fin m)) :=
  π.kernel.comap (fun p => (d, p)) (measurable_const.prodMk measurable_id)

instance {D : Type*} [MeasurableSpace D] {m : ℕ} (π : Policy D m) (d : D) :
    IsMarkovKernel (fixedKernel π d) := by unfold fixedKernel; infer_instance

def outcomeLaw {D : Type*} [MeasurableSpace D] {m : ℕ}
    (π : Policy D m) (d : D) (μ : Fin m → Distribution) :
    ProbabilityMeasure (Path m × Option (Fin m)) :=
  ⟨(experiment μ : Measure _) ⊗ₘ fixedKernel π d, by infer_instance⟩

/-- Any original-value maximizer succeeds, including zero and ties; none fails. -/
def successEvent (m : ℕ) : Set (Path m × Option (Fin m)) :=
  {z | ∃ t : Fin m, z.2 = some t ∧ ∀ i : Fin m, z.1.2 i ≤ z.1.2 (z.1.1 t)}

def success {D : Type*} [MeasurableSpace D] {m : ℕ}
    (π : Policy D m) (d : D) (μ : Fin m → Distribution) : ℝ :=
  ((outcomeLaw π d μ : Measure _) (successEvent m)).toReal

theorem successEvent_measurable (m : ℕ) : MeasurableSet (successEvent m) := by
  have heq : successEvent m = ⋃ σ : Equiv.Perm (Fin m), ⋃ t : Fin m,
      {z : Path m × Option (Fin m) |
        z.1.1 = σ ∧ z.2 = some t ∧ ∀ i : Fin m, z.1.2 i ≤ z.1.2 (σ t)} := by
    ext z
    simp only [successEvent, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨t, ht, hmax⟩
      exact ⟨z.1.1, t, rfl, ht, hmax⟩
    · rintro ⟨σ, t, hσ, ht, hmax⟩
      exact ⟨t, ht, by simpa only [hσ] using hmax⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro σ
  apply MeasurableSet.iUnion
  intro t
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
    ((measurable_snd (measurableSet_singleton (some t))).inter
      (MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) (by fun_prop)))

/-- Structural range bound: probability ranges used by real extrema are bounded. -/
theorem success_mem_unit {D : Type*} [MeasurableSpace D] {m : ℕ}
    (π : Policy D m) (d : D) (μ : Fin m → Distribution) :
    success π d μ ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · change ((outcomeLaw π d μ : Measure _) (successEvent m)).toReal ≤ 1
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using
      (prob_le_one (μ := (outcomeLaw π d μ : Measure _)) (s := successEvent m)))

end
end MomentAmbiguitySecretary.Secretary


