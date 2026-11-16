-- Prove2me | Definitions.Def_GMRDiversity_Supplement_Policy
-- name    : GMRDiversity_Supplement_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:07:47.041884+00:00
-- url     : https://prove2.me/theorems/6f8ee396-325e-4369-a9bd-5c39d957ee0d
-- title:
--   Adaptive randomized policies with full feedback and their run law
-- statement:
--   Let $\mathcal G$ be a GMR framework with one generation, one mutation and one recombination rule and full feedback. A **policy** $\pi\in\Pi^{\mathrm{obs}}_{\mathcal G}$ acts in rounds $t=1,2,\dots$. In round $1$ it generates. In every later round, after observing the history $(z_1,U(z_1)),\dots,(z_{t-1},U(z_{t-1}))$ and its own earlier actions, it chooses at random either
--
--   1. a generation, querying $z_t\sim\text{generation}$;
--   2. a mutation of an earlier candidate $z_i$, $i<t$, querying $z_t\sim\text{mutation}(z_i)$; or
--   3. a recombination of two earlier candidates $z_i,z_j$, $i,j<t$ not necessarily distinct, querying $z_t\sim\text{recombination}(z_i,z_j)$.
--
--   The randomness of every operator call is fresh and independent of everything before it. The **run** of $\pi$ is the law of the infinite sequence $\omega=((D_1,z_1),(D_2,z_2),\dots)$ of actions and candidates; it is the unique probability measure built from the first generation and the round-by-round kernels by the Ionescu-Tulcea theorem.
--
--   The value $V^\pi_T$, the budgeted optimum $V^*_n$ and the operator counts are all functionals of this run law.
--
--   **Formalization Note** The policy is behavioural: the action of round $t+2$ is drawn from a Markov kernel of the whole history of rounds $1,\dots,t+1$ (perfect recall), which yields the same joint law of actions and candidates as a policy with a shared internal seed. Under full feedback $U(z_s)$ is a function of $z_s$, so observing $z_s$ is observing $o_s$. The run law is `Kernel.trajMeasure`.
-- source:
--   A. Brandenberger, I. Doron-Arad, E. Mossel, Genetic Algorithms with Optimization Guided Operators, STOC 2027 submission (manuscript sha256 f89f4f770d5d05df82f0407a81287ce4ccf618727beb5415eef3ad56c36b6cbe), §2 'Policies', p.4

import Mathlib
import Definitions.Def_GMRDiversity_Supplement_GMRFramework

namespace GMRDiversity.Supplement

open MeasureTheory ProbabilityTheory Finset

variable {X : Type} [MeasurableSpace X]

/-- The observed history after rounds `1, …, t + 1`: for each round its action and its candidate
(slot `s` holds round `s + 1`). -/
abbrev Hist (X : Type) (t : ℕ) : Type := Π _ : Iic t, Op × X

/-- The candidate named by index `i` in a history of rounds `1, …, t + 1`; an index beyond the
history is read as the latest round `t + 1`. -/
def cand {t : ℕ} (h : Hist X t) (i : ℕ) : X :=
  (h ⟨min i t, Finset.mem_Iic.2 (min_le_right _ _)⟩).2

lemma measurable_cand (t i : ℕ) : Measurable (fun h : Hist X t => cand h i) :=
  measurable_snd.comp (measurable_pi_apply _)

/-- The law of the candidate produced by an action, given the history. -/
noncomputable def opMeasure (F : GMRFramework X) {t : ℕ} (h : Hist X t) : Op → Measure X
  | .generate => F.generation
  | .mutate i => F.mutation (cand h i)
  | .recombine i j => F.recombination (cand h i, cand h j)

/-- The operator kernel: history and action ↦ law of the new candidate. -/
noncomputable def opKernel (F : GMRFramework X) (t : ℕ) : Kernel (Hist X t × Op) X where
  toFun p := opMeasure F p.1 p.2
  measurable' := by
    refine measurable_from_prod_countable_left (fun o => ?_)
    cases o with
    | generate => exact measurable_const
    | mutate i => exact F.mutation.measurable.comp (measurable_cand t i)
    | recombine i j =>
      exact F.recombination.measurable.comp ((measurable_cand t i).prodMk (measurable_cand t j))

instance (F : GMRFramework X) (t : ℕ) : IsMarkovKernel (opKernel F t) := by
  refine ⟨fun p => ?_⟩
  have := F.generation_prob; have := F.mutation_markov; have := F.recombination_markov
  change IsProbabilityMeasure (opMeasure F p.1 p.2)
  cases p.2 <;> simp only [opMeasure] <;> infer_instance

/-- **Adaptive randomized policies with full feedback** `Π^obs_G` for a three-operator GMR
framework (Brandenberger, Doron-Arad, Mossel, *Genetic Algorithms with Optimization Guided
Operators*, STOC 2027 submission, manuscript sha256 f89f4f77…, §2 "Policies", p.4): "at each round
`t`, after observing the feedback history `o₁, …, o_{t−1}`, [π] chooses an integer `k` and a
distribution rule `D ∈ D_k`. If `k = 0`, it queries `z_t ∼ D`. If `k ≥ 1`, it chooses previous
indices `i₁, …, i_k < t`, not necessarily distinct, and queries `z_t ∼ D(z_{i₁}, …, z_{i_k})`. At
round `t = 1`, only generation … is feasible."

`act t` is the law of the action of round `t + 2` given the history of rounds `1, …, t + 1`
(their actions and candidates). Round `1` is always a generation.

**Formalization Note.** Randomization is behavioural: every round draws its action from a Markov
kernel of the whole history, which includes the policy's own earlier actions (perfect recall).
For a history-dependent randomized policy this induces the same joint law of actions and candidates
as a policy with a shared internal seed, so value and cost are those of p.4. Under full feedback
`o_s = (z_s, U(z_s))` and `U` is a fixed function, so observing `z_s` is observing `o_s`. -/
structure Policy (F : GMRFramework X) where
  /-- Law of the action of round `t + 2` given rounds `1, …, t + 1`. -/
  act : (t : ℕ) → Kernel (Hist X t) Op
  act_markov : ∀ t, IsMarkovKernel (act t)

/-- One round: draw the action, then the candidate from the chosen operator. -/
noncomputable def stepKernel {F : GMRFramework X} (π : Policy F) (t : ℕ) :
    Kernel (Hist X t) (Op × X) :=
  (π.act t) ⊗ₖ (opKernel F t)

instance {F : GMRFramework X} (π : Policy F) (t : ℕ) : IsMarkovKernel (stepKernel π t) := by
  have := π.act_markov t; unfold stepKernel; infer_instance

/-- **The run of a policy**: the law of the infinite sequence `ω` of (action, candidate) pairs,
`ω s = (D_{s+1}, z_{s+1})`, built by the Ionescu-Tulcea theorem (`Kernel.trajMeasure`) from the
first round (a generation, `z₁ ∼ generation`) and the kernels `stepKernel π`. The fresh randomness
of every operator call is independent of everything before it (p.4). -/
noncomputable def runLaw {F : GMRFramework X} (π : Policy F) : Measure (ℕ → Op × X) :=
  Kernel.trajMeasure (X := fun _ => Op × X)
    (F.generation.map (fun z => (Op.generate, z))) (stepKernel π)

instance {F : GMRFramework X} (π : Policy F) : IsProbabilityMeasure (runLaw π) := by
  have := F.generation_prob
  unfold runLaw
  have : IsProbabilityMeasure (F.generation.map (fun z => (Op.generate, z))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  infer_instance

end GMRDiversity.Supplement


