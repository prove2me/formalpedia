-- Prove2me | Definitions.Def_DirectionalBallisticity
-- name    : DirectionalBallisticity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:08.009726+00:00
-- url     : https://prove2.me/theorems/c6a12a76-a47d-44e5-b362-74c4955250a3
-- statement:
--   For a nonnegative integer d, the lattice is ℤᵈ, real vectors lie in ℝᵈ, and directions are coordinate indices paired with a sign, giving steps ±eᵢ. A row assigns nonnegative real weights summing to one to these directions; an environment assigns a row to each lattice site. States pair an environment with a position, and paths are sequences of lattice positions indexed by nonnegative integers. For a measure ν on rows, environmentLaw is the product measure with marginal ν at every site, so for probability ν the site rows are independent and identically distributed. UniformElliptic(ν) means that some κ>0 bounds every direction weight below for ν-almost every row. The current-row evaluation is measurable. The transition kernel keeps the environment fixed and moves from x to x±eᵢ with the corresponding weight in its row; it is a Markov kernel, as is the history kernel that applies this transition to the latest state. The initial law samples the environment and starts at the origin, and annealedLaw is the position-path marginal of the resulting trajectory measure. Using the usual dot product and coordinatewise embedding of lattice positions into ℝᵈ, DirectionallyTransient(ν,ℓ) means Xₙ·ℓ→+∞ almost surely under annealedLaw, while HasVelocity(ν,v) means Xₙ/n→v almost surely. MainStatement is the defined proposition that, for every d≥2, every uniformly elliptic probability measure ν on rows, and every unit vector ℓ, directional transience along ℓ implies the existence of a deterministic velocity v with v·ℓ>0 and HasVelocity(ν,v).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectionalBallisticity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DirectionalBallisticity.lean; bytes 16..3828
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

abbrev Lattice (d : ℕ) := Fin d → ℤ
abbrev Direction (d : ℕ) := Fin d × Bool
abbrev Vector (d : ℕ) := Fin d → ℝ
abbrev Row (d : ℕ) := {p : Direction d → ℝ≥0 // ∑ e, p e = 1}
abbrev Environment (d : ℕ) := Lattice d → Row d
abbrev State (d : ℕ) := Environment d × Lattice d
abbrev Path (d : ℕ) := ℕ → Lattice d

def step {d : ℕ} (e : Direction d) : Lattice d :=
  fun i => if i = e.1 then (if e.2 then 1 else -1) else 0

noncomputable def environmentLaw {d : ℕ} (ν : Measure (Row d)) :
    Measure (Environment d) := Measure.infinitePi (fun _ => ν)

def UniformElliptic {d : ℕ} (ν : Measure (Row d)) : Prop :=
  ∃ κ : ℝ≥0, 0 < κ ∧ ∀ᵐ p ∂ν, ∀ e, κ ≤ p.1 e

lemma measurable_current_row {d : ℕ} :
    Measurable (fun z : State d => z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro x
  exact measurable_pi_apply x

noncomputable def transition {d : ℕ} : Kernel (State d) (State d) where
  toFun z := ∑ e : Direction d,
    ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step e)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_fun_sum
    intro e _
    apply Measurable.mul
    · exact (measurable_pi_apply e |>.comp
        (measurable_subtype_coe.comp measurable_current_row)).coe_nnreal_ennreal
    · exact (Measure.measurable_coe hs).comp
        (Measure.measurable_dirac.comp (measurable_fst.prodMk
          (measurable_snd.add_const (step e))))

instance transition_markov {d : ℕ} : IsMarkovKernel (transition (d := d)) where
  isProbabilityMeasure z := by
    constructor
    change (∑ e : Direction d,
      ((z.1 z.2).1 e : ℝ≥0∞) • Measure.dirac (z.1, z.2 + step e)) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
      (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofNNReal_finsetSum, (z.1 z.2).2]
    rfl

noncomputable def historyTransition {d : ℕ} (n : ℕ) :
    Kernel ((i : Finset.Iic n) → State d) (State d) where
  toFun z := transition (z ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := transition.measurable.comp (measurable_pi_apply _)

instance historyTransition_markov {d : ℕ} (n : ℕ) :
    IsMarkovKernel (historyTransition (d := d) n) where
  isProbabilityMeasure _ := transition_markov.isProbabilityMeasure _

noncomputable def initialLaw {d : ℕ} (ν : Measure (Row d)) : Measure (State d) :=
  (environmentLaw ν).map (fun ω => (ω, (0 : Lattice d)))

noncomputable def annealedLaw {d : ℕ} (ν : Measure (Row d)) : Measure (Path d) :=
  (@Kernel.trajMeasure (fun _ => State d) _ (initialLaw ν) (historyTransition (d := d)) _).map
    (fun z n => (z n).2)

def dot {d : ℕ} (v ℓ : Vector d) : ℝ := ∑ i, v i * ℓ i

def realPosition {d : ℕ} (x : Lattice d) : Vector d := fun i => (x i : ℝ)

def DirectionallyTransient {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) : Prop :=
  ∀ᵐ X ∂annealedLaw ν,
    Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop

def HasVelocity {d : ℕ} (ν : Measure (Row d)) (v : Vector d) : Prop :=
  ∀ᵐ X ∂annealedLaw ν,
    Tendsto (fun n : ℕ => (fun i => (X n i : ℝ) / (n : ℝ))) atTop (𝓝 v)

open scoped ENNReal NNReal Classical Topology BigOperators

def MainStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ν : Measure (Row d)), IsProbabilityMeasure ν →
    UniformElliptic ν → ∀ (ℓ : Vector d), dot ℓ ℓ = 1 →
    DirectionallyTransient ν ℓ →
    ∃ v : Vector d, 0 < dot v ℓ ∧ HasVelocity ν v



end DirectionalTransience
end OAI


