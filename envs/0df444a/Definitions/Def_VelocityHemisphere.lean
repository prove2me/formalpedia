-- Prove2me | Definitions.Def_VelocityHemisphere
-- name    : VelocityHemisphere
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:35.197378+00:00
-- url     : https://prove2.me/theorems/10c91461-c3e1-494d-a036-636544fbd218
-- statement:
--   This block sets up a random walk in a random environment on the d-dimensional integer lattice ℤ^d. A direction is a pair (i,b) of a coordinate i and a sign flag, and step(e) is the unit lattice vector ±1 in coordinate i (+1 when the flag is true, −1 otherwise) and 0 elsewhere. A Row is a probability vector on the 2d directions (nonnegative reals summing to 1), an Environment assigns a Row to every lattice site, and a State is an environment together with a current site. For a measure ν on Rows, environmentLaw(ν) is the infinite product measure in which the rows at all sites are independent with law ν. UniformElliptic(ν) says that there is a constant κ>0 such that ν-almost every row has every direction probability at least κ. The transition kernel sends a state (ω,x) to the state (ω, x+step(e)) with probability equal to the row ω(x) at direction e, so the environment is fixed and only the site moves; the file proves that the map giving the current row is measurable and that this kernel is Markov. A history-dependent version of the kernel on finite state histories up to time n applies the transition to the latest state. initialLaw(ν) is environmentLaw(ν) paired with starting site 0. annealedLaw(ν) is the law on lattice paths ℕ → ℤ^d obtained by running these kernels from the initial law via the Ionescu-Tulcea trajectory measure and keeping only the positions. Finally, with dot(v,ℓ) the Euclidean inner product, TransientPaths(ℓ) is the set of paths whose inner product of position with ℓ tends to +∞, and VelocityPaths(v) is the set of paths X with X_n/n converging to the vector v.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/VelocityHemisphere.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/VelocityHemisphere.lean; bytes 16..3394
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

def TransientPaths {d : ℕ} (ℓ : Vector d) : Set (Path d) :=
  {X | Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop}

def VelocityPaths {d : ℕ} (v : Vector d) : Set (Path d) :=
  {X | Tendsto (fun n : ℕ => fun i => (X n i:ℝ)/(n:ℝ)) atTop (𝓝 v)}



end DirectionalTransience
end OAI


