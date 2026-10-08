-- Prove2me | Definitions.Def_DirectionalWalk
-- name    : DirectionalWalk
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:08.083988+00:00
-- url     : https://prove2.me/theorems/6ebee5b2-664f-4a99-90db-df1a226218fa
-- statement:
--   For a nonnegative integer d, sites are points of ℤᵈ and steps are signed coordinate directions, with stepVector equal to the corresponding positive or negative unit vector. A row is a probability vector on these 2d directions: every entry lies in [0,1] and the entries sum to one. An environment assigns a row to each site, a path is a sequence of sites indexed by nonnegative integers, and a state consists of an environment and a current site. StrictEllipticity(μ) means that μ-almost every row assigns strictly positive probability to every direction; no uniform positive lower bound is required. For a probability measure μ on rows, environmentLaw(μ) is the product measure giving independent rows with common law μ at all sites. The transition kernel keeps the environment fixed and moves from x to x plus a signed unit vector, with probability given by the corresponding entry of the row at x; this kernel is shown to be Markov. The history kernel applies this transition to the latest state and is also Markov. Starting with a sampled environment and a specified site x, annealed(μ,x) is the resulting law of the position path after discarding the environment coordinate. Finally, escape(ℓ), for ℓ ∈ ℝᵈ, consists of paths X whose scalar projections ∑ᵢ Xₙ,ᵢℓᵢ tend to +∞ as n tends to infinity. These constructions do not assume strict ellipticity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DirectionalWalk.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DirectionalWalk.lean; bytes 16..3089
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

abbrev Site (d : ℕ) := Fin d → ℤ
abbrev Step (d : ℕ) := Fin d × Bool

def stepVector {d : ℕ} (e : Step d) : Site d :=
  fun i => if i = e.1 then (if e.2 then 1 else -1) else 0

def Row (d : ℕ) :=
  {p : Step d → ℝ // (∀ e, p e ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ e, p e = 1}

instance (d : ℕ) : MeasurableSpace (Row d) := inferInstanceAs
  (MeasurableSpace {p : Step d → ℝ //
    (∀ e, p e ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ e, p e = 1})

abbrev Environment (d : ℕ) := Site d → Row d
abbrev Path (d : ℕ) := ℕ → Site d
abbrev State (d : ℕ) := Environment d × Site d

def StrictEllipticity {d : ℕ} (μ : Measure (Row d)) : Prop :=
  ∀ᵐ p ∂μ, ∀ e, 0 < p.val e

noncomputable def environmentLaw {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] : Measure (Environment d) :=
  Measure.infinitePi (fun _ => μ)

noncomputable def transition (d : ℕ) : Kernel (State d) (State d) where
  toFun s := ∑ e : Step d,
    ENNReal.ofReal ((s.1 s.2).val e) • Measure.dirac (s.1, s.2 + stepVector e)
  measurable' := by
    apply measurable_from_prod_countable_left
    intro x
    apply Finset.measurable_sum
    intro e he
    apply Measure.measurable_of_measurable_coe
    intro t ht
    simp only [Measure.smul_apply, smul_eq_mul]
    apply Measurable.mul
    · exact (measurable_pi_apply e |>.comp
        (measurable_subtype_coe.comp (measurable_pi_apply x))).ennreal_ofReal
    · exact (Measure.measurable_coe ht).comp
        (Measure.measurable_dirac.comp (measurable_id.prodMk measurable_const))

instance (d : ℕ) : IsMarkovKernel (transition d) where
  isProbabilityMeasure s := by
    constructor
    change (∑ e : Step d,
      ENNReal.ofReal ((s.1 s.2).val e) •
        Measure.dirac (s.1, s.2 + stepVector e)) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [(s.1 s.2).property.2, ENNReal.ofReal_one]
    · intro e he
      exact ((s.1 s.2).property.1 e).1

noncomputable def historyKernel (d n : ℕ) :
    Kernel ((i : Finset.Iic n) → State d) (State d) :=
  (transition d).comap (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance (d n : ℕ) : IsMarkovKernel (historyKernel d n) := by
  unfold historyKernel
  infer_instance

noncomputable def initialLaw {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (x : Site d) : Measure (State d) :=
  (environmentLaw μ).map (fun ω => (ω, x))

noncomputable def annealed {d : ℕ} (μ : Measure (Row d))
    [IsProbabilityMeasure μ] (x : Site d) : Measure (Path d) :=
  (Kernel.trajMeasure (X := fun _ => State d) (initialLaw μ x) (historyKernel d)).map
    (fun z n => (z n).2)

def escape {d : ℕ} (ℓ : Fin d → ℝ) : Set (Path d) :=
  {X | Tendsto (fun n => ∑ i, (X n i : ℝ) * ℓ i) atTop atTop}



end DirectionalZeroOne
end OAI


