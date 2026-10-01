-- Prove2me | Definitions.Def_ChapterLpRestrictSplit
-- name    : ChapterLpRestrictSplit
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T06:09:53.676109+00:00
-- url     : https://prove2.me/theorems/2a3cdd92-638c-4f27-9914-41c71c050424
-- title:
--   Chapter LpRestrictSplit
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLpRestrictSplit.lean`): generated def bundle for ChapterLpRestrictSplit. See BookProof/ChapterLpRestrictSplit.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLpRestrictSplit.lean

import Definitions.Def_ChapterLinftyMultiplication
import Mathlib


/-!
# Splitting `L²(μ)` along a measurable set (plan GAP-2, the reassembly step)

The classification list of the abelian von Neumann algebras is a list of *direct
sums*: a summand measure splits into an atomic and a diffuse part
(`ChapterMeasureAtomicDiffuse`), and the two parts are modelled separately
(`ChapterAtomicDiagonalModel`, `ChapterDiffuseUnitaryModel`).  To reassemble the two
models into a statement about `L²(μ)` itself one needs the Hilbert-space counterpart
of the splitting of the measure, and that is what this module supplies:

* `restrictEmbed` — extension by zero, `L²(μ|A) →ₗᵢ[ℂ] L²(μ)`, `u ↦ 1_A · u`;
* `restrictEmbed_coeFn`, `restrictEmbed_restrictOf` — its a.e. formula, and the fact
  that the piece of `u` living on `A` is recovered by restricting and re-embedding;
* `inner_restrictEmbed_eq_zero` — embeddings along disjoint sets have orthogonal
  ranges;
* `restrictEmbed_add_restrictEmbed_compl` — `u = 1_A·u + 1_{Aᶜ}·u`;
* `orthogonalFamily_splitEmbed`, `isHilbertSum_splitEmbed` — **HEADLINE**: `L²(μ)` is
  the Hilbert sum of `L²(μ|A)` and `L²(μ|Aᶜ)`;
* `restrictEmbed_intertwines` — the embeddings intertwine the multiplication
  operators, so the splitting is a splitting of the multiplication *algebra* as well.

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

open MeasureTheory

namespace BookProof.ChapterLpRestrictSplit

open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

/-! ## 1. Extension by zero -/

theorem indicator_ae_eq_of_restrict_ae_eq {A : Set α} (hA : MeasurableSet A) {f g : α → ℂ}
    (h : f =ᵐ[mu.restrict A] g) : A.indicator f =ᵐ[mu] A.indicator g := by
  filter_upwards [(ae_restrict_iff' hA).1 h] with x hx
  by_cases hxA : x ∈ A
  · simp [Set.indicator_of_mem hxA, hx hxA]
  · simp [Set.indicator_of_notMem hxA]

/-- Extending an `L²(μ|A)` function by zero lands in `L²(μ)`. -/
theorem memLp_indicator_of_restrict {A : Set α} (hA : MeasurableSet A)
    (u : Lp ℂ 2 (mu.restrict A)) : MemLp (A.indicator (u : α → ℂ)) 2 mu :=
  (memLp_indicator_iff_restrict hA).2 (Lp.memLp u)

/-- Extension by zero, as a linear map `L²(μ|A) → L²(μ)`. -/
def restrictEmbedLin {A : Set α} (hA : MeasurableSet A) :
    Lp ℂ 2 (mu.restrict A) →ₗ[ℂ] Lp ℂ 2 mu where
  toFun u := (memLp_indicator_of_restrict hA u).toLp _
  map_add' u v := by
    refine Lp.ext ?_
    filter_upwards [(memLp_indicator_of_restrict hA (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memLp_indicator_of_restrict hA u).toLp _)
        ((memLp_indicator_of_restrict hA v).toLp _),
      (memLp_indicator_of_restrict hA u).coeFn_toLp,
      (memLp_indicator_of_restrict hA v).coeFn_toLp,
      indicator_ae_eq_of_restrict_ae_eq (mu := mu) hA (Lp.coeFn_add u v)] with x h1 h2 h3 h4 h5
    rw [h1, h2]
    simp only [Pi.add_apply]
    rw [h3, h4, h5]
    by_cases hxA : x ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxA]
  map_smul' c u := by
    refine Lp.ext ?_
    filter_upwards [(memLp_indicator_of_restrict hA (c • u)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_indicator_of_restrict hA u).toLp _),
      (memLp_indicator_of_restrict hA u).coeFn_toLp,
      indicator_ae_eq_of_restrict_ae_eq (mu := mu) hA (Lp.coeFn_smul c u)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply, smul_eq_mul]
    by_cases hxA : x ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxA]

/-- **Extension by zero**, `L²(μ|A) →ₗᵢ[ℂ] L²(μ)`: it is an isometry because the
`L²(μ)` norm of `1_A · u` is computed by the restricted measure. -/
def restrictEmbed {A : Set α} (hA : MeasurableSet A) :
    Lp ℂ 2 (mu.restrict A) →ₗᵢ[ℂ] Lp ℂ 2 mu where
  toLinearMap := restrictEmbedLin hA
  norm_map' u := by
    change ‖(memLp_indicator_of_restrict hA u).toLp _‖ = ‖u‖
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_indicator_eq_eLpNorm_restrict hA]



/-- The piece of `u` supported on `A`, as an element of `L²(μ|A)`. -/
def restrictProj (A : Set α) (u : Lp ℂ 2 mu) : Lp ℂ 2 (mu.restrict A) :=
  ((Lp.memLp u).restrict A).toLp _





/-! ## 2. Orthogonality -/



/-! ## 3. `L²(μ)` as the Hilbert sum of the two pieces -/

/-- The two-element family of pieces: `A` for `true`, `Aᶜ` for `false`. -/
def splitSet (A : Set α) (b : Bool) : Set α := cond b A Aᶜ

theorem measurableSet_splitSet {A : Set α} (hA : MeasurableSet A) (b : Bool) :
    MeasurableSet (splitSet A b) := by
  cases b <;> simp [splitSet, hA, hA.compl]

/-- The two isometric embeddings of the pieces into `L²(μ)`. -/
def splitEmbed {A : Set α} (hA : MeasurableSet A) (b : Bool) :
    Lp ℂ 2 (mu.restrict (splitSet A b)) →ₗᵢ[ℂ] Lp ℂ 2 mu :=
  restrictEmbed (measurableSet_splitSet hA b)





/-! ## 4. The splitting is a splitting of the multiplication algebra -/



end BookProof.ChapterLpRestrictSplit

end


