-- Prove2me | Definitions.Def_ArtinKPB008
-- name    : ArtinKPB008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:19:47.083112+00:00
-- url     : https://prove2.me/theorems/8e43979b-6651-4ada-aee3-856b7edd8de0
-- title:
--   Definitions bundle ArtinKPB008 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 2 declarations of that development: 1 inductive type or structure and 1 theorem. The definitions and types are `ArtinKP.X.IsPOU`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.X_Discrete`, `KP.X_Quot`.
--
--   **Imports.** It imports the bundle `ArtinKPB006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB009`; the statement `ArtinKP.X.exists_isPOU_forall_pos`; the proof of `ArtinKP.X.exists_isPOU_forall_pos`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib
import Definitions.Def_ArtinKPB006

section
-- module Solutions.Artin.KP.X_Quot
/-! # WP-X, file 5: quotient measures and unfolding without fundamental domains

Abstract setting: a countable group `G` acting measurably on `(α, μ)` and preserving `μ`.
A *partition of unity* for the action is a measurable `η : α → ℝ≥0∞` with
`∑_g η (g • a) = 1` for all `a` (the indicator of a strict fundamental domain is one; in a
properly discontinuous situation an everywhere positive one always exists, `exists_isPOU`).
The quotient measure on `G \ α` is the push-forward of `η μ`; it does not depend on `η`
(`quotMeasure_eq`).  Everything is Tonelli:

* `lintegral_tsum_swap` : `∫ φ · Σ_g ψ∘g = ∫ ψ · Σ_g φ∘g`;
* `lintegral_mul_pou_eq` : independence of `η`;
* `lintegral_autom_mul_eq` : unfolding `∫_{G\α} (Σ_{H\G} f∘γ) u = ∫_{H\α} f u`;
* `setLIntegral_le_mul_lintegral_pou` : a set meeting each orbit at most `m` times has
  `∫_B f ≤ m ∫_{G\α} f`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-- A measurable partition of unity for the action of `G`: `∑_g η (g • a) = 1`. -/
structure IsPOU (G : Type*) {α : Type*} [MeasurableSpace α] [SMul G α] (η : α → ℝ≥0∞) : Prop where
  measurable : Measurable η
  tsum_eq : ∀ a, ∑' g : G, η (g • a) = 1

/-! ### The quotient measure -/

/-! ### Unfolding -/

/-! ### Multiplicity and existence of partitions of unity -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-X, file 6: discreteness of `SL(2, 𝓞_F)` on `X`, the quotient measure, `L²(Γ\X)`

* `entries_bounded`: if `Q` and `g • Q` lie in a box of `H3` the entries of `g` are bounded;
* `finite_return_box`: a box of `X` meets only finitely many of its `SL(2,𝓞_F)`-translates
  (`𝓞_F` is discrete in `ℂ^r`); the same for compact sets (`finite_return_of_isCompact`);
* a positive partition of unity for every subgroup `Γ ≤ SL(2,𝓞_F)`, the quotient measure
  `X.quotVol Γ` on `Γ \ X` (independent of the partition), `X.L2 Γ = L²(Γ\X)`;
* the cusp stabilizer `GammaInf Γ` and its action in coordinates.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### One factor -/

/-! ### The integral group -/

variable {F : Type*} [Field F] [NumberField F]

lemma X.measurableSet_box (n : ℕ) : MeasurableSet (X.box n : Set (X F)) := by
  have : (X.box n : Set (X F)) =
      ⋂ w, {P : X F | ‖P.x w‖ ≤ n} ∩ ({P | 1 / ((n : ℝ) + 1) ≤ P.v w} ∩ {P | P.v w ≤ (n : ℝ) + 1}) := by
    ext P; simp [X.box, H3.box, X.x, X.v]
  rw [this]
  refine MeasurableSet.iInter fun w => ?_
  refine (measurableSet_le ((X.continuous_x w).norm.measurable) measurable_const).inter
    ((measurableSet_le measurable_const (X.continuous_v w).measurable).inter
      (measurableSet_le (X.continuous_v w).measurable measurable_const))

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end


