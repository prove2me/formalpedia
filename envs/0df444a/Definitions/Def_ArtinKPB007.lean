-- Prove2me | Definitions.Def_ArtinKPB007
-- name    : ArtinKPB007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:19:57.381864+00:00
-- url     : https://prove2.me/theorems/886e2b76-56be-49d7-9e47-ae72a9f8550b
-- title:
--   Definitions bundle ArtinKPB007 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 6 declarations of that development: 1 definition, 3 instances and 2 theorems. The definitions and types are `ArtinKP.X.X.boxMult`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.X_Discrete`, `KP.X_Fourier`, `KP.X_Space`.
--
--   **Imports.** It imports the bundle `ArtinKPB006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB010`; the statement `ArtinKP.X.X.tsum_indicator_box_le_boxMult`; the proofs of `ArtinKP.X.X.tsum_indicator_box_le_boxMult` and `ArtinKP.X.exists_isPOU_forall_pos`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib
import Definitions.Def_ArtinKPB006

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX
/-! # WP-X, file 3: the space `X = (H³)^r`

`X F = InfinitePlace F → H3`, the action of `G∞ = InfinitePlace F → SL(2,ℂ)` and of `SL(2,F)`
(through the embeddings `w.embedding`), heights, pair heights, the invariant measure and the
torus `a(y)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

variable {F}

/-! ### Topology and measure -/

instance instMeasurableConstSMulGinfX : MeasurableConstSMul (Ginf F) (X F) :=
  ⟨fun g => measurable_pi_iff.mpr fun w =>
    (measurable_const_smul (g w)).comp (measurable_pi_apply w)⟩

instance instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX : MeasurableConstSMul (SL(2, F)) (X F) :=
  ⟨fun γ => measurable_const_smul (sigma F γ)⟩

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
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

theorem instCountableRingOfIntegers : Countable (𝓞 F) :=
  (RingOfIntegers.basis F).equivFun.toEquiv.injective.countable

theorem instCountableSLInt : Countable (SL(2, 𝓞 F)) :=
  haveI _iCO := instCountableRingOfIntegers (F := F)
  have : Countable (Matrix (Fin 2) (Fin 2) (𝓞 F)) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → 𝓞 F))
  Subtype.val_injective.countable

instance instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX : MeasurableConstSMul (SL(2, 𝓞 F)) (X F) :=
  ⟨fun γ => measurable_const_smul (intSL F γ)⟩

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
/-! # WP-X, file 9: local restriction and coefficient functionals on `L²(Γ\X)`

* `X.vol_box_lt_top`: boxes have finite measure;
* `X.restrictBox Γ n : L²(Γ\X) →L[ℂ] L²(box n)`, bounded;
* `X.coeffFunctional Γ n ψ … : L²(Γ\X) →L[ℂ] ℂ`, `u ↦ ∫_{box n} conj ψ · u`, for bounded measurable
  `ψ`.  The Fourier-coefficient functional `ℓ_{ν,φ}` of MATH (C6) is the case
  `ψ(P) = 1_D(x) · conj(e_∞(-ν x) φ(v))` with `D` a fundamental set of the translation lattice
  and `supp φ` compact (so that `D × supp φ` lies in a box).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The multiplicity of a box modulo `Γ`. -/
def X.boxMult (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) : ℕ :=
  ((finite_return_box (F := F) n).preimage
    (f := fun γ : Γ => (γ : SL(2, 𝓞 F))) Subtype.val_injective.injOn).toFinset.card

end

end ArtinKP.X
end


