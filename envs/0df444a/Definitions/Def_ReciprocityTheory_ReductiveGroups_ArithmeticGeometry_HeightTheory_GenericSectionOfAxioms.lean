-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GenericSectionOfAxioms
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GenericSectionOfAxioms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:42.833271+00:00
-- url     : https://prove2.me/theorems/d712b3f1-685c-4788-8ff8-77f4185d3ff8
-- title:
--   Generic Section Of Axioms
-- statement:
--   Definitions and structural lemmas for Generic Section Of Axioms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GenericSectionOfAxioms.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_SectionSheafQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
noncomputable def htOf (hd : d.AxH 𝒜) (h : d.S1) : Formalism.MainNotions.Gaps.HeightData.HtData where
  K := K
  D := d.D
  δ := d.del
  i := d.i
  g0 := d.g0
  L := d.wsize d.wL
  G := d.Gc
  PH := d.PHc
  Prw := d.Prw
  Pet := d.Pet
  S := fun k => meanK fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))
  etaPart := True
  Op := fun la => Op d.D d.N la
  SectionSheafQuotient := fun _ => ∀ c, OmS (Ω c) d.D d.N
  mA := fun la =>
    letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
    inferInstance
  A0 := fun la =>
    letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
    Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection hd.a4.choose la)
  t := fun _ => d.bvecG hd.sel hd.a4.choose
  Pts := fun la => Σ c, {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) // w ∈ d.PlOver la c}
  ep := fun _ _ => 1
  f := fun _ ζ => d.fze h ζ.1 ζ.2.1
  vEt := fun _ ζ => (d.ord ζ.1 (d.Wres ζ.1 ζ.2.1) (d.n1 • d.wde) (d.et ζ.1) : ℝ)
end Data
end ReciprocityTheory.ChartRestriction.G.T0


