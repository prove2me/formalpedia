-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T17:01:07.884837+00:00
-- url     : https://prove2.me/theorems/7f1ca3e9-0ca8-41f2-af79-36bdc93940a6
-- title:
--   HHINDC
-- statement:
--   Definitions and structural lemmas for HHINDC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HHINDC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
noncomputable def aNla (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (ta : ∀ c, A c) (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ c, ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (O c (d.Wres c w) (ta c) : ℝ)
noncomputable def anP (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ) (c : ι)
    (f : A c) (p : Ideal (KTp K d.D d.N)) : ℤ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
    (d.fze h c w : ℤ) * O c (d.Wres c w) f
noncomputable def aI (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (c : ι) (f : A c) (sg : K →+* ℂ)
    (z : BlockSphere d.D (d.N + 1)) : ℝ :=
  ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), Real.log (Nr c f P)
noncomputable def AH (h : d.S1) (O : ∀ c, AddValuation (Ω c) (WithTop ℤ) → A c → ℤ)
    (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (ta : ∀ c, A c) : ℝ :=
  (∑ᶠ la, d.aNla h O ta la * logNorm la) / (Module.finrank ℚ K : ℝ) +
    meanK (fun sg => ∑ c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
      -Real.log (Nr c (ta c) P)) ∂(blockSphereProb d.D (d.N + 1))) +
    ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.anP h O c (ta c) p : ℝ) * h0 (d.gen p)
end Data
end ReciprocityTheory.ChartRestriction.G.T0
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
end Data
end ReciprocityTheory.ChartRestriction.G.T0
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
end Data
end ReciprocityTheory.ChartRestriction.G.T0


