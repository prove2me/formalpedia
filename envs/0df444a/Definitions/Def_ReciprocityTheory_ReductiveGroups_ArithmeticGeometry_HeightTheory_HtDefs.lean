-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:27:45.292277+00:00
-- url     : https://prove2.me/theorems/6fc7d618-e4fa-445b-bf99-a474d6f2692b
-- title:
--   Ht Defs
-- statement:
--   Definitions and structural lemmas for Ht Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HtDefs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightIntegralEstimates
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
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
namespace Data
variable (d : Data K ι Ω WT A)
def HtOne : Set (Ideal (KTp K d.D d.N)) := {p | p.IsPrime ∧ p.height = 1}
noncomputable def gen (p : Ideal (KTp K d.D d.N)) : KTp K d.D d.N :=
  open Classical in if hp : p.IsPrincipal then (haveI := hp; Submodule.IsPrincipal.generator p) else 0
noncomputable def dg (q : KTp K d.D d.N) : ℕ := q.support.sup fun s => ∑ j, s (1, j)
def OverP (c : ι) (p : Ideal (KTp K d.D d.N)) : Set (AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ x : KTp K d.D d.N, 0 ≤ w (d.sH c x) ∧ (0 < w (d.sH c x) ↔ x ∈ p)}
def GoodP (c : ι) (p : Ideal (KTp K d.D d.N)) : Set (AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) :=
  {w | w ∈ d.OverP c p ∧ ∃ a : Ω c, a ≠ 0 ∧ d.Wres c w a ≠ 0}
noncomputable def nP (h : d.S1) (c : ι) (G : WT) (ta : A c) (p : Ideal (KTp K d.D d.N)) : ℤ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
    (d.fze h c w : ℤ) * d.ord c (d.Wres c w) G ta
noncomputable def ordMM (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (f : A c) : ℤ :=
  d.ord c v d.wL f - ⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)
noncomputable def nPMM (h : d.S1) (c : ι) (f : A c) (p : Ideal (KTp K d.D d.N)) : ℤ :=
  ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
    (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) f
noncomputable def aG (h : d.S1) (G : WT) (ta : ∀ c, A c) : ℤ :=
  ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ)
noncomputable def h0f (h : d.S1) (G : WT) (ta : ∀ c, A c) : ℝ :=
  ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    (d.nP h c G (ta c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)
noncomputable def NlaG (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ c, ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (d.ord c (d.Wres c w) G (ta c) : ℝ)
noncomputable def Nsg (G : WT) (ta : ∀ c, A c) (sg : K →+* ℂ) : ℝ :=
  ∑ c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
    -Real.log (d.nrm c G (ta c) P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))
noncomputable def Hgt (h : d.S1) (G : WT) (ta : ∀ c, A c) : ℝ :=
  (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) + meanK (d.Nsg G ta) +
    d.h0f h G ta
noncomputable def NlaMM (h : d.S1) (f : ∀ c, A c) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ c, ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (d.ordMM c (d.Wres c w) (f c) : ℝ)
noncomputable def NsgMM (f : ∀ c, A c) (sg : K →+* ℂ) : ℝ :=
  ∑ c, ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
    -Real.log (d.nrm c d.wL (f c) P / d.be c P)) ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))
noncomputable def mahlerMeasureHeight (h : d.S1) (f : ∀ c, A c) : ℝ :=
  ∑ c, ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
    (d.nPMM h c (f c) p : ℝ) * ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p)
noncomputable def HgtMM (h : d.S1) (f : ∀ c, A c) : ℝ :=
  (∑ᶠ la, d.NlaMM h f la * logNorm la) / (Module.finrank ℚ K : ℝ) + meanK (d.NsgMM f) +
    d.mahlerMeasureHeight h f
noncomputable def wx (x : Fin (d.N + 1) → K) : ∀ c, A c := ∑ j, x j • d.w j
noncomputable def rationalBaseRow (c : ι) : OmS (Ω c) d.D d.N :=
  ∑ j, d.sH c (MvPolynomial.X (0, j)) *
    algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))
noncomputable def fZ (h : d.S1) (c : ι) : KTf K d.D d.N :=
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
    ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p
end Data
end ReciprocityTheory.ChartRestriction.G.T0


