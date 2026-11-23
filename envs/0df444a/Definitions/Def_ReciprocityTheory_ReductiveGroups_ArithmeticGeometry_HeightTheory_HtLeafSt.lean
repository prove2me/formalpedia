-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:44.454983+00:00
-- url     : https://prove2.me/theorems/1ddd5fbf-f03b-4f0c-a771-44bf6133fb2c
-- title:
--   Ht Leaf St
-- statement:
--   Definitions and structural lemmas for Ht Leaf St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HtLeafSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GenericSectionOfAxioms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace LeafSt
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)
def PlaceTrivialOrPositive : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.OverP c p),
  (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∨
    (d.admitted c (d.Wres c w) ∧ IsTrivOn K (d.Wres c w) ∧
      ∃ j0, d.w j0 c ≠ 0 ∧ (∀ j, 0 ≤ d.Wres c w (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∧
        w (∑ j, d.sH c (MvPolynomial.X (0, j)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) = 0)
def AdmissibleValuationPrimeUnique : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι),
  ∀ v : AddValuation (Ω c) (WithTop ℤ), d.admitted c v → IsTrivOn K v →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.GoodP c p, d.Wres c w = v}.Subsingleton
def GeneratorMultiHomogeneous : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι),
  ∀ p ∈ d.HtOne, (∃ w, w ∈ d.GoodP c p) →
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun b : Fin (d.D + 1) => if b = 0 then 0 else d.dg (d.gen p))
        (d.gen p)
def DegreeSumIdentity : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N) (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c),
  ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) F ∧
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)) = d.delc c
def SpecialFibreFactorization : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N) (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) (x : Fin (d.N + 1) → K) (hx : d.wx x c ≠ 0),
  ∃ κ : K, κ ≠ 0 ∧
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
        (MvPolynomial.aeval (fun v : TVar d.D d.N =>
          if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F) =
      algebraMap K (KTf K d.D d.N) κ *
        ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p
def int_Nsg : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (c : ι) (sg : K →+* ℂ),
  (∀ (G : WT) (f : A c), G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) →
      f ∈ 𝒜 c G → f ≠ 0 →
      MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c G f P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) ∧
    (∀ f : A c, f ∈ 𝒜 c d.wL → f ≠ 0 →
      MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c d.wL f P / d.be c P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)))
def h_ind : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate),
  (∀ (G : WT) (ta ta' : ∀ c, A c),
      G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) →
      (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) → (∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0) →
      d.Hgt h G ta = d.Hgt h G ta') ∧
    (∀ f f' : ∀ c, A c, (∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) → (∀ c, f' c ∈ 𝒜 c d.wL ∧ f' c ≠ 0) →
      d.HgtMM h f = d.HgtMM h f') ∧
    (∀ x : Fin (d.N + 1) → K, (∀ c, d.wx x c ≠ 0) →
      (d.n1 : ℝ) * d.Hgt h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.Hgt h (d.n1 • d.wde) d.et =
        2 * d.n1 * d.Hgt h d.wL (d.wx x)) ∧
    (∀ (x : Fin (d.N + 1) → K) (ta' : ∀ c, A c), (∀ c, d.wx x c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) →
      d.Hgt h d.wF ta' + d.Hgt h d.G2 d.ta2 = (d.D + 4) * d.Hgt h d.wL (d.wx x))
def h_four : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c) (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (hord : ∀ c (v : AddValuation (Ω c) (WithTop ℤ)), d.admitted c v → 0 ≤ d.ord c v G (ta c)) (hbdd : ∀ sg : K →+* ℂ, BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (ta p.1) p.2)) (hint : ∀ (c : ι) (sg : K →+* ℂ), MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) => ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)), Real.log (d.nrm c G (ta c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))),
  -(d.del * meanK (fun sg => Real.log (d.supN sg G ta))) -
        d.D * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2) ≤ d.Hgt h G ta ∧
      (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤
        d.Hgt h G ta + d.del * meanK (fun sg => Real.log (d.supN sg G ta)) +
          d.D * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2)
def HeightMinMaxFormula : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K) (hx : ∀ c, d.wx x c ≠ 0) (F : ι → KTp K d.D d.N) (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c),
  d.HgtMM h (d.wx x) = ∑ c, ReciprocityTheory.MultiplicativeHeights.h0 (F c) + d.del * (harmonic d.N : ℝ) / 2
def h_seven : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (hF1d : d.TrivialPlaceHyp) (hSup : d.HtSup) (hI2be : d.HeightIntegralBoundEstimate) (x : Fin (d.N + 1) → K) (hx : ∀ c, d.wx x c ≠ 0) (ta' : ∀ c, A c) (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0),
  let lr := Real.log (d.N + 1 : ℕ) + 1 / 2
    let HL := d.Hgt h d.wL (d.wx x)
    let Hde := d.Hgt h (d.n1 • d.wde) d.et / d.n1
    let ade := (d.aG h (d.n1 • d.wde) d.et : ℝ) / d.n1
    let aG1 := (d.aG h ((2 : ℕ) • d.G1) d.ta1 : ℝ) / 2
    let X8 := d.HgtMM h (d.wx x) + d.del * ((∑ᶠ la, d.nu la * logNorm la) /
      (Module.finrank ℚ K : ℝ) + d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) + d.D * d.cc * d.g0 * ade * lr
    let Y := d.del * d.PI4 * d.D * d.wsize d.wL + d.D * aG1 * lr
    HL ≤ X8 + d.cc * d.g0 * Hde ∧ Hde ≤ HL + Y ∧
      d.Hgt h d.wF ta' ≤ (d.D + 4) * HL + d.del * d.PI4 * d.D * d.wsize d.wL +
        d.D * d.aG h d.G2 d.ta2 * lr
def norm_by_places : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι),
  (∀ p ∈ d.HtOne, (d.OverP c p).Finite) ∧
    ∀ y : OmS (Ω c) d.D d.N, y ≠ 0 →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w y ≠ 0}.Finite ∧
      ∃ κ : K, κ ≠ 0 ∧
        letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
        Algebra.norm (KTf K d.D d.N) y =
          algebraMap K (KTf K d.D d.N) κ *
            ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
              algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
                (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
                  (d.fze h c w : ℤ) * WithTop.untopD 0 (w y))
def norm_at_la : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K) (hϖ : ϖ ∈ la.asIdeal) (hϖ2 : ϖ ∉ la.asIdeal ^ 2) (y : OmS (Ω c) d.D d.N) (hy : y ≠ 0),
  ∃ u : Op d.D d.N la, IsUnit u ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) y =
        (algebraMap K (KTf K d.D d.N) (ϖ : K)) ^
          (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
            (d.fze h c w : ℤ) * WithTop.untopD 0 (w y)) * OpToKT d.D d.N la u
def norm_at_sg : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ),
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    ∀ᵐ z ∂(ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)),
      (d.ST c sg (d.tOf z)).Finite ∧ (d.ST c sg (d.tOf z)).ncard = d.delc c ∧
      (∀ (g : Ω c) (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), g ≠ 0 → b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ∧
      (∀ (a b : KTp K d.D d.N) (t0 : Fin (d.N + 1) → ℂ), b ≠ 0 →
        (Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) →
        d.evT sg t0 (d.tOf z) b ≠ 0 → d.evT sg t0 (d.tOf z) a / d.evT sg t0 (d.tOf z) b = ∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)),
          ∑ j, t0 j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)))
def places_over_la : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι),
  (d.PlOver la c).Finite ∧
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
        (d.fze h c w : ℤ) * ramIdx (K := K) (d.Wres c w) la) = d.delc c
def disc_lattice : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1),
  d.De hd h ≠ 0 ∧ ∀ la, (d.htOf hd h).Ila la ≠ ⊤ ∧
      2 * d.IL h hd.sel hd.a4.choose la ≤
        d.gOrd la (d.De hd h) + 2 * d.NlaG h d.wF hd.a4.choose la
def disc_global : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (ta' : ∀ c, A c) (hta' : ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0),
  (Function.support fun la => d.gOrd la (d.De hd h)).Finite ∧
    (Function.support fun la => d.NlaG h d.wF hd.a4.choose la).Finite ∧
    (∑ᶠ la, ((d.gOrd la (d.De hd h) : ℝ) + 2 * d.NlaG h d.wF hd.a4.choose la) * logNorm la) /
      (Module.finrank ℚ K : ℝ) ≤
      d.del * Real.log d.del +
        2 * ∑ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp (hd.sel k)))) +
        2 * d.D * d.aG h d.wF ta' * (Real.log (d.N + 1 : ℕ) + 1 / 2) + 2 * d.Hgt h d.wF ta'
def exists_generic : Prop :=
  ∀ (hd : d.AxH 𝒜) (h : d.S1),
  (∃ x : Fin (d.N + 1) → K, ∀ c, d.wx x c ≠ 0) ∧
    (∃ ta' : ∀ c, A c, ∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0)
end LeafSt
end ReciprocityTheory.ChartRestriction.G.T0


