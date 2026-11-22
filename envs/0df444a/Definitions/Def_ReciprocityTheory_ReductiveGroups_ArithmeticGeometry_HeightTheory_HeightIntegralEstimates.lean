-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightIntegralEstimates
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightIntegralEstimates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:55.106347+00:00
-- url     : https://prove2.me/theorems/90bdfe10-d120-44da-bec9-2fee7c860888
-- title:
--   Height Integral Estimates
-- statement:
--   Definitions and structural lemmas for Height Integral Estimates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HeightIntegralEstimates.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
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
variable (d : Data K ι Ω WT A) (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
structure AxH : Type where
  nonempty : Nonempty ι
  tower : ∀ c, IsScalarTower K (Ω c) (A c)
  towerO : ∀ c, IsScalarTower (𝓞 K) K (A c)
  D_ge : 3 ≤ d.D
  fg : ∀ c, (⊤ : IntermediateField K (Ω c)).FG
  trdeg : ∀ c, Algebra.trdeg K (Ω c) = d.D
  algClosed : ∀ c (a : Ω c), IsAlgebraic K a → a ∈ (algebraMap K (Ω c)).range
  graded : ∀ c, SetLike.GradedMonoid (𝒜 c)
  finrank_one : ∀ c G, Module.finrank (Ω c) (𝒜 c G) = 1
  mul_ne_zero : ∀ c {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' → f ≠ 0 → g ≠ 0 →
    f * g ≠ 0
  WW_span : d.WW = Submodule.span (𝓞 K) (Set.range d.w)
  w_mem : ∀ j c, d.w j c ∈ 𝒜 c d.wL
  w_base : ∀ c, d.w (d.jc c) c ≠ 0
  Thp_span : d.Thp = Submodule.span (𝓞 K) (Set.range d.thp)
  thp_mem : ∀ k c, d.thp k c ∈ 𝒜 c d.wF
  et_mem : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde)
  firstSectionMem : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1)
  secondSectionMem : ∀ c, d.ta2 c ∈ 𝒜 c d.G2
  et_ne : ∀ c, d.et c ≠ 0
  firstSectionNeZero : ∀ c, d.ta1 c ≠ 0
  secondSectionNeZero : ∀ c, d.ta2 c ≠ 0
  ord_mul : ∀ c v, d.admitted c v → ∀ {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.ord c v (G + G') (f * g) = d.ord c v G f + d.ord c v G' g
  ord_smul : ∀ c v, d.admitted c v → ∀ {G : WT} {f : A c} (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    ((d.ord c v G (a • f) : ℤ) : WithTop ℤ) = v a + (d.ord c v G f : WithTop ℤ)
  nrm_pos : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → f ≠ 0 → 0 < d.nrm c G f P
  nrm_zero : ∀ c (G : WT) (P : Ω c →+* ℂ), d.nrm c G 0 P = 0
  nrm_mul : ∀ c {G G' : WT} {f g : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.nrm c (G + G') (f * g) P = d.nrm c G f P * d.nrm c G' g P
  nrm_smul : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ) (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    d.nrm c G (a • f) P = ‖P a‖ * d.nrm c G f P
  nrm_conj : ∀ c (G : WT) (f : A c) (P : Ω c →+* ℂ),
    d.nrm c G f ((starRingEnd ℂ).comp P) = d.nrm c G f P
  bdd : ∀ (sg : K →+* ℂ) (G : WT) (f : ∀ c, A c),
    ((f ∈ d.WW ∧ G = d.wL) ∨ (f ∈ d.Thp ∧ G = d.wF) ∨ (f = d.et ∧ G = d.n1 • d.wde) ∨
      (f = d.ta1 ∧ G = (2 : ℕ) • d.G1) ∨ (f = d.ta2 ∧ G = d.G2)) →
    BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (f p.1) p.2)
  a1 : ∀ c, ∃ J : Fin d.D → Fin d.N,
    LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))
  ord_nonneg_WW : ∀ c v, d.admitted c v → ∀ f ∈ d.WW, f c ≠ 0 → 0 ≤ d.ord c v d.wL (f c)
  ord_nonneg_Thp : ∀ c v, d.admitted c v → ∀ f ∈ d.Thp, f c ≠ 0 → 0 ≤ d.ord c v d.wF (f c)
  ord_nonneg_et : ∀ c v, d.admitted c v → 0 ≤ d.ord c v (d.n1 • d.wde) (d.et c)
  ordDoubleFirstSection_nonneg : ∀ c v, d.admitted c v → 0 ≤ d.ord c v ((2 : ℕ) • d.G1) (d.ta1 c)
  ordSecondSectionNonneg : ∀ c v, d.admitted c v → 0 ≤ d.ord c v d.G2 (d.ta2 c)
  a3' : ∀ c {G : WT} {f : A c}, f ∈ 𝒜 c G → f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite
  sel : Fin d.del → Fin d.np
  a4 : ∃ e : ∀ c, A c, (∀ c, e c ∈ 𝒜 c d.wF ∧ e c ≠ 0) ∧
    (∀ p : Fin d.del → MvPolynomial (TVar d.D d.N) K,
      (∀ c, ∑ k, d.sH c (p k) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c)) = 0) →
      ∀ k, p k = 0) ∧
    (∀ y : ∀ c, OmS (Ω c) d.D d.N, ∃ q : MvPolynomial (TVar d.D d.N) K, (∀ c, d.sH c q ≠ 0) ∧
      ∃ p : Fin d.del → MvPolynomial (TVar d.D d.N) K, ∀ c, d.sH c q * y c = ∑ k, d.sH c (p k) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c)))
  i_ge : 1 ≤ d.i
  g_zero_ge_ask_sum : 1 ≤ d.g0
  cc_nonneg : 0 ≤ d.cc
  cc_le : d.cc ≤ 1
  ccg0 : d.cc * d.g0 ≤ 1 / 2
  size_L : 1 ≤ d.wsize d.wL
  DF_le : d.DF ≤ d.wsize d.wL
  rw_le : Real.log (d.N + 1 : ℕ) + 1 / 2 ≤ d.Prw * (d.wsize d.wL - 1)
  nK_le : Real.log (Module.finrank ℚ K) ≤ d.PO
  rd_le : Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) ≤ d.PO
  P_ge : 1 ≤ d.PN ∧ 1 ≤ d.PQ ∧ 1 ≤ d.tableDegreeThreeBase ∧ 1 ≤ d.PP0' ∧ 1 ≤ d.Pd ∧ 1 ≤ d.Gc ∧ 1 ≤ d.PI4 ∧
    1 ≤ d.Pet ∧ 1 ≤ d.tableLineDegreeFive ∧ 1 ≤ d.tableLineDegreeTwo ∧ 1 ≤ d.Prw ∧ 1 ≤ d.PO
  a13 : ∀ c (sg : K →+* ℂ) {G : WT} {f : A c}, f ∈ 𝒜 c G → f ≠ 0 →
    AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
      ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
        Real.log (d.nrm c G f P)) d.sphMeasure
variable {𝒜}
def FinitePlaceHyp : Prop :=
  (∀ la, 0 ≤ d.nu la) ∧
  ((Function.support d.nu).Finite) ∧
  ((∑ᶠ la, d.nu la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤ d.PN * d.wsize d.wL) ∧
  (∀ c v la, d.admitted c v → IsOver (K := K) v la →
      ((⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) : ℤ) : ℝ) ≤
        (ramIdx (K := K) v la : ℝ) * d.nu la +
          d.cc / (2 * d.i) * d.ord c v (d.n1 • d.wde) (d.et c))
def TrivialPlaceHyp : Prop :=
  (∀ c v, d.admitted c v → IsTrivOn K v →
      ((⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) : ℤ) : ℝ) ≤
        d.cc / (2 * d.i) * d.ord c v (d.n1 • d.wde) (d.et c))
def HtLAM : Prop :=
  (∀ c, ∀ g ∈ Submodule.span (𝓞 K)
        (Set.range fun s : Fin d.n96 → Fin (d.N + 1) => ∏ k, d.w (s k)), g c ≠ 0 →
      -(d.PP0' * d.n96 * d.wsize d.wL) ≤
        meanK fun sg => Real.log (d.supNc c sg (d.n96 • d.wL) (g c)))
def HtSup : Prop :=
  (meanK (fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j))) ≤ d.Gc * d.wsize d.wL) ∧
  (∀ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp k))) ≤ d.Gc * d.wsize d.wF) ∧
  (meanK (fun sg => Real.log (d.supN sg ((2 : ℕ) • d.G1) d.ta1)) ≤
      2 * d.PI4 * d.D * d.wsize d.wL) ∧
  (meanK (fun sg => Real.log (d.supN sg d.G2 d.ta2)) ≤ d.PI4 * d.D * d.wsize d.wL)
def HeightIntegralEstimateTrivialPlace : Prop :=
  (meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) / d.i ≤ d.Pet)
def HeightIntegralBoundEstimate : Prop :=
  (∀ c (P : Ω c →+* ℂ),
      -Real.log (d.be c P) ≤
        d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) + d.cc * d.tableLineDegreeTwo)
def PHc : ℝ := 2 * d.PH + d.Gc
end Data
end ReciprocityTheory.ChartRestriction.G.T0


