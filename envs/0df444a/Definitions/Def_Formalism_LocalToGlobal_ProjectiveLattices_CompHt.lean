-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CompHt
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T10:50:09.088923+00:00
-- url     : https://prove2.me/theorems/321e3e52-650d-43b1-9855-99967e89c95e
-- title:
--   Comp Ht
-- statement:
--   Definitions and structural lemmas for Comp Ht, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompHt.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightIntegralEstimates
import Theorems.Thm_Formalism_L2_Pj_finrank_AG
import Theorems.Thm_Formalism_L2_Pj_mul_ne_zero_AG
import Theorems.Thm_Formalism_L2_Pj_nrmC_mul
import Theorems.Thm_Formalism_L2_Pj_nrmC_pos
import Theorems.Thm_Formalism_L2_Pj_nrmC_smul
import Theorems.Thm_Formalism_L2_Pj_nrmC_zero
import Theorems.Thm_Formalism_L2_Pj_ordC_mul
import Theorems.Thm_Formalism_L2_Pj_ordC_smul
import Theorems.Thm_Formalism_L2_Pj_valC_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
abbrev WtR (E : Type) [Field E] : Type := ((E →+* ℂ) × ℕ → ℕ) × ℕ
abbrev valG (h : GenFrEx Xo c) (u : WtR E) (f : Rul Xo c) : ∀ Z : Comp Xo c, AC Z := valC h u.1 u.2 f
def dataOf (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ) :
    Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z) where
  D := Dd
  N := N
  T := T
  i := i
  g0 := g0
  cc := cc
  wL := wtZ uL.1 uL.2
  wF := wtZ uF.1 uF.2
  wde := wtZ ude.1 ude.2
  ord Z v := ordC (δ Z v) v
  nrm Z := nrmC fn (yP Z)
  M := letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
    Submodule.span (𝓞 c.F) (valG h uka '' MR)
  WW := letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
    Submodule.span (𝓞 c.F) (Set.range fun k => valG h uL (wR k))
  Thp := letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
    Submodule.span (𝓞 c.F) (Set.range fun k => valG h uF (thpR k))
  Th0 := letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
    Submodule.span (𝓞 c.F) (Set.range fun k => valG h uF0 (th0R k))
  Thk := letI : ∀ Z : Comp Xo c, Module (𝓞 c.F) (AC Z) := fun Z => Algebra.toModule
    Submodule.span (𝓞 c.F) (Set.range fun k => valG h uka (thkR k))
  w k := valG h uL (wR k)
  jc := jc
  np := np
  thp k := valG h uF (thpR k)
  n0 := n0
  th0 k := valG h uF0 (th0R k)
  nk := nk
  thk k := valG h uka (thkR k)
  et := valG h uet etR
  ta1 := valG h uta1 ta1R
  ta2 := valG h uta2 ta2R
  nu := nu
  ip := ip
  wsize := wsize
  DF := DF
  PN := PN
  PQ := PQ
  tableDegreeThreeBase := tableDegreeThreeBase
  PP0' := PP0'
  Pd := Pd
  Gc := Gc
  PI4 := PI4
  Pet := Pet
  tableLineDegreeFive := tableLineDegreeFive
  tableLineDegreeTwo := tableLineDegreeTwo
  Prw := Prw
  PO := PO
  f := f
  r := r
section Laws
variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))
variable (Xo c) in

def CompNe : Prop := Nonempty (Comp Xo c)
variable (Xo c) in

def FnFG : Prop := ∀ Z : Comp Xo c, (⊤ : IntermediateField c.F (Om Z)).FG
variable (Xo c) in

def FnTrdeg (Dd : ℕ) : Prop := ∀ Z : Comp Xo c, Algebra.trdeg c.F (Om Z) = Dd
variable (Xo c) in

def FnAlgClosed : Prop :=
  ∀ (Z : Comp Xo c) (a : Om Z), IsAlgebraic c.F a → a ∈ (algebraMap c.F (Om Z)).range
def NZAt (h : GenFrEx Xo c) (f : Rul Xo c) : Prop := ∀ Z, evC h Z f ≠ 0
def LawBdd : Prop :=
  ∀ (sg : c.F →+* ℂ) (G : WTZ E) (f : ∀ Z, AC Z),
    ((f ∈ d.WW ∧ G = d.wL) ∨ (f ∈ d.Thp ∧ G = d.wF) ∨ (f = d.et ∧ G = d.n1 • d.wde) ∨
      (f = d.ta1 ∧ G = (2 : ℕ) • d.G1) ∨ (f = d.ta2 ∧ G = d.G2)) →
    BddAbove (Set.range fun p : (Σ Z, PT (Ω := Om Z) sg) => d.nrm p.1 G (f p.1) p.2)
def A1Bigness : Prop := ∀ Z, ∃ J : Fin d.D → Fin d.N,
    LinearIndependent (Om Z) fun k => KaehlerDifferential.D c.F (Om Z) (d.x Z (J k))
def A2RegularityOrders : Prop :=
  (∀ Z v, d.admitted Z v → ∀ f ∈ d.WW, f Z ≠ 0 → 0 ≤ d.ord Z v d.wL (f Z)) ∧
  (∀ Z v, d.admitted Z v → ∀ f ∈ d.Thp, f Z ≠ 0 → 0 ≤ d.ord Z v d.wF (f Z)) ∧
  (∀ Z v, d.admitted Z v → 0 ≤ d.ord Z v (d.n1 • d.wde) (d.et Z)) ∧
  (∀ Z v, d.admitted Z v → 0 ≤ d.ord Z v ((2 : ℕ) • d.G1) (d.ta1 Z)) ∧
  (∀ Z v, d.admitted Z v → 0 ≤ d.ord Z v d.G2 (d.ta2 Z))
def LawA3' : Prop := ∀ Z {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 → {v | d.admitted Z v ∧ d.ord Z v G f ≠ 0}.Finite
def A4Selection (sel : Fin d.del → Fin d.np) : Prop :=
  ∃ e : ∀ Z, AC Z, (∀ Z, e Z ∈ AG Z d.wF ∧ e Z ≠ 0) ∧
    (∀ p : Fin d.del → MvPolynomial (TVar d.D d.N) c.F,
      (∀ Z, ∑ k, d.sH Z (p k) *
        algebraMap (Om Z) (OmS (Om Z) d.D d.N) (ratio (Ω := Om Z) (d.thp (sel k) Z) (e Z)) = 0) →
      ∀ k, p k = 0) ∧
    (∀ y : ∀ Z, OmS (Om Z) d.D d.N, ∃ q : MvPolynomial (TVar d.D d.N) c.F, (∀ Z, d.sH Z q ≠ 0) ∧
      ∃ p : Fin d.del → MvPolynomial (TVar d.D d.N) c.F, ∀ Z, d.sH Z q * y Z = ∑ k, d.sH Z (p k) *
        algebraMap (Om Z) (OmS (Om Z) d.D d.N) (ratio (Ω := Om Z) (d.thp (sel k) Z) (e Z)))
def A13Measurable : Prop :=
  ∀ Z (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
      ∑ᶠ P ∈ d.ST Z sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
        Real.log (d.nrm Z G f P)) d.sphMeasure
def NumOK : Prop :=
  3 ≤ d.D ∧ 1 ≤ d.i ∧ 1 ≤ d.g0 ∧ 0 ≤ d.cc ∧ d.cc ≤ 1 ∧ d.cc * d.g0 ≤ 1 / 2 ∧ 1 ≤ d.wsize d.wL ∧
  d.DF ≤ d.wsize d.wL ∧ Real.log (d.N + 1 : ℕ) + 1 / 2 ≤ d.Prw * (d.wsize d.wL - 1) ∧
  Real.log (Module.finrank ℚ c.F) ≤ d.PO ∧
  Real.log (|(NumberField.discr c.F : ℝ)| ^ (1 / (Module.finrank ℚ c.F : ℝ))) ≤ d.PO ∧
  (1 ≤ d.PN ∧ 1 ≤ d.PQ ∧ 1 ≤ d.tableDegreeThreeBase ∧ 1 ≤ d.PP0' ∧ 1 ≤ d.Pd ∧ 1 ≤ d.Gc ∧ 1 ≤ d.PI4 ∧
    1 ≤ d.Pet ∧ 1 ≤ d.tableLineDegreeFive ∧ 1 ≤ d.tableLineDegreeTwo ∧ 1 ≤ d.Prw ∧ 1 ≤ d.PO)
end Laws
theorem valC_ne_zero {h : GenFrEx Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} {Z : Comp Xo c}
    (hf : evC h Z f ≠ 0) : valC h a n f Z ≠ 0 := by
  intro hz
  apply hf
  have := congrArg (fun x : AC Z => x.coeff (wtZ a n)) hz
  simpa [valC, AddMonoidAlgebra.coeff_single] using this
section AxHOf
variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
def axHOf (hne : CompNe Xo c) (hfg : FnFG Xo c) (htr : FnTrdeg Xo c Dd) (hac : FnAlgClosed Xo c)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) (het : NZAt h etR) (hta1 : NZAt h ta1R) (hta2 : NZAt h ta2R)
    (huet : wtZ uet.1 uet.2 = (i * g0) • wtZ ude.1 ude.2)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hfn : FnNe Xo c fn) (hconj : FnConj Xo c fn yP)
    (hbdd : LawBdd (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha1 : A1Bigness (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha2 : A2RegularityOrders (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha3' : LawA3' (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (sel : Fin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).del → Fin np)
    (ha4 : A4Selection (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) sel)
    (hnum : NumOK (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r))
    (ha13 : A13Measurable (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r)) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).AxH (fun Z => AG Z) := by
  obtain ⟨hD, hi, hg, hc0, hc1, hcg, hL, hDF, hrw, hnK, hrd, hP⟩ := hnum
  exact
  { nonempty := hne
    tower := fun _ => inferInstance
    towerO := fun _ => inferInstance
    D_ge := hD
    fg := hfg
    trdeg := htr
    algClosed := hac
    graded := fun Z => gradedAG Z
    finrank_one := finrank_AG
    mul_ne_zero := fun _ _ _ _ _ hf hg hf0 hg0 => mul_ne_zero_AG hf hg hf0 hg0
    WW_span := rfl
    w_mem := fun k Z => valC_mem h uL.1 uL.2 (wR k) Z
    w_base := fun Z => valC_ne_zero (hwb Z)
    Thp_span := rfl
    thp_mem := fun k Z => valC_mem h uF.1 uF.2 (thpR k) Z
    et_mem := fun Z => by
      have := valC_mem h uet.1 uet.2 etR Z
      rw [huet] at this
      exact this
    firstSectionMem := fun Z => by
      have := valC_mem h uta1.1 uta1.2 ta1R Z
      rw [huta1] at this
      exact this
    secondSectionMem := fun Z => by
      have := valC_mem h uta2.1 uta2.2 ta2R Z
      rw [huta2] at this
      exact this
    et_ne := fun Z => valC_ne_zero (het Z)
    firstSectionNeZero := fun Z => valC_ne_zero (hta1 Z)
    secondSectionNeZero := fun Z => valC_ne_zero (hta2 Z)
    ord_mul := fun Z v _ _ _ _ _ hf hg hf0 hg0 => ordC_mul (δ Z v) v hf hg hf0 hg0
    ord_smul := fun Z v _ _ _ a hf hf0 ha => ordC_smul (δ Z v) v a hf hf0 ha
    nrm_pos := fun Z _ _ P hf hf0 => nrmC_pos fn (yP Z) hfn P hf hf0
    nrm_zero := fun Z G P => nrmC_zero fn (yP Z) G P
    nrm_mul := fun Z _ _ _ _ P hf hg _ _ => nrmC_mul fn (yP Z) hfn P hf hg
    nrm_smul := fun Z _ _ P a hf _ _ => nrmC_smul fn (yP Z) P a hf
    nrm_conj := fun Z G x P => hconj Z G x P
    bdd := hbdd
    a1 := ha1
    ord_nonneg_WW := ha2.1
    ord_nonneg_Thp := ha2.2.1
    ord_nonneg_et := ha2.2.2.1
    ordDoubleFirstSection_nonneg := ha2.2.2.2.1
    ordSecondSectionNonneg := ha2.2.2.2.2
    a3' := ha3'
    sel := sel
    a4 := ha4
    i_ge := hi
    g_zero_ge_ask_sum := hg
    cc_nonneg := hc0
    cc_le := hc1
    ccg0 := hcg
    size_L := hL
    DF_le := hDF
    rw_le := hrw
    nK_le := hnK
    rd_le := hrd
    P_ge := hP
    a13 := ha13 }
end AxHOf
end Formalism.L2.Pj


