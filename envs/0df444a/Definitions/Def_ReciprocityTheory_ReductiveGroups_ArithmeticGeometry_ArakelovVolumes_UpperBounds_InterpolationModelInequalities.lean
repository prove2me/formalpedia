-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:46.613833+00:00
-- url     : https://prove2.me/theorems/879a5001-f219-408f-a367-a473b97d3c83
-- title:
--   Interpolation Model Inequalities
-- statement:
--   Definitions and structural lemmas for Interpolation Model Inequalities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/InterpolationModelInequalities.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_Bridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
open scoped ContDiff ENNReal
noncomputable section
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]
def BasePotentialExistence {r : ℕ} (X : FD.Data E r) (de : Wt X.Ψ r) (rr a1 : ℝ) : Prop :=
  ∃ ps0 : Frame X.Ψ r → ℝ, IsInvFn X ps0 ∧
    (∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps0 (cpt X x0 z)) {z | cpt X x0 z ∈ X.dom}) ∧
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      -(rr / 2 * leviM X (phla X de) x0 z ξ) ≤ leviM X ps0 x0 z ξ) ∧
    cfwM X ps0 a1
def InterpolationModelInequalities {r : ℕ} (X : FD.Data E r) {N : ℕ} (L eW : Wt X.Ψ r) (w : Fin N → Frame X.Ψ r → ℂ)
    (et : Frame X.Ψ r → ℂ) (c i : ℝ) (ph : Frame X.Ψ r → ℝ) : Prop :=
  (∃ K : ℝ, ∀ x ∈ X.dom, Real.exp (-(2 * c * ph x)) ≤ K * ∑ k, X.pnorm L (w k) x ^ 2) ∧
  ∃ K : ℝ, ∀ x ∈ X.dom, X.pnorm eW et x ^ 2 ≤ K * Real.exp (-(2 * i * ph x))
def InstArchStatement : Prop :=
  ∀ (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ)
    (R : Reading (𝒜 := 𝒜) d c X sg) (het : d.et c ∈ R.Rg) (hta1 : d.ta1 c ∈ R.Rg)
    (hta2 : d.ta2 c ∈ R.Rg) (k0 : Fin d.np) (hthp : d.thp k0 c ∈ R.Rg)
    (ph : Frame X.Ψ r → ℝ) (c1 a1 rr : ℝ)
    (hF : d.wF ∈ R.WE) (hde : (2 : ℕ) • d.wde ∈ R.WE),
    d.AxW 𝒜 → Even d.g0 →
    2 ≤ nd X → 11 * nd X ^ 2 ≤ d.T → 1 ≤ d.i → 1 ≤ d.g0 → 0 < d.cc → (d.T : ℝ) * d.cc * d.g0 ≤ 1 →
    0 < c1 → 0 < a1 → 0 ≤ rr → rr * (1 + c1 / a1) ≤ 2 * d.T →
    (∀ j, R.rd ⟨d.w j c, R.w_mem j⟩ ∈ X.SSgt (R.wt ⟨d.wL, R.wL_mem⟩) 0) →
    (∀ x ∈ X.dom, ∃ j, R.rd ⟨d.w j c, R.w_mem j⟩ x ≠ 0) →
    X.IsSec ((d.i * (d.g0 / 2)) • R.wt ⟨(2 : ℕ) • d.wde, hde⟩) (R.rd ⟨d.et c, het⟩) →
    (∃ x ∈ X.dom, R.rd ⟨d.et c, het⟩ x ≠ 0) →
    R.rd ⟨d.ta1 c, hta1⟩ ∈ X.SSgt ((2 : ℕ) • R.wt ⟨d.wL, R.wL_mem⟩ - R.wt ⟨(2 : ℕ) • d.wde, hde⟩) 0 →
    (∃ x ∈ X.dom, R.rd ⟨d.ta1 c, hta1⟩ x ≠ 0) →
    R.rd ⟨d.ta2 c, hta2⟩ ∈ X.SSgt ((nd X + 4 : ℕ) • R.wt ⟨d.wL, R.wL_mem⟩ - R.wt ⟨d.wF, hF⟩) 0 →
    (∃ x ∈ X.dom, R.rd ⟨d.ta2 c, hta2⟩ x ≠ 0) →
    R.rd ⟨d.thp k0 c, hthp⟩ ∈ X.SSgt (R.wt ⟨d.wF, hF⟩) 0 →
    (∃ x ∈ X.dom, R.rd ⟨d.thp k0 c, hthp⟩ x ≠ 0) →
    IsInvFn X ph → (∀ x ∈ X.dom, 0 ≤ ph x) →
    (∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 → ca / X.la1 x ^ 2 ≤ ph x) →
    (∀ x ∈ X.dom, (d.T : ℝ) * d.cc * ph x ≤ c1 / X.la1 x ^ 2) →
    InterpolationModelInequalities X (R.wt ⟨d.wL, R.wL_mem⟩) ((d.i * (d.g0 / 2)) • R.wt ⟨(2 : ℕ) • d.wde, hde⟩) (fun j x => R.rd ⟨d.w j c, R.w_mem j⟩ x)
      (R.rd ⟨d.et c, het⟩) d.cc d.i ph →
    BasePotentialExistence X (R.wt ⟨(2 : ℕ) • d.wde, hde⟩) rr a1 →
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X (R.wt ⟨d.wL, R.wL_mem⟩)) x0 z ξ) →
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X ((2 : ℕ) • R.wt ⟨d.wL, R.wL_mem⟩ - R.wt ⟨(2 : ℕ) • d.wde, hde⟩)) x0 z ξ) →
    (∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 ≤ t → t * rr ≤ 2 * d.T →
      ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
        2 * η * leviM X (phla X (R.wt ⟨d.wL, R.wL_mem⟩)) x0 z ξ ≤
          leviM X (phla X (R.wt ⟨d.wF, hF⟩ - kapW X - nd X • R.wt ⟨d.wL, R.wL_mem⟩)) x0 z ξ -
            t * (rr / 2) * leviM X (phla X (R.wt ⟨(2 : ℕ) • d.wde, hde⟩)) x0 z ξ) →
    ∃ (Xa : ArchInM X) (e : Fin Xa.N ≃ Fin (d.N + 1)),
      Xa.L = R.wt ⟨d.wL, R.wL_mem⟩ ∧ Xa.de = R.wt ⟨(2 : ℕ) • d.wde, hde⟩ ∧ Xa.Fp = R.wt ⟨d.wF, hF⟩ ∧ Xa.T = d.T ∧
      Xa.i = d.i ∧ Xa.g0 = d.g0 ∧ Xa.c = d.cc ∧ Xa.c1 = c1 ∧ Xa.a1 = a1 ∧ Xa.rr = rr ∧ Xa.ph = ph ∧
      (∀ j, Xa.w j = R.rd ⟨d.w (e j) c, R.w_mem _⟩) ∧
      Xa.et = R.rd ⟨d.et c, het⟩ ∧ Xa.th1 = R.rd ⟨d.ta1 c, hta1⟩ ∧
      Xa.th2 = R.rd ⟨d.ta2 c, hta2⟩ ∧ Xa.thp = R.rd ⟨d.thp k0 c, hthp⟩
def IsDominantR {r : ℕ} (X : FD.Data E r) (v : X.Ψ → Fin r → ℝ) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i ≤ j → (j : ℕ) < X.p0 → v τ j ≤ v τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i ≤ j → v τ j ≤ v τ i) ∧
    (∀ i j : Fin r, (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → v τ i ≤ v τ j)
def CurvNumStatement : Prop :=
  ∀ (r : ℕ) (X : FD.Data E r) (L de Fp : Wt X.Ψ r) (T rr η : ℝ), 0 < η → 0 < rr → 0 ≤ T →
    IsStrictDom X L → IsStrictDom X (2 • L - de) →
    (∀ t ∈ ({0, 2 * T / rr} : Set ℝ), IsDominantR X fun τ a =>
      ((Fp - kapW X - nd X • L) τ a : ℝ) - t * (rr / 2) * (de τ a : ℝ) - 2 * η * (L τ a : ℝ)) →
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X L) x0 z ξ) ∧
    (∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < leviM X (phla X (2 • L - de)) x0 z ξ) ∧
    ∀ t : ℝ, 0 ≤ t → t * rr ≤ 2 * T → ∀ x0 ∈ X.dom, ∀ z, cpt X x0 z ∈ X.dom → ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviM X (phla X L) x0 z ξ ≤
        leviM X (phla X (Fp - kapW X - nd X • L)) x0 z ξ - t * (rr / 2) * leviM X (phla X de) x0 z ξ
def de2W {r : ℕ} (X : FD.Data E r) : Wt X.Ψ r := fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1
def TorusHyp {r : ℕ} (X : FD.Data E r) : Prop :=
  (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
    Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - FD.cc (w0 : E)) • v)) -
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) ∧
  (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧
  (ReciprocityTheory.ChartRestriction.G.I2.PT.f E : ℝ) ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧
  16 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ∧
  ∃ m : ℕ, 1 ≤ m ∧ m ^ 4 ≤ ReciprocityTheory.ChartRestriction.G.I2.PT.f E ∧ (X.p0 ≤ m ∨ r - X.p0 ≤ m)
def BasePotentialExistenceInstance : Prop :=
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    BasePotentialExistence X.toData (de2W X.toData) (r : ℝ)
      (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card)))
def TTset (T : ReciprocityTheory.ChartRestriction.G.I2.PT E) : Set (Fin T.r → ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim) :=
  {a | (∀ j, a j ∈ ZSpan.fundamentalDomain T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ T.L) ∧
    ∀ x ∈ T.L, ∃ c : Fin T.r → 𝓞 E, ∃ y ∈ T.L,
      x = ∑ j, ReciprocityTheory.ChartRestriction.G.I2.act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}
def psiT {r : ℕ} {X : FD.Data E r} {x : Frame X.Ψ r} (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt X x) : ℝ :=
  Real.log (∑ᶠ (a : Fin A.T.r → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) (_ : a ∈ TTset A.T),
    ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)
def psi0 {r : ℕ} (X : FD.Data E r) (x : Frame X.Ψ r) : ℝ :=
  open Classical in if h : Nonempty (ReciprocityTheory.ChartRestriction.G.I2.TorusAt X x) then psiT (Classical.choice h) else 0
def BasePotentialPositivity : Prop :=
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    ∀ x ∈ X.toData.dom, ∀ A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt X.toData x,
      0 < ∑ᶠ (a : Fin A.T.r → ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) (_ : a ∈ TTset A.T),
        ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s
def BasePotentialInvariance : Prop :=
  BasePotentialPositivity (E := E) →
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    IsInvFn X.toData (psi0 X.toData) ∧
    ∀ x0 ∈ X.toData.dom, ContDiffOn ℝ ∞ (fun z => psi0 X.toData (cpt X.toData x0 z))
      {z | cpt X.toData x0 z ∈ X.toData.dom}
def BasePotentialSmoothness : Prop :=
  BasePotentialPositivity (E := E) →
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    ∀ x0 ∈ X.toData.dom, ContDiffOn ℝ ∞ (fun z => psi0 X.toData (cpt X.toData x0 z))
      {z | cpt X.toData x0 z ∈ X.toData.dom}
def BasePotentialLeviForm : Prop :=
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    ∀ x0 ∈ X.toData.dom, ∀ z, cpt X.toData x0 z ∈ X.toData.dom → ∀ ξ : Fin (nd X.toData) → ℂ,
      -((r : ℝ) / 2 * leviM X.toData (phla X.toData (de2W X.toData)) x0 z ξ) ≤
        leviM X.toData (psi0 X.toData) x0 z ξ
def BasePotentialComparison : Prop :=
  BasePotentialPositivity (E := E) →
  ∀ (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → TorusHyp X.toData →
    cfwM X.toData (psi0 X.toData)
      (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr E : ℝ)| ^ ((1 : ℝ) / X.Ψ.card)))
end
end ReciprocityTheory.ChartRestriction.G.AR.Up


