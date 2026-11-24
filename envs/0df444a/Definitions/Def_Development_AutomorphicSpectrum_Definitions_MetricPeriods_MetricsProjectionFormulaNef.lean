-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_MetricsProjectionFormulaNef
-- name    : Development_AutomorphicSpectrum_Definitions_MetricPeriods_MetricsProjectionFormulaNef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:29.571811+00:00
-- url     : https://prove2.me/theorems/598bcd9a-fbeb-4341-80e1-01ea8a7b0615
-- title:
--   Metrics Projection Formula Nef
-- statement:
--   Definitions and structural lemmas for Metrics Projection Formula Nef, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/MetricsProjectionFormulaNef.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_KleimanSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GenericComplexPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Birational
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsTwiceDifferentiableAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def combLine {σ : Type} [Fintype σ] (A : σ → HermLine ι) (n : σ → ℤ) : HermLine ι where
  a := fun k => ∑ x, n x * (A x).a k
  h z := ∏ x, (A x).h z ^ n x
  pos z hz := Finset.prod_pos fun x _ => zpow_pos ((A x).pos z hz) _
  smul c z hc := by
    have h0 : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have h1 : ∀ k, ‖c k‖ ^ (∑ x, n x * (A x).a k) = ∏ x, (‖c k‖ ^ (A x).a k) ^ n x := by
      intro k
      classical
      induction (Finset.univ : Finset σ) using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add₀ (h0 k), ih, ← zpow_mul, mul_comm (n x)]
    simp only [fun x => (A x).smul c z hc, mul_zpow, Finset.prod_mul_distrib, h1]
    rw [Finset.prod_comm]
    simp only [Finset.prod_zpow]
namespace AnSys
variable {e : ℕ} {σ : Type} (S : AnSys e σ)
def nComp : ℕ := Nat.card (ConnectedComponents S.X)
def degNumDe (w : Fin e → σ) : ℝ := S.degNum w / S.nComp
def degPolyDe [Fintype σ] : MvPolynomial σ ℝ := formPoly e S.degNumDe
end AnSys
structure Realis {D : ℕ} {σ : Type} (S : AnSys D σ) (P : Ideal (MRing ι)) where
  arith : IsArithVar P (D + 1)

  J : Ideal (MRing ι)

  R : AnLogRes P J D

  π : R.X → S.X
  holo : HoloMap R.A S.A π

  deg : ℕ
  deg_pos : 0 < deg

  br : Set S.X
  degree : IsDegreeOff S.A R.A π deg br

  ref : σ → HermLine ι
  ref_smooth : ∀ a, IsSmoothHerm (ref a)
  ref_pot : ∀ a, SamePot R.A Set.univ (potOf R (ref a)) ((S.th a).pullback π holo.1)

  line : σ → ℝ → HermLine ι
  line_deg : ∀ a t, (line a t).a = (ref a).a
  line_smooth : ∀ a t, 0 < t → t ≤ S.t₀ → IsSmoothHerm (line a t)
  line_eq : ∀ a t, 0 < t → t ≤ S.t₀ → ∀ x,
    Real.log ((line a t).h (R.lift x x)) = Real.log ((ref a).h (R.lift x x)) + S.phT a t (π x)
namespace Realis
variable {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (II : IntersectionSystem)
def num (t : ℝ) (w : Fin (D + 1) → σ) : ℝ :=
  II K ι P (D + 1) (fun j => Re.line (w j) t) / Re.deg
def limNum (w : Fin (D + 1) → σ) : ℝ := limUnder (𝓝[>] 0) fun t => Re.num II t w
def FT [Fintype σ] (t : ℝ) : MvPolynomial σ ℝ := formPoly (D + 1) (Re.num II t)
def PB [Fintype σ] : MvPolynomial σ ℝ := formPoly (D + 1) (Re.limNum II)
def de : ℕ := S.nComp * Re.deg
def numDe (t : ℝ) (w : Fin (D + 1) → σ) : ℝ :=
  II K ι P (D + 1) (fun j => Re.line (w j) t) / Re.de
def limNumDe (w : Fin (D + 1) → σ) : ℝ := Re.limNum II w / S.nComp
def FTDe [Fintype σ] (t : ℝ) : MvPolynomial σ ℝ := formPoly (D + 1) (Re.numDe II t)
def PBDe [Fintype σ] : MvPolynomial σ ℝ := formPoly (D + 1) (Re.limNumDe II)
def comap {σ' : Type} (f : σ' → σ) : Realis (S.comap f) P where
  arith := Re.arith
  J := Re.J
  R := Re.R
  π := Re.π
  holo := Re.holo
  deg := Re.deg
  deg_pos := Re.deg_pos
  br := Re.br
  degree := Re.degree
  ref a := Re.ref (f a)
  ref_smooth a := Re.ref_smooth (f a)
  ref_pot a := Re.ref_pot (f a)
  line a := Re.line (f a)
  line_deg a := Re.line_deg (f a)
  line_smooth a := Re.line_smooth (f a)
  line_eq a := Re.line_eq (f a)
end Realis
section Weights
variable {D N : ℕ} {Ψ : Type} [Fintype Ψ] {S : AnSys D (Option (Ψ × Fin N))} {P : Ideal (MRing ι)}
  (Re : Realis S P) (II : IntersectionSystem)
def Realis.PBs : MvPolynomial (Option (Ψ × Fin N)) ℝ := toWtS (Re.PB II)
def Realis.PBwt : MvPolynomial (Ψ × Fin N) ℝ := toWt ((Re.comap some).PB II)
def scaleS {τ : Type} (k : ℕ) : MvPolynomial (Option τ) ℝ →ₐ[ℝ] MvPolynomial (Option τ) ℝ :=
  aeval fun o : Option τ => o.elim (C (k : ℝ)⁻¹ * X none) fun p => X (some p)
def Realis.PBsDe (k : ℕ) : MvPolynomial (Option (Ψ × Fin N)) ℝ := scaleS k (toWtS (Re.PBDe II))
def Realis.PBwtDe : MvPolynomial (Ψ × Fin N) ℝ := toWt ((Re.comap some).PBDe II)
end Weights
def NefAt (P : Ideal (MRing ι)) (p : ℕ) (a : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsMultiProjPrime W → P ≤ W → charOf W = p →
    ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) → 0 ≤ geoNum 1 W fun _ => a
def VertClose (P : Ideal (MRing ι)) (T : Finset ℕ) (α : ℕ → ℝ) (A B : HermLine ι) : Prop :=
  ∃ (f g : MRing ι) (df dg : K → ℕ), IsMultiHomog f df ∧ IsMultiHomog g dg ∧ f ∉ P ∧ g ∉ P ∧
    (∀ k, (df k : ℤ) - dg k = A.a k - B.a k) ∧
    (∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ * B.h z = ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z) ∧
    (∀ W, charOf W ∉ T → divCycle P f W = divCycle P g W) ∧
    ∀ W, charOf W ∈ T →
      |(divCycle P f W : ℝ) - divCycle P g W| ≤ α (charOf W) * divCycle P (C (charOf W : ℤ)) W
def Inputs : Prop :=
  (ConvergenceStatement ∧ ConvergenceSignedStatement ∧ ConvergenceRateStatement ∧ UnifIntStatement ∧
    PullbackStatement ∧ RegGlobalStatement) ∧
  (ResExistsStatement ∧ ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement ∧ ArithmeticIntersectionNonneg) ∧
  (ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement ∧ ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement) ∧
  (ReciprocityTheory.ChartRestriction.G.AI.I4.PFStatement ∧ ReciprocityTheory.ChartRestriction.G.AI.I4.LineFibreStatement ∧
    ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) ∧
  (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg ∧ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement ∧
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.SiuZStatement)
namespace Inputs
end Inputs
end GlobalTheory.CompanionTheory.Ar.PB


