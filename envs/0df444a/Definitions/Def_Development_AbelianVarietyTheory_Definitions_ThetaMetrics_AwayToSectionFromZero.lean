-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:13.896809+00:00
-- url     : https://prove2.me/theorems/bf1c931a-5e4b-4ae2-8f30-c09994f91d19
-- title:
--   Away To Section From Zero
-- statement:
--   Definitions and structural lemmas for Away To Section From Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AwayToSectionFromZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)
namespace GlobalTheory.ProjFrac
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
instance isPrime_point (x : Proj 𝒜) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  ProjectiveSpectrum.isPrime x
def ev (U : (Proj 𝒜).Opens) (x : Proj 𝒜) (hx : x ∈ U) :
    Γ(Proj 𝒜, U) →+* Localization.AtPrime x.asHomogeneousIdeal.toIdeal :=
  (algebraMap (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) _).comp
    (openToLocalization 𝒜 U x hx).hom
variable {𝒜}
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in

theorem _root_.GlobalTheory.ProjFrac.ext {U : (Proj 𝒜).Opens} {s t : Γ(Proj 𝒜, U)}
    (h : ∀ x hx, _root_.GlobalTheory.ProjFrac.ev 𝒜 U x hx s =
      _root_.GlobalTheory.ProjFrac.ev 𝒜 U x hx t) : s = t := by
  refine Subtype.ext (funext fun y => HomogeneousLocalization.val_injective _ ?_)
  exact h y.1 y.2
variable (𝒜) in

def frac (U : (Proj 𝒜).Opens) {d : ℕ} (a b : A) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (hU : U ≤ Proj.basicOpen 𝒜 b) : Γ(Proj 𝒜, U) :=
  ⟨fun y => HomogeneousLocalization.mk ⟨d, ⟨a, ha⟩, ⟨b, hb⟩, hU y.2⟩, fun y =>
    ⟨U, y.2, 𝟙 _, d, ⟨a, ha⟩, ⟨b, hb⟩, _, fun _ => rfl⟩⟩
section
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b} {hU' : U ≤ Proj.basicOpen 𝒜 b'}
theorem ev_frac (x : Proj 𝒜) (hx : x ∈ U) :
    ev 𝒜 U x hx (frac 𝒜 U a b ha hb hU) = Localization.mk a ⟨b, hU hx⟩ := rfl
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_eq (h : a * b' = a' * b) :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU =
      _root_.GlobalTheory.ProjFrac.frac 𝒜 U a' b' ha' hb' hU' := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [_root_.GlobalTheory.ProjFrac.ev_frac, _root_.GlobalTheory.ProjFrac.ev_frac,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [OneMemClass.coe_one, one_mul]; linear_combination h⟩
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_mul :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU *
        _root_.GlobalTheory.ProjFrac.frac 𝒜 U a' b' ha' hb' hU' =
      _root_.GlobalTheory.ProjFrac.frac 𝒜 U (a * a') (b * b') (SetLike.mul_mem_graded ha ha')
        (SetLike.mul_mem_graded hb hb') (by rw [Proj.basicOpen_mul]; exact le_inf hU hU') := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [map_mul, _root_.GlobalTheory.ProjFrac.ev_frac, _root_.GlobalTheory.ProjFrac.ev_frac,
    _root_.GlobalTheory.ProjFrac.ev_frac, Localization.mk_mul]
  rfl
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_mul_eq {d'' : ℕ} {a'' b'' : A} {ha'' : a'' ∈ 𝒜 d''}
    {hb'' : b'' ∈ 𝒜 d''} {hU'' : U ≤ Proj.basicOpen 𝒜 b''} (h : a * a' * b'' = a'' * (b * b')) :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U a b ha hb hU *
        _root_.GlobalTheory.ProjFrac.frac 𝒜 U a' b' ha' hb' hU' =
      _root_.GlobalTheory.ProjFrac.frac 𝒜 U a'' b'' ha'' hb'' hU'' :=
  _root_.GlobalTheory.ProjFrac.frac_mul.trans (_root_.GlobalTheory.ProjFrac.frac_eq h)
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite in
variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] in
variable {𝒜} in
variable {U V : (Proj 𝒜).Opens} {d d' : ℕ} {a b a' b' : A} {ha : a ∈ 𝒜 d} {hb : b ∈ 𝒜 d}
  {ha' : a' ∈ 𝒜 d'} {hb' : b' ∈ 𝒜 d'} {hU : U ≤ Proj.basicOpen 𝒜 b}
  {hU' : U ≤ Proj.basicOpen 𝒜 b'} in

theorem _root_.GlobalTheory.ProjFrac.frac_self :
    _root_.GlobalTheory.ProjFrac.frac 𝒜 U b b hb hb hU = 1 := by
  refine _root_.GlobalTheory.ProjFrac.ext fun x hx => ?_
  rw [map_one, _root_.GlobalTheory.ProjFrac.ev_frac]
  exact Localization.mk_self (⟨b, hU hx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)
end
variable (𝒜) in

def fracUnit (U : (Proj 𝒜).Opens) {d : ℕ} (a b : A) (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (hUa : U ≤ Proj.basicOpen 𝒜 a) (hUb : U ≤ Proj.basicOpen 𝒜 b) : Γ(Proj 𝒜, U)ˣ where
  val := frac 𝒜 U a b ha hb hUb
  inv := frac 𝒜 U b a hb ha hUa
  val_inv := (frac_mul_eq (by ring)).trans (frac_self (hb := ha) (hU := hUa))
  inv_val := (frac_mul_eq (by ring)).trans (frac_self (hb := ha) (hU := hUa))
section Map
variable {B τ : Type} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ} [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
end Map
end GlobalTheory.ProjFrac


