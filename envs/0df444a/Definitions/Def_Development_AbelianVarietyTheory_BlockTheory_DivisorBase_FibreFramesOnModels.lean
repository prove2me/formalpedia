-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_FibreFramesOnModels
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_FibreFramesOnModels
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:35.533067+00:00
-- url     : https://prove2.me/theorems/c3cbac2d-1640-444c-bdf4-261fb3ea965d
-- title:
--   Fibre Frames On Models
-- statement:
--   Definitions and structural lemmas for Fibre Frames On Models, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/FibreFramesOnModels.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
abbrev KeyRule : Type 1 := ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ
def IsKeyRule (κ : KeyRule) : Prop :=
    (∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (M : Matrix (Fin P.g) (Fin P.g) K), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ 8 * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ 4 * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩) ∧
    (∀ (K K' : Type) [Field K] [CharZero K] [Field K'] [CharZero K'] (f : K →+* K') (x : KeyIn K) (x' : KeyIn K'),
      KeyPB x' x f → (κ K' x' : K') = f (κ K x)) ∧
    (∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K]
      [IsFractionRing R K] (x : KeyIn R) (xK : KeyIn K), KeyPB xK x (algebraMap R K) →
      ∃ u : Rˣ, (κ K xK : K) = algebraMap R K u ∧
        ∀ (k : Type) [Field k] [CharZero k] (r : R →+* k) (xk : KeyIn k), Function.Surjective r → KeyPB xk x r →
          (κ k xk : k) = r u) ∧
    (∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ),
      τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) →
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) →
      u.IsRig x.rig → u.IsFn x.th (thetaChar τ a b) →
      (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) → κ ℂ x = 1) ∧
    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
      (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (nth nη : ℝ),
      u.IsAH Hm χ → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) →
      IsAddFundamentalDomain u.Λ Fd volume →
      nth = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (z ⬝ᵥ Hm.mulVec (star z)).re)) / (volume Fd).toReal →
      nη = (volume Fd).toReal / (Real.pi ^ x.P.g * ‖W.det‖ ^ 2) →
      ‖(κ ℂ x : ℂ)‖ * nth ^ 4 * nη ^ 2 = (2 * Real.pi) ^ (2 * x.P.g)
section Fibre
variable {R R' : Type} [CommRing R] [CommRing R']
def IsFibreOf (x : KeyIn R') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (rig : LB.Gen (L.pull (eSec G)))
    (θ : L.Sec) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (f : R →+* R') : Prop :=
  ∃ (φ : x.P.A.left ⟶ G.left) (he : eSec x.P.A ≫ φ = spMap f ≫ eSec G)
    (e : LB.Iso x.P.L (L.pull φ)) (hg : x.P.g = n) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x.P.A G (spMap f) φ ∧ e.IsGen ∧
    LB.Gen.Maps (LB.linCombIso e (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap f) he L rig) ∧
    (∀ (j : (L.pull φ).ι) (i : x.P.L.ι) (h : (L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (θ.f (j PUnit.unit)) =
        (show Γ(x.P.A.left, (L.pull φ).U j ⊓ x.P.L.U i) from (e.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x.v i).left ≫ φ = spMap F ≫ (w (i.cast hg)).left
def IsMul {X : Over (Sp R)} {L : LB X.left} (σ : L.Sec) (a : R) (θ : L.Sec) : Prop :=
  ∀ i, σ.f i = constFn X.hom _ a * θ.f i
def Generates {X : Over (Sp R)} {L : LB X.left} (θ : L.Sec) : Prop :=
  ∀ σ : L.Sec, ∃! a : R, IsMul σ a θ
end Fibre
section Box
variable {S : Scheme.{0}}
abbrev pow (G : Over S) (N : ℕ) : Over S := ∏ᶜ (fun _ : Fin N => G)
abbrev pr (G : Over S) (N : ℕ) (k : Fin N) : (pow G N).left ⟶ G.left := (Pi.π (fun _ : Fin N => G) k).left
abbrev boxLB (G : Over S) (L : LB G.left) (N : ℕ) : LB (pow G N).left :=
  LB.LinComb L (K := Fin N) (pr G N) (fun _ => 1)
def tensorSec {X Y : Scheme.{0}} {L : LB X} {N : ℕ} (φ : Fin N → (Y ⟶ X)) (θ : L.Sec) :
    (LB.LinComb L (K := Fin N) φ (fun _ => 1)).Sec where
  f j := ∏ k, ((φ k).appLE _ _ (LB.wchart_le L φ j k)).hom (θ.f (j k))
  compat j j' := by
    have hle : ∀ k, LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) := fun k =>
      le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k))
    show resG Y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)
        (∏ k, ((φ k).appLE _ _ (LB.wchart_le L φ j k)).hom (θ.f (j k))) =
      ((∏ k, (res (hle k) (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (1 : ℤ) :
        Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ) : Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')) *
      resG Y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ _)
        (∏ k, ((φ k).appLE _ _ (LB.wchart_le L φ j' k)).hom (θ.f (j' k)))
    rw [map_prod, map_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have h := congrArg ((φ k).appLE _ _ (hle k)).hom (θ.compat (j k) (j' k))
    rw [map_mul] at h
    simp only [← CommRingCat.comp_apply, Scheme.Hom.map_appLE] at h
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, zpow_one]
    exact h
abbrev boxSec (G : Over S) {L : LB G.left} (θ : L.Sec) (N : ℕ) : (boxLB G L N).Sec := tensorSec (pr G N) θ
end Box
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def IsBaseRing (β : O →+* c.F) : Prop :=
  Function.Injective β ∧ ∀ x : c.F, IsIntegral ℤ x → x ∈ Set.range β
def UnitAt (κ : KeyRule) (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K] : Prop :=
  ∀ (y : Sp K ⟶ Xo.XF c) (yt : Sp V ⟶ Y.X), spMap (algebraMap V K) ≫ yt = y ≫ Y.j →
    ∀ (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w →
      ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) →
        (Generates (X := t.G) θ →
          (∃ u : Vˣ, (κ K x : K) = algebraMap V K u) ∧
          ∀ N : ℕ, 8 ∣ N → Generates (X := pow t.G N) (boxSec t.G θ N)) ∧
        ∀ N : ℕ, 8 ∣ N → ∀ (σ : (boxLB t.G t.PP.L N).Sec) (a : V), Generates (X := pow t.G N) σ →
          IsMul (X := pow t.G N) (boxSec t.G θ N) a σ →
          ∃ u : Vˣ, algebraMap V K a * (κ K x : K) ^ (N / 8) = algebraMap V K u
def AtValuedPoints (Q : ∀ (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K], Prop) : Prop :=
  (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Q V K) ∧
  ∀ (V C : Type) [CommRing V] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra V C], IsUnitBall V C → Q V C
def FramesAt (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [CharZero K] [Algebra V K] : Prop :=
  ∀ (y : Sp K ⟶ Xo.XF c) (yt : Sp V ⟶ Y.X), spMap (algebraMap V K) ≫ yt = y ≫ Y.j →
    ∃ (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)) (θ : t.PP.L.Sec) (x : KeyIn K),
      IsLieBasis w ∧ Generates (X := t.G) θ ∧ IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K)
def KeyUnitOnModels : Prop :=
  ∀ κ : KeyRule, IsKeyRule κ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
      (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ),
      1 ≤ D.p + D.q → IsBaseRing β → p.Prime → Y.LevelStructureConditions p → Y.N3 → Y.N4 → Y.SplitFibres →
      AtValuedPoints (fun V K _ _ _ _ => UnitAt κ Y V K)
def FramesOnModels : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ),
    1 ≤ D.p + D.q → IsBaseRing β → p.Prime → Y.LevelStructureConditions p → Y.N3 → Y.N4 → Y.SplitFibres →
    AtValuedPoints (fun V K _ _ _ _ => FramesAt Y V K)
end GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels


