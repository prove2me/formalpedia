-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:32:15.940542+00:00
-- url     : https://prove2.me/theorems/d486ce60-7121-496f-977b-d3ffb9be3886
-- title:
--   Is Lie Basis
-- statement:
--   Definitions and structural lemmas for Is Lie Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsLieBasis.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Semi
section Lie
variable {R : Type} [CommRing R]
abbrev epsR (R : Type) [CommRing R] : Over (Sp R) := Over.mk (spMap (algebraMap R (DualNumber R)))
def epsScaleR (c : R) : DualNumber R →+* DualNumber R :=
  (TrivSqZeroExt.map (c • (LinearMap.id : R →ₗ[R] R))).toRingHom
def IsTangent {G : Over (Sp R)} [GrpObj G] (v : epsR R ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = η[G].left
def IsLieComb {G : Over (Sp R)} [GrpObj G] {n : ℕ} (c : Fin n → R) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) : Prop :=
  ∃ u : Fin n → (epsR R ⟶ G), (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod
def IsLieBasis {G : Over (Sp R)} [GrpObj G] {n : ℕ} (v : Fin n → (epsR R ⟶ G)) : Prop :=
  (∀ i, IsTangent (v i)) ∧ ∀ w, IsTangent w → ∃! c : Fin n → R, IsLieComb c v w
end Lie
def constFn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) (a : R) : Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
structure KeyIn (R : Type) [CommRing R] where
  P : Out.PolAV (Sp R)
  g_pos : 1 ≤ P.g
  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen
  th : P.L.Sec
  th_ne : ∀ s : Sp R, ∃ x : P.A.left, P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th
  v : Fin P.g → (epsR R ⟶ P.A)
  basis : IsLieBasis v
def KeyPB {R R' : Type} [CommRing R] [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R') : Prop :=
  ∃ (φ : x'.P.A.left ⟶ x.P.A.left) (he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
      (rigPullOf φ (spMap f) he x.P.L x.rig) ∧
    (∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι)
      (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (x.th.f (j PUnit.unit)) =
        (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x'.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x'.v i).left ≫ φ = spMap F ≫ (x.v (i.cast hg)).left
section Complex
variable {X : Scheme.{0}}
def valAt (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : ℂ :=
  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((x.appLE U ⊤ h).hom f)
open Classical in

def valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : ℂ := if h : ⊤ ≤ x ⁻¹ᵁ U then valAt x U h f else 0
structure HolUnif (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) where
  ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)
  ex_add : ∀ z w, ex (z + w) = ex z * ex w
  ex_onto : Function.Surjective ex
  Λ : Submodule ℤ (Fin g → ℂ)
  ker : ∀ z, ex z = 1 ↔ z ∈ Λ
  discrete : DiscreteTopology Λ
  full : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤
  hol : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valAt' (ex z).left U f) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}
  fr : L.ι → (Fin g → ℂ) → ℂ
  fr_hol : ∀ i, DifferentiableOn ℂ (fr i) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i}
  fr_ne : ∀ i z, ⊤ ≤ (ex z).left ⁻¹ᵁ L.U i → fr i z ≠ 0
  fr_compat : ∀ i j z, ⊤ ≤ (ex z).left ⁻¹ᵁ (L.U i ⊓ L.U j) →
    fr i z = valAt' (ex z).left (L.U i ⊓ L.U j) (L.g i j).val * fr j z
namespace HolUnif
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
def IsFn (s : L.Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → valAt' (u.ex z).left (L.U i) (s.f i) = θ z * u.fr i z
def IsRig (rig : LB.Gen (L.pull (eSec A))) : Prop :=
  ∀ j : (L.pull (eSec A)).ι, ⊤ ≤ (L.pull (eSec A)).U j →
    u.fr (j PUnit.unit) 0 = valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U j) (rig.s j).val
def IsDiff (w : Fin g → ℂ) (v : epsR ℂ ⟶ A) : Prop :=
  ∀ (U : A.left.Opens) (h : ⊤ ≤ v.left ⁻¹ᵁ U) (f : Γ(A.left, U)),
    TrivSqZeroExt.snd (show DualNumber ℂ from
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.left.appLE U ⊤ h).hom f)) =
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w
def IsAH (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) ∧ (∀ l, ‖χ l‖ = 1) ∧
    ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)
end HolUnif
def thetaChar {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (z : Fin g → ℂ) : ℂ :=
  ∑' n : Fin g → ℤ, Complex.exp (Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n i : ℂ)) + a)) +
    2 * Real.pi * Complex.I * (((fun i => (n i : ℂ)) + a) ⬝ᵥ (z + b)))
end Complex
def KeyFormula : Prop :=
  ∃ κ : ∀ (K : Type) [Field K] [CharZero K], KeyIn K → Kˣ,

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
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


