-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PolarizationCorrespondence
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_PolarizationCorrespondence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:25.541863+00:00
-- url     : https://prove2.me/theorems/86d400c2-ff7b-4ea6-b00e-d01dfcf58442
-- title:
--   Polarization Correspondence
-- statement:
--   Definitions and structural lemmas for Polarization Correspondence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PolarizationCorrespondence.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence
section Dual
variable {R R' : Type} [CommRing R] [CommRing R']
def epsHom (f : R →+* R') (c : R') : DualNumber R →+* DualNumber R' where
  toFun x := TrivSqZeroExt.inl (f x.fst) + TrivSqZeroExt.inr (c * f x.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [mul_add]
  map_mul' x y := by
    ext
    · simp
    · simp
      ring
@[simp] lemma epsHom_fst (f : R →+* R') (c : R') (x : DualNumber R) :
    (epsHom f c x).fst = f x.fst := by simp [epsHom]
@[simp] lemma epsHom_snd (f : R →+* R') (c : R') (x : DualNumber R) :
    (epsHom f c x).snd = c * f x.snd := by simp [epsHom]
variable (R) in

def epsRed : DualNumber R →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom
variable (R) in

abbrev SpEps : Over (Sp R) := Over.mk (spMap (algebraMap R (DualNumber R)))
variable (R) in

def epsZero : 𝟙_ (Over (Sp R)) ⟶ SpEps R :=
  Over.homMk (spMap (epsRed R)) (by
    change spMap (epsRed R) ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (epsRed R).comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext a; simp [epsRed, TrivSqZeroExt.algebraMap_eq_inl]
    rw [this, CommRingCat.ofHom_id, Spec.map_id])
def epsScale (c : R) : SpEps R ⟶ SpEps R :=
  Over.homMk (spMap (epsHom (RingHom.id R) c)) (by
    change spMap (epsHom (RingHom.id R) c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (epsHom (RingHom.id R) c).comp (algebraMap R (DualNumber R)) =
        algebraMap R (DualNumber R) := by
      ext a <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this])
lemma epsZero_scale (c : R) : epsZero R ≫ epsScale c = epsZero R := by
  ext1
  change spMap (epsRed R) ≫ spMap (epsHom (RingHom.id R) c) = spMap (epsRed R)
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (epsRed R).comp (epsHom (RingHom.id R) c) = epsRed R := by
    refine RingHom.ext fun x => ?_
    simp [epsRed]
  rw [this]
end Dual
section Lie
variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
def lieSub : Subgroup (SpEps R ⟶ G) where
  carrier := {v | epsZero R ≫ v = η[G]}
  one_mem' := by
    change epsZero R ≫ (1 : SpEps R ⟶ G) = η[G]
    rw [comp_one, Hom.one_def, toUnit_unit, Category.id_comp]
  mul_mem' := by
    intro a b ha hb
    change epsZero R ≫ (a * b) = η[G]
    have h1 : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [comp_mul, show epsZero R ≫ a = η[G] from ha, show epsZero R ≫ b = η[G] from hb, h1, _root_.mul_one]
  inv_mem' := by
    intro a ha
    change epsZero R ≫ a⁻¹ = η[G]
    have h1 : (η[G] : 𝟙_ (Over (Sp R)) ⟶ G) = 1 := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [GrpObj.comp_inv, show epsZero R ≫ a = η[G] from ha, h1, inv_one]
abbrev Tan : Type := ↥(lieSub G)
variable {G}
def Tan.smul (c : R) (v : Tan G) : Tan G :=
  ⟨epsScale c ≫ v.1, by
    change epsZero R ≫ epsScale c ≫ v.1 = η[G]
    rw [← Category.assoc, epsZero_scale]
    exact v.2⟩
def linComb {n : ℕ} (c : Fin n → R) (v : Fin n → Tan G) : Tan G :=
  (List.ofFn fun i => Tan.smul (c i) (v i)).prod
def IsLieBasis {n : ℕ} (v : Fin n → Tan G) : Prop :=
  Function.Bijective fun c : Fin n → R => linComb c v
def TanCorr {R' : Type} [CommRing R'] {G' : Over (Sp R')} [GrpObj G'] (f : R →+* R')
    (φ : G'.left ⟶ G.left) (v' : Tan G') (v : Tan G) : Prop :=
  v'.1.left ≫ φ = spMap (epsHom f 1) ≫ v.1.left
example (v : Tan G) : TanCorr (RingHom.id R) (𝟙 G.left) (Tan.smul 1 v) v := by
  simp [TanCorr, Tan.smul, epsScale]
example (c : R) (v : Tan G) : linComb ![c] ![v] = Tan.smul c v := by
  simp [linComb]
end Lie
section Input
def NonzeroOnFibres {S : Scheme.{0}} (A : Over S) {L : LB A.left} (s : LB.Sec L) : Prop :=
  ∀ y : S, ∃ x : A.left, A.hom x = y ∧ x ∈ nonzeroLocus s
def GeneratesSections {S : Scheme.{0}} (A : Over S) {L : LB A.left} (s : LB.Sec L) : Prop :=
  ∀ t : LB.Sec L, ∃ r : Γ(S, ⊤), ∀ i,
    t.f i = (A.hom.appLE ⊤ (L.U i) le_top).hom r * s.f i
def SecCorr {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (φ : X' ⟶ X) (w : LB.Iso L' (L.pull φ))
    (s' : LB.Sec L') (s : LB.Sec L) : Prop :=
  ∀ (j : PUnit → L.ι) (i : L'.ι),
    resG X' (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => φ) j PUnit.unit) :
        (L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ L.U (j PUnit.unit))
      ((φ.app (L.U (j PUnit.unit))).hom (s.f (j PUnit.unit))) =
    (@id (Γ(X', (L.pull φ).U j ⊓ L'.U i)ˣ) (w.s (j, i))).val *
      resG X' (inf_le_right : (L.pull φ).U j ⊓ L'.U i ≤ L'.U i) (s'.f i)
structure KeyInput (R : Type) [CommRing R] where

  P : PolAV (Sp R)
  dim_pos : 1 ≤ P.g

  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen

  th : LB.Sec P.L
  th_ne : NonzeroOnFibres P.A th

  b : Fin P.g → Tan P.A
  b_basis : IsLieBasis b
variable {R R' : Type} [CommRing R] [CommRing R']
def PolCorr (f : R →+* R') (x : KeyInput R) (x' : KeyInput R') (φ : x'.P.A.left ⟶ x.P.A.left)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) : Prop :=
  IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    (∃ he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A,
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
        (rigPullOf φ (spMap f) he x.P.L x.rig)) ∧
    SecCorr φ w x'.th x.th
def IsBaseChange (f : R →+* R') (x : KeyInput R) (x' : KeyInput R') : Prop :=
  ∃ (φ : x'.P.A.left ⟶ x.P.A.left) (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g),
    PolCorr f x x' φ w ∧ ∀ i : Fin x'.P.g, TanCorr f φ (x'.b i) (x.b (Fin.cast hg i))
def IsBaseChangeDet (f : R →+* R') (x : KeyInput R) (x' : KeyInput R') : Prop :=
  ∃ (φ : x'.P.A.left ⟶ x.P.A.left) (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g),
    PolCorr f x x' φ w ∧
    ∃ (u : Fin x'.P.g → Tan x'.P.A) (M : Matrix (Fin x'.P.g) (Fin x'.P.g) R'),
      (∀ i, TanCorr f φ (u i) (x.b (Fin.cast hg i))) ∧ M.det = 1 ∧ ∀ i, x'.b i = linComb (M i) u
end Input
end GlobalTheory.IndefiniteRowSideFullHecke.PolarizationCorrespondence


