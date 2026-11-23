-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_HodgeTateCharacterSystems
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:04.382055+00:00
-- url     : https://prove2.me/theorems/c32ecd30-4bad-40bd-b9b0-3f8074320e4a
-- title:
--   Hodge Tate Character Systems
-- statement:
--   Definitions and structural lemmas for Hodge Tate Character Systems, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/HodgeTateCharacterSystems.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems
noncomputable section
section Local
variable {O : Type u} [CommRing O] [IsLocalRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G]
def unitSec : Spec (CommRingCat.of O) ⟶ G.left := η[G].left
lemma unitSec_hom : unitSec G ≫ G.hom = 𝟙 _ := Over.w η[G]
def origin : G.left := unitSec G (closedPoint (CommRingCat.of O))
def LocRing : Type u := G.left.presheaf.stalk (origin G)
instance : CommRing (LocRing G) :=
  inferInstanceAs (CommRing (G.left.presheaf.stalk (origin G)))
def fromLoc : Spec (CommRingCat.of (LocRing G)) ⟶ G.left := G.left.fromSpecStalk (origin G)
def strMap : CommRingCat.of O ⟶ CommRingCat.of (LocRing G) :=
  Spec.preimage (fromLoc G ≫ G.hom)
instance : Algebra O (LocRing G) := (strMap G).hom.toAlgebra
def augMap : CommRingCat.of (LocRing G) ⟶ CommRingCat.of O :=
  Scheme.stalkClosedPointTo (unitSec G)
lemma spec_augMap : Spec.map (augMap G) ≫ fromLoc G = unitSec G :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk (unitSec G)
lemma spec_strMap : Spec.map (strMap G) = fromLoc G ≫ G.hom := Spec.map_preimage _
lemma strMap_augMap : strMap G ≫ augMap G = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, spec_strMap, ← Category.assoc, spec_augMap, unitSec_hom, Spec.map_id]
def aug : LocRing G →ₐ[O] O :=
  { (augMap G).hom with
    commutes' := fun r => congrArg (fun φ => φ.hom r) (strMap_augMap G) }
def augIdeal : Ideal (LocRing G) := RingHom.ker (aug G)
def Cotangent : Type u := (augIdeal G).Cotangent
instance : AddCommGroup (Cotangent G) := inferInstanceAs (AddCommGroup (augIdeal G).Cotangent)
instance : Module O (Cotangent G) := inferInstanceAs (Module O (augIdeal G).Cotangent)
abbrev Lie : Type u := Module.Dual O (Cotangent G)
lemma sub_aug_mem (a : LocRing G) : a - algebraMap O (LocRing G) (aug G a) ∈ augIdeal G := by
  rw [augIdeal, RingHom.mem_ker]
  simp
def dAt (a : LocRing G) : Cotangent G :=
  (augIdeal G).toCotangent ⟨a - algebraMap O (LocRing G) (aug G a), sub_aug_mem G a⟩
lemma dAt_add (a b : LocRing G) : dAt G (a + b) = dAt G a + dAt G b := by
  unfold dAt
  have e : (⟨a + b - algebraMap O (LocRing G) (aug G (a + b)), sub_aug_mem G (a + b)⟩ : augIdeal G) =
      ⟨a - algebraMap O (LocRing G) (aug G a), sub_aug_mem G a⟩ +
        ⟨b - algebraMap O (LocRing G) (aug G b), sub_aug_mem G b⟩ := by
    apply Subtype.ext
    simp only [map_add, Submodule.coe_add]
    ring
  rw [e]
  exact map_add _ _ _
lemma dAt_algebraMap (r : O) : dAt G (algebraMap O (LocRing G) r) = 0 := by
  unfold dAt
  have e : (⟨algebraMap O (LocRing G) r - algebraMap O (LocRing G) (aug G (algebraMap O (LocRing G) r)),
      sub_aug_mem G _⟩ : augIdeal G) = 0 := by
    apply Subtype.ext
    simp
  rw [e]
  exact map_zero _
lemma dAt_mul (a b : LocRing G) : dAt G (a * b) = aug G a • dAt G b + aug G b • dAt G a := by
  unfold dAt
  have ha := sub_aug_mem G a
  have hb := sub_aug_mem G b
  have e : (⟨a * b - algebraMap O (LocRing G) (aug G (a * b)), sub_aug_mem G (a * b)⟩ : augIdeal G) =
      algebraMap O (LocRing G) (aug G a) • ⟨b - algebraMap O (LocRing G) (aug G b), hb⟩ +
        algebraMap O (LocRing G) (aug G b) • ⟨a - algebraMap O (LocRing G) (aug G a), ha⟩ +
          ⟨(a - algebraMap O (LocRing G) (aug G a)) * (b - algebraMap O (LocRing G) (aug G b)),
            Ideal.mul_mem_left _ _ hb⟩ := by
    apply Subtype.ext
    simp only [map_mul, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
    ring
  have hz : (augIdeal G).toCotangent
      ⟨(a - algebraMap O (LocRing G) (aug G a)) * (b - algebraMap O (LocRing G) (aug G b)),
        Ideal.mul_mem_left _ _ hb⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul ha hb
  rw [e]
  show (augIdeal G).toCotangent (_ + _ + _) = aug G a • (augIdeal G).toCotangent _ + aug G b • (augIdeal G).toCotangent _
  rw [map_add, map_add, hz, add_zero, map_smul, map_smul, algebraMap_smul, algebraMap_smul]
variable {G} in

def tangentAlg {R : Type u} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R) :
    LocRing G →ₐ[O] DualNumber R where
  toFun a := TrivSqZeroExt.inl (algebraMap O R (aug G a)) + TrivSqZeroExt.inr (v (dAt G a))
  map_one' := by
    have := dAt_algebraMap G 1
    rw [map_one] at this
    simp [this]
  map_mul' a b := by
    ext
    · simp
    · simp [dAt_mul, ← Algebra.smul_def, add_comm]
      simp [Algebra.smul_def, mul_comm, add_comm]
  map_zero' := by
    have := dAt_algebraMap G 0
    rw [map_zero] at this
    simp [this]
  map_add' a b := by
    ext
    · simp
    · simp [dAt_add]
  commutes' r := by
    simp [dAt_algebraMap, TrivSqZeroExt.algebraMap_eq_inl']
end Local
section Points
variable (O : Type u) [CommRing O]
def specOver (R : Type u) [CommRing R] [Algebra O R] : Over (Spec (CommRingCat.of O)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap O R)))
variable {O} in

def readFn {R : Type u} [CommRing R] [Algebra O R] (s : Γ((specOver O R).left, ⊤)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom s
end Points
section Tangent
variable {O : Type u} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
def tangentPt {R : Type u} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R) :
    specOver O (DualNumber R) ⟶ G :=
  Over.homMk (Spec.map (CommRingCat.ofHom (tangentAlg v).toRingHom) ≫ fromLoc G) (by
    change (Spec.map _ ≫ fromLoc G) ≫ G.hom = Spec.map _
    rw [Category.assoc, ← spec_strMap, ← Spec.map_comp]
    congr 1
    ext r : 2
    exact (tangentAlg v).commutes r)
end Tangent
section Characters
variable {S : Scheme.{u}} {G : Over S} [GrpObj G]
lemma comp_mulN {T : Over S} (x : T ⟶ G) (N : ℕ) : x ≫ mulN G N = x ^ N := by
  induction N with
  | zero =>
    rw [mulN.eq_1, pow_zero, Hom.one_def, ← Category.assoc, toUnit_unique (x ≫ toUnit G) (toUnit T)]
  | succ n ih =>
    rw [mulN.eq_2, ← Category.assoc, comp_lift, ih, Category.comp_id, pow_succ, Hom.mul_def]
def torsionLift {N : ℕ} {T : Over S} (x : T ⟶ G) (hx : x ^ N = 1) : T ⟶ torsion G N :=
  Limits.pullback.lift x (toUnit T) (by rw [comp_mulN, hx, Hom.one_def])
lemma torsionLift_ι {N : ℕ} {T : Over S} (x : T ⟶ G) (hx : x ^ N = 1) :
    torsionLift x hx ≫ torsion.ι G N = x :=
  Limits.pullback.lift_fst _ _ _
lemma torsion_ι_pow (N : ℕ) : torsion.ι G N ^ N = 1 := by
  rw [← comp_mulN]
  change Limits.pullback.fst (mulN G N) η ≫ mulN G N = 1
  rw [Limits.pullback.condition, Hom.one_def, toUnit_unique (Limits.pullback.snd _ _) (toUnit _)]
variable (G) in

def torsionIncl (p n : ℕ) : torsion G (p ^ n) ⟶ torsion G (p ^ (n + 1)) :=
  torsionLift (torsion.ι G (p ^ n)) (by rw [pow_succ, pow_mul, torsion_ι_pow, one_pow])
variable [IsCommMonObj G] (G)
structure TorsionChar (N : ℕ) where

  hom : torsion G N ⟶ Gm S
  map_mul : ∀ (T : Over S) (x y : T ⟶ G) (hx : x ^ N = 1) (hy : y ^ N = 1),
    torsionLift (N := N) (x * y) (by rw [mul_pow, hx, hy, _root_.one_mul]) ≫ hom =
      (torsionLift x hx ≫ hom) * (torsionLift y hy ≫ hom)
structure CharSystem (p : ℕ) where

  char : ∀ n : ℕ, TorsionChar G (p ^ n)
  compat : ∀ n : ℕ, torsionIncl G p n ≫ (char (n + 1)).hom = (char n).hom
variable {G}
def CharSystem.ofCharacter (p : ℕ) (c : characters G) : CharSystem G p where
  char n :=
    { hom := torsion.ι G (p ^ n) ≫ c.1
      map_mul := fun T x y hx hy => by
        haveI := c.2
        simp only [← Category.assoc, torsionLift_ι]
        exact MonObj.mul_comp x y c.1 }
  compat n := by rw [← Category.assoc, torsionIncl, torsionLift_ι]
def CharSystem.tautological (S : Scheme.{u}) [IsCommMonObj (Gm S)] (p : ℕ) :
    CharSystem (Gm S) p :=
  CharSystem.ofCharacter p ⟨𝟙 _, inferInstance⟩
def gmValue {T : Over S} (z : T ⟶ Gm S) : Γ(T.left, ⊤) :=
  z.left.appTop.hom (charUnit S (ULift.{u} ℤ) (ULift.up 1)).val
end Characters
section HodgeTate
variable {O : Type u} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))}
  [GrpObj G] [IsCommMonObj G]
def TorsionChar.IsDlog {N : ℕ} (χ : TorsionChar G N) (f : Cotangent G) : Prop :=
  ∀ v : Cotangent G →ₗ[O] (O ⧸ Ideal.span {(N : O)}),
    ∃ h : tangentPt v ^ N = 1,
      readFn (gmValue (torsionLift (tangentPt v) h ≫ χ.hom)) = 1 + TrivSqZeroExt.inr (v f)
def CharSystem.IsHT {p : ℕ} (t : CharSystem G p) (f : Cotangent G) : Prop :=
  ∀ n : ℕ, (t.char n).IsDlog f
variable (G)
def htSpan (p : ℕ) : Submodule O (Cotangent G) :=
  Submodule.span O {f | ∃ t : CharSystem G p, t.IsHT f}
def HTInclusionAt (p : ℕ) (ζ : O) : Prop :=
  ∀ f : Cotangent G, (ζ - 1) • f ∈ htSpan G p
end HodgeTate
section Valued
variable {C : Type u} [Field C]
def IsPadicCompleteSetting (O : ValuationSubring C) (p : ℕ) : Prop :=
  p.Prime ∧ IsAlgClosed C ∧ CharZero C ∧ (p : O) ∈ maximalIdeal O ∧
    IsAdicComplete (Ideal.span {(p : O)}) O
def HodgeTateInclusion (O : ValuationSubring C) (p : ℕ) (G : Over (Spec (CommRingCat.of O)))
    [GrpObj G] [IsCommMonObj G] : Prop :=
  (∃ ζ : O, IsPrimitiveRoot ζ p) ∧ ∀ ζ : O, IsPrimitiveRoot ζ p → HTInclusionAt G p ζ
end Valued
end
end GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems


