-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFrobGBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:22.138845+00:00
-- url     : https://prove2.me/theorems/ad318850-06db-4977-bc72-5467aaf8411e
-- title:
--   Exists Frob GBase Change
-- statement:
--   Definitions and structural lemmas for Exists Frob GBase Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFrobGBaseChange.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.FrobField
def powHom (R : Type) [CommRing R] (p r : ℕ) (hp : p.Prime) (h : (p : R) = 0) : R →+* R where
  toFun x := x ^ p ^ r
  map_one' := one_pow _
  map_mul' x y := mul_pow _ _ _
  map_zero' := zero_pow (pow_ne_zero _ hp.ne_zero)
  map_add' x y := by
    obtain ⟨c, hc⟩ := exists_add_pow_prime_pow_eq hp x y r
    rw [hc, h]; simp
theorem cast_zero {X : Scheme.{0}} {p : ℕ} (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens) : (p : Γ(X, U)) = 0 := by
  have := congrArg (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom h
  rwa [map_natCast, map_zero] at this
theorem cast_zero_of_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {p : ℕ} (h : (p : Γ(Y, ⊤)) = 0) :
    (p : Γ(X, ⊤)) = 0 := by
  have := congrArg f.appTop.hom h
  rwa [map_natCast, map_zero] at this
def absPre (X : Scheme.{0}) (p r : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) :
    X.toPresheafedSpace.Hom X.toPresheafedSpace where
  base := 𝟙 _
  c := { app := fun U => CommRingCat.ofHom (powHom (X.presheaf.obj U) p r hp (cast_zero h U.unop))
         naturality := fun U V i => by
           ext x
           exact (map_pow (X.presheaf.map i).hom x _).symm }
def absFrob (X : Scheme.{0}) (p r : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) : X ⟶ X :=
  ⟨⟨absPre X p r hp h, fun x => ⟨fun a ha => by
    obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq (x := x) a
    have e := PresheafedSpace.stalkMap_germ_apply (absPre X p r hp h) U x hU s
    erw [e] at ha
    have e2 : (X.presheaf.germ U x hU).hom (s ^ p ^ r) = (X.presheaf.germ U x hU).hom s ^ p ^ r :=
      map_pow _ _ _
    have ha' : IsUnit ((X.presheaf.germ U x hU).hom (s ^ p ^ r)) := ha
    rw [e2] at ha'
    exact (isUnit_pow_iff (pow_ne_zero _ hp.ne_zero)).1 ha'⟩⟩⟩
theorem absFrob_nat {X Y : Scheme.{0}} (f : X ⟶ Y) (p r : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) : absFrob X p r hp hX ≫ f = f ≫ absFrob Y p r hp hY := by
  refine Scheme.Hom.ext rfl fun U => ?_
  ext x
  have e : ∀ (V : X.Opens) (i : Opposite.op V ⟶ Opposite.op V) (y : Γ(X, V)),
      (X.presheaf.map i).hom y = y := by
    intro V i y
    rw [Subsingleton.elim i (𝟙 _), CategoryTheory.Functor.map_id]; rfl
  exact (e (f ⁻¹ᵁ U) _ _).trans (map_pow (f.app U).hom x _).symm
theorem absFrob_spec (k : Type) [CommRing k] (p r : ℕ) (hp : p.Prime) (h : (p : Γ(Sp k, ⊤)) = 0)
    (τ : k →+* k) (hτ : ∀ c, τ c = c ^ p ^ r) : absFrob (Sp k) p r hp h = spMap τ := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv]
  rw [← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom τ)]
  ext c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, hτ, map_pow]
  rfl
def Q {X : Scheme.{0}} (φ : X ⟶ X) (n : ℕ) (U : X.Opens) (f : Γ(X, U)) : Prop :=
  ∃ h : U = φ ⁻¹ᵁ U, (φ.appLE U U h.le).hom f = f ^ n
theorem Q.comp {X : Scheme.{0}} {φ ψ : X ⟶ X} {n n' : ℕ} {U : X.Opens} {f : Γ(X, U)}
    (a : Q φ n U f) (b : Q ψ n' U f) : Q (φ ≫ ψ) (n * n') U f := by
  obtain ⟨h, e⟩ := a
  obtain ⟨h', e'⟩ := b
  refine ⟨by rw [Scheme.Hom.comp_preimage, ← h', ← h], ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE φ ψ U U U h'.le h.le, CommRingCat.hom_comp, RingHom.comp_apply, e',
    map_pow, e, pow_mul]
theorem Q.id {X : Scheme.{0}} (U : X.Opens) (f : Γ(X, U)) : Q (𝟙 X) 1 U f := by
  refine ⟨rfl, ?_⟩
  simp [Scheme.Hom.appLE]
  exact GlobalTheory.AbLaw.rs_self (X := X) le_rfl f
theorem Q.pow {X : Scheme.{0}} {F : End X} {q m : ℕ} {U : X.Opens} {f : Γ(X, U)}
    (a : Q (show X ⟶ X from F ^ m) (q ^ m) U f) (j : ℕ) :
    Q (show X ⟶ X from F ^ (m * j)) (q ^ (m * j)) U f := by
  induction j with
  | zero => simpa using Q.id U f
  | succ j ih =>
    have := a.comp ih
    rw [Nat.mul_succ, pow_add, pow_add, mul_comm (q ^ (m * j))]
    exact this
def Good {X : Scheme.{0}} (F : End X) (q : ℕ) (U : X.Opens) (f : Γ(X, U)) : Prop :=
  ∃ m, 1 ≤ m ∧ Q (show X ⟶ X from F ^ m) (q ^ m) U f
theorem Good.two {X : Scheme.{0}} {F : End X} {q : ℕ} {U V : X.Opens} {f : Γ(X, U)} {g : Γ(X, V)}
    (a : Good F q U f) (b : Good F q V g) :
    ∃ m, 1 ≤ m ∧ Q (show X ⟶ X from F ^ m) (q ^ m) U f ∧ Q (show X ⟶ X from F ^ m) (q ^ m) V g := by
  obtain ⟨m, hm, a⟩ := a
  obtain ⟨n, hn, b⟩ := b
  refine ⟨m * n, Nat.mul_pos hm hn, a.pow n, ?_⟩
  rw [mul_comm]; exact b.pow m
def goodSubring {X : Scheme.{0}} (F : End X) (p r : ℕ) (hp : p.Prime) (U : X.Opens)
    (hc : (p : Γ(X, U)) = 0) (h : U = (show X ⟶ X from F) ⁻¹ᵁ U) : Subring Γ(X, U) where
  carrier := {f | Good F (p ^ r) U f}
  mul_mem' := fun a b => by
    obtain ⟨m, hm, ⟨h, e⟩, ⟨h', e'⟩⟩ := Good.two a b
    exact ⟨m, hm, h, by rw [map_mul, e, e', mul_pow]⟩
  add_mem' := fun {x y} a b => by
    obtain ⟨m, hm, ⟨h, e⟩, ⟨h', e'⟩⟩ := Good.two a b
    refine ⟨m, hm, h, ?_⟩
    rw [map_add, e, e', ← pow_mul]
    exact (map_add (powHom _ p (r * m) hp hc) x y).symm
  one_mem' := ⟨1, le_rfl, by rw [pow_one]; exact h, by rw [map_one, one_pow]⟩
  zero_mem' := ⟨1, le_rfl, by rw [pow_one]; exact h, by
    rw [map_zero, zero_pow (pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))]⟩
  neg_mem' := fun {x} a => by
    obtain ⟨m, hm, h, e⟩ := a
    refine ⟨m, hm, h, ?_⟩
    rw [map_neg, e, ← pow_mul]
    exact (map_neg (powHom _ p (r * m) hp hc) x).symm
theorem cast_zero_sp (k : Type) [CommRing k] {p : ℕ} (h : (p : k) = 0) : (p : Γ(Sp k, ⊤)) = 0 := by
  have := congrArg (Scheme.ΓSpecIso (.of k)).inv.hom h
  rwa [map_natCast, map_zero] at this
section Rel
variable {W k : Type} [CommRing W] [CommRing k] (ρ : W →+* k) (p r : ℕ) (hp : p.Prime) (hk : (p : k) = 0)
  (hρ : ∀ w, ρ w ^ (p ^ r) = ρ w)
include hρ in
theorem absFrob_comp_spMap : absFrob (Sp k) p r hp (cast_zero_sp k hk) ≫ spMap ρ = spMap ρ := by
  rw [absFrob_spec k p r hp _ (powHom k p r hp hk) (fun _ => rfl), ← Spec.map_comp]
  congr 1
  ext w
  exact hρ w
def relLeft (G : Over (Sp W)) : pullback G.hom (spMap ρ) ⟶ pullback G.hom (spMap ρ) :=
  pullback.lift (absFrob _ p r hp (cast_zero_of_hom (pullback.snd _ _) (cast_zero_sp k hk)) ≫ pullback.fst _ _)
    (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        absFrob_nat _ p r hp _ (cast_zero_sp k hk), Category.assoc, absFrob_comp_spMap ρ p r hp hk hρ])
def relNat : Over.pullback (spMap ρ) ⟶ Over.pullback (spMap ρ) where
  app G := Over.homMk (relLeft ρ p r hp hk hρ G) (pullback.lift_snd _ _ _)
  naturality G G' φ := by
    ext1
    apply pullback.hom_ext
    · simp only [Over.comp_left, Over.homMk_left, relLeft, Category.assoc, pullback.lift_fst,
        Over.pullback_map_left]
      erw [pullback.lift_fst_assoc]
      rw [← Category.assoc]
      erw [← absFrob_nat (X := pullback G.hom (spMap ρ)) (Y := pullback G'.hom (spMap ρ)) _ p r hp
        (cast_zero_of_hom (pullback.snd G.hom (spMap ρ)) (cast_zero_sp k hk))]
      erw [Category.assoc, pullback.lift_fst, Category.assoc]
    · simp only [Over.comp_left, Over.homMk_left, relLeft, Category.assoc, Over.pullback_map_left]
      erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
end Rel
end GlobalTheory.SS.FrobField
namespace GlobalTheory.SS
open FrobField
end GlobalTheory.SS
end


