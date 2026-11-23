-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:59.340869+00:00
-- url     : https://prove2.me/theorems/920cc8e0-6b68-4ab8-92a9-f227309de2f8
-- title:
--   Comm Alg Functor Coboundary Zero Mem Cocycles One
-- statement:
--   Definitions and structural lemmas for Comm Alg Functor Coboundary Zero Mem Cocycles One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean

import Mathlib
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
open CategoryTheory
namespace GlobalTheory.CatCoh
universe v u v' u' v'' u''
section Complex
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
abbrev mp {T T' : C} (φ : T ⟶ T') : F.obj T →ₐ[R] F.obj T' := (F.map φ).hom
theorem mp_comp {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (b : F.obj T) :
    mp F (φ ≫ ψ) b = mp F ψ (mp F φ b) := by
  simp [mp]
theorem mp_id (T : C) (b : F.obj T) : mp F (𝟙 T) b = b := by
  simp [mp]
abbrev C0 := ∀ T : C, F.obj T
abbrev C1 := ∀ (T T' : C) (_ : T ⟶ T'), F.obj T'
abbrev C2 := ∀ (T T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T''
def d0 : C0 F →ₗ[R] C1 F where
  toFun g T T' φ := g T' - mp F φ (g T)
  map_add' g g' := by funext T T' φ; simp only [Pi.add_apply, map_add]; ring
  map_smul' r g := by funext T T' φ; simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply]
def d1 : C1 F →ₗ[R] C2 F where
  toFun f T T' T'' φ ψ := mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ
  map_add' g g' := by funext T T' T'' φ ψ; simp only [Pi.add_apply, map_add]; ring
  map_smul' r g := by
    funext T T' T'' φ ψ; simp only [Pi.smul_apply, map_smul, smul_sub, smul_add, RingHom.id_apply]
theorem amitsur_d0_apply (g : C0 F) {T T' : C} (φ : T ⟶ T') : d0 F g T T' φ = g T' - mp F φ (g T) := rfl
theorem d1_apply (f : C1 F) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    d1 F f T T' T'' φ ψ = mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ := rfl
def Z1 : Submodule R (C1 F) where
  carrier := {f | ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
    f T T'' (φ ≫ ψ) = mp F ψ (f T T' φ) + f T' T'' ψ}
  add_mem' {f g} hf hg T T' T'' φ ψ := by
    simp only [Pi.add_apply, map_add, hf φ ψ, hg φ ψ]; ring
  zero_mem' T T' T'' φ ψ := by simp
  smul_mem' r f hf T T' T'' φ ψ := by
    simp only [Pi.smul_apply, map_smul, hf φ ψ, smul_add]
def Z2 : Submodule R (C2 F) where
  carrier := {z | ∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''),
    mp F χ (z T T' T'' φ ψ) + z T T'' T''' (φ ≫ ψ) χ = z T T' T''' φ (ψ ≫ χ) + z T' T'' T''' ψ χ}
  add_mem' {f g} hf hg T T' T'' T''' φ ψ χ := by
    simp only [Pi.add_apply, map_add]; linear_combination hf φ ψ χ + hg φ ψ χ
  zero_mem' T T' T'' T''' φ ψ χ := by simp
  smul_mem' r f hf T T' T'' T''' φ ψ χ := by
    simp only [Pi.smul_apply, map_smul, ← smul_add, hf φ ψ χ]
variable {F}
theorem Z1.comp (f : Z1 F) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    f.1 T T'' (φ ≫ ψ) = mp F ψ (f.1 T T' φ) + f.1 T' T'' ψ := f.2 φ ψ
theorem Z1.id (f : Z1 F) (T : C) : f.1 T T (𝟙 T) = 0 := by
  have h := Z1.comp f (𝟙 T) (𝟙 T)
  rw [Category.id_comp, mp_id] at h
  linear_combination -h
variable (F)
theorem commAlgFunctorCoboundaryZero_mem_cocyclesOne (g : C0 F) : d0 F g ∈ Z1 F := by
  intro T T' T'' φ ψ
  simp only [amitsur_d0_apply, mp_comp, map_sub]
  ring
theorem differential_one_mem_scaled_lattice (f : C1 F) : d1 F f ∈ Z2 F := by
  intro T T' T'' T''' φ ψ χ
  simp only [d1_apply, map_add, map_sub, mp_comp, Category.assoc]
  ring
def H1 : Type _ := Z1 F ⧸ LinearMap.range ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F))
def H2 : Type _ := Z2 F ⧸ LinearMap.range ((d1 F).codRestrict (Z2 F) (differential_one_mem_scaled_lattice F))
instance : AddCommGroup (H1 F) := inferInstanceAs (AddCommGroup (_ ⧸ LinearMap.range _))
instance : Module R (H1 F) := inferInstanceAs (Module R (_ ⧸ LinearMap.range _))
instance : AddCommGroup (H2 F) := inferInstanceAs (AddCommGroup (_ ⧸ LinearMap.range _))
instance : Module R (H2 F) := inferInstanceAs (Module R (_ ⧸ LinearMap.range _))
def H1.mk : Z1 F →ₗ[R] H1 F := Submodule.mkQ _
def H2.mk : Z2 F →ₗ[R] H2 F := Submodule.mkQ _
variable {F}
theorem H1.mk_eq_zero {f : Z1 F} : H1.mk F f = 0 ↔ ∃ g, d0 F g = f.1 := by
  change Submodule.Quotient.mk f = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
theorem H2.mk_eq_zero {z : Z2 F} : H2.mk F z = 0 ↔ ∃ f, d1 F f = z.1 := by
  change Submodule.Quotient.mk z = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, congrArg Subtype.val hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, Subtype.ext hf⟩
variable (F)
def cupZ : Z1 F →ₗ[R] Z1 F →ₗ[R] Z2 F :=
  LinearMap.mk₂ R
    (fun a b ↦ ⟨fun T T' T'' φ ψ ↦ mp F ψ (a.1 T T' φ) * b.1 T' T'' ψ, fun T T' T'' T''' φ ψ χ ↦ by
      simp only [Z1.comp a, Z1.comp b, map_mul, map_add, mp_comp]; ring⟩)
    (fun a a' b ↦ Subtype.ext (by funext T T' T'' φ ψ; simp [add_mul]))
    (fun r a b ↦ Subtype.ext (by funext T T' T'' φ ψ; simp))
    (fun a b b' ↦ Subtype.ext (by funext T T' T'' φ ψ; simp [mul_add]))
    (fun r a b ↦ Subtype.ext (by funext T T' T'' φ ψ; simp))
theorem cupZ_apply (a b : Z1 F) {T T' T'' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (cupZ F a b).1 T T' T'' φ ψ = mp F ψ (a.1 T T' φ) * b.1 T' T'' ψ := rfl
def cup : H1 F →ₗ[R] H1 F →ₗ[R] H2 F :=
  LinearMap.liftQ₂ _ _ ((cupZ F).compr₂ (H2.mk F))
    (by
      rintro _ ⟨g, rfl⟩
      ext b
      refine H2.mk_eq_zero.2 ⟨fun T T' φ ↦ mp F φ (g T) * b.1 T T' φ, ?_⟩
      funext T T' T'' φ ψ
      simp only [d1_apply, cupZ_apply, LinearMap.codRestrict_apply, amitsur_d0_apply, Z1.comp b, map_mul,
        map_sub, mp_comp]
      ring)
    (by
      rintro _ ⟨g, rfl⟩
      ext a
      refine H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * g T'), ?_⟩
      funext T T' T'' φ ψ
      simp only [d1_apply, cupZ_apply, LinearMap.codRestrict_apply, amitsur_d0_apply, Z1.comp a, map_mul,
        map_neg]
      ring)
end Complex
section Pull
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
structure CoefMap (σ : R →+* R') (F : C ⥤ CommAlgCat.{0} R) (F' : C' ⥤ CommAlgCat.{0} R') where

  G : C' ⥤ C

  α : ∀ T : C', F.obj (G.obj T) →+* F'.obj T
  naturality : ∀ {T T' : C'} (φ : T ⟶ T') (b : F.obj (G.obj T)),
    α T' (mp F (G.map φ) b) = mp F' φ (α T b)
  smul : ∀ (T : C') (r : R) (b : F.obj (G.obj T)), α T (r • b) = σ r • α T b
namespace CoefMap
variable {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''}
def id (F : C ⥤ CommAlgCat.{0} R) : CoefMap (RingHom.id R) F F where
  G := 𝟭 C
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl
def comp (m : CoefMap σ F F') (n : CoefMap τ F' F'') : CoefMap (τ.comp σ) F F'' where
  G := n.G ⋙ m.G
  α T := (n.α T).comp (m.α (n.G.obj T))
  naturality φ b := (congrArg (n.α _) (m.naturality (n.G.map φ) b)).trans (n.naturality φ _)
  smul T r b := (congrArg (n.α _) (m.smul _ r b)).trans (n.smul _ _ _)
def restrict (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) : CoefMap (RingHom.id R) F (G ⋙ F) where
  G := G
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl
variable (m : CoefMap σ F F')
def pullbackOneCocycle : Z1 F →ₛₗ[σ] Z1 F' where
  toFun f := ⟨fun T T' φ ↦ m.α T' (f.1 _ _ (m.G.map φ)), fun T T' T'' φ ψ ↦ by
    simp only [Functor.map_comp, Z1.comp f, map_add, m.naturality]⟩
  map_add' f g := Subtype.ext (by funext T T' φ; simp)
  map_smul' r f := Subtype.ext (by funext T T' φ; simp [m.smul])
def pullbackTwoCocycle : Z2 F →ₛₗ[σ] Z2 F' where
  toFun z := ⟨fun T T' T'' φ ψ ↦ m.α T'' (z.1 _ _ _ (m.G.map φ) (m.G.map ψ)),
    fun T T' T'' T''' φ ψ χ ↦ by
      simp only [Functor.map_comp, ← map_add, ← m.naturality, z.2 (m.G.map φ) (m.G.map ψ) (m.G.map χ)]⟩
  map_add' f g := Subtype.ext (by funext T T' T'' φ ψ; simp)
  map_smul' r f := Subtype.ext (by funext T T' T'' φ ψ; simp [m.smul])
theorem pullCocycleOne_apply (f : Z1 F) {T T' : C'} (φ : T ⟶ T') :
    (m.pullbackOneCocycle f).1 T T' φ = m.α T' (f.1 _ _ (m.G.map φ)) := rfl
theorem pullCocycleTwo_apply (z : Z2 F) {T T' T'' : C'} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (m.pullbackTwoCocycle z).1 T T' T'' φ ψ = m.α T'' (z.1 _ _ _ (m.G.map φ) (m.G.map ψ)) := rfl
def pull1 : H1 F →ₛₗ[σ] H1 F' :=
  Submodule.mapQ _ _ m.pullbackOneCocycle (by
    rintro _ ⟨g, rfl⟩
    refine ⟨fun T ↦ m.α T (g _), Subtype.ext ?_⟩
    funext T T' φ
    simp only [LinearMap.codRestrict_apply, pullCocycleOne_apply, amitsur_d0_apply, map_sub, m.naturality])
def pull2 : H2 F →ₛₗ[σ] H2 F' :=
  Submodule.mapQ _ _ m.pullbackTwoCocycle (by
    rintro _ ⟨g, rfl⟩
    refine ⟨fun T T' φ ↦ m.α T' (g _ _ (m.G.map φ)), Subtype.ext ?_⟩
    funext T T' T'' φ ψ
    simp only [LinearMap.codRestrict_apply, pullCocycleTwo_apply, d1_apply, map_sub, map_add, m.naturality,
      Functor.map_comp])
end CoefMap
end Pull
end GlobalTheory.CatCoh


