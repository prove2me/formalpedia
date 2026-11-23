-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_KerScheme
-- name    : Development_AbelianVarietyTheory_Definitions_ModuliSpaces_KerScheme
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:40.252121+00:00
-- url     : https://prove2.me/theorems/bdb9a2d3-2ba9-41c0-8913-be57c7ab1825
-- title:
--   Ker Scheme
-- statement:
--   Definitions and structural lemmas for Ker Scheme, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/KerScheme.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
namespace GlobalTheory.HkFam
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
def admitted (l : Level H) (𝔓 : Ideal (𝓞 E)) (p : ℕ) : Prop :=
  𝔓.IsMaximal ∧ 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ 𝔓 ∧ ¬ p ∣ l.M'
abbrev Ob (D : Datum H) (l : Level H) {S : Scheme.{0}} (s : S ⟶ Sp (KA l)) := Obj D l (baseKA l) s
variable {S : Scheme.{0}}
def HeckeSet (D : Datum H) (t : SAB H S) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (K : Set t.G.left) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ C : Subgroup (Over.mk x ⟶ t.G),
    (∀ z, z ∈ C ↔ Set.range z.left ⊆ K) ∧ t.HeckeKer (Over.mk x) D 𝔓 p i C
def KerSet {G G' : Over S} [GrpObj G'] (ψ : G ⟶ G') (K : Set G.left) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ G), z ≫ ψ = 1 ↔ Set.range z.left ⊆ K
def EtSet (G : Over S) (K : Set G.left) : Prop :=
  ∃ (C : Over S) (j : C ⟶ G), IsFinite C.hom ∧ Etale C.hom ∧ IsClosedImmersion j.left ∧ Set.range j.left = K
def Lists {G : Over S} [GrpObj G] (N : ℕ) {n : ℕ} (σ : Fin n → (𝟙_ (Over S) ⟶ G)) (K : Set G.left) : Prop :=
  (∀ j, σ j ^ N = 1) ∧ K = (⋃ j, Set.range (σ j).left) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), Function.Injective fun j => x ≫ (σ j).left
def IsIsogT (t t' : SAB H S) (p : ℕ) (ψ : t.G ⟶ t'.G) : Prop :=
  IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧
    LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)
variable {s : S ⟶ Sp (KA l)}
def IsIsog (o o' : Ob D l s) (p : ℕ) (ψ : o.t.G ⟶ o'.t.G) : Prop :=
  IsIsogT o.t o'.t p ψ ∧ ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a, o.eta (p' • a) ≫ ψ = o'.eta a ∧ o.etaA (p' • a) ≫ ψ = o'.etaA a
def IsHecke (o o' : Ob D l s) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (ψ : o.t.G ⟶ o'.t.G) : Prop :=
  IsIsog o o' p ψ ∧ ∃ K, KerSet ψ K ∧ HeckeSet D o.t 𝔓 p i K
def HasQuot (o : Ob D l s) (p : ℕ) (K : Set o.t.G.left) : Prop :=
  ∃ (o' : Ob D l s) (ψ : o.t.G ⟶ o'.t.G), IsIsog o o' p ψ ∧ KerSet ψ K
structure KerScheme (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) where

  Hk : Scheme.{0}

  π₁ : Hk ⟶ Xo.X
  fin₁ : IsFinite π₁
  et₁ : Etale π₁

  o₁ : Ob D l (π₁ ≫ Xo.s)

  m₁ : ObjMap o₁ Xo.univ π₁

  K : Set o₁.t.G.left
  hecke : HeckeSet D o₁.t 𝔓 p i K
  et : EtSet o₁.t.G K
  rep : ∀ (S : Scheme.{0}) (s : S ⟶ Sp (KA l)), IsReduced S → ∀ (o : Ob D l s) (K' : Set o.t.G.left), EtSet o.t.G K' →
    HeckeSet D o.t 𝔓 p i K' → ∃! h : S ⟶ Hk, h ≫ π₁ ≫ Xo.s = s ∧ ∃ n : ObjMap o o₁ h, K' = n.toSABMap.φ ⁻¹' K
structure Corr (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) extends KerScheme Xo 𝔓 p i where

  π₂ : Hk ⟶ Xo.X
  base₂ : π₂ ≫ Xo.s = π₁ ≫ Xo.s

  o₂ : Ob D l (π₁ ≫ Xo.s)

  m₂ : ObjMap o₂ Xo.univ π₂

  ψ : o₁.t.G ⟶ o₂.t.G
  isog : IsIsog o₁ o₂ p ψ
  ker : KerSet ψ K
  univ : ∀ (S : Scheme.{0}) (s : S ⟶ Sp (KA l)), IsReduced S → ∀ (o o' : Ob D l s) (ψ' : o.t.G ⟶ o'.t.G), IsHecke o o' 𝔓 p i ψ' →
    ∃! h : S ⟶ Hk, h ≫ π₁ ≫ Xo.s = s ∧ ∃ (n₁ : ObjMap o o₁ h) (n₂ : ObjMap o' o₂ h),
      ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left
def PointQuot (Xo : Moduli D l) (p : ℕ) {k : Type} [Field k] (y y'' : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)) : Prop :=
  y'' ≫ Xo.s = y ≫ Xo.s ∧
    ∃ (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
      (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G)),
      ψ ≫ pullback.snd _ _ = pullback.snd _ _ ∧ (∀ x, fibPt _ x ≫ ψ = fibPt _ (ψp x)) ∧
      (∀ a x, ψp (x ≫ Xo.univ.t.act.act a) = ψp x ≫ Xo.univ.t.act.act a) ∧
      Function.Surjective ψp ∧ ψp.ker = C ∧
      (∀ (n : ℕ) (x x' : Over.mk y ⟶ Xo.univ.t.G) (c : kˣ), n.Coprime p →
        Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn c) →
        Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n (ψp x) (ψp x') (unitOn (c ^ (p ^ 2)))) ∧
      ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a,
        ψp (toUnit _ ≫ Xo.univ.eta (p' • a)) = toUnit _ ≫ Xo.univ.eta a ∧
        ψp (toUnit _ ≫ Xo.univ.etaA (p' • a)) = toUnit _ ≫ Xo.univ.etaA a
def KerScheme.Carries {Xo : Moduli D l} {𝔓 : Ideal (𝓞 E)} {p i : ℕ} (Z : KerScheme Xo 𝔓 p i) {k : Type} [Field k]
    (z : Sp k ⟶ Z.Hk) (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)) : Prop :=
  z ≫ Z.π₁ = y ∧ ∀ (u : Over.mk z ⟶ Z.o₁.t.G) (v : Over.mk y ⟶ Xo.univ.t.G), v.left = u.left ≫ Z.m₁.toSABMap.φ →
    (Set.range u.left ⊆ Z.K ↔ v ∈ C)
example : ToroidalHeckeCompatibility (H := H) (D := D) ↔ ∀ (l : Level H) (Xo : Moduli D l) (P : Ideal (𝓞 E)) (p i : ℕ),
    admitted l P p → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)),
      Xo.univ.t.HeckeKer (Over.mk y) D P p i C → ∃! y'', PointQuot Xo p y y'' C :=
  ⟨fun h l Xo P p i ⟨a, b, c, d, e⟩ => h l Xo P p i a b c d e,
    fun h l Xo P p i a b c d e => h l Xo P p i ⟨a, b, c, d, e⟩⟩
example (G : Over S) [GrpObj G] [IsSeparated G.hom] : EtSet G (Set.range (η[G] : 𝟙_ (Over S) ⟶ G).left) := by
  have hw : (η[G] : 𝟙_ (Over S) ⟶ G).left ≫ G.hom = 𝟙 _ := Over.w _
  have : IsClosedImmersion ((η[G] : 𝟙_ (Over S) ⟶ G).left ≫ G.hom) := by rw [hw]; infer_instance
  exact ⟨𝟙_ (Over S), η[G], inferInstanceAs (IsFinite (𝟙 S)), inferInstanceAs (Etale (𝟙 S)),
    IsClosedImmersion.of_comp _ G.hom, rfl⟩
example (P : Ideal (𝓞 E)) (h : 2 ∣ l.A) : ¬ admitted l P 2 := fun hA => hA.2.2.2.2 (h.trans (Nat.dvd_lcm_right _ _))
end GlobalTheory.HkFam
end


