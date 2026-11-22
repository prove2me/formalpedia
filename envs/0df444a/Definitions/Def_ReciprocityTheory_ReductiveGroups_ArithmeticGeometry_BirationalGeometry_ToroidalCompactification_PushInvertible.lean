-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:49.396095+00:00
-- url     : https://prove2.me/theorems/4a0f11e5-cb7a-4084-af17-9aa392948a7a
-- title:
--   Push Invertible
-- statement:
--   Definitions and structural lemmas for Push Invertible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushInvertible.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
def KA (l : Level H) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {H.rt0, zeta l.A}
def baseKA (l : Level H) : Base l (KA l) where
  unit n hn := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
  ρ := ⟨H.rt0, IntermediateField.subset_adjoin _ _ (by simp)⟩
  ρ_sq := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  ζ := ⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩
  ζ_prim := IsPrimitiveRoot.of_map_of_injective (f := (KA l).val.toRingHom)
    (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne') Subtype.val_injective
def Datum.dim (D : Datum H) : ℕ := Module.finrank ℚ E / 2 * D.p * D.q
def constPt {k : Type} [Field k] {X : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X) : Sp (DualNumber k) ⟶ X :=
  spMap (algebraMap k (DualNumber k)) ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x
structure Moduli (D : Datum H) (l : Level H) where
  X : Scheme.{0}
  s : X ⟶ Sp (KA l)
  qproj : IsQProjOver s
  smooth : SmoothOfRelativeDimension D.dim s
  univ : Obj D l (baseKA l) s
  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ o : Obj D l (baseKA l) s',
    ∃! f : S ⟶ X, f ≫ s = s' ∧ Nonempty (ObjMap o univ f)
  unram : ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ X) (o : Obj D l (baseKA l) (x ≫ s)),
    Nonempty (ObjMap o univ x) → Nonempty (ObjMap o univ (constPt x)) → x = constPt x
structure Coeff (l : Level H) where
  F : IntermediateField ℚ ℂ
  fin : FiniteDimensional ℚ F
  conj : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F
  zeta_mem : zeta l.M' ∈ F
  le : KA l ≤ F
variable {D : Datum H} {l : Level H}
abbrev Moduli.XF (Xo : Moduli D l) (c : Coeff l) : Scheme.{0} :=
  pullback Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
structure Model (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O] (β : O →+* c.F) where
  X : Scheme.{0}
  s : X ⟶ Sp O
  normal : IsNormalScheme X
  proj : IsProjOver s
  flat : Flat s
  jQ : Xo.XF c ⟶ pullback s (spMap β)
  jQ_over : jQ ≫ pullback.snd _ _ = pullback.snd _ _
  jQ_open : IsOpenImmersion jQ
  jQ_dense : Dense (Set.range jQ)
  t : SAB H X
  oF : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  m0 : ObjMap oF Xo.univ (pullback.fst _ _)
  m : SABMap oF.t t (jQ ≫ pullback.fst _ _)
  ab_gen : pullback.fst s (spMap β) ⁻¹' abLocus t.G = Set.range jQ
namespace Model
variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
def j : Xo.XF c ⟶ Y.X := Y.jQ ≫ pullback.fst _ _
def Descends : Prop :=
  ∃ (XK : Scheme.{0}) (sK : XK ⟶ Sp (KA l)) (GK : Over XK) (_ : GrpObj GK) (jK : Xo.X ⟶ XK)
    (φK : Xo.univ.t.G.left ⟶ GK.left) (e : pullback Y.s (spMap β) ⟶ XK)
    (GQ : Over (pullback Y.s (spMap β))) (_ : GrpObj GQ) (φ₁ : GQ.left ⟶ Y.t.G.left) (φ₂ : GQ.left ⟶ GK.left)
    (ψ : Y.oF.t.G.left ⟶ GQ.left),
    IsOpenImmersion jK ∧ jK ≫ sK = Xo.s ∧ IsGrpPullback Xo.univ.t.G GK jK φK ∧
    IsPullback e (pullback.snd _ _) sK (spMap (IntermediateField.inclusion c.le).toRingHom) ∧
    Y.jQ ≫ e = pullback.fst _ _ ≫ jK ∧
    IsGrpPullback GQ Y.t.G (pullback.fst _ _) φ₁ ∧ IsGrpPullback GQ GK e φ₂ ∧
    ψ ≫ φ₁ = Y.m.φ ∧ ψ ≫ GQ.hom = Y.oF.t.G.hom ≫ Y.jQ ∧ ψ ≫ φ₂ = Y.m0.toSABMap.φ ≫ φK
def LevelActs : Prop :=
  ∀ (r : Xo.XF c ≅ Xo.XF c) (ν : SABMap Y.oF.t Y.oF.t r.hom) (gM gA : D.La →ₗ[𝓞 E] D.La),
    r.hom ≫ pullback.snd _ _ = pullback.snd _ _ →
    (∀ a, (Y.oF.eta (gM a)).left ≫ ν.φ = r.hom ≫ (Y.oF.eta a).left) →
    (∀ a, (Y.oF.etaA (gA a)).left ≫ ν.φ = r.hom ≫ (Y.oF.etaA a).left) →
    ∃ (ρ : Y.X ≅ Y.X) (mu : SABMap Y.t Y.t ρ.hom),
      ρ.hom ≫ Y.s = Y.s ∧ Y.j ≫ ρ.hom = r.hom ≫ Y.j ∧ Y.m.φ ≫ mu.φ = ν.φ ≫ Y.m.φ
def Extends (U : Y.X.Opens) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) : Prop :=
  ∃ σ' : U.toScheme ⟶ Y.t.G.left, σ' ≫ Y.t.G.hom = U.ι ∧
    ∀ j' : Xo.XF c ⟶ U.toScheme, j' ≫ U.ι = Y.j → j' ≫ σ' = σ.left ≫ Y.m.φ
end Model
def PushInvertible {X : Scheme.{0}} (G : Over X) (L : LB G.left) : Prop :=
  ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V),
    (∀ (W : X.Opens) (hW : W ≤ V), ∀ s ∈ secOn L (G.hom ⁻¹ᵁ W), ∃! a : Γ(X, W), ∀ i,
      s i = (G.hom.appLE W (G.hom ⁻¹ᵁ W ⊓ L.U i) inf_le_left).hom a *
        resG G.left (inf_le_inf_right _ (G.hom.preimage_mono hW)) (θ i)) ∧
    ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)
def IsTransition {l₂ : Level H} {Xo : Moduli D l} {Xo₂ : Moduli D l₂} {c : Coeff l} {c₂ : Coeff l₂}
    {O O₂ : Type} [CommRing O] [CommRing O₂] {β : O →+* c.F} {β₂ : O₂ →+* c₂.F}
    (Y : Model Xo c β) (Y₂ : Model Xo₂ c₂ β₂) (b : O →+* O₂) (π : Y₂.X ⟶ Y.X) : Prop :=
  ∃ (π' : Y₂.X ⟶ pullback Y.s (spMap b)) (mu : SABMap Y₂.t Y.t π) (r : Xo₂.XF c₂ ⟶ Xo.XF c),
    π' ≫ pullback.fst _ _ = π ∧ π' ≫ pullback.snd _ _ = Y₂.s ∧ IsFinite π' ∧ Y₂.j ≫ π = r ≫ Y.j ∧
    (∀ a, (Y₂.oF.eta a ^ (l₂.M / l.M)).left ≫ Y₂.m.φ ≫ mu.φ = r ≫ (Y.oF.eta a).left ≫ Y.m.φ) ∧
    (∀ a, (Y₂.oF.etaA a ^ (l₂.A / l.A)).left ≫ Y₂.m.φ ≫ mu.φ = r ≫ (Y.oF.etaA a).left ≫ Y.m.φ)
def Dominates {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F}
    {β' : O' →+* c.F} (Y : Model Xo c β) (Y' : Model Xo c β') (b : O →+* O') : Prop :=
  ∃ (f : pullback Y.s (spMap b) ⟶ Y'.X) (t : SAB H (pullback Y.s (spMap b)))
    (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t Y'.t f),
    f ≫ Y'.s = pullback.snd _ _ ∧
    (∀ a : Xo.XF c ⟶ pullback Y.s (spMap b), a ≫ pullback.fst _ _ = Y.j → a ≫ f = Y'.j) ∧
    ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left),
      g ≫ m₁.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
      g ≫ m₂.φ = g₂ ≫ Y'.m.φ
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


