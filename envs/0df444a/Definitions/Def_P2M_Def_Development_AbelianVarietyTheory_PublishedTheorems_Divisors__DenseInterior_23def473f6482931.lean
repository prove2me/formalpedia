-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:40.540739+00:00
-- url     : https://prove2.me/theorems/7d36fb36-ab2e-4f93-bc19-4f607f584b3f
-- title:
--   Dense Interior
-- statement:
--   Definitions and structural lemmas for Dense Interior, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/DenseInterior.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsChartIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped Matrix
namespace GlobalTheory.LogKS
attribute [local instance] Over.cartesianMonoidalCategory
def IsField {Z : Scheme.{0}} (W₀ : Z.Opens) (d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)) : Prop :=
  (∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f') ∧
    (∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = f * d W f' + f' * d W f) ∧
    ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG Z h f) = resG Z h (d W f)
def chart {X : Scheme.{0}} (U : X.affineOpens) : Sp Γ(X, U.1) ⟶ X := U.2.fromSpec
def logDer {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Sp K) (I : X.IdealSheafData) (U : X.affineOpens) :
    Submodule Γ(X, U.1) (Derivation ℤ Γ(X, U.1) Γ(X, U.1)) where
  carrier := {D | (∀ a, D (constFn s U.1 a) = 0) ∧ ∀ f ∈ I.ideal U, D f ∈ I.ideal U}
  zero_mem' := ⟨fun _ => rfl, fun _ _ => zero_mem _⟩
  add_mem' := fun {D D'} h h' =>
    ⟨fun a => by simp [h.1 a, h'.1 a], fun f hf => add_mem (h.2 f hf) (h'.2 f hf)⟩
  smul_mem' := fun r D h =>
    ⟨fun a => by simp [h.1 a], fun f hf => Ideal.mul_mem_left _ r (h.2 f hf)⟩
def balanced {O R : Type} [CommRing R] {n : ℕ} (bar : O → O) (A : O → Matrix (Fin n) (Fin n) R) :
    Submodule R (Matrix (Fin n) (Fin n) R) where
  carrier := {Θ | Θᵀ = Θ ∧ ∀ a, (A a)ᵀ * Θ = Θ * A (bar a)}
  zero_mem' := ⟨by simp, fun a => by simp⟩
  add_mem' := fun {Θ Θ'} h h' =>
    ⟨by rw [Matrix.transpose_add, h.1, h'.1], fun a => by rw [Matrix.mul_add, Matrix.add_mul, h.2, h'.2]⟩
  smul_mem' := fun r Θ h =>
    ⟨by rw [Matrix.transpose_smul, h.1], fun a => by rw [Matrix.mul_smul, Matrix.smul_mul, h.2]⟩
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
def IsTranslate {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (g : Sp S ⟶ t.G.left)
    (v : Sp (DualNumber R) ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  ∃ g' v' : tEpsG (g ≫ t.G.hom) ⟶ t.G, g'.left = spMap (algebraMap S (DualNumber S)) ≫ g ∧
    v'.left = spMap (dualMap φ) ≫ v ∧ (g' * v').left = w
def IsKS (V : X.Opens) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (D : Γ(X, U.1) → Γ(X, U.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) : Prop :=
  ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι)
    (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)),
    ⨆ i, W i = t.G.hom ⁻¹ᵁ (U.1 ⊓ V) ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧
    (∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)),
      d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r)) ∧
    ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O))
      (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left)
      (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)),
      g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) →
      valR g₀ O (d i O f - d i' O f) =
        ∑ a, ∑ b, φ (Θ a b) *
          ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) *
          (valR (w a) O f).snd
def HasLogKS {K : Type} [CommRing K] (s : X ⟶ Sp K) (V : X.Opens) : Prop :=
  ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left))
    (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(X, U.1)),
    (∀ i, IsTanAtG t (chart U) (v i)) →
    (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) →
    (∀ a i, IsCombAtG t (chart U) v (A a i) (v i ≫ (t.act.act a).left)) →
    ∃ e : logDer s (Scheme.IdealSheafData.vanishingIdeal V.compl) U ≃ₗ[Γ(X, U.1)] balanced H.bar A,
      ∀ (D : logDer s (Scheme.IdealSheafData.vanishingIdeal V.compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)),
        IsKS t V U v D.1 Θ ↔ Θ = (e D).1
variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F))
theorem isIso_fst : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (𝟙 _))
    infer_instance
  infer_instance
instance isOpenImmersion_j : IsOpenImmersion Y.j := by
  have := isIso_fst Y
  have := Y.jQ_open
  unfold Model.j
  infer_instance
def interior : Y.X.Opens := Y.j.opensRange
def boundary : Y.X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (interior Y).compl
end GlobalTheory.LogKS
namespace GlobalTheory.Published
open GlobalTheory.LogKS
def ToroidalCompactification : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
      ∃ Y : Model Xo c (RingHom.id c.F),
        SmoothOfRelativeDimension Dw.dim Y.s ∧ ReciprocityTheory.AnForm.R.FinalTheorems.Snc (boundary Y) ∧
          HasLogKS Y.t Y.s (interior Y)
end GlobalTheory.Published


