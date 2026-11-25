-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Statements_LocalTrivialization_LocTrivOfRetraction
-- name    : Development_AbelianVarietyTheory_Statements_LocalTrivialization_LocTrivOfRetraction
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:12.211869+00:00
-- url     : https://prove2.me/theorems/e9ee50f4-856a-4b8f-9d03-735618c3bb93
-- title:
--   Loc Triv Of Retraction
-- statement:
--   Definitions and structural lemmas for Loc Triv Of Retraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/LocalTrivialization/LocTrivOfRetraction.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Theorems.Thm_GlobalTheory_SplitTorus_isGrpPullback_bcMap
import Theorems.Thm_GlobalTheory_ToSplit_act_comp
import Theorems.Thm_GlobalTheory_TorsorUnit_act_comp
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_add
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_UU_isWt_zero
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_GlobalTheory_invariant_functions_descend
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
def GtToTQSt : Prop := ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] (Dat : E.GtDatum G),
  ∃ Q : TQ G E.X, Q.i = Dat.i
def ActGradeSt : Prop := ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X]
  (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V →
  (snd (splitTorus S X) G).left ⁻¹ᵁ V ≤ ((fst (splitTorus S X) G ≫ i) * snd (splitTorus S X) G).left ⁻¹ᵁ V →
  (∀ u : Γ(G.left, V), ∃ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧
  ∀ a : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0
def QuotSchemeSt : Prop := ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J →
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
  [IsCommMonObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left),
  IsGrpPullback G₀ G (red J) F → ∀ (Q₀ : TQ G₀ X) (i : splitTorus _ X ⟶ G), IsMonHom i → TorusCompat (red J) F Q₀.i i →
  ∃ (B : Over (Spec (CommRingCat.of A))) (q : G ⟶ B) (j : Q₀.B.left ⟶ B.left),
    IsPullback j Q₀.B.hom B.hom (red J) ∧ Q₀.q.left ≫ j = F ≫ q.left ∧ IsAffineHom q.left ∧
    ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧
      (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧
      (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧
      ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ
def LocTrivSt : Prop := ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G]
  (i : splitTorus S X ⟶ G) (q : G ⟶ B), IsMonHom i → IsAffineHom q.left →
  (∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧
      (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧
      (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧
      ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) →
  Mono i ∧ Flat q.left ∧ Surjective q.left ∧ (Smooth G.hom → Smooth B.hom) ∧
    ∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ splitTorus S X, g' = (t ≫ i) * g
def LevelTQSt : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J →
  ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G]
  [IsCommMonObj G] [Smooth G.hom] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left),
  IsGrpPullback G₀ G (red J) F → ∀ Q₀ : TQ G₀ X, ∃ Q : TQ G X, TorusCompat (red J) F Q₀.i Q.i
def TQUniqSt : Prop := ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G]
  (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → ∀ (Q : TQ G X) (Q' : TQ G' X),
  TorusCompat f F Q'.i Q.i → ∃ β : Q'.B.left ⟶ Q.B.left, Q'.q.left ≫ β = F ≫ Q.q.left ∧ IsGrpPullback Q'.B Q.B f β
def TQBaseSt : Prop := ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X] (G : Over S) [GrpObj G]
  (G' : Over S') [GrpObj G'] (F : G'.left ⟶ G.left), IsGrpPullback G' G f F → ∀ Q : TQ G X,
  ∃ Q' : TQ G' X, TorusCompat f F Q'.i Q.i
def TQDimSt : Prop := ∀ (S : Scheme.{0}) [Nonempty S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (G : Over S) [GrpObj G] (Q : TQ G X) (g g' : ℕ), SmoothOfRelativeDimension g G.hom →
  SmoothOfRelativeDimension g' Q.B.hom → g = g' + Module.finrank ℤ X
def TQPtsSt : Prop := ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  (G : Over S) [GrpObj G] [IsCommMonObj G] (Q : TQ G X) (A : Type) [CommRing A] [IsLocalRing A]
  (p : Spec (CommRingCat.of A) ⟶ S), (∀ b : Over.mk p ⟶ Q.B, ∃ g : Over.mk p ⟶ G, g ≫ Q.q = b) ∧
  ∀ N : ℕ, (∀ a : Aˣ, ∃ r : Aˣ, r ^ N = a) → ∀ b : Over.mk p ⟶ Q.B, b ^ N = 1 → ∃ g : Over.mk p ⟶ G, g ^ N = 1 ∧ g ≫ Q.q = b
section Checks
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]
theorem TQ.act_comp {G : Over S} [GrpObj G] (Q : TQ G X) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) :
    ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  have e : (t ≫ Q.i) ≫ Q.q = 1 := by
    rw [Category.assoc, Q.isKernel.w, ← Category.assoc, Hom.one_def, toUnit_unique (t ≫ toUnit _) (toUnit _)]
  rw [MonObj.mul_comp, e, _root_.one_mul]
theorem TQ.invariants {G : Over S} [GrpObj G] (Q : TQ G X) (V : Q.B.left.Opens) :
    (∀ a : Γ(G.left, Q.q.left ⁻¹ᵁ V), IsWt Q.i _ a 0 ↔ ∃ c, (Q.q.left.app V).hom c = a) ∧
      Function.Injective (Q.q.left.app V).hom ∧
      (snd (splitTorus _ X) G).left ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) ≤
        ((fst (splitTorus _ X) G ≫ Q.i) * snd _ G).left ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) := by
  have := Q.q_affine
  obtain ⟨h₁, -, h₃⟩ := invariant_functions_descend S G Q.B _ Q.q Q.i Q.q_hom Q.i_hom Q.q_flat Q.q_surj
    inferInstance Q.isKernel V
  refine ⟨fun a => ⟨fun h => h₃ a fun Z t g k₁ k₂ => ?_, ?_⟩, h₁, ?_⟩
  · rw [h Z t g k₁ k₂, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]
  · rintro ⟨c, rfl⟩ Z t g k₁ k₂
    have e : ∀ (r : Z.left ⟶ G.left) (k : ⊤ ≤ r ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V)),
        (r.appLE _ ⊤ k).hom ((Q.q.left.app V).hom c) = ((r ≫ Q.q.left).appLE V ⊤ k).hom c := fun r k =>
      (congrArg (fun q => q.hom c) (Scheme.Hom.comp_appLE r Q.q.left V ⊤ k)).symm
    have e' : ∀ (r r' : Z.left ⟶ Q.B.left) (_ : r = r') (k : ⊤ ≤ r ⁻¹ᵁ V) (k' : ⊤ ≤ r' ⁻¹ᵁ V),
        (r.appLE V ⊤ k).hom c = (r'.appLE V ⊤ k').hom c := by
      rintro r _ rfl k k'; rfl
    rw [e, e, ← chV_val, chV_zero, Units.val_one, _root_.one_mul]
    have k : ((t ≫ Q.i) * g).left ≫ Q.q.left = g.left ≫ Q.q.left := by
      rw [← Over.comp_left, ← Over.comp_left, Q.act_comp]
    exact e' _ _ k _ _
  · have e := congrArg (fun q => q.left) (Q.act_comp (fst (splitTorus _ X) G) (snd _ G))
    simp only [Over.comp_left] at e
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, e]
theorem TQ.locTriv_of_retraction {G : Over S} [GrpObj G] (Q : TQ G X) (p : G ⟶ splitTorus S X) [IsMonHom p]
    (hp : Q.i ≫ p = 𝟙 _) (b : Q.B.left) : ∃ V : Q.B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧
      (∀ a : Γ(G.left, Q.q.left ⁻¹ᵁ V), IsWt Q.i _ a 0 ↔ ∃ c, (Q.q.left.app V).hom c = a) ∧
      Function.Injective (Q.q.left.app V).hom ∧
      (snd (splitTorus _ X) G).left ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) ≤
        ((fst (splitTorus _ X) G ≫ Q.i) * snd _ G).left ⁻¹ᵁ (Q.q.left ⁻¹ᵁ V) ∧
      ∃ u : Multiplicative X →* Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt Q.i _ (u (Multiplicative.ofAdd χ)).val χ := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hb, -⟩ := Q.B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ b) isOpen_univ
  obtain ⟨h₁, h₂, h₃⟩ := Q.invariants V
  exact ⟨V, hb, hV, h₁, h₂, h₃,
    (Units.map (G.left.presheaf.map (homOfLE le_top).op).hom.toMonoidHom).comp (splitTorusPointsEquiv S X G p),
    fun χ => (isWt_of_retraction p hp χ).res le_top⟩
theorem isGrpPullback_unit (f : S' ⟶ S) : IsGrpPullback (𝟙_ (Over S')) (𝟙_ (Over S)) f f :=
  ⟨IsPullback.of_vert_isIso (fst := f) (snd := 𝟙 S') (f := 𝟙 S) (g := f) ⟨by simp⟩, fun T x y x₀ y₀ hx _ => by
    rw [toUnit_unique (x₀ * y₀) x₀, toUnit_unique (x * y) x, hx]⟩
theorem span_eps_nilpotent : IsNilpotent (Ideal.span {(DualNumber.eps : DualNumber ℚ)}) ∧
    Ideal.span {(DualNumber.eps : DualNumber ℚ)} ≠ ⊥ := by
  refine ⟨⟨2, ?_⟩, fun h => ?_⟩
  · rw [Ideal.span_singleton_pow, pow_two, DualNumber.eps_mul_eps]; simp
  · have := congrArg TrivSqZeroExt.snd (Ideal.span_singleton_eq_bot.1 h)
    simp at this
example (h : ActGradeSt) (A : CommRingCat.{0}) (u : Γ((splitTorus (Spec A) X).left, ⊤)) :
    ∃ a : X →₀ Γ((splitTorus (Spec A) X).left, ⊤), (∀ χ, IsWt (𝟙 _) ⊤ (a χ) χ) ∧ u = a.sum fun _ x => x :=
  have : IsAffine (splitTorus (Spec A) X).left := isAffine_of_isAffineHom (splitTorus (Spec A) X).hom
  (h _ _ X (𝟙 _) inferInstance ⊤ (isAffineOpen_top _) le_top).1 u
example (χ₁ χ₂ : X) : ∃ a : X →₀ Γ((splitTorus S X).left, ⊤), (∀ χ, IsWt (𝟙 _) ⊤ (a χ) χ) ∧
    (charUnit S X χ₁).val + (charUnit S X χ₂).val = a.sum fun _ x => x := by
  classical
  have w : ∀ ψ χ : X, IsWt (𝟙 _) ⊤ (Finsupp.single ψ (charUnit S X ψ).val χ) χ := fun ψ χ => by
    rw [Finsupp.single_apply]
    split_ifs with e
    · exact e ▸ isWt_charUnit ψ
    · exact isWt_zero χ
  refine ⟨Finsupp.single χ₁ (charUnit S X χ₁).val + Finsupp.single χ₂ (charUnit S X χ₂).val,
    fun χ => (w χ₁ χ).add (w χ₂ χ), ?_⟩
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
    Finsupp.sum_single_index rfl]
example (G : Over S) [GrpObj G] (i : splitTorus S PUnit ⟶ G) [IsMonHom i] (V : G.left.Opens) :
    (∀ u : Γ(G.left, V), ∃ a : PUnit →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) ∧ u = a.sum fun _ x => x) ∧
    ∀ a : PUnit →₀ Γ(G.left, V), (∀ χ, IsWt i V (a χ) χ) → (a.sum fun _ x => x) = 0 → a = 0 := by
  refine ⟨fun u => ⟨Finsupp.single 0 u, fun χ Z t g h₁ h₂ => ?_, by rw [Finsupp.sum_single_index rfl]⟩, fun a _ h => ?_⟩
  · have e : (t ≫ i) * g = g := by rw [point_eq_of_subsingleton t 1, MonObj.one_comp, _root_.one_mul]
    have e' : ∀ (r r' : Z.left ⟶ G.left) (_ : r = r') (k : ⊤ ≤ r ⁻¹ᵁ V) (k' : ⊤ ≤ r' ⁻¹ᵁ V) (c),
        (r.appLE V ⊤ k).hom c = (r'.appLE V ⊤ k').hom c := by
      rintro r _ rfl k k' c; rfl
    rw [← chV_val, Subsingleton.elim χ 0, chV_zero, Units.val_one, _root_.one_mul]
    have k : ((t ≫ i) * g).left = g.left := by rw [e]
    exact e' _ _ k _ _ _
  · rw [Finsupp.sum_fintype _ _ fun _ => rfl, Fintype.sum_unique] at h
    exact Finsupp.ext fun χ => Subsingleton.elim default χ ▸ h
example (h : QuotSchemeSt) : ∃ (B : Over (Spec (CommRingCat.of (DualNumber ℚ)))) (q : splitTorus _ ℤ ⟶ B),
    IsAffineHom q.left := by
  obtain ⟨B, q, -, -, -, hq, -⟩ := h (DualNumber ℚ) _ span_eps_nilpotent.1 ℤ (splitTorus _ ℤ) (splitTorus _ ℤ) _
    (SplitTorus.isGrpPullback_bcMap _ ℤ) (TQ.torus _ ℤ) (𝟙 _) inferInstance (torusCompat_bcMap _)
  exact ⟨B, q, hq⟩
example (A : Type) [CommRing A] (J : Ideal A) :
    ∃ (B : Over (Spec (CommRingCat.of A))) (q : splitTorus _ X ⟶ B) (j : (TQ.torus _ X).B.left ⟶ B.left),
      IsPullback j (TQ.torus _ X).B.hom B.hom (red J) ∧
      (TQ.torus _ X).q.left ≫ j = SplitTorus.bcMap (red J) X ≫ q.left ∧ IsAffineHom q.left ∧
      ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧
        (∀ a : Γ((splitTorus _ X).left, q.left ⁻¹ᵁ V), IsWt (𝟙 _) _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧
        Function.Injective (q.left.app V).hom ∧
        (snd (splitTorus _ X) (splitTorus _ X)).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤
          ((fst (splitTorus _ X) (splitTorus _ X) ≫ 𝟙 _) * snd _ (splitTorus _ X)).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧
        ∃ u : Multiplicative X →* Γ((splitTorus _ X).left, q.left ⁻¹ᵁ V)ˣ,
          ∀ χ, IsWt (𝟙 _) _ (u (Multiplicative.ofAdd χ)).val χ :=
  ⟨𝟙_ _, toUnit _, red J, (isGrpPullback_unit (red J)).1, by
    show (toUnit (splitTorus _ X)).left ≫ _ = _
    rw [Rosenlicht.toUnit_left, Rosenlicht.toUnit_left]
    exact (SplitTorus.bcMap_hom _ X).symm, (TQ.torus _ X).q_affine,
    (TQ.torus _ X).locTriv_of_retraction (𝟙 _) (Category.id_comp _)⟩
example (h : LocTrivSt) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) : Mono (TQ.prod X A hA).i :=
  (h S X _ A _ _ (TQ.prod X A hA).i_hom (TQ.prod X A hA).q_affine
    ((TQ.prod X A hA).locTriv_of_retraction (fst _ _) (lift_fst _ _))).1
example (h : LevelTQSt) : Nonempty (TQ (splitTorus (Spec (CommRingCat.of (DualNumber ℚ))) ℤ) ℤ) :=
  (h (DualNumber ℚ) _ span_eps_nilpotent.1 ℤ (splitTorus _ ℤ) (splitTorus _ ℤ) _
    (SplitTorus.isGrpPullback_bcMap _ ℤ) (TQ.torus _ ℤ)).nonempty
example (f : S' ⟶ S) :
    (∃ Q : TQ (splitTorus S X) X, TorusCompat f (SplitTorus.bcMap f X) (TQ.torus S' X).i Q.i) ∧
      ∃ Q' : TQ (splitTorus S' X) X, TorusCompat f (SplitTorus.bcMap f X) Q'.i (TQ.torus S X).i :=
  ⟨⟨TQ.torus S X, torusCompat_bcMap f⟩, TQ.torus S' X, torusCompat_bcMap f⟩
example (h : TQUniqSt) (h' : TQBaseSt) (f : S' ⟶ S) :
    (∃ β, IsGrpPullback (TQ.torus S' X).B (TQ.torus S X).B f β) ∧ Nonempty (TQ (splitTorus S' X) X) :=
  ⟨(h S S' f X _ _ _ (SplitTorus.isGrpPullback_bcMap f X) (TQ.torus S X) (TQ.torus S' X)
      (torusCompat_bcMap f)).imp fun _ e => e.2,
    (h' S S' f X _ _ _ (SplitTorus.isGrpPullback_bcMap f X) (TQ.torus S X)).nonempty⟩
example (f : S' ⟶ S) : ∃ β : (TQ.torus S' X).B.left ⟶ (TQ.torus S X).B.left,
    (TQ.torus S' X).q.left ≫ β = SplitTorus.bcMap f X ≫ (TQ.torus S X).q.left ∧
      IsGrpPullback (TQ.torus S' X).B (TQ.torus S X).B f β :=
  ⟨f, by
    show (toUnit (splitTorus S' X)).left ≫ _ = _ ≫ (toUnit (splitTorus S X)).left
    rw [Rosenlicht.toUnit_left, Rosenlicht.toUnit_left]
    exact (SplitTorus.bcMap_hom _ X).symm, isGrpPullback_unit f⟩
example (h : TQDimSt) [Nonempty S] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.finrank ℤ X = 0 + Module.finrank ℤ X :=
  h S X _ (TQ.torus S X) _ 0 inferInstance (inferInstanceAs (SmoothOfRelativeDimension 0 (𝟙 S)))
example (h : TQPtsSt) (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (p : Spec (CommRingCat.of ℂ) ⟶ S) (N : ℕ)
    (hN : 0 < N) (b : Over.mk p ⟶ A) (hb : b ^ N = 1) :
    ∃ g : Over.mk p ⟶ splitTorus S ℤ ⊗ A, g ^ N = 1 ∧ g ≫ snd _ _ = b := by
  have := hA.comm
  refine (h S ℤ _ (TQ.prod ℤ A hA) ℂ p).2 N (fun a => ?_) b hb
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq a.val hN
  have h0 : r ≠ 0 := by
    rintro rfl
    exact a.ne_zero (hr.symm.trans (zero_pow hN.ne'))
  exact ⟨Units.mk0 r h0, Units.ext (by simpa using hr)⟩
example (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) (Z : Over S) (N : ℕ) (b : Z ⟶ A) :
    ∃ g : Z ⟶ splitTorus S X ⊗ A, (b ^ N = 1 → g ^ N = 1) ∧ g ≫ (TQ.prod X A hA).q = b := by
  refine ⟨lift 1 b, fun hb => ?_, lift_snd _ _⟩
  ext
  · rw [MonObj.pow_comp, lift_fst, one_pow, MonObj.one_comp]
  · rw [MonObj.pow_comp, lift_snd, hb, MonObj.one_comp]
end Checks
end GlobalTheory.UU
end


