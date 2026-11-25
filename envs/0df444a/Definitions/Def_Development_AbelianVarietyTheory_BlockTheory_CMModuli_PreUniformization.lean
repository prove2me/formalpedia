-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PreUniformization
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_PreUniformization
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:25.692272+00:00
-- url     : https://prove2.me/theorems/c3d1e334-e9f8-4cb2-a731-d40044eda9a2
-- title:
--   Pre Uniformization
-- statement:
--   Definitions and structural lemmas for Pre Uniformization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PreUniformization.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_cub_alg
import Theorems.Thm_GlobalTheory_UU_inv_left_comp
import Theorems.Thm_GlobalTheory_UU_one_left_comp
import Theorems.Thm_GlobalTheory_UU_toBase_mul_pullback
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization
variable {R : Type} [CommRing R] [IsDomain R]
abbrev Red (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Over (Spec (CommRingCat.of R)) :=
  (Over.map (thick R I e)).obj (thickObj R I e G)
def isoV {X₁ X₂ Y Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (r : Z ⟶ Y) (z : Z) (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gw w r z (J₂ (r ≫ f₂)) (fun _ => J₁ (r ≫ f₁))
def cst {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    Z.presheaf.stalk z :=
  gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c)
abbrev pt3 (I : Ideal R) (e : ℕ) {G H : Over (Spec (CommRingCat.of R))} (p : Red I e G ⟶ H)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x y u : T ⟶ thickObj R I e G) :
    T.left ⟶ (H ⊗ H ⊗ H).left :=
  (lift ((Over.map (thick R I e)).map x ≫ p)
    (lift ((Over.map (thick R I e)).map y ≫ p) ((Over.map (thick R I e)).map u ≫ p))).left
structure PreUnif (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] where
  smooth : Smooth G.hom
  separated : IsSeparated G.hom

  gen : (Over.pullback (jK R)).obj G ≅ A.A
  gen_hom : IsMonHom gen.hom

  L : RigLB G

  cub : CubicalStr G L

  sym : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])
  sym_gen : sym.IsGen
  sym_rig : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J), Good L.L z J →
    val sym (r ≫ eSec G) z J = 1
  extendsL : ∃ w : LB.Iso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK R))), w.IsGen

  j : ∀ e : ℕ, GtCoord I D e G
  j_base : ∀ e : ℕ, thickMap R I e G ≫ (j (e + 1)).pG.left = (j e).pG.left
  j_coord : ∀ (e : ℕ) (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
    val ((j (e + 1)).t χ) (r ≫ thickMap R I e G) z J = val ((j e).t χ) r z J

  ph : ∀ e : ℕ, LB.Iso (L.L.pull (fstG I e G).left) (D.P.L.pull (j e).pG.left)
  ph_gen : ∀ e, (ph e).IsGen
  ph_rig : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (z : Z) (JL) (JM),
    Good L.L z JL → Good D.P.L z JM →
    val (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (r ≫ thick R I e) z JM =
      isoV (ph e) (r ≫ eSec (thickObj R I e G)) z JL JM *
        val (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) L.rig (r ≫ thick R I e) z JL
  ph_even : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (JL) (JM),
    Good L.L z JL → Good D.P.L z JM →
    val D.sym (r ≫ (j e).pG.left) z JM * isoV (ph e) r z JL JM =
      isoV (ph e) (r ≫ (ι[thickObj R I e G]).left) z JL JM * val sym (r ≫ (fstG I e G).left) z JL
  ph_cub : ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y u : T ⟶ thickObj R I e G)
    (z : T.left) (JL) (JM), Good L.L z JL → Good D.P.L z JM →
    val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t (pt3 I e (j e).pG x y u) z JM *
        isoV (ph e) (x * y).left z JL JM * isoV (ph e) (x * u).left z JL JM * isoV (ph e) (y * u).left z JL JM *
        isoV (ph e) (1 : T ⟶ thickObj R I e G).left z JL JM =
      isoV (ph e) (x * y * u).left z JL JM * isoV (ph e) x.left z JL JM * isoV (ph e) y.left z JL JM *
        isoV (ph e) u.left z JL JM *
        val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) cub.t (pt3 I e (fstG I e G) x y u) z JL
  ph_compat : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (JL) (JM),
    Good L.L z JL → Good D.P.L z JM →
    isoV (ph (e + 1)) (r ≫ thickMap R I e G) z JL JM = isoV (ph e) r z JL JM
def compφ (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (α : D.X) :
    Fin 4 → ((T ⊗ D.P.A).left ⟶ D.P.A.left) :=
  ![(snd T D.P.A).left, (snd T D.P.A * (toUnit _ ≫ D.c α)).left, (toUnit (T ⊗ D.P.A) ≫ D.c α).left,
    (toUnit (T ⊗ D.P.A) ≫ η[D.P.A]).left]
abbrev SecB (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (compφ D T α) ![(k : ℤ) - 1, 1, -1, 1])
abbrev RawFam (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) : Type :=
  ∀ α : D.X, SecB D (TF (R := R) F) k α
def RawFam.ofFam {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} (s : Fam D F k) :
    RawFam D F k := s.s
namespace PreUnif
variable {I : Ideal R} {D : DegPre R} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : PreUnif I D A G)
abbrev SecG (T : Over (Spec (CommRingCat.of R))) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb U.L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => (k : ℤ)))
def ExpAt {T : Over (Spec (CommRingCat.of R))} {k : ℕ} (e : ℕ) (σ : U.SecG T k) (f : ∀ α : D.X, SecB D T k α) : Prop :=
  ∃ S : Finset D.X,
    (∀ α ∉ S, ∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ T) (b : Z ⟶ Red I e D.P.A) (z : Z.left) (J),
      Good D.P.L z J → sval (f α) (lift r (b ≫ D.prBe I e)).left z J = 0) ∧
    ∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ T) (x : Z ⟶ Red I e G) (z : Z.left) (JL) (JM),
      Good U.L.L z JL → Good D.P.L z JM →
      (isoV (U.ph e) x.left z JL JM).val ^ k * sval σ (lift r (x ≫ fstG I e G)).left z JL =
        ∑ α ∈ S, sval (f α) (lift r (x ≫ (U.j e).pG)).left z JM * (val ((U.j e).t α) x.left z JM).val
def Exp {T : Over (Spec (CommRingCat.of R))} {k : ℕ} (σ : U.SecG T k) (f : ∀ α : D.X, SecB D T k α) : Prop :=
  ∀ e : ℕ, U.ExpAt e σ f
def AgreeAt {T : Over (Spec (CommRingCat.of R))} (e : ℕ) (x : T ⟶ G) (g : GtPt D T) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ T) (y : Z ⟶ Red I e G), y ≫ fstG I e G = r ≫ x →
    y ≫ (U.j e).pG = r ≫ g.b ∧ ∀ (χ : D.X) (z : Z.left) (J), Good D.P.L z J →
      val ((U.j e).t χ) y.left z J = val (g.s χ) r.left z J
def Agree {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ G) (g : GtPt D T) : Prop := ∀ e : ℕ, U.AgreeAt e x g
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
def ExpGF {k : ℕ} (σ' : U.SecG (TF (R := R) F) k) (s : RawFam D F k) : Prop :=
  ∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → U.SecG (𝟙_ _) k) (f : Fin n → ∀ α : D.X, SecB D (𝟙_ _) k α),
    (∀ i, U.Exp (σ i) (f i)) ∧
    (∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ TF (R := R) F) (x : Z ⟶ G) (z : Z.left) (J), Good U.L.L z J →
      sval σ' (lift r x).left z J = ∑ i, cst r.left z (c i) * sval (σ i) (lift (toUnit Z) x).left z J) ∧
    ∀ (α : D.X) (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ TF (R := R) F) (b : Z ⟶ D.P.A) (z : Z.left) (J),
      Good D.P.L z J →
      sval (s α) (lift r b).left z J = ∑ i, cst r.left z (c i) * sval (f i α) (lift (toUnit Z) b).left z J
def ExpAF {k : ℕ} (w : LB.Iso (A.L.pull U.gen.hom.left) (U.L.L.pull (pullback.fst G.hom (jK R))))
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : RawFam D F k) : Prop :=
  w.IsGen ∧ ∃ σ' : U.SecG (TF (R := R) F) k, U.ExpGF F σ' s ∧
    ∀ (Z : Scheme.{0}) (a : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (g : Z ⟶ (TF (R := R) F ⊗ G).left)
      (x : Z ⟶ ((Over.pullback (jK R)).obj G).left),
      (a ≫ (fst (TFK (R := R) F) A.A).left : Z ⟶ Spec (CommRingCat.of F)) = g ≫ (fst (TF (R := R) F) G).left →
      a ≫ (snd (TFK (R := R) F) A.A).left = x ≫ U.gen.hom.left →
      g ≫ (snd (TF (R := R) F) G).left = x ≫ pullback.fst G.hom (jK R) →
      ∀ (z : Z) (JA) (JL), Good A.L z JA → Good U.L.L z JL →
        sval σ' g z JL = (isoV w x z JA JL).val ^ k *
          sval (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ)) t a z JA
end PreUnif
section Ph
variable (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
def Ph (k : ℕ) (y : D.X) (g : GtPtF D F)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε k))) (s s' : RawFam D F k) : Prop :=
  g.b ^ k = toUnit _ ≫ D.c y ∧ w.IsGen ∧
  ∀ (α : D.X) (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ TF (R := R) F) (x : Z ⟶ D.P.A) (z : Z.left)
    (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    sval (s' (α + y)) (lift r x).left z J =
      (cubN (cubV D.cub z J) k (toUnit Z ≫ D.c α) (r ≫ g.b) x * (cubV D.cub z J (toUnit Z ≫ D.c α) x (r ≫ g.b))⁻¹ *
        val (g.s α) r.left z J * val w r.left z J).val * sval (s α) (lift r (x * (r ≫ g.b))).left z J
def PhQ (k : ℕ) (p : QkPt D F k) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (s s' : RawFam D F k) : Prop :=
  Ph D F k p.y p.g w s s'
end Ph
section OfUnifPre
theorem gm_res_pull {X Y Z : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)ˣ) {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (r : Z ⟶ Y) (z : Z) (hz : r z ∈ V) : gm r z V (res h (pullU f U a)) = gm (r ≫ f) z U a :=
  (gm_res r z h hz _).trans (gm_pull r f z U (h hz) a)
theorem gm_of_res₂ {Y Z : Scheme.{0}} {U₁ U₂ : Y.Opens} {a₁ : Γ(Y, U₁)ˣ} {a₂ : Γ(Y, U₂)ˣ}
    (H : ∀ (V : Y.Opens) (h₁ : V ≤ U₁) (h₂ : V ≤ U₂), res h₁ a₁ = res h₂ a₂) (r : Z ⟶ Y) (z : Z)
    (m₁ : r z ∈ U₁) (m₂ : r z ∈ U₂) : gm r z U₁ a₁ = gm r z U₂ a₂ :=
  (gm_res r z inf_le_left ⟨m₁, m₂⟩ _).symm.trans ((congrArg (gm r z _) (H _ _ _)).trans
    (gm_res r z inf_le_right ⟨m₁, m₂⟩ _))
theorem gm_of_res₃ {Y Z : Scheme.{0}} {U₁ U₂ U₃ : Y.Opens} {a₁ : Γ(Y, U₁)ˣ} {a₂ : Γ(Y, U₂)ˣ} {a₃ : Γ(Y, U₃)ˣ}
    (H : ∀ (V : Y.Opens) (h₁ : V ≤ U₁) (h₂ : V ≤ U₂) (h₃ : V ≤ U₃), res h₁ a₁ * res h₂ a₂ = res h₃ a₃) (r : Z ⟶ Y)
    (z : Z) (m₁ : r z ∈ U₁) (m₂ : r z ∈ U₂) (m₃ : r z ∈ U₃) : gm r z U₁ a₁ * gm r z U₂ a₂ = gm r z U₃ a₃ := by
  have m : r z ∈ U₁ ⊓ U₂ ⊓ U₃ := ⟨⟨m₁, m₂⟩, m₃⟩
  have := congrArg (gm r z _) (H (U₁ ⊓ U₂ ⊓ U₃) (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
    inf_le_right)
  rwa [map_mul, gm_res r z _ m, gm_res r z _ m, gm_res r z _ m] at this
theorem gm_of_res₄ {Y Z : Scheme.{0}} {U₁ U₂ U₃ U₄ : Y.Opens} {a₁ : Γ(Y, U₁)ˣ} {a₂ : Γ(Y, U₂)ˣ} {a₃ : Γ(Y, U₃)ˣ}
    {a₄ : Γ(Y, U₄)ˣ} (H : ∀ (V : Y.Opens) (h₁ : V ≤ U₁) (h₂ : V ≤ U₂) (h₃ : V ≤ U₃) (h₄ : V ≤ U₄),
      res h₁ a₁ * res h₂ a₂ = res h₃ a₃ * res h₄ a₄) (r : Z ⟶ Y)
    (z : Z) (m₁ : r z ∈ U₁) (m₂ : r z ∈ U₂) (m₃ : r z ∈ U₃) (m₄ : r z ∈ U₄) :
    gm r z U₁ a₁ * gm r z U₂ a₂ = gm r z U₃ a₃ * gm r z U₄ a₄ := by
  have m : r z ∈ U₁ ⊓ U₂ ⊓ U₃ ⊓ U₄ := ⟨⟨⟨m₁, m₂⟩, m₃⟩, m₄⟩
  have := congrArg (gm r z _) (H (U₁ ⊓ U₂ ⊓ U₃ ⊓ U₄) (inf_le_left.trans (inf_le_left.trans inf_le_left))
    (inf_le_left.trans (inf_le_left.trans inf_le_right)) (inf_le_left.trans inf_le_right) inf_le_right)
  rwa [map_mul, map_mul, gm_res r z _ m, gm_res r z _ m, gm_res r z _ m, gm_res r z _ m] at this
theorem isoV_of {X₁ X₂ Y Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (r : Z ⟶ Y) (z : Z) (J₁ : (Z ⟶ X₁) → L₁.ι) (J₂ : (Z ⟶ X₂) → L₂.ι)
    {a₁ a₂} (h₁ : r ≫ f₁ = a₁) (h₂ : r ≫ f₂ = a₂) :
    isoV w r z J₁ J₂ = gm r z ((L₂.pull f₂).U (fun _ => J₂ a₂) ⊓ (L₁.pull f₁).U (fun _ => J₁ a₁))
      (w.s (fun _ => J₂ a₂, fun _ => J₁ a₁)) := by
  subst h₁ h₂; rfl
theorem mem_iso {X₁ X₂ Y Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (r : Z ⟶ Y) {z : Z} {J₁ : (Z ⟶ X₁) → L₁.ι} {J₂ : (Z ⟶ X₂) → L₂.ι} (g₁ : Good L₁ z J₁) (g₂ : Good L₂ z J₂)
    {a₁ a₂} (h₁ : r ≫ f₁ = a₁) (h₂ : r ≫ f₂ = a₂) :
    r z ∈ (L₂.pull f₂).U (fun _ => J₂ a₂) ⊓ (L₁.pull f₁).U (fun _ => J₁ a₁) := by
  subst h₁ h₂; exact ⟨mem_pull.2 (g₂ (r ≫ f₂)), mem_pull.2 (g₁ (r ≫ f₁))⟩
variable {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
def redHom (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* (Over.mk (T.hom ≫ thick R I e) ⟶ G) :=
  GlobalTheory.UU.toBaseHom (GlobalTheory.UU.toBase_mul_pullback G (thick R I e)) T
def baseHom {D : DegPre R} {e : ℕ} (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* (Over.mk (T.hom ≫ thick R I e) ⟶ D.P.A) :=
  (redHom I e D.P.A T).comp (MonoidHom.mk' (fun x => x ≫ g.q) fun x y => by
    have := g.q_hom; exact MonObj.mul_comp _ _ _)
theorem baseHom_left {D : DegPre R} {e : ℕ} (g : GtCoord I D e G)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G) :
    (baseHom g T x).left = x.left ≫ g.pG.left := Category.assoc _ _ _
theorem red_one (e : ℕ) : eSec (thickObj R I e G) ≫ (fstG I e G).left = thick R I e ≫ eSec G := by
  have := GlobalTheory.UU.one_left_comp (GlobalTheory.UU.toBase_mul_pullback G (thick R I e)) (𝟙_ _)
  rw [GlobalTheory.UU.one_left] at this
  exact ((congrArg (· ≫ (fstG I e G).left) (Category.id_comp _)).symm.trans this).trans
    (congrArg (· ≫ eSec G) (Category.id_comp _))
theorem red_inv (e : ℕ) : (ι[thickObj R I e G]).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left := by
  have := GlobalTheory.UU.inv_left_comp (GlobalTheory.UU.toBase_mul_pullback G (thick R I e)) (𝟙 _)
  rw [Hom.inv_def, Category.id_comp] at this
  exact this.trans (congrArg (· ≫ (ι[G]).left) (Category.id_comp _))
theorem base_one {D : DegPre R} {e : ℕ} (g : GtCoord I D e G) :
    eSec (thickObj R I e G) ≫ g.pG.left = thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have a : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (fun q => q.left) (IsMonHom.one_hom g.q)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I e D.P.A).left) a).trans (red_one e))
theorem base_inv {D : DegPre R} {e : ℕ} (g : GtCoord I D e G) :
    (ι[thickObj R I e G]).left ≫ g.pG.left = g.pG.left ≫ (ι[D.P.A]).left := by
  have := g.q_hom
  have a : (ι[thickObj R I e G]).left ≫ g.q.left = g.q.left ≫ (ι[thickObj R I e D.P.A]).left :=
    congrArg (fun q => q.left) (GrpObj.inv_hom g.q)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (fstG I e D.P.A).left) a).trans
    ((Category.assoc _ _ _).trans ((congrArg (g.q.left ≫ ·) (red_inv e)).trans (Category.assoc _ _ _).symm)))
variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : UnifPre I D A G)
theorem unifPre_rig (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (z : Z) (JL) (JM)
    (hL : Good U.LG.L z JL) (hM : Good D.toPre.P.L z JM) :
    val (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig (r ≫ thick R I e) z JM =
      isoV (U.w e) (r ≫ eSec (thickObj R I e G)) z JL JM *
        val (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rig (r ≫ thick R I e) z JL := by
  have h₁ : (r ≫ eSec (thickObj R I e G)) ≫ (fstG I e G).left = (r ≫ thick R I e) ≫ eSec G :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (red_one e)).trans (Category.assoc _ _ _).symm)
  have h₂ : (r ≫ eSec (thickObj R I e G)) ≫ (U.gt e).pG.left = (r ≫ thick R I e) ≫ eSec D.toPre.P.A :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (base_one _)).trans (Category.assoc _ _ _).symm)
  rw [isoV_of _ _ _ _ _ h₁ h₂]
  have m₁ := mem_iso (r ≫ eSec (thickObj R I e G)) hL hM h₁ h₂
  have m₂ := hL.mem (fun _ : PUnit => eSec G) (r ≫ thick R I e)
  have m₃ := hM.mem (fun _ : PUnit => eSec D.toPre.P.A) (r ≫ thick R I e)
  have H := gm_of_res₃ (U.w_rig e (fun _ => JM ((r ≫ thick R I e) ≫ eSec D.toPre.P.A),
    fun _ => JL ((r ≫ thick R I e) ≫ eSec G))) r z m₁ m₂ m₃
  exact (gm_pull r _ z _ m₃ _).symm.trans (H.symm.trans (congrArg₂ (· * ·) (gm_pull r _ z _ m₁ _) (gm_pull r _ z _ m₂ _)))
theorem unifPre_even (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (JL) (JM)
    (hL : Good U.LG.L z JL) (hM : Good D.toPre.P.L z JM) :
    val D.toPre.sym (r ≫ (U.gt e).pG.left) z JM * isoV (U.w e) r z JL JM =
      isoV (U.w e) (r ≫ (ι[thickObj R I e G]).left) z JL JM * val U.symG (r ≫ (fstG I e G).left) z JL := by
  have h₁ : (r ≫ (ι[thickObj R I e G]).left) ≫ (fstG I e G).left = (r ≫ (fstG I e G).left) ≫ (ι[G]).left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (red_inv e)).trans (Category.assoc _ _ _).symm)
  have h₂ : (r ≫ (ι[thickObj R I e G]).left) ≫ (U.gt e).pG.left = (r ≫ (U.gt e).pG.left) ≫ (ι[D.toPre.P.A]).left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) (base_inv _)).trans (Category.assoc _ _ _).symm)
  have h₃ : r ≫ (fstG I e G).left = (r ≫ (fstG I e G).left) ≫ 𝟙 _ := (Category.comp_id _).symm
  have h₄ : r ≫ (U.gt e).pG.left = (r ≫ (U.gt e).pG.left) ≫ 𝟙 _ := (Category.comp_id _).symm
  rw [isoV_of _ _ _ _ _ h₁ h₂, isoV_of _ _ _ _ _ h₃ h₄]
  have H₀ := U.w_even e (fun k => JL ((r ≫ (fstG I e G).left) ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k))
    (fun k => JM ((r ≫ (U.gt e).pG.left) ≫ (![(ι[D.toPre.P.A]).left, 𝟙 D.toPre.P.A.left] : Fin 2 → _) k))
    (fun a b h => congrArg JL ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h).trans (Category.assoc _ _ _).symm)))
    (fun a b h => congrArg JM ((Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h).trans (Category.assoc _ _ _).symm)))
  have m₁ := hM.mem ![(ι[D.toPre.P.A]).left, 𝟙 D.toPre.P.A.left] (r ≫ (U.gt e).pG.left)
  have m₂ := mem_iso r hL hM h₃ h₄
  have m₃ := mem_iso (r ≫ (ι[thickObj R I e G]).left) hL hM h₁ h₂
  have m₄ := hL.mem ![(ι[G]).left, 𝟙 G.left] (r ≫ (fstG I e G).left)
  have H := gm_of_res₄ H₀ r z m₁ m₂ m₃ m₄
  exact (congrArg₂ (· * ·) (gm_pull r _ z _ m₁ _) rfl).symm.trans
    (H.trans (congrArg₂ (· * ·) (gm_pull r _ z _ m₃ _) (gm_pull r _ z _ m₄ _)))
theorem unifPre_compat (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (JL) (JM)
    (hL : Good U.LG.L z JL) (hM : Good D.toPre.P.L z JM) :
    isoV (U.w (e + 1)) (r ≫ thickMap R I e G) z JL JM = isoV (U.w e) r z JL JM := by
  have h₁ : (r ≫ thickMap R I e G) ≫ (fstG I (e + 1) G).left = r ≫ (fstG I e G).left :=
    (Category.assoc _ _ _).trans (congrArg (r ≫ ·) ((pullback.lift_fst _ _ _).trans (Category.comp_id _)))
  have h₂ : (r ≫ thickMap R I e G) ≫ (U.gt (e + 1)).pG.left = r ≫ (U.gt e).pG.left :=
    (Category.assoc _ _ _).trans (congrArg (r ≫ ·) (U.gt_q e))
  rw [isoV_of _ _ _ _ _ h₁ h₂, isoV_of _ r _ _ _ rfl rfl]
  have m₁ := mem_iso (r ≫ thickMap R I e G) hL hM h₁ h₂
  have H := gm_of_res₂ (U.w_compat e (fun _ => JM (r ≫ (U.gt e).pG.left), fun _ => JL (r ≫ (fstG I e G).left))) r z m₁
    (mem_iso r hL hM rfl rfl)
  exact (gm_pull r _ z _ m₁ _).symm.trans H
theorem psum_three_comp (e : ℕ) {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H] (p : Red I e G ⟶ H)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (β : (T ⟶ thickObj R I e G) →* (Over.mk (T.hom ≫ thick R I e) ⟶ H)) (hβ : ∀ x, (β x).left = x.left ≫ p.left)
    (x y u : T ⟶ thickObj R I e G) (k : thK) :
    (psum (thickObj R I e G) ![x, y, u] k.down).left ≫ p.left = pt3 I e p x y u ≫ thφ H (x3 H) k := by
  have b : ∀ a, β a = (Over.map (thick R I e)).map a ≫ p := fun a => Over.OverMorphism.ext (hβ a)
  refine (hβ _).symm.trans (congrArg (fun q => q.left) ((psum_hom β _ k.down).trans (Eq.trans
    (congrArg (fun q => psum H q k.down) (funext fun i => ?_))
    (psum_hom (preHom (lift ((Over.map (thick R I e)).map x ≫ p)
      (lift ((Over.map (thick R I e)).map y ≫ p) ((Over.map (thick R I e)).map u ≫ p)))) (x3 H) k.down).symm)))
  fin_cases i <;> simp [x3, preHom, b] <;> rfl
theorem unifPre_cub (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x y u : T ⟶ thickObj R I e G)
    (z : T.left) (JL) (JM) (hL : Good U.LG.L z JL) (hM : Good D.toPre.P.L z JM) :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (pt3 I e (U.gt e).pG x y u) z JM *
        isoV (U.w e) (x * y).left z JL JM * isoV (U.w e) (x * u).left z JL JM * isoV (U.w e) (y * u).left z JL JM *
        isoV (U.w e) (1 : T ⟶ thickObj R I e G).left z JL JM =
      isoV (U.w e) (x * y * u).left z JL JM * isoV (U.w e) x.left z JL JM * isoV (U.w e) y.left z JL JM *
        isoV (U.w e) u.left z JL JM *
        val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (pt3 I e (fstG I e G) x y u) z JL := by
  have h₁ := psum_three_comp e (fstG I e G) (redHom I e G T) (fun _ => rfl) x y u
  have h₂ := psum_three_comp e (U.gt e).pG (baseHom (U.gt e) T) (baseHom_left _) x y u
  have m := fun k : thK => mem_iso (psum (thickObj R I e G) ![x, y, u] k.down).left hL hM (h₁ k) (h₂ k)
  let jL : thK → U.LG.L.ι := fun k => JL (pt3 I e (fstG I e G) x y u ≫ thφ G (x3 G) k)
  let jM : thK → D.toPre.P.L.ι := fun k => JM (pt3 I e (U.gt e).pG x y u ≫ thφ _ (x3 _) k)
  let W : thK → T.left.Opens := fun k => (psum (thickObj R I e G) ![x, y, u] k.down).left ⁻¹ᵁ
    ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM k) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL k))
  have H := U.w_cub e T ![x, y, u] jL jM (fun a b h => congrArg JL h) (fun a b h => congrArg JM h)
    (_ ⊓ _ ⊓ Finset.univ.inf W) (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
    (fun k => inf_le_right.trans (Finset.inf_le (f := W) (Finset.mem_univ k)))
  have hW : z ∈ Finset.univ.inf W := by
    refine Finset.inf_induction (p := fun V : T.left.Opens => z ∈ V) trivial (fun _ a _ b => ⟨a, b⟩) fun k _ => m k
  have hz : (𝟙 T.left : T.left ⟶ T.left) z ∈ pt3 I e (U.gt e).pG x y u ⁻¹ᵁ (Theta D.toPre.P.A D.toPre.P.L).U jM ⊓
      pt3 I e (fstG I e G) x y u ⁻¹ᵁ (Theta G U.LG.L).U jL ⊓ Finset.univ.inf W :=
    ⟨⟨hM.mem (thφ _ (x3 _)) _, hL.mem (thφ G (x3 G)) _⟩, hW⟩
  have H' := (gm_res_pull _ _ _ _ (𝟙 _) z hz).symm.trans ((congrArg (gm (𝟙 T.left) z _) H).trans
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
      (map_zpow _ _ _).trans (congrArg (· ^ thε k) (gm_res_pull _ _ _ _ (𝟙 _) z hz))))
      (gm_res_pull _ _ _ _ (𝟙 _) z hz))))
  simp only [Category.id_comp] at H'
  refine GlobalTheory.UU.cub_alg (H'.trans (congrArg₂ (· * ·) ?_ rfl))
  refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (prod_cub x y u (fun q => isoV (U.w e) q z JL JM))
  have a : (lift x (lift y u)).left ≫ thφ _ (x3 _) k = (psum (thickObj R I e G) ![x, y, u] k.down).left :=
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x (lift y u))) (x3 _) k.down).trans
      (congrArg (fun q => psum _ q k.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])))
  rw [a, isoV_of _ _ _ _ _ (h₁ k) (h₂ k)]
def PreUnif.ofUnifPre : PreUnif I D.toPre A G where
  smooth := U.smooth
  separated := U.separated
  gen := U.gen
  gen_hom := U.gen_hom
  L := U.LG
  cub := U.cubG
  sym := U.symG
  sym_gen := U.symG_gen
  sym_rig _ r _ _ hJ := (val_pull hJ U.symG (eSec G) r).symm.trans ((val_corr hJ U.symG_rig r).trans (val_one _))
  extendsL := U.ext
  j := U.gt
  j_base := U.gt_q
  j_coord e χ _ r _ _ hJ := (val_pull hJ _ _ r).symm.trans (val_corr hJ (U.gt_t e χ) r)
  ph := U.w
  ph_gen := U.w_gen
  ph_rig := unifPre_rig U
  ph_even := unifPre_even U
  ph_cub := unifPre_cub U
  ph_compat := unifPre_compat U
end OfUnifPre
end GlobalTheory.IndefiniteRowSideFullHecke.PreUniformization
end


