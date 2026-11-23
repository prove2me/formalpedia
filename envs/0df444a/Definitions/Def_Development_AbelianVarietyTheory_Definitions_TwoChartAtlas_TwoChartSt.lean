-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
-- name    : Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:46:06.470005+00:00
-- url     : https://prove2.me/theorems/c58688f7-f8fd-40fb-b9d5-5257771669f1
-- title:
--   Two Chart St
-- statement:
--   Definitions and structural lemmas for Two Chart St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwoChartAtlas/TwoChartSt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer
variable {R : Type} [CommRing R]
def toJet {κ : Type} [Finite κ] (m : ℕ) (g : MvPowerSeries κ R) : JetR R κ m :=
  Ideal.Quotient.mk _ (MvPowerSeries.truncTotal (m + 1) g)
abbrev Fam (G : Over (Spec (CommRingCat.of R))) (κ : Type) : Type := ∀ m : ℕ, sp (R₀ := R) (JetR R κ m) ⟶ G
def IsCompat {G : Over (Spec (CommRingCat.of R))} {κ : Type} (y : Fam G κ) : Prop :=
  ∀ m, spMap (jetTruncR R κ m) ≫ y (m + 1) = y m
def IsFPt {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {κ : Type} (y : Fam G κ) : Prop :=
  IsCompat y ∧ ∀ m, spMap (jetAug R κ m) ≫ y m = 1
def Rep {G : Over (Spec (CommRingCat.of R))} {d : ℕ} {κ : Type} [Finite κ] (x : Fam G (Fin d))
    (a : Fin d → MvPowerSeries κ R) (y : Fam G κ) : Prop :=
  (∀ j, constantCoeff (a j) = 0) ∧ ∀ m, ∃ ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m,
    (∀ j, ψ (zR m j) = toJet m (a j)) ∧ y m = spMap ψ ≫ x m
def IsLawOf {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} (x : Fam G (Fin d)) (F : Fin d → PS R 2 d) : Prop :=
  (∀ i, constantCoeff (F i) = 0) ∧ ∀ (n : ℕ) (a b : Pt R n d) (y z : Fam G (Fin n × Fin d)),
    Rep x a y → Rep x b z → Rep x (addOf F a b) (fun m => y m * z m)
def IsMapOf {G G' : Over (Spec (CommRingCat.of R))} {d : ℕ} (x : Fam G (Fin d)) (x' : Fam G' (Fin d))
    (f : G ⟶ G') (φ : Pt R 1 d) : Prop :=
  (∀ i, constantCoeff (φ i) = 0) ∧ ∀ (n : ℕ) (a : Pt R n d) (y : Fam G (Fin n × Fin d)),
    Rep x a y → Rep x' (comp1 φ a) (fun m => y m ≫ f)
open Classical in

def fnVal {A : Type} [CommRing A] {X : Scheme.{0}} (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (f : Γ(X, U)) : A :=
  if h : ⊤ ≤ p ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((p.appLE U ⊤ h).hom f) else 0
def HasSer {κ : Type} [Finite κ] {X : Scheme.{0}} (p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X)
    (U : X.Opens) (f : Γ(X, U)) (g : MvPowerSeries κ R) : Prop :=
  ∀ m, ⊤ ≤ p m ⁻¹ᵁ U ∧ fnVal (p m) U f = toJet m g
def IsSer1 {G : Over (Spec (CommRingCat.of R))} {d : ℕ} (x : Fam G (Fin d)) (U : G.left.Opens) (f : Γ(G.left, U))
    (g : PS R 1 d) : Prop :=
  ∀ (n : ℕ) (a : Pt R n d) (y : Fam G (Fin n × Fin d)), Rep x a y → HasSer (fun m => (y m).left) U f (ev ![a] g)
def IsSer2 {G : Over (Spec (CommRingCat.of R))} {d : ℕ} (x : Fam G (Fin d)) (U : (G ⊗ G).left.Opens)
    (f : Γ((G ⊗ G).left, U)) (g : PS R 2 d) : Prop :=
  ∀ (n : ℕ) (a b : Pt R n d) (y z : Fam G (Fin n × Fin d)), Rep x a y → Rep x b z →
    HasSer (fun m => (lift (y m) (z m)).left) U f (ev ![a, b] g)
def IsSer3 {G : Over (Spec (CommRingCat.of R))} {d : ℕ} (x : Fam G (Fin d)) (U : (G ⊗ G ⊗ G).left.Opens)
    (f : Γ((G ⊗ G ⊗ G).left, U)) (g : PS R 3 d) : Prop :=
  ∀ (n : ℕ) (a b c : Pt R n d) (y z w : Fam G (Fin n × Fin d)), Rep x a y → Rep x b z → Rep x c w →
    HasSer (fun m => (lift (y m) (lift (z m) (w m))).left) U f (ev ![a, b, c] g)
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair)
section FBOf
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
def IsNormRos {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) (f g : A ⟶ A)
    (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) : Prop :=
  u.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)
def primφ {S : Scheme.{0}} {A : Over S} [GrpObj A] (w : A ⟶ A) : Fin 5 → (A.left ⟶ A.left) :=
  ![𝟙 A.left, (𝟙 A * w : A ⟶ A).left, 𝟙 A.left, w.left, (1 : A ⟶ A).left]
def primε : Fin 5 → ℤ := ![1, -1, 1, 1, -1]
structure IsFBOf {O : Type} [CommRing O] [StarRing O] (Lr : RigLB G) (c : CubicalStr G Lr)
    (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε))
    {d : ℕ} (x : Fam G (Fin d)) (j : Lr.L.ι) (B : FB R d O) : Prop where
  law : IsLawOf x B.G.F
  map : ∀ a, IsMapOf x x (act.act a) (B.A.act a)
  ph1 : IsSer3 x _ (c.t.s (fun _ => j)).val B.ph1
  ph2 : B.ph2 = B.ph1
  sy : B.sy = 1
  ad : ∀ a, IsSer2 x _ ((u a).s (fun _ => j))⁻¹.val (B.ad a)
def IsGermOf (L : LB G.left) (w : G ⟶ G) (ρ : LB.Gen (LB.LinComb L (primφ w) primε)) {d : ℕ} (x : Fam G (Fin d))
    (j : L.ι) (m : ℕ) (s : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 G.left) (fun _ => (m : ℤ))).Sec) (f : PS R 1 d) : Prop :=
  ∃ σ r : PS R 1 d, IsSer1 x _ (s.f (fun _ => j)) σ ∧ IsSer1 x _ (ρ.s (fun _ => j)).val r ∧ f * r ^ m = σ
end FBOf
def JetAlgSt : Prop := ∀ (R : Type) [CommRing R] (κ : Type) [Finite κ],
  (∀ m, ∃ τ : MvPowerSeries κ R →ₐ[R] JetR R κ m, (∀ g, τ g = toJet m g) ∧ ∀ j, τ (X j) = zR m j) ∧
  (∀ m (g : MvPowerSeries κ R), jetTruncR R κ m (toJet (m + 1) g) = toJet m g ∧ jetAug R κ m (toJet m g) = constantCoeff g) ∧
  (∀ g g' : MvPowerSeries κ R, (∀ m, toJet m g = toJet m g') → g = g') ∧
  (∀ p : ∀ m, JetR R κ m, (∀ m, jetTruncR R κ m (p (m + 1)) = p m) → ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = p m) ∧
  ∀ (σ : Type) [Finite σ] (a : σ → MvPowerSeries κ R), (∀ j, constantCoeff (a j) = 0) → ∀ m,
    (∃ ψ : JetR R σ m →ₐ[R] JetR R κ m, ∀ j, ψ (zR m j) = toJet m (a j)) ∧
    ∀ ψ : JetR R σ m →ₐ[R] JetR R κ m, (∀ j, ψ (zR m j) = toJet m (a j)) →
      ∀ g : MvPowerSeries σ R, ψ (toJet m g) = toJet m (MvPowerSeries.subst a g)
def RepSt : Prop := ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x →
  ∀ (κ : Type) [Finite κ],
    (∀ a : Fin d → MvPowerSeries κ R, (∀ j, constantCoeff (a j) = 0) → ∃! y, Rep x a y) ∧
    (∀ y : Fam G κ, IsFPt y → ∃! a, Rep x a y) ∧ (∀ a (y : Fam G κ), Rep x a y → IsFPt y) ∧
    Rep x (0 : Fin d → MvPowerSeries κ R) (fun _ => 1) ∧
    ∀ (κ' : Type) [Finite κ'] (b : κ → MvPowerSeries κ' R) (ψ : ∀ m, JetR R κ m →ₐ[R] JetR R κ' m),
      (∀ i, constantCoeff (b i) = 0) → (∀ m i, ψ m (zR m i) = toJet m (b i)) →
      ∀ a (y : Fam G κ), Rep x a y → Rep x (fun j => MvPowerSeries.subst b (a j)) (fun m => spMap (ψ m) ≫ y m)
def LawSt : Prop := ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x →
  (∃ Gl : FGLaw R d, IsLawOf x Gl.F) ∧ ∀ F F', IsLawOf x F → IsLawOf x F' → F = F'
def MapSt : Prop := ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] (d : ℕ) (x : Fam G (Fin d))
    (x' : Fam G' (Fin d)), IsUnivChart G d x → IsUnivChart G' d x' →
  ∀ f : G ⟶ G', η[G] ≫ f = η[G'] → ∃! φ, IsMapOf x x' f φ
def ActSt : Prop := ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x →
  ∀ (O : Type) [CommRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (Gl : FGLaw R d), IsLawOf x Gl.F →
    ∃ A : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.OAct O Gl, ∀ a, IsMapOf x x (act.act a) (A.act a)
def TwoChartSt : Prop := ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x x' : Fam G (Fin d)), IsUnivChart G d x → IsUnivChart G d x' →
  ∃ φ φi : Pt R 1 d, IsInvPair φ φi ∧ IsMapOf x' x (𝟙 G) φ ∧ IsMapOf x x' (𝟙 G) φi ∧
    (∀ F F', IsLawOf x F → IsLawOf x' F' → ∀ i, F' i = transF F φ φi i) ∧
    ∀ (f : G ⟶ G) (α α' : Pt R 1 d), IsMapOf x x f α → IsMapOf x' x' f α' → α' = comp1 φi (comp1 α φ)
def DLinSt : Prop := ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (G' : Over (Spec (CommRingCat.of R))) [GrpObj G'] (d : ℕ) (x : Fam G (Fin d))
    (x' : Fam G' (Fin d)) (hx : IsUnivChart G d x) (hx' : IsUnivChart G' d x') (f : G ⟶ G') (φ : Pt R 1 d),
  IsMapOf x x' f φ → ∀ (w : sp (R₀ := R) (DualNumber R) ⟶ G) (hw : IsTan w) (hw' : IsTan (w ≫ f)),
    tcoord hx' (w ≫ f) hw' = (dLin φ).mulVec (tcoord hx w hw)
def SerSt : Prop := ∀ (R : Type) [CommRing R] (κ : Type) [Finite κ] (X : Scheme.{0})
    (p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X), (∀ m, (spMap (jetTruncR R κ m)).left ≫ p (m + 1) = p m) →
  ∀ U : X.Opens, ⊤ ≤ p 0 ⁻¹ᵁ U →
    (∃ τ : Γ(X, U) →+* MvPowerSeries κ R, ∀ f g, HasSer p U f g ↔ g = τ f) ∧
    (∀ (V : X.Opens) (h : U ≤ V) (f : Γ(X, V)) g, HasSer p V f g ↔ HasSer p U ((X.presheaf.map (homOfLE h).op).hom f) g) ∧
    (∀ (Y : Scheme.{0}) (q : X ⟶ Y) (V : Y.Opens) (h : U ≤ q ⁻¹ᵁ V) (f : Γ(Y, V)) g,
      HasSer (fun m => p m ≫ q) V f g ↔ HasSer p U ((q.appLE V U h).hom f) g) ∧
    ∀ (κ' : Type) [Finite κ'] (b : κ → MvPowerSeries κ' R) (ψ : ∀ m, JetR R κ m →ₐ[R] JetR R κ' m),
      (∀ i, constantCoeff (b i) = 0) → (∀ m i, ψ m (zR m i) = toJet m (b i)) →
      ∀ f g, HasSer p U f g → HasSer (fun m => (spMap (ψ m)).left ≫ p m) U f (MvPowerSeries.subst b g)
def SerExSt : Prop := ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x →
  (∀ U : G.left.Opens, ⊤ ≤ η[G].left ⁻¹ᵁ U → ∀ f, ∃! g, IsSer1 x U f g) ∧
  (∀ U : (G ⊗ G).left.Opens, ⊤ ≤ (lift η[G] η[G]).left ⁻¹ᵁ U → ∀ f, ∃! g, IsSer2 x U f g) ∧
  (∀ U : (G ⊗ G ⊗ G).left.Opens, ⊤ ≤ (lift η[G] (lift η[G] η[G])).left ⁻¹ᵁ U → ∀ f, ∃! g, IsSer3 x U f g)
def ValSerSt : Prop := ∀ (A : Type) [CommRing A] (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (j : L.ι)
    (z : Spec (CommRingCat.of A)) (Ψ : Set (Spec (CommRingCat.of A) ⟶ X)), Ψ.Finite → (∀ ψ ∈ Ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U j) →
  ∃ J, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good L z J ∧
    ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε))
      (r : Spec (CommRingCat.of A) ⟶ Y), (∀ k, r ≫ φ k ∈ Ψ) →
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val t r z J).val =
        ((Spec (CommRingCat.of A)).presheaf.germ ⊤ z trivial).hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (fnVal r _ (t.s (fun _ => j)).val))
def RosIdSt : Prop := ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G],
  Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom →
  ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)),
    (∀ a, IsNormRos Lr.L _ _ (u a)) → ∀ (T : Over S) (z : T.left) (J), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good Lr.L z J →
    let v := fun a (x y : T ⟶ G) => ReciprocityTheory.ChartRestriction.G.Geo.Tor.val₂ (u a) z J x y
    let θ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubV c z J
    (∀ a x x' y, v a (x * x') y * θ x x' (y ≫ act.act (star a)) = θ (x ≫ act.act a) (x' ≫ act.act a) y * (v a x y * v a x' y)) ∧
    (∀ a x y y', v a x (y * y') * θ x (y ≫ act.act (star a)) (y' ≫ act.act (star a)) = θ (x ≫ act.act a) y y' * (v a x y * v a x y')) ∧
    (∀ x y, v 1 x y = 1) ∧
    (∀ a b x y, v (a * b) x y = v a (x ≫ act.act b) y * v b x (y ≫ act.act (star a))) ∧
    (∀ a b x y, v (a + b) x y * θ x (y ≫ act.act (star a)) (y ≫ act.act (star b)) =
      θ (x ≫ act.act a) (x ≫ act.act b) y * (v a x y * v b x y)) ∧
    (∀ a x y, v a x y * v (star a) y x = 1)
def FBOfSt : Prop := ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G],
  Function.Surjective (G ⊗ G).hom.appTop.hom → Function.Surjective (G ⊗ G ⊗ G).hom.appTop.hom →
  ∀ (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)),
    (∀ a, IsNormRos Lr.L _ _ (u a)) → ∀ (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x →
    ∀ j : Lr.L.ι, ⊤ ≤ η[G].left ⁻¹ᵁ Lr.L.U j → ∃ B : FB R d O, IsFBOf Lr c act u x j B
structure Related {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d) : Prop where
  inv : IsInvPair φ φi
  ax0 : ev (n := 1) ![0, pt R (n := 1) d 0] ε = 1
  ax1 : ev (n := 1) ![pt R (n := 1) d 0, 0] ε = 1
  law : ∀ i, B'.G.F i = transF B.G.F φ φi i
  act : ∀ a, B'.A.act a = comp1 φi (comp1 (B.A.act a) φ)
  ph1 : B'.ph1 * ev (n := 3) ![addOf B'.G.F (pt R (n := 3) d 0) (pt R (n := 3) d 1), pt R (n := 3) d 2] ε =
    ev (n := 3) ![comp1 φ (pt R (n := 3) d 0), comp1 φ (pt R (n := 3) d 1), comp1 φ (pt R (n := 3) d 2)] B.ph1 * (ev (n := 3) ![pt R (n := 3) d 0, pt R (n := 3) d 2] ε * ev (n := 3) ![pt R (n := 3) d 1, pt R (n := 3) d 2] ε)
  ph2 : B'.ph2 * ev (n := 3) ![pt R (n := 3) d 0, addOf B'.G.F (pt R (n := 3) d 1) (pt R (n := 3) d 2)] ε =
    ev (n := 3) ![comp1 φ (pt R (n := 3) d 0), comp1 φ (pt R (n := 3) d 1), comp1 φ (pt R (n := 3) d 2)] B.ph2 * (ev (n := 3) ![pt R (n := 3) d 0, pt R (n := 3) d 1] ε * ev (n := 3) ![pt R (n := 3) d 0, pt R (n := 3) d 2] ε)
  sy : B'.sy * ε = ev (n := 2) ![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] B.sy * ev (n := 2) ![pt R (n := 2) d 1, pt R (n := 2) d 0] ε
  ad : ∀ a, B'.ad a * ev (n := 2) ![pt R (n := 2) d 0, comp1 (B'.A.act (star a)) (pt R (n := 2) d 1)] ε =
    ev (n := 2) ![comp1 φ (pt R (n := 2) d 0), comp1 φ (pt R (n := 2) d 1)] (B.ad a) * ev (n := 2) ![comp1 (B'.A.act a) (pt R (n := 2) d 0), pt R (n := 2) d 1] ε
def HMulSt : Prop := ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (Lr : RigLB G) (c : CubicalStr G Lr) (O : Type) [CommRing O] [StarRing O] (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G)
    (u : ∀ a : O, LB.Gen (LB.LinComb Lr.L (rosatiφ G (act.act a) (act.act (star a))) rosatiε)),
    (∀ a, (u a).IsGen) → ∀ (d : ℕ) (x x' : Fam G (Fin d)), IsUnivChart G d x → IsUnivChart G d x' →
    ∀ j j' : Lr.L.ι, ⊤ ≤ η[G].left ⁻¹ᵁ Lr.L.U j → ⊤ ≤ η[G].left ⁻¹ᵁ Lr.L.U j' →
    ∀ B B' : FB R d O, IsFBOf Lr c act u x j B → IsFBOf Lr c act u x' j' B' →
    ∃ (φ φi : Pt R 1 d) (ε : PS R 2 d), Related B B' φ φi ε ∧ IsMapOf x' x (𝟙 G) φ ∧
      ∀ (w0 : O) (ρ : LB.Gen (LB.LinComb Lr.L (primφ (act.act w0)) primε)), ρ.IsGen → ∀ (m : ℕ) s (f f' : PS R 1 d),
        IsGermOf Lr.L (act.act w0) ρ x j m s f → IsGermOf Lr.L (act.act w0) ρ x' j' m s f' →
        f' * ev (n := 1) ![pt R (n := 1) d 0, comp1 (B'.A.act w0) (pt R (n := 1) d 0)] ε ^ m = ev (n := 1) ![φ] f
def IntTransSt : Prop := ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B B' : FB R d O)
    (φ φi : Pt R 1 d) (ε : PS R 2 d), Related B B' φ φi ε →
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d), B.IsCanonGauge k h →
    ∃ h' : PS k 2 d, B'.IsCanonGauge k h' ∧ ∀ (w0 : O) (m : ℕ) (f f' : PS k 1 d),
      f' * FB.toK k (ev (n := 1) ![pt R (n := 1) d 0, comp1 (B'.A.act w0) (pt R (n := 1) d 0)] ε) ^ m =
        ev (n := 1) ![fun i => FB.toK k (φ i)] f →
      ∀ (Λ : Type) [Fintype Λ] (u : Λ → Fin d → k) (P : MvPolynomial Λ k),
        B'.nabVal k h' w0 m f' u P = B.nabVal k h w0 m f (fun l => ((dLin φ).map (algebraMap R k)).mulVec (u l)) P
def ChartBCSt : Prop := ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] (β : R →+* R')
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G']
    (π : G'.left ⟶ G.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom β)) π →
    ∀ (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x → ∃ x' : Fam G' (Fin d), IsUnivChart G' d x' ∧
      (∀ F, IsLawOf x F → IsLawOf x' (fun i => MvPowerSeries.map β (F i))) ∧
      (∀ (f : G ⟶ G) (f' : G' ⟶ G') α, f'.left ≫ π = π ≫ f.left → IsMapOf x x f α →
        IsMapOf x' x' f' (fun i => MvPowerSeries.map β (α i))) ∧
      (∀ (U : G.left.Opens) (f : Γ(G.left, U)) g, IsSer1 x U f g →
        IsSer1 x' (π ⁻¹ᵁ U) ((π.app U).hom f) (MvPowerSeries.map β g)) ∧
      (∀ π₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, π₂ ≫ (fst G G).left = (fst G' G').left ≫ π →
        π₂ ≫ (snd G G).left = (snd G' G').left ≫ π → ∀ (U : (G ⊗ G).left.Opens) (f : Γ((G ⊗ G).left, U)) g,
        IsSer2 x U f g → IsSer2 x' (π₂ ⁻¹ᵁ U) ((π₂.app U).hom f) (MvPowerSeries.map β g)) ∧
      ∀ π₃ : (G' ⊗ G' ⊗ G').left ⟶ (G ⊗ G ⊗ G).left, π₃ ≫ (fst G _).left = (fst G' _).left ≫ π →
        π₃ ≫ (snd G _ ≫ fst G G).left = (snd G' _ ≫ fst G' G').left ≫ π →
        π₃ ≫ (snd G _ ≫ snd G G).left = (snd G' _ ≫ snd G' G').left ≫ π →
        ∀ (U : (G ⊗ G ⊗ G).left.Opens) (f : Γ((G ⊗ G ⊗ G).left, U)) g,
        IsSer3 x U f g → IsSer3 x' (π₃ ⁻¹ᵁ U) ((π₃.app U).hom f) (MvPowerSeries.map β g)
def GermExSt : Prop := ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (w : G ⟶ G), η[G] ≫ w = η[G] →
  ∀ (ρ : LB.Gen (LB.LinComb L (primφ w) primε)) (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x →
    ∀ j : L.ι, ⊤ ≤ η[G].left ⁻¹ᵁ L.U j → ∀ m s, ∃! f, IsGermOf L w ρ x j m s f
section Basic₂
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
example : ∑ i, primε i = 1 := by decide
end Basic₂
end GlobalTheory.JetSer


