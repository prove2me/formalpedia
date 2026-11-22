-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:03.297832+00:00
-- url     : https://prove2.me/theorems/79e5ac0c-a785-4dd3-9c1f-42a0195c434a
-- title:
--   Has Arc Data Iff
-- statement:
--   Definitions and structural lemmas for Has Arc Data Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/HasArcDataIff.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
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
open scoped CategoryTheory.Obj Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
structure ArcWit (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b)
    {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (f : O' →+* R) (u : R) (χ : Sp R ⟶ Y.X) where
  t : SAB H (Sp R)
  m : SABMap t Y.t χ
  P : PELUnif I t
  φ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left
  he : eSec P.D.toPre.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A
  w : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ)
  e : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X
  spec :
    letI := H.starRing
    IsGrpPullback P.D.toPre.P.A a.D₀.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P.D.toPre.P.A) (fun _ => 1)) P.D.toPre.rig
      (rigPullOf φ (spMap f) he a.D₀.P.L a.D₀.rig) ∧
    (∀ x, (P.oD.onB.act x).left ≫ φ = φ ≫ (a.oa.onB.act x).left) ∧
    (∀ y, (P.D.toPre.c (e y)).left ≫ φ = spMap f ≫ (a.D₀.c y).left) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (uF : F),
      (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x))) →
      uF = algebraMap (FractionRing R) F (algebraMap R _ u) →
      (∀ y, GenRel w (LB.pullGen _ _ _ (P.D.toPre.psi (e y)) (Out.jFK (R := R) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := O') F)) (uF ^ (a.be y y / 2))) ∧
      ∀ (yF : Sp F ⟶ Xo.XF c), yF ≫ Y.j = Out.jFK (R := R) F ≫ Out.jK R ≫ χ →
        ∀ (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing O') k) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G),
          ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v) ∨
            (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
              HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v)) →
          ∀ (q₀ : Out.QkPt a.D₀ F k) (q : Out.QkPt P.D.toPre F k) (x : Out.TFK (R := R) F ⟶ P.A.A),
            QkExt (algebraMap _ F) p₀ q₀ → q.y = e q₀.y →
            (∀ z, GenRel w (q.g.s (e z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / k))) →
            x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK R) ≫ m.φ = yF ≫ σ.left ≫ Y.m.φ →
            P.ToA F k q x
def valR {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (f : Γ(X, U)) : A :=
  if h : ⊤ ≤ x ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) else 0
def GenRelR {A : Type} [CommRing A] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ))
    {K : Type} [Fintype K] {pt : K → (Sp A ⟶ B)} {pt₀ : K → (Sp A ⟶ B₀)} {ε ε₀ : K → ℤ}
    (t : LB.Gen (LB.LinComb M pt ε)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε₀)) : Prop :=
  (∀ k, pt k ≫ φ = pt₀ k) ∧ ∀ (j : K → M.ι) (j₀ : K → M₀.ι),
    (∀ k, ⊤ ≤ pt k ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀ k, j k)) →
    valR (𝟙 (Sp A)) _ (t.s j).val =
      (∏ k, valR (pt k) _ ((show (Γ(B, (LB.div (M₀.pull φ) M).U (fun _ => j₀ k, j k)))ˣ from
        w.s (fun _ => j₀ k, j k)) ^ (-ε k)).val) * valR (𝟙 (Sp A)) _ (t₀.s j₀).val
def IsRigIso {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F)) : Prop :=
  w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (m.rigPull L.L L.rig)
def eTwoPi (w : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * w)
def SumsAt (s : PowerSeries ℂ) (w x : ℂ) : Prop := HasSum (fun n => PowerSeries.coeff n s * eTwoPi w ^ n) x
def IsThetaFrameAt {g : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] (L : RigLB G) (y : Sp ℂ ⟶ S)
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (θ : (Fin g → ℂ) → ℂ) (fr : L.L.ι → (Fin g → ℂ) → ℂ) : Prop :=
  (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.L.U j}) ∧ (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
      fr j z = valAt' (e z) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val * fr j' z) ∧
    (∀ j, ⊤ ≤ e 0 ⁻¹ᵁ L.L.U j → fr j 0 = valAt' y ((L.L.pull (eSec G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val) ∧
    ∃ s : (L.L.pull (pullback.fst G.hom y)).Sec, ∀ j z (x : Sp ℂ ⟶ pullback G.hom y),
      x ≫ pullback.fst _ _ = e z → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ e z ⁻¹ᵁ L.L.U j →
      valAt' x ((L.L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z
def thetaCharOff {g : ℕ} (S : Finset (Fin g)) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (z : Fin g → ℂ) : ℂ :=
  ∑' n : {n : Fin g → ℤ // ∀ k ∈ S, n k = 0},
    Complex.exp (Real.pi * Complex.I * (((fun i => (n.1 i : ℂ)) + a) ⬝ᵥ τ.mulVec ((fun i => (n.1 i : ℂ)) + a)) +
      2 * Real.pi * Complex.I * (((fun i => (n.1 i : ℂ)) + a) ⬝ᵥ (z + b)))
def IsFnInRigFrame {g : ℕ} (D₀ : Out.DegPre ℂ) (e : (Fin g → ℂ) → (Sp ℂ ⟶ D₀.P.A.left)) (th : D₀.P.L.Sec)
    (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∃ fr : D₀.P.L.ι → (Fin g → ℂ) → ℂ,
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ D₀.P.L.U j}) ∧ (∀ j z, ⊤ ≤ e z ⁻¹ᵁ D₀.P.L.U j → fr j z ≠ 0) ∧
    (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (D₀.P.L.U j ⊓ D₀.P.L.U j') →
      fr j z = valAt' (e z) (D₀.P.L.U j ⊓ D₀.P.L.U j') (D₀.P.L.g j j').val * fr j' z) ∧
    (∀ j, ⊤ ≤ e 0 ⁻¹ᵁ D₀.P.L.U j →
      fr j 0 = valAt' (𝟙 (Sp ℂ)) ((D₀.P.L.pull (eSec D₀.P.A)).U (fun _ => j)) (D₀.rig.s (fun _ => j)).val) ∧
    ∀ j z, ⊤ ≤ e z ⁻¹ᵁ D₀.P.L.U j → valAt' (e z) (D₀.P.L.U j) (th.f j) = θ z * fr j z
section ThetaShiftProofs
variable [Algebra (FractionRing ℂ) ℂ]
def chiVal {D₀ : Out.DegPre ℂ} (g : Out.GtPtF D₀ ℂ) (χ : D₀.X) (j : Fin 4 → D₀.P.L.ι) : ℂ :=
  valR (A := ℂ) (𝟙 (Sp ℂ)) _ ((g.s χ).s j).val
def IsTorusPt {D₀ : Out.DegPre ℂ} (g : Out.GtPtF D₀ ℂ) (x : D₀.X → ℂ) : Prop :=
  g.b = Out.DegPre.zeroF D₀ ℂ ∧ ∀ χ j, LB.Coh D₀.P.L (Out.DegPre.gtφ D₀ ℂ g.b χ) j →
    ⊤ ≤ LB.wchart D₀.P.L (Out.DegPre.gtφ D₀ ℂ g.b χ) j → chiVal g χ j = x χ
structure HolArc (Y : Model Xo c β) (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β))
    (χ : Sp (PowerSeries ℂ) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) where
  i : Fin Fu.n
  T : ℝ
  P₀ : (Fu.Di i).La →+ (Fin g → ℂ)
  N : (Fu.Di i).La →+ (Fin g → ℂ)
  Pw : ℂ → ((Fu.Di i).La →+ (Fin g → ℂ))
  Pw_eq : ∀ w v, Pw w v = P₀ v + w • N v
  y : (Fu.Di i).La →ₗ[𝓞 E] a.D₀.X
  y_onto : Function.Surjective y
  ex₀ : (Fin g → ℂ) → Out.GtPtF a.D₀ ℂ
  period : ∀ w : ℂ, T < w.im → IsPeriod (Fu.Di i) ty (Pw w)
  add : ∀ z z', (ex₀ z).IsAdd (ex₀ z') (ex₀ (z + z'))
  onto : Function.Surjective ex₀
  lin : letI := H.starRing; ∀ (x : 𝓞 E) z, GtAct a.oa x (ex₀ z) (ex₀ (fun k => ty k (x : E) * z k))
  hol_b : IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ _ from (ex₀ z).b.left))
  hol_chi : ∀ x j, DifferentiableOn ℂ (fun z => chiVal (ex₀ z) x j)
    {z | ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφ a.D₀ ℂ (ex₀ z).b x) j}
  ker : ∀ z, (ex₀ z).IsZero ↔ ∃ v, y v = 0 ∧ z = P₀ v
  iota : ∀ v, Out.GtPtF.IsIota (y v) (ex₀ (P₀ v))
  shift : ∀ (w : ℂ) v, IsTorusPt (ex₀ (w • N v)) (fun x => eTwoPi (w * a.be (y v) x))
  levelA : ∀ v, ∃ q : Out.QkPt a.D₀ ℂ l.A, q.y = y (Fu.t i v) ∧ q.g = ex₀ ((l.A : ℂ)⁻¹ • P₀ (Fu.t i v)) ∧
    ∀ q', QkExt (algebraMap _ ℂ) (a.etaA v) q' → Out.QkPt.Equiv a.D₀ ℂ q q'
  levelM : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∃ q : Out.QkPt a.D₀ ℂ l.M, q.y = y (Fu.t i v) ∧ q.g = ex₀ ((l.M : ℂ)⁻¹ • P₀ (Fu.t i v)) ∧
      ∀ q', QkExt (algebraMap _ ℂ) (a.eta v) q' → Out.QkPt.Equiv a.D₀ ℂ q q'

  riemann : ∀ v, (∀ v', y v' = 0 → (Fu.Di i).EF v v' = 0) ↔
    (y v = 0 ∧ ∀ (s : ℂ), ∃ x, IsTorusPt (ex₀ (s • P₀ v)) x ∧ ∀ v', x (y v') = eTwoPi (-(s * (Fu.Di i).EF v v')))

  point : ∀ (U : Y.X.Opens) (f : Γ(Y.X, U)), ⊤ ≤ χ ⁻¹ᵁ U → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im →
    ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u i (Pw w) → yF ≫ pullback.snd _ _ = spMap bF →
      ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ U ∧ SumsAt (valR χ U f) w (valAt' (yF ≫ Y.j) U f)

  diff : ∀ (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G)
    (V : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, V)),
    IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (ex₀ z).b.left)) z₀ ν.b.left →
    (∀ x j, ⊤ ≤ LB.wchart a.D₀.P.L (Out.DegPre.gtφT a.D₀ (epsR ℂ) ν.b x) j →
      valR (A := DualNumber ℂ) (𝟙 _) _ ((ν.s x).s j).val =
        TrivSqZeroExt.inl (chiVal (ex₀ 0) x j) + TrivSqZeroExt.inr (fderiv ℂ (fun z => chiVal (ex₀ z) x j) 0 z₀)) →
    (∀ (n : ℕ) (ρ : DualNumber (PowerSeries ℂ) →+* DualNumber (PowerSeries ℂ ⧸ Ideal.span {PowerSeries.X} ^ (n + 1)))
      (κ : DualNumber ℂ →+* DualNumber (PowerSeries ℂ ⧸ Ideal.span {(PowerSeries.X : PowerSeries ℂ)} ^ (n + 1)))
      (vn : Sp (DualNumber (PowerSeries ℂ ⧸ Ideal.span {(PowerSeries.X : PowerSeries ℂ)} ^ (n + 1))) ⟶
        (Out.thickObj (PowerSeries ℂ) (Ideal.span {PowerSeries.X}) n W.t.G).left),
      (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ r)) → ρ DualNumber.eps = DualNumber.eps →
      (∀ r, κ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (PowerSeries.C r))) →
      κ DualNumber.eps = DualNumber.eps →
      vn ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left = spMap ρ ≫ v.left →
      ∀ x, GenRelR W.w (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) vn) (LB.pullGen _ _ _ (ν.s x) (spMap κ))) →
    ⊤ ≤ (v.left ≫ W.m.φ) ⁻¹ᵁ V → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im →
      ∀ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left), (∀ z, xF z ≫ Y.m0.toSABMap.φ = (Fu.ex i (Pw w) z).left ∧
        xF z ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF) →
        SumsAt (TrivSqZeroExt.snd (valR (A := DualNumber (PowerSeries ℂ)) (v.left ≫ W.m.φ) V f)) w
          (fderiv ℂ (fun z => valAt' (xF z ≫ Y.m.φ) V f) 0 z₀)

  theta : ∀ (th : a.D₀.P.L.Sec) (σ : Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Fu.Di i).La) (S : Finset (Fin g)) (h : Matrix (Fin g) (Fin g) ℂ)
    (τ : ℂ → Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ)
    (w₂ : LB.Iso W.P.U.LG.L (Y.t.PP.L.pull W.m.φ)) (w₁ : LB.Iso Y.oF.t.PP.L (Y.t.PP.L.pull Y.m.φ))
    (w₀ : LB.Iso Y.oF.t.PP.L (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ)),
    (∃ j, th.f j ≠ 0) → (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 (show _ from σ) fam) →
    (∀ (j : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι) (V : W.P.D.toPre.P.A.left.Opens)
      (h₁ : V ≤ LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j)
      (h₂ : V ≤ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀),
      LB.Coh W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j →
      (W.φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (W.w.s (fun _ => j₀, j 1)).val * resG _ h₁ ((fam 0).f j)) →
    (∀ u v, (Fu.Di i).EF (bas u) (bas v) = -omegaStd u v) → (∀ u, y (bas u) = 0 ↔ ∀ k ∈ S, u (.inr k) = 0) →
    (∀ w k, h.mulVec (Pw w (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      h.mulVec (Pw w (bas (Pi.single (.inr k) 1))) = (τ w).mulVec (Pi.single k 1)) →
    (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) →
    IsRigIso W.m.cm W.P.U.LG Y.t.PP w₂ → IsRigIso Y.m.cm Y.oF.t.PP Y.t.PP w₁ →
    IsRigIso Y.m0.toSABMap.cm Y.oF.t.PP Xo.univ.t.PP w₀ →
    (∃ w fr, T < w.im ∧ IsThetaFrameAt Xo.univ.t.PP (Fu.u i (Pw w)) (fun z => (Fu.ex i (Pw w) z).left)
      (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr) →
    ∃ κ : ℂ, κ ≠ 0 ∧ (∀ k ∈ S, c₁ k = 0) ∧
      (∀ w : ℂ, T < w.im → IsFnInRigFrame a.D₀ (fun z => (show Sp ℂ ⟶ _ from (ex₀ z).b.left)) th
        (fun z => κ * thetaCharOff S (τ w) c₁ c₂ (h.mulVec z))) ∧
      ∀ (U : Y.X.Opens) (s : ∀ j, Γ(Y.t.G.left, Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j)) (r : PowerSeries ℂ),
      ⊤ ≤ χ ⁻¹ᵁ U → s ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ U) →
      (∀ (j : Y.t.PP.L.ι) (k : W.P.U.LG.L.ι) (V : W.t.G.left.Opens)
        (h₁ : V ≤ W.m.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ U ⊓ Y.t.PP.L.U j))
        (h₂ : V ≤ (LB.div (Y.t.PP.L.pull W.m.φ) W.P.U.LG.L).U (fun _ => j, k))
        (h₃ : V ≤ LB.wchart W.P.U.LG.L (fun _ : Fin 1 => 𝟙 W.t.G.left) (fun _ => k)),
        (W.m.φ.appLE _ _ h₁).hom (s j) =
          resG _ h₂ (w₂.s (fun _ => j, k)).val * constFn W.t.G.hom V r * resG _ h₃ (σ.f (fun _ => k))) →
      ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∃ rw : ℂ, SumsAt r w rw ∧
        ∀ fr, IsThetaFrameAt Xo.univ.t.PP (Fu.u i (Pw w)) (fun z => (Fu.ex i (Pw w) z).left)
            (fun z => thetaChar (τ w) c₁ c₂ (h.mulVec z)) fr →
          ∀ (z : Fin g → ℂ) (x : Sp ℂ ⟶ Y.oF.t.G.left) (j : Y.t.PP.L.ι) (k : Y.oF.t.PP.L.ι) (j₀ : Xo.univ.t.PP.L.ι),
            x ≫ Y.m0.toSABMap.φ = (Fu.ex i (Pw w) z).left → x ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF →
            ⊤ ≤ x ⁻¹ᵁ (LB.div (Y.t.PP.L.pull Y.m.φ) Y.oF.t.PP.L).U (fun _ => j, k) →
            ⊤ ≤ x ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) Y.oF.t.PP.L).U (fun _ => j₀, k) →
            valAt' x _ (w₀.s (fun _ => j₀, k)).val * valAt' (x ≫ Y.m.φ) _ (s j) =
              valAt' x _ (w₁.s (fun _ => j, k)).val * (κ * rw * thetaChar (τ w) c₁ c₂ (h.mulVec z) * fr j₀ z)
end ThetaShiftProofs
def ToroidalArchimedeanCondition : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (bF : c.F →+* ℂ)
    [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (a : ArcIn D l β ℂ (bF.comp β))
    (χ : Sp (PowerSeries ℂ) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty),
    bF (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 → IsTypeFn H D.p D.q ty →
    (∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A) →
    χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β) →
    (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) →
    Nonempty (HolArc Y bF a χ W Fu)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


