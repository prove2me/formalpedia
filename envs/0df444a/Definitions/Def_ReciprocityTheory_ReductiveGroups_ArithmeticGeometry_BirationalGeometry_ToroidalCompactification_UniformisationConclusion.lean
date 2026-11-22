-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:28.79926+00:00
-- url     : https://prove2.me/theorems/115fa2d6-cc2b-4b7e-9c72-0c1c93a224ec
-- title:
--   Uniformisation Conclusion
-- statement:
--   Definitions and structural lemmas for Uniformisation Conclusion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/UniformisationConclusion.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
@[reducible] def Host.starRing (H : Host E) : StarRing (𝓞 E) where
  star := H.bar
  star_involutive a := by
    apply RingOfIntegers.ext
    show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  star_mul a b := by show H.bar (a * b) = H.bar b * H.bar a; rw [map_mul, mul_comm]
  star_add a b := map_add H.bar a b
def OAct.toRingAct {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (a : OAct O G) :
    Out.RingAct G O :=
  ⟨a.act, a.hom, a.one, fun x y => by rw [mul_comm, a.mul], fun x y => a.add x y⟩
def ofRingAct {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (a : Out.RingAct G O) :
    OAct O G :=
  ⟨a.act, a.hom, a.map_one, fun x y => by rw [mul_comm, a.map_mul], fun x y => a.map_add x y⟩
open Classical in

def valF {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) : F :=
  if h : ⊤ ≤ x ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((x.appLE U ⊤ h).hom f) else 0
section Data
variable {R : Type} [CommRing R] [IsDomain R] {O : Type} [CommRing O] [StarRing O]
def TraceFormTwistIso (D : Out.DegPre R) [Module O D.X] (oa : D.OAct O) (w0 : O) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.P.A.left, (oa.onB.act w0).left, (toUnit D.P.A ≫ η[D.P.A]).left]
      ![1, -2, -1, 2]),
    u.IsGen ∧ LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (eSec D.P.A)) (LB.oneGen D.P.L) ∧
    ∀ y, LB.Gen.Corr D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (D.tau y (w0 • y)) (LB.pullGen D.P.L _ _ u (D.xK y)))
      (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK)
def PsiUnitOn (D : Out.DegPre R) (χ : D.X) (U : Set (Sp R)) : Prop :=
  ∀ (j : PUnit → D.P.L.ι) (V : (Sp R).Opens), IsAffineOpen V → (V : Set (Sp R)) ⊆ U →
    V ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) →
    ∀ h : Out.jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U j,
      ∃ r : Γ(Sp R, V), IsUnit r ∧
        ((Out.jK R).app V).hom r = ((Out.TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val
variable {D : Out.DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
def GtAct [Module O D.X] (oa : D.OAct O) (a : O) (g g' : Out.GtPtF D F) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (Out.rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) Out.rosatiε), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (Out.zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
          (LB.pullGen D.P.L _ _ u (lift (Out.DegPre.cF D F χ) g.b).left)) (g'.s χ)
def QkAdd {k : ℕ} (p p' p'' : Out.QkPt D F k) : Prop :=
  ∃ q : Out.QkPt D F k, q.y = p.y + p'.y ∧ p.g.IsAdd p'.g q.g ∧ Out.QkPt.Equiv D F q p''
def QkAct [Module O D.X] (oa : D.OAct O) {k : ℕ} (a : O) (p p' : Out.QkPt D F k) : Prop :=
  ∃ q : Out.QkPt D F k, q.y = a • p.y ∧ GtAct oa a p.g q.g ∧ Out.QkPt.Equiv D F q p'
def QkExt {F' : Type} [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F') {k : ℕ} (p : Out.QkPt D F k)
    (p' : Out.QkPt D F' k) : Prop :=
  p'.y = p.y ∧ p'.g.b.left = spMap f ≫ p.g.b.left ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (p'.g.s χ) (LB.pullGen D.P.L _ _ (p.g.s χ) (spMap f))
end Data
variable {H : Host E}
structure PELUnif {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) where
  D : Out.DegData R I
  [mod : Module (𝓞 E) D.toPre.X]
  oD : letI := H.starRing; D.toPre.OAct (𝓞 E)
  A : Out.PolAV (Sp (FractionRing R))
  oA : letI := H.starRing; A.OAct (𝓞 E)
  U : Out.Unif I D A t.G
  bundle : U.LG = t.PP
  lin : letI := H.starRing; U.toUnifPre.OLinear (𝓞 E) oD oA t.act.toRingAct
  w0 : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0
attribute [instance] PELUnif.mod
def PELUnif.ToA {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t)
    (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (p : Out.QkPt P.D.toPre F k)
    (x : Out.TFK (R := R) F ⟶ P.A.A) : Prop :=
  Out.QkToAkU P.U.toUnifPre F k p x
def PELUnif.TorsionIso {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t) : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
    ∃ f : Out.QkPt P.D.toPre F k → (Out.TFK (R := R) F ⟶ P.A.A),
      (∀ p x, P.ToA F k p x ↔ x = f p) ∧ (∀ x, x ^ k = 1 → ∃ p, f p = x) ∧
      (∀ p p', f p = f p' ↔ Out.QkPt.Equiv P.D.toPre F p p') ∧
      (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') ∧
      (∀ a p p', QkAct P.oD a p p' → f p' = f p ≫ P.oA.act a) ∧
      ∀ p p' (z : Fˣ), Out.WeilQkIs P.D.toPre F k p p' z ↔ Out.WeilIs P.A.A P.A.L k (f p) (f p') (unitOn z)
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def Model.SplitFibres (Y : Model Xo c β) : Prop :=
  ∀ x : Y.X, ∃ (k : Type) (_ : Field k) (_ : Algebra (Y.X.residueField x) k),
    FiniteDimensional (Y.X.residueField x) k ∧ Algebra.IsSeparable (Y.X.residueField x) k ∧
    ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField x) k)) ≫ Y.X.fromSpecResidueField x)).obj Y.t.G)
def UniformisationConclusion {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (U : Set (Sp R)) : Prop :=
  ∃ P : PELUnif (IsLocalRing.maximalIdeal R) t, (∀ y, PsiUnitOn P.D.toPre y U) ∧ P.TorsionIso
def Model.N3 (Y : Model Xo c β) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R →
    IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty →
      (∃ S : SplitExt (Sp (IsLocalRing.ResidueField R)),
        S.IsGt ((Over.pullback (spMap (IsLocalRing.residue R))).obj t.G)) →
      UniformisationConclusion t (ξ ⁻¹' abLocus Y.t.G)
structure TateIsoQ (D : Datum H) {R : Type} [CommRing R] [IsDomain R] (D₀ : Out.DegPre R) [Module (𝓞 E) D₀.X]
    (oa : letI := H.starRing; D₀.OAct (𝓞 E)) (F : Type) [Field F] [Algebra (FractionRing R) F] where
  ζ : ℕ → Fˣ
  ζ_prim : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n
  ζ_pow : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n
  ev : ∀ n : ℕ, D.La → Out.QkPt D₀ F n
  add : ∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))
  lin : letI := H.starRing; ∀ n, 0 < n → ∀ (x : 𝓞 E) a, QkAct oa x (ev n a) (ev n (x • a))
  ker : ∀ n, 0 < n → ∀ a b, Out.QkPt.Equiv D₀ F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e
  onto : ∀ n, 0 < n → ∀ p, ∃ a, Out.QkPt.Equiv D₀ F (ev n a) p
  tower : ∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : Out.QkPt D₀ F n,
    q.y = (ev (n * m) a).y ∧ Out.GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ Out.QkPt.Equiv D₀ F q (ev n a)
  isom : ∀ n, 0 < n → ∀ a b, Out.WeilQkIs D₀ F n (ev n a) (ev n b) ((ζ n ^ D.EF a b : Fˣ) : F)
structure ArcIn (D : Datum H) (l : Level H) {c : Coeff l} {O : Type} [CommRing O] (β : O →+* c.F) (O' : Type)
    [CommRing O'] [IsDomain O'] (b : O →+* O') where
  D₀ : Out.DegPre O'
  [mod : Module (𝓞 E) D₀.X]
  oa : letI := H.starRing; D₀.OAct (𝓞 E)
  nontriv : Nontrivial D₀.X
  even : D₀.PsiEven
  bimult : D₀.TauBimult
  gen : ∀ y, PsiUnitOn D₀ y Set.univ
  w0 : letI := H.starRing; TraceFormTwistIso D₀ oa H.w0
  be : LinearMap.BilinForm ℤ D₀.X
  be_symm : ∀ y z, be y z = be z y
  be_pos : ∀ y, y ≠ 0 → 0 < be y y
  be_adj : ∀ (a : 𝓞 E) y z, be (a • y) z = be y (H.bar a • z)
  be_dvd : ∀ y z, (2 * l.M' : ℤ) ∣ be y z
  eta : D.La → Out.QkPt D₀ (FractionRing O') l.M
  etaA : D.La → Out.QkPt D₀ (FractionRing O') l.A
  geom : letI := H.starRing
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing O') F] (r z : O),
      ((β r : c.F) : ℂ) = H.rt0 → ((β z : c.F) : ℂ) = zeta l.A →
      ∀ f : O' →+* F, f = (algebraMap (FractionRing O') F).comp (algebraMap O' _) →
      (∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct oa.onB.toRingAct) (spMap f) τ n ∧
        n + Module.finrank (𝓞 E) D₀.X = if τ H.rt = f (b r) then D.p else D.q) ∧
      ∃ I : TateIsoQ D D₀ oa F, (I.ζ l.A : F) = f (b z) ∧
        (∀ a q, QkExt (algebraMap _ F) (etaA a) q → Out.QkPt.Equiv D₀ F q (I.ev l.A a)) ∧
        ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∀ q,
          QkExt (algebraMap _ F) (eta a) q → Out.QkPt.Equiv D₀ F q (I.ev l.M a)
attribute [instance] ArcIn.mod
def GenRel {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ : B ⟶ B₀} (w : LB.Iso M (M₀.pull φ))
    {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb M pt ε)) (t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)) (x : F) : Prop :=
  (∀ k, pt k ≫ φ = pt₀ k) ∧ ∀ (j : K → M.ι) (j₀ : K → M₀.ι),
    (∀ k, ⊤ ≤ pt k ⁻¹ᵁ (LB.div (M₀.pull φ) M).U (fun _ => j₀ k, j k)) →
    valF (𝟙 (Sp F)) _ (t.s j).val =
      x * (∏ k, valF (pt k) _ (w.s (fun _ => j₀ k, j k)).val ^ (-ε k)) * valF (𝟙 (Sp F)) _ (t₀.s j₀).val
def Model.HasArcData (Y : Model Xo c β) {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b)
    {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (f : O' →+* R) (u : R) (χ : Sp R ⟶ Y.X) : Prop :=
  ∃ (t : SAB H (Sp R)) (m : SABMap t Y.t χ) (P : PELUnif I t) (φ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.D.toPre.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X),
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
def Model.N4 (Y : Model Xo c β) : Prop :=
  ∀ (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : O →+* O') (ϖ : O') (a : ArcIn D l β O' b),
    ((IsField O' ∧ ϖ = 1) ∨ (IsDiscreteValuationRing O' ∧ Irreducible ϖ ∧ IsAdicComplete (Ideal.span {ϖ}) O')) →
    ∃ χ : Sp (PowerSeries O') ⟶ Y.X,
      (∀ χ' : Sp (PowerSeries O') ⟶ Y.X, χ' = χ ↔
        χ' ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧
        (∀ x : Sp (PowerSeries O'), χ' x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧
        (∀ x : Sp (PowerSeries O'), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ' x ∈ Set.range Y.j) ∧
        Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O')) PowerSeries.X χ') ∧
      (Irreducible ϖ → ∀ (y' : Sp O' ⟶ Y.X) (ev : PowerSeries O' →+* O'), y' ≫ Y.s = spMap b →
        Set.range (Out.jK O' ≫ y') ⊆ Set.range Y.j →
        Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id O') ϖ y' →
        (∀ x, ev (PowerSeries.C x) = x) → ev PowerSeries.X = ϖ → spMap ev ≫ χ = y')
def PartI : Prop :=
  N0 ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q →
    ∀ Xo : ∀ l : Level H, Moduli D l,
      ∃ Y : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W,
        (∀ p W hp hW, N2 (Y p W hp hW) ∧ ∀ i, (Y p W hp hW i).SplitFibres ∧ (Y p W hp hW i).N3 ∧ (Y p W hp hW i).N4) ∧ N6 Y
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


