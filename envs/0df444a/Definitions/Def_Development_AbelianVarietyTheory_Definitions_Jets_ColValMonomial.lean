-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
-- name    : Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:51.456081+00:00
-- url     : https://prove2.me/theorems/81a78bce-0197-440c-ac75-f8c08fb6af78
-- title:
--   Col Val Monomial
-- statement:
--   Definitions and structural lemmas for Col Val Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/ColValMonomial.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FamGerm
structure Pt1 (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (F : Type) [Field F] [Algebra (FractionRing V) F] where
  ϖ : V
  hϖ : Irreducible ϖ
  complete : IsAdicComplete (maximalIdeal V) V
  t : SAB H (Sp V)
  P : PELUnif (maximalIdeal V) t
  tors : P.TorsionIso
  Q : P.D.toPre.X → ℤ
  hQ : QForm.IsQ P.D.toPre ϖ Q
  v : AddValuation F (WithTop ℚ)
  hv : ValOver ϖ F v
  d : ℕ
  x : JetSer.Fam t.G (Fin d)
  hx : Chart.IsUnivChart t.G d x
  j : P.U.LG.L.ι
  hj : ⊤ ≤ η[t.G].left ⁻¹ᵁ P.U.LG.L.U j
  u : letI := H.starRing; ∀ a : 𝓞 E, LB.Gen (LB.LinComb P.U.LG.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε)
  hu : letI := H.starRing; ∀ a, JetSer.IsNormRos P.U.LG.L _ _ (u a)
  B : letI := H.starRing; FB V d (𝓞 E)
  hB : letI := H.starRing; JetSer.IsFBOf P.U.LG P.U.cubG t.act u x j B
  ρ : LB.Gen (LB.LinComb P.U.LG.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)
  hρ : ρ.IsGen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)
def Pt1.Germ (q : ℕ) (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d) : Prop :=
  ∃ (l : ℕ) (c : Fin l → F) (σ : Fin l → H0 y.P.U.LG.L q) (fi : Fin l → ∀ α, y.P.D.toPre.SecB q α) (g : Fin l → PS V 1 y.d) (r : PS V 1 y.d),
    (∀ i e, y.P.U.ExpandsAt e q (σ i) (fi i)) ∧
    (∀ α, GeneratorPullback.SecLin y.P.D.toPre.P.L (DegPre.famφ y.P.D.toPre F α) (DegPre.famε q) (s.s α) (y.P.D.toPre.famφB α) (DegPre.famε q)
      (fun i => fi i α) (DegPre.prB y.P.D.toPre F).left (fun i => scal (fst (TF (R := V) F) y.P.D.toPre.P.A).left (c i))) ∧
    JetSer.IsSer1 y.x _ (y.ρ.s (fun _ => y.j)).val r ∧
    (∀ i, ∃ S, JetSer.IsSer1 y.x _ ((σ i).f (fun _ => y.j)) S ∧ g i * r ^ q = S) ∧
    f = ∑ i, MvPowerSeries.C (c i) * MvPowerSeries.map (TWO.algVF (V := V) (F := F)) (g i)
def Pt1.Red (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ) : Prop :=
  0 ≤ Cc ∧ 0 ≤ M₀ ∧ (∀ i, (y.Q (b i) : ℝ) ≤ Cc) ∧ ∀ i z, |(QForm.bOf y.P.D.toPre y.Q (b i) z : ℝ)| ≤ M₀ * y.Q z
def Pt1.Transl (q : ℕ) (c : 𝓞 E) (s h : Fam y.P.D.toPre F q) : Prop :=
  ∃ (p : QkPt y.P.D.toPre F q) (x : TFK (R := V) F ⟶ y.P.A.A)
    (w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F p.g.b) (DegPre.lineε q))) (ζ : F) (t' : Fam y.P.D.toPre F q),
    y.P.ToA F q p x ∧ (letI := H.starRing; x ≫ y.P.oA.act c = 1) ∧ w.IsGen ∧ ζ ≠ 0 ∧ FinOrd y.P.D F q p w ζ ∧
      PhiRel y.P.D.toPre F q p w s t' ∧ Fam.IsSmul y.P.D.toPre F ζ t' h
def Pt1.CharAt (a : 𝓞 E) (p : ℕ) {Λ : Type} (e : Λ → Fin y.d → TWO.Ov y.v) (yy : Λ → TWO.Ov y.v) : Prop :=
  letI := H.starRing
  ∃ (κ : (TFK (R := V) F ⟶ y.P.A.A) → Fˣ) (Z : Over (Spec (CommRingCat.of (TWO.Ov y.v)))) (jZ : Z.left ⟶ y.t.G.left) (k : Γ(Z.left, ⊤)),
    (∀ z z', z ≫ y.P.oA.act a = 1 → z' ≫ y.P.oA.act a = 1 → κ (z * z') = κ z * κ z') ∧
    IsFinite Z.hom ∧ Flat Z.hom ∧ IsReduced (Pdiv.specO (TWO.Ov y.v) F ⊗ Z).left ∧
    jZ ≫ y.t.G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom (TWO.fO y.v y.hϖ y.hv)) ∧
    jZ ≫ (y.t.act.act a).left = jZ ≫ (1 : y.t.G ⟶ y.t.G).left ∧
    (∀ (c : Pdiv.specO (TWO.Ov y.v) F ⟶ Z) (z : TFK (R := V) F ⟶ y.P.A.A),
      (z ≫ y.P.U.gen.inv).left ≫ pullback.fst y.t.G.hom (jK V) = c.left ≫ jZ → JetSer.fnVal c.left ⊤ k = (κ z : F)) ∧
    ∀ l, ∃ (w : Pdiv.specO (TWO.Ov y.v) (DualNumber (TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)})) ⟶ Z)
      (φ : Chart.JetR V (Fin y.d) 1 →+* DualNumber (TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)})),
      (∀ i, φ (Chart.zR 1 i) = TrivSqZeroExt.inr (Ideal.Quotient.mk _ (e l i))) ∧
      w.left ≫ jZ = Spec.map (CommRingCat.ofHom φ) ≫ (y.x 1).left ∧
      JetSer.fnVal w.left ⊤ k = 1 + TrivSqZeroExt.inr (Ideal.Quotient.mk _ (yy l))
def Pt1.colVal [Algebra V F] [CharZero F] (h : PS F 2 y.d) (q : ℕ) {Λ : Type} [Fintype Λ] (e : Λ → Fin y.d → F) {n : ℕ}
    (P : MvPolynomial (Λ × Fin n) F) (f : Fin n → PS F 1 y.d) : F :=
  letI := H.starRing
  ∑ mo ∈ P.support, P.coeff mo * ∏ b, y.B.nabVal F h H.w0 q (f b) e (MvPolynomial.monomial (colM mo b) 1)
def minorsP (k : Type) [CommRing k] {T : Type} [Fintype T] [DecidableEq T] {r : T → ℕ} {n : ℕ} (col : ∀ τ, Fin (r τ) → Fin n)
    (m : ∀ τ, Fin (r τ) → ℕ) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k :=
  ∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s
def GermExSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ q : ℕ, 1 ≤ q → ∃ gm : Fam y.P.D.toPre F q →ₗ[F] PS F 1 y.d, ∀ s f, y.Germ q s f ↔ f = gm s
def GermValSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ q : ℕ, 1 ≤ q → ∀ (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d), y.Germ q s f → (∀ r : ℚ, (∀ χ, VGe y.P.D F y.v q χ (s.s χ) r) → ∀ mo, ((r : ℚ) : WithTop ℚ) ≤ y.v (MvPowerSeries.coeff mo f)) ∧ ∀ (χ : y.P.D.toPre.X) (x : F) (r r' : ℚ), Val0 y.P.D F q χ (s.s χ) x → y.v x = (r : ℚ) → r < r' → (∀ β, β ≠ χ → VGe y.P.D F y.v q β (s.s β) r') → y.v (MvPowerSeries.constantCoeff f) = (r : ℚ)
def JetsSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ q n : ℕ, 4 * n + 4 ≤ q → (n : ℝ) * M₀ < q → ∃ gm : ℚ, 0 ≤ gm ∧ (gm : ℝ) ≤ (n : ℝ) ^ 2 * Cc / q ∧ ∀ g : PS F 1 y.d, (∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo g)) → ∃ (s : Fam y.P.D.toPre F q) (f : PS F 1 y.d), NuGe y.P.D y.Q F y.v q s (-gm) ∧ y.Germ q s f ∧ (∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo f)) ∧ ∀ mo : Fin 1 × Fin y.d →₀ ℕ, mo.degree ≤ n → MvPowerSeries.coeff mo f = MvPowerSeries.coeff mo g
def PullGermSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (a : 𝓞 E) (N k : ℕ), 1 ≤ N → 4 ≤ k → a * star a = (N : 𝓞 E) → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∃ (w : PS V 1 y.d) (κ : Vˣ), FB.toK F w = FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (N : F) • y.B.hL F h H.w0) ∧ ∀ (s : Fam y.P.D.toPre F k) (s' : Fam y.P.D.toPre F (k * N)) (f : PS F 1 y.d), PullAl y.P.D F y.P.oD a k N s s' → y.Germ k s f → y.Germ (k * N) s' (MvPowerSeries.C (algebraMap V F κ) * (ev (n := 1) ![y.B.actK F a] f * FB.toK F w ^ k))
def EigGermSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (a : 𝓞 E) (p k : ℕ), p.Prime → 4 ≤ k → a * star a = (p : 𝓞 E) → ∀ (Λ : Type) (e : Λ → Fin y.d → TWO.Ov y.v) (yy : Λ → TWO.Ov y.v) (α : Λ → TWO.Ov y.v), (∀ l, α l ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ l, (dAct F y.B a).mulVec (fun i => (e l i : F)) = (α l : F) • fun i => (e l i : F)) → y.CharAt a p e yy → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), Nat.Coprime p k → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∃ (pt : QkPt y.P.D.toPre F (k * p)) (x : TFK (R := V) F ⟶ y.P.A.A), y.P.ToA F (k * p) pt x ∧ x ≫ y.P.oA.act (star a) = 1 ∧ ∀ (w : LB.Gen (LB.LinComb y.P.D.toPre.P.L (DegPre.lineφ y.P.D.toPre F pt.g.b) (DegPre.lineε (k * p)))), w.IsGen → ∀ (s : Fam y.P.D.toPre F k) (s' t' : Fam y.P.D.toPre F (k * p)) (c : F), PullAl y.P.D F y.P.oD a k p s s' → PhiRel y.P.D.toPre F (k * p) pt w s' t' → (∀ χ, VGe y.P.D F y.v (k * p) χ ((c • t').s χ) 0) → ∀ (h : PS F 2 y.d) (ω : PS V 1 y.d), y.B.IsCanonGauge F h → FB.toK F ω = FB.expS F (ev (n := 1) ![y.B.actK F a] (y.B.hL F h H.w0) - (p : F) • y.B.hL F h H.w0) → ∀ f : PS F 1 y.d, y.Germ (k * p) (c • t') (f * FB.toK F ω ^ k) → ∀ l mo, y.v (p : F) ≤ y.v (MvPowerSeries.coeff mo (Dof (y.B.FK F) (fun i => (e l i : F)) f - MvPowerSeries.C (yy l : F) * f))
def CharExSt : Prop := ∀ (p : ℕ) [Fact p.Prime], Pdiv.ThmAGtStC p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)
def RSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (α : 𝓞 E) (N n D : ℕ), α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) → IsUnit ((N : ℕ) : V) → 4 * D + 4 ≤ N → (D : ℝ) * M₀ < N → ∀ (θα : Fam y.P.D.toPre F (1 * N)), (∀ s, NuGe y.P.D y.Q F y.v (1 * N) s 0 → ∃ (m : ℕ) (t : Fin m → Fam y.P.D.toPre F (1 * N)) (c : Fin m → F), (∀ i, y.Transl (1 * N) (star α) θα (t i)) ∧ (∀ i, 0 ≤ y.v (c i)) ∧ s = ∑ i, c i • t i) → ∀ (h : PS F 2 y.d) (Λ : Type) [Fintype Λ] (e : Λ → Fin y.d → F) (I : Type) [Fintype I] [Nonempty I] (Pi : I → MvPolynomial (Λ × Fin n) F) (c : I → F), (∀ i, 0 ≤ y.v (c i)) → (∑ i, c i • Pi i).totalDegree ≤ D → ∀ (g : Fin n → PS F 1 y.d), (∀ b mo, 0 ≤ y.v (MvPowerSeries.coeff mo (g b))) → ∀ gm : ℚ, y.v (y.colVal h (1 * N) e (∑ i, c i • Pi i) g) = (gm : ℚ) → ∃ (i : I) (t : Fin n → Fam y.P.D.toPre F (1 * N)) (f : Fin n → PS F 1 y.d) (gm' : ℚ), (∀ b, y.Transl (1 * N) (star α) θα (t b) ∧ y.Germ (1 * N) (t b) (f b)) ∧ y.v (y.colVal h (1 * N) e (Pi i) f) = (gm' : ℚ) ∧ (gm' : ℝ) ≤ gm + (D : ℝ) ^ 2 * Cc / N
def LemmaBSt : Prop := ∀ (p : ℕ) [Fact p.Prime], Pdiv.ThmAGtStC p → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (a : 𝓞 E) (k : ℕ), a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → Nat.Coprime p k → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → ∀ (isV : T → Prop) [DecidablePred isV], (∀ t, isV t → τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ¬ isV t → IsUnit (τ t a)) → (∃ lam : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ (n : ℕ) (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ), (∀ t, Function.Injective (col t)) → (∀ t i, col t i ∈ S ↔ isV t) → ∀ D : ℕ, D = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) → D < p - 1 → 4 * D + 4 ≤ k → (D : ℝ) * M₀ < k → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∀ ep : ℚ, y.v (p : F) = (ep : ℚ) → ∃ (s : Fin n → Fam y.P.D.toPre F k) (s' t : Fin n → Fam y.P.D.toPre F (k * p)) (f : Fin n → PS F 1 y.d) (gm : ℚ), (∀ b, NuGe y.P.D y.Q F y.v (k) (s b) 0 ∧ PullAl y.P.D F y.P.oD a k p (s b) (s' b) ∧ y.Transl (k * p) (star a) (s' b) (t b) ∧ y.Germ (k * p) (t b) (f b)) ∧ y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (minorsP F col m) f) = (gm : ℚ) ∧ (gm : ℝ) ≤ (D : ℝ) * ep / (p - 1) + S.card * r * Cc / (4 * k) + (D : ℝ) ^ 2 * Cc / k
def CorSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : Pt1 E H V F), letI := H.starRing; ∀ (a a' : 𝓞 E) (N N' n : ℕ), 1 ≤ N → 1 ≤ N' → Nat.Coprime N N' → a * star a = (N : 𝓞 E) → a' * star a' = (N' : 𝓞 E) → ∀ (θ' : Fam y.P.D.toPre F (1 * N')) (θ₂ : Fam y.P.D.toPre F (1 * N' * N)), θ' ≠ 0 → PullAl y.P.D F y.P.oD a (1 * N') N θ' θ₂ → (∀ s, NuGe y.P.D y.Q F y.v (1 * N') s 0 → ∃ (m : ℕ) (t : Fin m → Fam y.P.D.toPre F (1 * N')) (c : Fin m → F), (∀ i, y.Transl (1 * N') (star a') θ' (t i)) ∧ (∀ i, 0 ≤ y.v (c i)) ∧ s = ∑ i, c i • t i) → ∀ (h : PS F 2 y.d) (Λ : Type) [Fintype Λ] (e : Λ → Fin y.d → F) (I : Type) [Fintype I] [Nonempty I] (Pi : I → MvPolynomial (Λ × Fin n) F) (c : I → F), (∀ i, 0 ≤ y.v (c i)) → ∀ (s : Fin n → Fam y.P.D.toPre F (1 * N')) (s' t : Fin n → Fam y.P.D.toPre F (1 * N' * N)) (f : Fin n → PS F 1 y.d), (∀ b, NuGe y.P.D y.Q F y.v (1 * N') (s b) 0 ∧ PullAl y.P.D F y.P.oD a (1 * N') N (s b) (s' b) ∧ y.Transl (1 * N' * N) (star a) (s' b) (t b) ∧ y.Germ (1 * N' * N) (t b) (f b)) → ∀ gm : ℚ, y.v (y.colVal h (1 * N' * N) e (∑ i, c i • Pi i) f) = (gm : ℚ) → ∃ (i : I) (t₂ : Fin n → Fam y.P.D.toPre F (1 * N' * N)) (f₂ : Fin n → PS F 1 y.d), (∀ b, y.Transl (1 * N' * N) (star (a' * a)) θ₂ (t₂ b) ∧ y.Germ (1 * N' * N) (t₂ b) (f₂ b)) ∧ y.v (y.colVal h (1 * N' * N) e (Pi i) f₂) ≤ (gm : ℚ)
def PtExSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (F : Type) [Field F] [Algebra (FractionRing V) F] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → ∀ (ϖ : V), Irreducible ϖ → ∀ v : AddValuation F (WithTop ℚ), ValOver ϖ F v → ∃ y : Pt1 E H V F, y.t = t ∧ HEq y.P P ∧ y.v = v ∧ y.ϖ = ϖ
section Basic₂
section ColVal
variable [Algebra V F] [CharZero F] (h : PS F 2 y.d) (q : ℕ) {Λ : Type} [Fintype Λ] (e : Λ → Fin y.d → F) {n : ℕ}
end ColVal
example (k : Type) [CommRing k] {n : ℕ} (b : Fin n) (m : ℕ) :
    minorsP k (T := Unit) (r := fun _ => 1) (fun _ _ => b) (fun _ _ => m) = MvPolynomial.X (⟨(), 0⟩, b) ^ m := by
  simp [minorsP]
example (k : Type) [CommRing k] :
    minorsP k (T := Unit) (r := fun _ => 2) (n := 2) (fun _ i => i) (fun _ s => s.val) =
      MvPolynomial.X (⟨(), 0⟩, 0) * MvPolynomial.X (⟨(), 1⟩, 1) -
        MvPolynomial.X (⟨(), 0⟩, 1) * MvPolynomial.X (⟨(), 1⟩, 0) := by
  simp [minorsP, Fin.prod_univ_two, Matrix.det_fin_two]
end Basic₂
end GlobalTheory.FamGerm


