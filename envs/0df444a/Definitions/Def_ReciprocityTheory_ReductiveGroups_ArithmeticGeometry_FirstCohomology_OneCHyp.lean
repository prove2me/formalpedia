-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:30.552834+00:00
-- url     : https://prove2.me/theorems/7b9c1144-85f0-41a1-9937-c0e5f26d1daa
-- title:
--   One CHyp
-- statement:
--   Definitions and structural lemmas for One CHyp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/OneCHyp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
def AlphaBarEnumStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    letI := H.starRing
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F],
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
        (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c))),
      ∃ (p : Fin (N ^ P.A.g) → QkPt P.D.toPre F (1 * N))
        (x : Fin (N ^ P.A.g) → (TFK (R := V) F ⟶ P.A.A)),
        (∀ b, P.ToA F (1 * N) (p b) (x b)) ∧ (∀ b, x b ≫ P.oA.act (star α) = 1) ∧
        Function.Injective x ∧
        ∀ y : TFK (R := V) F ⟶ P.A.A, y ≫ P.oA.act (star α) = 1 → ∃ b, x b = y
def CanonLiftFixStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    letI := H.starRing
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F]
      (θ : Fam P.D.toPre F 1) (θα : Fam P.D.toPre F (1 * N)), PullAl P.D F P.oD α 1 N θ θα →
    ∀ (p : QkPt P.D.toPre F (1 * N)) (x : TFK (R := V) F ⟶ P.A.A), P.ToA F (1 * N) p x →
      x ≫ P.oA.act α = 1 →
      ∃ w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * N))),
        w.IsGen ∧ FinOrd P.D F (1 * N) p w 1 ∧ PhiRel P.D.toPre F (1 * N) p w θα θα
def AlphaPairStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso →
    letI := H.starRing
    ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) →
      IsUnit ((N : ℕ) : V) →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F],
    ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a)
        (fun n g g' c => WeilIs P.A.A P.A.L n g g' (unitOn c))),
    ∀ (x x' : TFK (R := V) F ⟶ P.A.A), x ≫ P.oA.act (star α) = 1 → x' ≫ P.oA.act (star α) = 1 → x ≠ x' →
      ∃ z : TFK (R := V) F ⟶ P.A.A, z ≫ P.oA.act α = 1 ∧
        ∃ c c' : Γ((TFK (R := V) F).left, ⊤)ˣ,
          WeilIs P.A.A P.A.L N z x c ∧ WeilIs P.A.A P.A.L N z x' c' ∧ c ≠ c'
def DimSplitStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t),
    P.A.g = Module.finrank ℤ P.D.toPre.X + P.D.toPre.P.g
def QkActExistsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t),
    letI := H.starRing
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ) (a : 𝓞 E)
      (p : QkPt P.D.toPre F k), ∃ p' : QkPt P.D.toPre F k, QkAct P.oD a p p'
def DvrLevelFrame : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O),
      TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N : ℕ), 1 ≤ N → a * star a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)), PullAl D F oa a k N s s' →
      ∀ (χ : D.toPre.X) (σ : D.toPre.SecB k χ)
        (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) (c : F),
        GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k) σF
          (D.toPre.famφB χ) (DegPre.famε k) σ (DegPre.prB D.toPre F).left 1 →
        (∀ j, (s.s χ).f j = DegPre.constBF D.toPre F c _ * σF.f j) →
        (¬ ∃ σ' : D.toPre.SecB k χ, ∀ j, σ.f j = constFn D.toPre.P.A.hom _ ϖ * σ'.f j) →
        ∀ r : ℚ, NuGe D Q F v (k * N) s' r → ((r + (Q χ : ℚ) / k : ℚ) : WithTop ℚ) ≤ v c
def FinOrdExistsStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen → ∃ ζ : F, ζ ≠ 0 ∧ FinOrd D F k p w ζ
end ReciprocityTheory.ChartRestriction.G.H1


