-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FramedFamilyStatement
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_FramedFamilyStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:36:08.275422+00:00
-- url     : https://prove2.me/theorems/4d612526-eae4-41bb-ab03-d09577a73818
-- title:
--   Framed Family Statement
-- statement:
--   Definitions and structural lemmas for Framed Family Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FramedFamilyStatement.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ColumnValueStatement
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
def BoxLiftSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (n : ℕ)
    (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V))))
    (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n) (U' : Unif (maximalIdeal V) D' A' G')
    (_PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ x' : TFK (R := V) F ⟶ A'.A, (∀ i, ∃ p : QkPt P.D.toPre F k, P.ToA F k p (x' ≫ pA.pr i)) →
      ∃ p' : QkPt D'.toPre F k, QkToAkU U'.toUnifPre F k p' x'
def PullTotSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
    (F : Type) [Field F] [Algebra (FractionRing V) F]
    (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (N : ℕ),
      1 ≤ N → a * star a = (N : O) → star a * a = (N : O) →
      ∀ k : ℕ, 1 ≤ k → ∀ s : Fam D.toPre F k, ∃ s' : Fam D.toPre F (k * N), PullAl D F oa a k N s s'
def ExpGSurjSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
    (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ s : Fam D.toPre F k, ∃ σ' : U.toUnifPre.SecGF F k, U.toUnifPre.ExpandsG F k σ' s
def FramedFamilyStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' → 5 ≤ g' →
  ∀ (π : 𝓞 E), π * star π = (g : 𝓞 E) → (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) [GrpObj G₁] [IsCommMonObj G₁] (pD : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA : IsPowPolAV A₁ P.A 1) (pG : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (_PU : UnifPowOf3 pD pA pG U₁ P.U)
    [Module (𝓞 E) D₁.toPre.X] (oD₁ : D₁.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ (p : QkPt D₁.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F p.g.b) (DegPre.lineε (g' * g)))) (ζ : F),
    w.IsGen → ζ ≠ 0 → FinOrd D₁ F (g' * g) p w ζ →
  ∀ x : TFK (R := T.V) F ⟶ A₁.A, (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) → QkToAkU U₁.toUnifPre F (g' * g) p x →
  ∀ χ₀ : D₁.toPre.X,
    ∃ s : Fam D₁.toPre F g', NuGe D₁ (sumQ pD.xe Q) F v g' s 0 ∧
      (∀ α : D₁.toPre.X, (∀ z : D₁.toPre.X, α ≠ χ₀ + g' • z) → ∀ j, (s.s α).f j = 0) ∧
      ∀ s₂ t₀ t : Fam D₁.toPre F (g' * g),
        PullAl D₁ F oD₁ (star π) g' g s s₂ → PhiRel D₁.toPre F (g' * g) p w s₂ t₀ → Fam.IsSmul D₁.toPre F ζ t₀ t →
        NuGe D₁ (sumQ pD.xe Q) F v (g' * g) t 0 ∧
        (∀ α : D₁.toPre.X, (∀ z : D₁.toPre.X, α ≠ π • χ₀ + p.y + g' • (π • z)) → ∀ j, (t.s α).f j = 0) ∧
        ∃ c₁ : F, Val0 D₁ F (g' * g) (π • χ₀ + p.y) (t.s (π • χ₀ + p.y)) c₁ ∧
          v c₁ = (((sumQ pD.xe Q (π • χ₀ + p.y) : ℚ) / ((g' * g : ℕ) : ℚ) : ℚ) : WithTop ℚ)
def GermTermSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (n : ℕ), 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ k : ℕ, 1 ≤ k →
  ∀ (t : Fam D'.toPre F k) (σ' : U'.toUnifPre.SecGF F k) (h : PS F n (chD C.ch)),
    U'.toUnifPre.ExpandsG F k σ' t → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F k σ' h →
    NuGe D' (sumQ pD.xe Q) F v k t 0 →
  ∀ χ' : D'.toPre.X,
    (∀ α : D'.toPre.X, α ≠ χ' → (∃ j, (t.s α).f j ≠ 0) → sumQ pD.xe Q χ' < sumQ pD.xe Q α) →
    (∀ e, (((sumQ pD.xe Q χ' : ℚ) / (k : ℚ) : ℚ) : WithTop ℚ) ≤ v (MvPowerSeries.coeff e h)) ∧
    ∀ c₁ : F, Val0 D' F k χ' (t.s χ') c₁ → v c₁ = (((sumQ pD.xe Q χ' : ℚ) / (k : ℚ) : ℚ) : WithTop ℚ) →
      v (MvPowerSeries.constantCoeff h) = v c₁
def LemmaASt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' → 5 ≤ g' →
  ∀ (π : 𝓞 E), π * star π = (g : 𝓞 E) → (∃ u u' : 𝓞 E, u * π + u' * star π = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) [GrpObj G₁] [IsCommMonObj G₁] (pD : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA : IsPowPolAV A₁ P.A 1) (pG : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (PU : UnifPowOf3 pD pA pG U₁ P.U)
    [Module (𝓞 E) D₁.toPre.X] (oD₁ : D₁.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ (u : PS F 1 (chD C.ch)), (∀ e, 0 ≤ v (MvPowerSeries.coeff e u)) → MvPowerSeries.constantCoeff u = 1 →
    ev (n := 2) ![fun j => MvPowerSeries.map (algebraMap T.V F) (C.FT j)] u =
      ev (n := 2) ![pt F (chD C.ch) 0] u * ev (n := 2) ![pt F (chD C.ch) 1] u →
  ∃ κ : (TFK (R := T.V) F ⟶ P.A.A) → Fˣ,
    (∀ z z', z ≫ P.oA.act (star π) = 1 → z' ≫ P.oA.act (star π) = 1 → κ (z * z') = κ z * κ z') ∧
    ∀ x : TFK (R := T.V) F ⟶ A₁.A, (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) →
      (∀ z, z ≫ P.oA.act (star π) = 1 → WeilIs P.A.A P.A.L (g' * g) z (x ≫ pA.pr 0) (unitOn (κ z))) →
    letI := io.toAlgebra
    ∀ (s : Fam D₁.toPre F g') (s₂ : Fam D₁.toPre F (g' * g)) (p : QkPt D₁.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (t₀ t : Fam D₁.toPre F (g' * g)) (σ' : U₁.toUnifPre.SecGF F (g' * g)) (h : PS F 1 (chD C.ch)),
      NuGe D₁ (sumQ pD.xe Q) F v g' s 0 → PullAl D₁ F oD₁ (star π) g' g s s₂ →
      w.IsGen → ζ ≠ 0 → FinOrd D₁ F (g' * g) p w ζ → QkToAkU U₁.toUnifPre F (g' * g) p x →
      PhiRel D₁.toPre F (g' * g) p w s₂ t₀ → Fam.IsSmul D₁.toPre F ζ t₀ t →
      U₁.toUnifPre.ExpandsG F (g' * g) σ' t →
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h →
    ∀ c₀ : F, c₀ ≠ 0 → (∀ e, v c₀ ≤ v (MvPowerSeries.coeff e h)) →
    ∀ Pv : MvPolynomial (LtN Dw 1) F, (∀ mm, 0 ≤ v (Pv.coeff mm)) →
      (∀ ℓ ∈ Pv.vars, 0 < v (algebraMap T.Fr F (io (embK c ℓ.1 (star π))))) → Pv.totalDegree < g →
      v c₀ + v ((g : ℕ) : F) ≤
        v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h
            (fun ℓ : LtN Dw 1 => ℓ.2.2) (fun (ℓ : LtN Dw 1) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) Pv -
          MvPolynomial.eval (fun ℓ : LtN Dw 1 => MvPowerSeries.constantCoeff
              (DofN (fun j => MvPowerSeries.map (algebraMap T.V F) (C.FT j)) (0 : Fin 1)
                (fun j => algebraMap T.V F (C.uvecT ⟨ℓ.1, ℓ.2.1⟩ j)) u)) Pv *
            MvPowerSeries.constantCoeff h)
end Formalism.MainNotions.ModuliIntegralCharts.H1


