-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ColumnValueStatement
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ColumnValueStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:56.633859+00:00
-- url     : https://prove2.me/theorems/058bfb7d-3679-422f-9600-30a874dea570
-- title:
--   Column Value Statement
-- statement:
--   Definitions and structural lemmas for Column Value Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ColumnValueStatement.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LemmaBStatement
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
def OneColumnStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' → 5 ≤ g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
        (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))),
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) [GrpObj G₁] [IsCommMonObj G₁] (pD : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA : IsPowPolAV A₁ P.A 1) (pG : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (PU : UnifPowOf3 pD pA pG U₁ P.U)
    [Module (𝓞 E) D₁.toPre.X] (oD₁ : D₁.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ x : TFK (R := T.V) F ⟶ A₁.A, (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) →
    letI := io.toAlgebra
    ∃ (s : Fam D₁.toPre F g') (s₂ : Fam D₁.toPre F (g' * g)) (p : QkPt D₁.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (t₀ t : Fam D₁.toPre F (g' * g))
      (σ' : U₁.toUnifPre.SecGF F (g' * g)) (h : PS F 1 (chD C.ch)) (c₀ : F) (ρ₀ : ℚ),
      NuGe D₁ (sumQ pD.xe Q) F v g' s 0 ∧
      PullAl D₁ F oD₁ (star π) g' g s s₂ ∧
      (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D₁ F (g' * g) p w ζ) ∧
      QkToAkU U₁.toUnifPre F (g' * g) p x ∧
      PhiRel D₁.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D₁.toPre F ζ t₀ t ∧
      U₁.toUnifPre.ExpandsG F (g' * g) σ' t ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h ∧
      v c₀ = (ρ₀ : WithTop ℚ) ∧ (ρ₀ : ℝ) ≤ r * Φ / (4 * g') ∧
      (∀ e, v c₀ ≤ v (MvPowerSeries.coeff e h)) ∧ v (MvPowerSeries.constantCoeff h) = v c₀
def ColumnValueStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' → 5 ≤ g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
        (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))),
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
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
    letI := io.toAlgebra
    ∃ (x : TFK (R := T.V) F ⟶ A₁.A) (s : Fam D₁.toPre F g') (s₂ : Fam D₁.toPre F (g' * g))
      (p : QkPt D₁.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (t₀ t : Fam D₁.toPre F (g' * g))
      (σ' : U₁.toUnifPre.SecGF F (g' * g)) (h : PS F 1 (chD C.ch)) (c₀ : F) (ρ₀ : ℚ),
      (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
      NuGe D₁ (sumQ pD.xe Q) F v g' s 0 ∧
      PullAl D₁ F oD₁ (star π) g' g s s₂ ∧
      (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D₁ F (g' * g) p w ζ) ∧
      QkToAkU U₁.toUnifPre F (g' * g) p x ∧
      PhiRel D₁.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D₁.toPre F ζ t₀ t ∧
      U₁.toUnifPre.ExpandsG F (g' * g) σ' t ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h ∧
      v c₀ = (ρ₀ : WithTop ℚ) ∧ (ρ₀ : ℝ) ≤ r * Φ / (4 * g') ∧
      (∀ e, v c₀ ≤ v (MvPowerSeries.coeff e h)) ∧ v (MvPowerSeries.constantCoeff h) = v c₀ ∧
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


