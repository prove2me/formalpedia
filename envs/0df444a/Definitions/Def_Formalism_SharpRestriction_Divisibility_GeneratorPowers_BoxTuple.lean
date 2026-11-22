-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BoxTuple
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_BoxTuple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:09.180421+00:00
-- url     : https://prove2.me/theorems/88f66199-af69-486b-af63-1a2c6c2f17c4
-- title:
--   Box Tuple
-- statement:
--   Definitions and structural lemmas for Box Tuple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/BoxTuple.lean

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
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace BoxTuple
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
def BoxTup (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (v : AddValuation F (WithTop ℚ)) (g g' : ℕ) (π : 𝓞 E)
    {n : ℕ} {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)}
    [GrpObj G'] [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n}
    (pG : IsPowGrp G' C.I.G.G n) {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E))
    (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
    (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F n (chD C.ch)) : Prop :=
  NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
  PullAl D' F oD' (star π) g' g s s₂ ∧
  (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (g' * g) p w ζ) ∧
  QkToAkU U'.toUnifPre F (g' * g) p x ∧ (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
  PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
  U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
  IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h
end BoxTuple
open BoxTuple
def BoxAssemblySt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)) (g g' : ℕ) (π : 𝓞 E) (n₁ n₂ : ℕ)
    (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre (n₁ + n₂))
    (pA : IsPowPolAV A' P.A (n₁ + n₂)) (pG : IsPowGrp G' C.I.G.G (n₁ + n₂))
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin (n₁ + n₂)), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin (n₁ + n₂)),
      oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∃ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (pD₁ : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA₁ : IsPowPolAV A₁ P.A 1) (pG₁ : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (PU₁ : UnifPowOf3 pD₁ pA₁ pG₁ U₁ P.U)
    (_ : Module (𝓞 E) D₁.toPre.X) (oD₁ : D₁.toPre.OAct (𝓞 E))
    (D₂ : DegData T.V (maximalIdeal T.V)) (A₂ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₂ : Over (Sp T.V)) (_ : GrpObj G₂) (_ : IsCommMonObj G₂) (pD₂ : IsPowDeg D₂.toPre P.D.toPre n₂)
    (pA₂ : IsPowPolAV A₂ P.A n₂) (pG₂ : IsPowGrp G₂ C.I.G.G n₂)
    (U₂ : Unif (maximalIdeal T.V) D₂ A₂ G₂) (PU₂ : UnifPowOf3 pD₂ pA₂ pG₂ U₂ P.U)
    (_ : Module (𝓞 E) D₂.toPre.X) (oD₂ : D₂.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD₁.xe (a • x) i = a • pD₁.xe x i) ∧
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD₁.pw.pr i = pD₁.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) ∧
    (∀ (a : 𝓞 E) (x : D₂.toPre.X) (i : Fin n₂), pD₂.xe (a • x) i = a • pD₂.xe x i) ∧
    (∀ (a : 𝓞 E) (i : Fin n₂),
      oD₂.onB.act a ≫ pD₂.pw.pr i = pD₂.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) ∧
    ∀ (s₁ : Fin n₁ → Fam D₁.toPre F g') (s₂₁ : Fin n₁ → Fam D₁.toPre F (g' * g))
      (p₁ : Fin n₁ → QkPt D₁.toPre F (g' * g))
      (w₁ : ∀ i, LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F (p₁ i).g.b) (DegPre.lineε (g' * g))))
      (ζ₁ : Fin n₁ → F) (x₁ : Fin n₁ → (TFK (R := T.V) F ⟶ A₁.A)) (t₀₁ t₁ : Fin n₁ → Fam D₁.toPre F (g' * g))
      (σ₁ : Fin n₁ → U₁.toUnifPre.SecGF F (g' * g)) (h₁ : Fin n₁ → PS F 1 (chD C.ch)),
      (∀ i, BoxTup C P Q F v g g' π pG₁ PU₁ oD₁ (s₁ i) (s₂₁ i) (p₁ i) (w₁ i) (ζ₁ i) (x₁ i) (t₀₁ i) (t₁ i)
        (σ₁ i) (h₁ i)) →
    ∀ (sb : Fam D₂.toPre F g') (s₂b : Fam D₂.toPre F (g' * g)) (pb : QkPt D₂.toPre F (g' * g))
      (wb : LB.Gen (LB.LinComb D₂.toPre.P.L (DegPre.lineφ D₂.toPre F pb.g.b) (DegPre.lineε (g' * g))))
      (ζb : F) (xb : TFK (R := T.V) F ⟶ A₂.A) (t₀b tb : Fam D₂.toPre F (g' * g))
      (σb : U₂.toUnifPre.SecGF F (g' * g)) (hb : PS F n₂ (chD C.ch)),
      BoxTup C P Q F v g g' π pG₂ PU₂ oD₂ sb s₂b pb wb ζb xb t₀b tb σb hb →
    ∃ (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
      (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F (n₁ + n₂) (chD C.ch)),
      BoxTup C P Q F v g g' π pG PU oD' s s₂ p w ζ x t₀ t σ' h ∧
      h = (∏ i : Fin n₁, MvPowerSeries.rename
            (fun q : Fin 1 × Fin (chD C.ch) => ((Fin.castAdd n₂ i, q.2) : Fin (n₁ + n₂) × Fin (chD C.ch))) (h₁ i)) *
          MvPowerSeries.rename
            (fun q : Fin n₂ × Fin (chD C.ch) => ((Fin.natAdd n₁ q.1, q.2) : Fin (n₁ + n₂) × Fin (chD C.ch))) hb ∧
      (∀ i : Fin n₁, x ≫ pA.pr (Fin.castAdd n₂ i) = x₁ i ≫ pA₁.pr 0) ∧
      ∀ i : Fin n₂, x ≫ pA.pr (Fin.natAdd n₁ i) = xb ≫ pA₂.pr i
def SecondFrameStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n₂ : ℕ) (D₂ : DegData T.V (maximalIdeal T.V)) (A₂ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₂ : Over (Sp T.V)) [GrpObj G₂] [IsCommMonObj G₂] (pD : IsPowDeg D₂.toPre P.D.toPre n₂)
    (pA : IsPowPolAV A₂ P.A n₂) (pG : IsPowGrp G₂ C.I.G.G n₂)
    (U₂ : Unif (maximalIdeal T.V) D₂ A₂ G₂) (PU : UnifPowOf3 pD pA pG U₂ P.U)
    [Module (𝓞 E) D₂.toPre.X] (oD₂ : D₂.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₂.toPre.X) (i : Fin n₂), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n₂),
      oD₂.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ (m : (E →+* ℂ) → ℕ → ℕ) (D : ℕ),
    (∀ τ s, m τ s ≠ 0 → ¬ 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))) →
      1 ≤ s ∧ s ≤ Dw.mult τ ∧ s ≤ n₂) →
    degOf Dw m ≤ D → 4 * D + 4 ≤ g' → (D : ℝ) * M0 < g' →
    letI := io.toAlgebra
    ∃ (s : Fam D₂.toPre F g') (s₂ : Fam D₂.toPre F (g' * g)) (p : QkPt D₂.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D₂.toPre.P.L (DegPre.lineφ D₂.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (x : TFK (R := T.V) F ⟶ A₂.A) (t₀ t : Fam D₂.toPre F (g' * g))
      (σ' : U₂.toUnifPre.SecGF F (g' * g)) (h : PS F n₂ (chD C.ch)) (ρ₂ : ℚ),
      BoxTup C P Q F v g g' π pG PU oD₂ s s₂ p w ζ x t₀ t σ' h ∧
      v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h
          (fun ℓ : LtN Dw n₂ => ℓ.2.2) (fun (ℓ : LtN Dw n₂) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (minorProd Dw F (fun τ => ¬ 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₂ id)) =
        (ρ₂ : WithTop ℚ) ∧
      (ρ₂ : ℝ) ≤ (D : ℝ) ^ 2 * Φ / g'
def DirOntoSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (g : ℕ), g.Prime →
    ¬ IsUnit ((g : ℕ) : T.V) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ∀ t : Lt1 Dw → T.V, ∃ a : Fin (chD C.ch) → T.V, ∀ ℓ, ∑ j, a j * C.uvecT ℓ j = t ℓ
end Formalism.MainNotions.ModuliIntegralCharts.H1


