-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LemmaBStatement
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_LemmaBStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:24:34.501807+00:00
-- url     : https://prove2.me/theorems/06afca44-64ff-4366-9bd6-5ba2f74bbb42
-- title:
--   Lemma BStatement
-- statement:
--   Definitions and structural lemmas for Lemma BStatement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/LemmaBStatement.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpBijectiveUniformisation
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCSt
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GSt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def leadMinor (Dw : Datum H) {n : ℕ} (K : Type) [CommRing K] (τ : E →+* ℂ) (s : ℕ) (hs : s ≤ Dw.mult τ) (cop : Fin s → Fin n) :
    MvPolynomial (LtN Dw n) K :=
  Matrix.det (Matrix.of fun (a i : Fin s) =>
    (MvPolynomial.X (⟨τ, (Fin.castLE hs a, cop i)⟩ : LtN Dw n) : MvPolynomial (LtN Dw n) K))
def minorProd (Dw : Datum H) {n : ℕ} (K : Type) [CommRing K] (typ : (E →+* ℂ) → Prop) (m : (E →+* ℂ) → ℕ → ℕ) (nb : ℕ)
    (cop : Fin nb → Fin n) : MvPolynomial (LtN Dw n) K :=
  open Classical in
  ∏ τ : E →+* ℂ, if typ τ then
    ∏ s ∈ Finset.range (Dw.mult τ + 1),
      (if h : s ≤ Dw.mult τ ∧ s ≤ nb then
        leadMinor Dw K τ s h.1 (fun i => cop (Fin.castLE h.2 i)) else 1) ^ m τ s
  else 1
def degOf (Dw : Datum H) (m : (E →+* ℂ) → ℕ → ℕ) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ s ∈ Finset.range (Dw.mult τ + 1), s * m τ s
end GSt
open GSt
def LemmaBStatement : Prop :=
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

  ∀ (O : Type) [CommRing O] [Algebra O F] [Algebra T.V O] [IsScalarTower T.V O F],
    Function.Injective (algebraMap O F) → (∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) →
    IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O →
    ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
        (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))),

  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →

  ∀ (n₁ n₂ : ℕ), 1 ≤ n₁ + n₂ → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre (n₁ + n₂))
    (pA : IsPowPolAV A' P.A (n₁ + n₂)) (pG : IsPowGrp G' C.I.G.G (n₁ + n₂))
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin (n₁ + n₂)), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin (n₁ + n₂)),
      oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →

  ∀ (m : (E →+* ℂ) → ℕ → ℕ),
    (∀ τ s, m τ s ≠ 0 → 1 ≤ s ∧ s ≤ Dw.mult τ ∧
      s ≤ (if 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))) then n₁ else n₂)) →
    degOf Dw m < g - 1 → 4 * degOf Dw m + 4 ≤ g' → (degOf Dw m : ℝ) * M0 < g' →
  ∀ (ρg : ℚ), v ((g : ℕ) : F) = (ρg : WithTop ℚ) →
    letI := io.toAlgebra
    ∃ (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
      (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F (n₁ + n₂) (chD C.ch)) (ρ : ℚ),
      NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
      PullAl D' F oD' (star π) g' g s s₂ ∧
      (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (g' * g) p w ζ) ∧
      QkToAkU U'.toUnifPre F (g' * g) p x ∧ (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
      PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
      U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h ∧
      v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h
          (fun ℓ : LtN Dw (n₁ + n₂) => ℓ.2.2) (fun (ℓ : LtN Dw (n₁ + n₂)) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (minorProd Dw F (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₁
              (fun i => Fin.castAdd n₂ i) *
            minorProd Dw F (fun τ => ¬ 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₂
              (fun i => Fin.natAdd n₁ i))) = (ρ : WithTop ℚ) ∧
      (ρ : ℝ) ≤ (ρg : ℝ) * degOf Dw m / (g - 1) + n₁ * r * Φ / (4 * g') + 2 * degOf Dw m ^ 2 * Φ / g'
end Formalism.MainNotions.ModuliIntegralCharts.H1


