-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpBijectiveUniformisation
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpBijectiveUniformisation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:19:49.292412+00:00
-- url     : https://prove2.me/theorems/d6c42acf-a498-4c5d-8dd6-411b383de1b8
-- title:
--   Exp Bijective Uniformisation
-- statement:
--   Definitions and structural lemmas for Exp Bijective Uniformisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpBijectiveUniformisation.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
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
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)
attribute [local instance] Over.cartesianMonoidalCategory
namespace ExpBijectiveUniformisation
section Help
variable {X Y Z : Scheme.{0}}
lemma wchart_comp_le (L : LB X) (g : Y ⟶ X) (z : Z ⟶ Y) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : PUnit.{1} => z ≫ g) (fun _ => j 0) ≤ z ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => g) j := by
  intro y hy
  have h1 : (z ≫ g).base y ∈ L.U (j 0) := Set.mem_iInter.1 hy ⟨⟩
  show z.base y ∈ (⋂ k : Fin 1, g.base ⁻¹' (L.U (j k) : Set X))
  refine Set.mem_iInter.2 fun k => ?_
  rw [Fin.fin_one_eq_zero k]
  exact h1
def genCast {L L' : LB X} (h : L = L') {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (b : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L' φ ε) :=
  h ▸ b
def sumQ {X1 Xn : Type} [AddCommGroup X1] [AddCommGroup Xn] {n : ℕ} (xe : Xn ≃+ (Fin n → X1)) (Q : X1 → ℤ) :
    Xn → ℤ :=
  fun x => ∑ i, Q (xe x i)
end Help
section GermN
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def jcN (V F : Type) [CommRing V] [Field F] [Algebra V F] (d n m : ℕ) (i : Fin n) :
    Sp (Jet F (Fin n × Fin d) m) ⟶ Sp (Jet V (Fin 1 × Fin d) m) :=
  spMap (((jetCopy (S := F) d m i : Jet F (Fin 1 × Fin d) m →ₐ[F] Jet F (Fin n × Fin d) m) :
      Jet F (Fin 1 × Fin d) m →+* Jet F (Fin n × Fin d) m).comp
    (jetCoef (algebraMap V F) (Fin 1 × Fin d) m))
def jptN {V : Type} [CommRing V] {t : SAB H (Sp V)} {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (F : Type)
    [Field F] [Algebra V F] (n m : ℕ) (i : Fin n) : Sp (Jet F (Fin n × Fin d) m) ⟶ t.G.left :=
  jcN V F d n m i ≫ (xT m).left
def IsGermN {V : Type} [CommRing V] [IsDomain V] {I : Ideal V} {t : SAB H (Sp V)} (P : PELUnif I t) {d n : ℕ}
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V)
    (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t)
    {D' : DegData V I} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Sp V)} [GrpObj G']
    [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} (pG : IsPowGrp G' t.G n)
    {U' : Unif I D' A' G'} (PU : UnifPowOf pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] (q : ℕ)
    (σ' : U'.toUnifPre.SecGF F q) (f : PS F n d) : Prop :=
  ∀ m, ∃ (z : Sp (Jet F (Fin n × Fin d) m) ⟶ (UnifPre.GF (R := V) (G := G') F).left)
    (τ : LB.Gen (LB.LinComb U'.LG.L (K := PUnit.{1}) (fun _ => z ≫ UnifPre.gFK (R := V) (G := G') F)
      (fun _ => (q : ℤ))))
    (b : LB.Gen (LB.LinComb P.U.LG.L (K := Fin n)
      (fun i => (z ≫ UnifPre.gFK (R := V) (G := G') F) ≫ (pG.pr i).left) (fun _ => (q : ℤ)))),
    z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G')).left =
      spMap (algebraMap F (Jet F (Fin n × Fin d) m)) ∧
    (∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i) ∧
    GeneratorPullback.MapsAt P.U.LG.L U'.LG.L (fun i => (pG.pr i).left) PU.wL (z ≫ UnifPre.gFK (R := V) (G := G') F) q τ b ∧
    LB.Gen.Corr t.PP.L _ _ _ _ (genCast (congrArg RigLB.L P.bundle) _ _ b)
      (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
        LB.pullGen t.PP.L _ _ (genPowG t _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m) q) (jcN V F d n m i)) ∧
    ∀ j : Fin 1 → U'.LG.L.ι,
      ((Sp (Jet F (Fin n × Fin d) m)).presheaf.map
          (homOfLE (wchart_comp_le U'.LG.L (UnifPre.gFK (R := V) (G := G') F) z j)).op).hom
        ((z.app _).hom (σ'.f j)) =
      ((Sp (Jet F (Fin n × Fin d) m)).presheaf.map (homOfLE le_top).op).hom (toΓ _ (psJet m f)) *
        (τ.s (fun _ => j 0)).val
end GermN
section St
open IsLocalRing
def BidegreeTwoJetStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n : ℕ), 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (q D : ℕ), 4 * D + 4 ≤ q → (D : ℝ) * M0 < q →
  ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f →
    ∃ (s : Fam D'.toPre F q) (σ' : U'.toUnifPre.SecGF F q) (g : PS F n (chD C.ch)) (lam : F),
      NuGe D' (sumQ pD.xe Q) F v q s 0 ∧ U'.toUnifPre.ExpandsG F q σ' s ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g ∧
      lam ≠ 0 ∧ (∃ ρ : ℚ, v lam = (ρ : WithTop ℚ) ∧ (ρ : ℝ) ≤ (D : ℝ) ^ 2 * Φ / q) ∧
      ∀ e : Fin n × Fin (chD C.ch) →₀ ℕ, e.degree ≤ D →
        MvPowerSeries.coeff e g = MvPowerSeries.coeff e (lam • MvPowerSeries.map (algebraMap T.Fr F) f)
def GermOfFamSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (n : ℕ), 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ q : ℕ, 1 ≤ q →
    (∀ σ' : U'.toUnifPre.SecGF F q, ∃ g : PS F n (chD C.ch),
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g) ∧
    ∀ (s : Fam D'.toPre F q) (σ' : U'.toUnifPre.SecGF F q), U'.toUnifPre.ExpandsG F q σ' s →
      NuGe D' (sumQ pD.xe Q) F v q s 0 → ∀ g : PS F n (chD C.ch),
        IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g →
        ∀ e, 0 ≤ v (MvPowerSeries.coeff e g)
end St
end ExpBijectiveUniformisation
end Formalism.MainNotions.ModuliIntegralCharts.H1


