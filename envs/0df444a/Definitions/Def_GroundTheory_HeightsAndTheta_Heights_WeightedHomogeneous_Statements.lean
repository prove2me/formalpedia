-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:23.327791+00:00
-- url     : https://prove2.me/theorems/a4e96076-d224-465b-a5a0-7410221e5da2
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/Statements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
def ChartFormsAlt.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P),
    ∃ d₀ : ι → ℕ, ∀ d : ι → ℕ, d₀ ≤ d → ∃ g, D.IsFormSystem d g
def ChartCrossRatio.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ),
    D.IsFormSystem d g → ∀ (c c' : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)),
      chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal
def ChartVanishing.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ),
    D.IsFormSystem d g → ∀ z ∈ P.points ℂ, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ j, evalCone z (g c j) = 0) ↔ evalCone z (chartMonomial c d) = 0
def ChartPrimality.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P),
    ∃ Q : ArithVariety D.extSizes, Q.ideal = D.extIdeal
def ExtensionDimension.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P),
    ringKrullDim (MvPolynomial (Coord D.extSizes) ℤ ⧸ D.extIdeal) = ringKrullDim P.CoordRing + 1
def ChartRingDescription.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (c : (k : ι) → Fin (n k + 1)), P.IsLive c → ∀ j : Fin (D.size + 1), D.elt j ≠ 0 →
      D.extChartRing c j = Subring.closure (insert (D.xi c j)⁻¹ (P.chartRing c : Set P.FunField))
def ConePoints.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ),
    D.IsFormSystem d g →
      (∀ (c : (k : ι) → Fin (n k + 1)) (i j : Fin (D.size + 1)),
        D.liftOld (g c j) * X (D.newCoord i) - D.liftOld (g c i) * X (D.newCoord j) ∈ D.extIdeal) ∧
      ∀ w ∈ D.extPoints, D.basePart₂ w ∈ P.points ℂ ∧ ∃ la : ℂ, la ≠ 0 ∧
        ∀ c : (k : ι) → Fin (n k + 1), evalCone (D.basePart₂ w) (chartMonomial c d) ≠ 0 →
          ∀ j, D.newPart w j =
            la * evalCone (D.basePart₂ w) (g c j) / evalCone (D.basePart₂ w) (chartMonomial c d)
def ConePointsConverse.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ),
    D.IsFormSystem d g → ∀ z ∈ P.points ℂ, ∀ c : (k : ι) → Fin (n k + 1),
      evalCone z (chartMonomial c d) ≠ 0 → D.joinPt z (fun j ↦ evalCone z (g c j)) ∈ D.extPoints
def HomogGeneratorsExist.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n),
    ∃ (r : ℕ) (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ), P.IsHomogGenerators G δ
def ChartDenominatorAlt.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ),
    D.IsFormSystem d g → ∀ (r : ℕ) (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ),
      P.IsHomogGenerators G δ →
        (∀ z : Cone n ℂ, BlockNonzero z → 0 < D.den d g G δ z) ∧
          ContDiffOn ℝ ∞ (D.den d g G δ) {z | BlockNonzero z}
def ChartMetric.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (N : HermLine n), N.deg = D.deg →
    ∀ (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ),
    D.IsFormSystem d g → ∀ (r : ℕ) (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ),
      P.IsHomogGenerators G δ →
        (∃ H : HermLine D.extSizes, H.deg = AddBlockData.newDeg ∧
          (∀ w, BlockNonzero w → H.metric w = D.plusMetric N d g G δ w) ∧
          (N.ConjInvariant → H.ConjInvariant)) ∧
        ∀ w ∈ D.extPoints, ∀ (c : (k : ι) → Fin (n k + 1)) (la : ℂ),
          evalCone (D.basePart₂ w) (chartMonomial c d) ≠ 0 →
          (∀ j, D.newPart w j =
            la * evalCone (D.basePart₂ w) (g c j) / evalCone (D.basePart₂ w) (chartMonomial c d)) →
          D.plusMetric N d g G δ w = ‖la‖ * N.metric (D.basePart₂ w)
def PlurisubharmonicMetric.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (N : HermLine n), N.deg = D.deg →
    ∀ (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ),
    D.IsFormSystem d g → ∀ (r : ℕ) (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ),
      P.IsHomogGenerators G δ →
      ∀ (e : ℕ) (γ : (Fin e → ℂ) → Cone D.extSizes ℂ) (u₀ : Fin e → ℂ), AnalyticAt ℂ γ u₀ →
        (∀ᶠ u in nhds u₀, γ u ∈ D.extPoints) →
        ∃ la : (Fin e → ℂ) → ℂ, AnalyticAt ℂ la u₀ ∧ la u₀ ≠ 0 ∧
          ∀ᶠ u in nhds u₀, D.plusMetric N d g G δ (γ u) = ‖la u‖ * N.metric (D.basePart₂ (γ u))
def SectionNorm.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (N : HermLine n), N.deg = D.deg →
    ∀ (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ),
    D.IsFormSystem d g → ∀ (r : ℕ) (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ),
      P.IsHomogGenerators G δ → ∀ (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)),
        D.liftOld (g c j) ∉ D.extIdeal → ∀ w ∈ D.extPoints, evalCone (D.basePart₂ w) (g c j) ≠ 0 →
          ‖evalCone w (X (D.newCoord j) * D.liftOld (chartMonomial c d))‖ /
              ‖evalCone w (D.liftOld (g c j))‖ /
            (D.plusMetric N d g G δ w / N.metric (D.basePart₂ w)) = 1
def SectionCycle.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ),
    D.IsFormSystem d g → ∀ (c : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)),
      D.liftOld (g c j) ∉ D.extIdeal → ∀ W,
        NumbersDVR.ratDiv (ι := fun o ↦ Fin (D.extSizes o + 1)) D.extIdeal
          (X (D.newCoord j) * D.liftOld (chartMonomial c d)) (D.liftOld (g c j)) W = 0
def SmallSections.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P),
    (∀ (τ : ℕ) (F : MvPolynomial (Fin (D.size + 1)) ℤ), F.IsHomogeneous τ →
      ∃ s : IntegralSection P (τ • D.deg), s.toFun = aeval D.elt F) ∧
    ∀ (N : HermLine n), N.deg = D.deg →
    ∀ (d : ι → ℕ) (g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ),
    D.IsFormSystem d g → ∀ (r : ℕ) (G : Fin r → MvPolynomial (Coord n) ℤ) (δ : Fin r → ι → ℕ),
      P.IsHomogGenerators G δ →
    ∀ (τ : ℕ) (F : MvPolynomial (Fin (D.size + 1)) ℤ), F.IsHomogeneous τ →
    ∀ p q : MvPolynomial (Coord n) ℤ, P.mkF p = aeval D.elt F * P.mkF q →
      (∀ c : (k : ι) → Fin (n k + 1), P.IsLive c →
        chartMonomial c d ^ τ * p - aeval (g c) F * q ∈ P.ideal) ∧
      ((∀ w ∈ D.extPoints,
          ‖eval₂ (Int.castRingHom ℂ) (D.newPart w) F‖ ≤ D.plusMetric N d g G δ w ^ τ) →
        ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ ‖evalCone z q‖ * N.metric z ^ τ)
def BlockSurjectivity.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (k₀ : ι),
    projBlock k₀ '' P.points ℂ = conePoints (P.projIdeal k₀) ℂ
def SupNormEquality.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (k₀ : ι) (m : ℕ),
    (∀ f : MvPolynomial (Coord n) ℤ, IsWeightedHomogeneous (coordDeg n) f (m • Pi.single k₀ 1) →
      ∃ f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
        IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ n k₀)) f' (fun _ ↦ m) ∧
          rename (blockIncl k₀) f' = f) ∧
    ∀ f' : MvPolynomial (Coord (fun _ : Unit ↦ n k₀)) ℤ,
      IsWeightedHomogeneous (coordDeg (fun _ : Unit ↦ n k₀)) f' (fun _ ↦ m) → ∀ B : ℝ,
        (∀ z ∈ P.points ℂ, ‖evalCone z (rename (blockIncl k₀) f')‖ ≤ B * l2Norm (z k₀) ^ m) ↔
          (∀ z' ∈ conePoints (P.projIdeal k₀) ℂ, ‖evalCone z' f'‖ ≤ B * l2Norm (z' ()) ^ m)
def BlockImage.Statement : Prop :=
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (k₀ : ι),
    ∃ Q : ArithVariety (fun _ : Unit ↦ n k₀), Q.ideal = P.projIdeal k₀) ∧
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (Ω : Type) [Field Ω] (y : Coord n → Ω) (k₀ : ι)
    (D : ℕ), Geo.IsArithVar (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) (D + 1) →
    (Geo.mCoordIdeal (ι := blockIdx n) y).comap (rename (blockIncl k₀)) =
        Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) ∧
      (Geo.Birational (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩) →
        Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ n k₀)
          (Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ n k₀) (fun p ↦ y ⟨k₀, p.2⟩)) (D + 1))
def SectionInjectivity.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (M : HermLine n)
    (k q : ℕ), k < q →
    ∀ (e : IntegralSection P ((M.pow k).mul (HermLine.standard n).inv).deg) (C : ℝ),
      e.toFun ≠ 0 → e.SupNormLE ((M.pow k).mul (HermLine.standard n).inv) C → ∀ t : ℕ,
        (∀ s : IntegralSection P (((M.pow (q - k)).mul (HermLine.standard n)).pow t).deg,
          s.SupNormLE (((M.pow (q - k)).mul (HermLine.standard n)).pow t) (-(t * C)) →
            ∃ s' : IntegralSection P (M.pow (q * t)).deg,
              s'.toFun = s.toFun * e.toFun ^ t ∧ s'.SupNormLE (M.pow (q * t)) 0) ∧
        ∀ s₁ s₂ : IntegralSection P (((M.pow (q - k)).mul (HermLine.standard n)).pow t).deg,
          s₁.toFun * e.toFun ^ t = s₂.toFun * e.toFun ^ t → s₁.toFun = s₂.toFun
def LatticePacking.Statement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (L : Submodule ℤ V), L.FG →
    ∀ B : ℝ, 0 ≤ B → (∀ x ∈ L, x ≠ 0 → Real.exp (-B) ≤ ‖x‖) →
      {x : V | x ∈ L ∧ ‖x‖ ≤ 1}.Finite ∧
        ({x : V | x ∈ L ∧ ‖x‖ ≤ 1}.ncard : ℝ) ≤ Real.exp (Module.finrank ℤ L * (B + Real.log 5))
def HadamardGramBound.Statement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (r : ℕ) (v b : Fin r → V),
    LinearIndependent ℝ v → (∀ i, ‖v i‖ ≤ 1) → (∀ i, v i ∈ Submodule.span ℤ (Set.range b)) →
      0 < (Matrix.of fun i j ↦ @inner ℝ V _ (b i) (b j)).det ∧ (Matrix.of fun i j ↦ @inner ℝ V _ (b i) (b j)).det ≤ 1
def MonomialMap.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (L : HermLine n),
    (∀ k, 0 ≤ L.deg k) → ∀ (q m r : ℕ), r < q →
    ∀ (g : IntegralSection P L.deg) (h : IntegralSection P (HermLine.standard n).deg),
      g.toFun ≠ 0 → g.SupNormLE L 0 → h.toFun ≠ 0 → h.SupNormLE (HermLine.standard n) 0 →
        (∀ s : IntegralSection P (L.pow (q * m + r)).deg, s.SupNormLE (L.pow (q * m + r)) 0 →
          ∃ s' : IntegralSection P (((L.pow q).mul (HermLine.standard n)).pow (m + 1)).deg,
            s'.toFun = s.toFun * g.toFun ^ (q - r) * h.toFun ^ (m + 1) ∧
              s'.SupNormLE (((L.pow q).mul (HermLine.standard n)).pow (m + 1)) 0) ∧
        ∀ s₁ s₂ : IntegralSection P (L.pow (q * m + r)).deg,
          s₁.toFun * g.toFun ^ (q - r) * h.toFun ^ (m + 1) =
            s₂.toFun * g.toFun ^ (q - r) * h.toFun ^ (m + 1) → s₁.toFun = s₂.toFun
def MonomialMapNorm.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (L : HermLine n),
    (∀ k, 0 ≤ L.deg k) → ∀ (q m r : ℕ), r < q →
    ∀ (g : IntegralSection P L.deg) (h : IntegralSection P (HermLine.standard n).deg),
      g.toFun ≠ 0 → g.SupNormLE L 0 → h.toFun ≠ 0 → h.SupNormLE (HermLine.standard n) 0 →
        (∀ s : P.FunField, P.IsNormalSection (L.pow (q * m + r)).deg s →
          P.IsSmallFor (L.pow (q * m + r)) s →
            P.IsNormalSection (((L.pow q).mul (HermLine.standard n)).pow (m + 1)).deg
                (s * g.toFun ^ (q - r) * h.toFun ^ (m + 1)) ∧
              P.IsSmallFor (((L.pow q).mul (HermLine.standard n)).pow (m + 1))
                (s * g.toFun ^ (q - r) * h.toFun ^ (m + 1))) ∧
        ∀ s₁ s₂ : P.FunField, s₁ * g.toFun ^ (q - r) * h.toFun ^ (m + 1) =
          s₂ * g.toFun ^ (q - r) * h.toFun ^ (m + 1) → s₁ = s₂
def SpanningAtDominantWeight.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (Ω : Type) [Field Ω] (y : Coord n → Ω)
    (b : ι → ℕ) (m : ℕ) (x' : Fin (m + 1) → Ω),
    Submodule.span ℤ (Set.range x') = Submodule.span ℤ (monomialValues y b) → ∀ τ : ℕ,
      Geo.secM (ι := blockIdx fun _ : Unit ↦ m) (fun p ↦ x' p.2) (fun _ ↦ τ) =
          Geo.secM (ι := blockIdx n) y (τ • b) ∧
        Geo.secM (ι := blockIdx n) y (τ • b) =
          (Submodule.span ℤ (monomialValues y (τ • b))).toAddSubgroup ∧
        (∀ (A : Geo.HermLine (blockIdx n)) (Q : Ideal (MvPolynomial (Coord n) ℤ)),
          Geo.MonomialsBounded (ι := blockIdx n) Q A b → ∀ z ∈ Geo.mcPts (ι := blockIdx n) Q,
            ∀ μ : Coord n →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = (τ • b) k) → ‖∏ p, z p ^ μ p‖ ≤ A.h z ^ τ) ∧
        ∀ A : Geo.HermLine (blockIdx n), (∀ k, A.a k = b k) →
          Geo.MonomialsBounded (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) A b →
          ∀ μ : Coord n →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = (τ • b) k) →
            Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) y A τ (∏ p, y p ^ μ p)
def LatticePointCount.Statement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (r : ℕ) (b : Fin r → V),
    LinearIndependent ℝ b → ∀ (S : Set V) (C : ℝ), 0 ≤ C → (∀ s ∈ S, ‖s‖ ≤ C) →
      Submodule.span ℤ S = Submodule.span ℤ (Set.range b) →
        {x : V | x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ 1}.Finite ∧
          Real.log ({x : V | x ∈ Submodule.span ℤ (Set.range b) ∧ ‖x‖ ≤ 1}.ncard) ≤
            -(1 / 2) * Real.log (Matrix.of fun i j ↦ @inner ℝ V _ (b i) (b j)).det + r * Real.log (2 * (1 + r * C))
def WeightedDegree.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : ℕ),
    ringKrullDim P.CoordRing = ((D + 1 + Fintype.card ι : ℕ) : WithBot ℕ∞) →
    ∀ (a : Fin D → ι → ℤ) (p : ℕ) [Fact p.Prime],
      NumbersDVR.intNum ℚ (P.ideal.map (MvPolynomial.map (Int.castRingHom ℚ))) a =
        NumbersDVR.cycEval
          (fun W ↦ NumbersDVR.intNum (ZMod p) (W.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) a)
          (NumbersDVR.divCycle P.ideal (C (p : ℤ)))
def GeometricArithmeticNumbers.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : ℕ),
    ringKrullDim P.CoordRing = ((D + 1 + Fintype.card ι : ℕ) : WithBot ℕ∞) →
    ∀ (a : Fin D → ι → ℤ) (p : ℕ) [Fact p.Prime],
      NumbersDVR.intNum ℚ (P.ideal.map (MvPolynomial.map (Int.castRingHom ℚ))) a =
        ∑ᶠ V ∈ Geo.divSupp (ι := blockIdx n) P.ideal (C (p : ℤ)),
          (Geo.multAt (ι := blockIdx n) (P.ideal ⊔ Ideal.span {C (p : ℤ)}) V : ℤ) *
            Geo.geoNum (ι := blockIdx n) D V a
def FibrePoints.Statement : Prop :=
  Geo.DegreeStatement → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (P : ArithVariety n) (D : ℕ),
    ringKrullDim P.CoordRing = ((D + 1 + Fintype.card ι : ℕ) : WithBot ℕ∞) →
    ∀ L : Fin D → Geo.HermLine (blockIdx n), (∀ j, Geo.IsSmoothHerm (L j)) →
      Geo.ptsIntegral (ι := blockIdx n) P.ideal (Geo.pot L) (fun _ ↦ 1) =
        (NumbersDVR.intNum ℚ (P.ideal.map (MvPolynomial.map (Int.castRingHom ℚ)))
          (fun j ↦ (L j).a) : ℝ)
def BoundedMonomials.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (A : HermLine n)
    (s : IntegralSection P A.deg),
    (∀ z ∈ P.points ℂ, ∀ (c c' : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ)
        (e e' : MvPolynomial (Coord n) ℤ),
      IsChartForm P A.deg s.num s.den c d e → IsChartForm P A.deg s.num s.den c' d' e' →
      (∀ k, z k (c k) ≠ 0) → (∀ k, z k (c' k) ≠ 0) →
        ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z) =
          ‖evalCone z e'‖ / (‖evalCone z (chartMonomial c' d')‖ * A.metric z)) ∧
    ∃ C : ℝ, s.SupNormLE A C
def SectionSmall.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (A : HermLine n)
    (s : IntegralSection P A.deg),
    (∀ C : ℝ, s.SupNormLE A C → ∀ p q : MvPolynomial (Coord n) ℤ, P.mkF p = s.toFun * P.mkF q →
      ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ Real.exp C * (‖evalCone z q‖ * A.metric z)) ∧
    (s.SupNormLE A 0 ↔ P.IsSmallFor A s.toFun)
def DualBasisExists.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (F : HermLattice K (r + 1)),
    ∃ (N : ℕ) (φ : Fin (N + 1) → Fin (r + 1) → K), IsDualBasis F.lattice φ
def OneBlockStandard.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e r : ℕ) (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)),
    IsDualBasis (HermLattice.standard K (r + 1)).lattice (oneBlockForms om) ∧
      latticeIdeal (oneBlockForms (r := r) om) = oneBlockIdeal om ∧
      ∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), latticePoint (oneBlockForms om) σ w = oneBlockPoint om σ w
def OneBlockModel.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r N : ℕ) (F : HermLattice K (r + 1))
    (φ : Fin (N + 1) → Fin (r + 1) → K), IsDualBasis F.lattice φ →
    (∃ Q : ArithVariety (fun _ : Unit ↦ N), Q.ideal = latticeIdeal φ) ∧
    Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) = latticeIdeal φ ∧
    Geo.IsArithVar (ι := blockIdx fun _ : Unit ↦ N) (latticeIdeal φ) (r + 1) ∧
    Geo.Birational (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) ∧
    ∀ m : ℕ, 1 ≤ m →
      latticeMap φ '' {f | IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f (fun _ ↦ m)} =
        (Submodule.span (𝓞 K) {p : MvPolynomial (Fin (r + 1)) K |
          ∃ u : Fin m → Fin (r + 1) → K, (∀ i, u i ∈ latticeDual F.lattice) ∧
            p = ∏ i, latticeForm (u i)} : Set _)
open Classical in

def OneBlockPoints.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r N : ℕ) (F : HermLattice K (r + 1))
    (φ : Fin (N + 1) → Fin (r + 1) → K), IsDualBasis F.lattice φ →
    (∀ z ∈ conePoints (latticeIdeal φ) ℂ, ∃! σ : K →+* ℂ,
      ∃ w : Fin (r + 1) → ℂ, w ≠ 0 ∧ z = latticePoint φ σ w) ∧
    (∀ (σ : K →+* ℂ) (w : Fin (r + 1) → ℂ), w ≠ 0 →
      latticePoint φ σ w ∈ conePoints (latticeIdeal φ) ℂ) ∧
    ∀ (σ : K →+* ℂ) (j₀ : Fin (r + 1)), ∃ R : Fin (N + 1) → ℂ, ∀ (τ : K →+* ℂ) (j : Fin (r + 1)),
      ∑ b, R b * τ (φ b j) = if τ = σ ∧ j = j₀ then 1 else 0
def PointHeightDegree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r N : ℕ) (F : HermLattice K (r + 1))
    (φ : Fin (N + 1) → Fin (r + 1) → K), IsDualBasis F.lattice φ →
    (∃ A : HermLine (fun _ : Unit ↦ N), A.deg = 1 ∧ LatticeMetricAgrees φ F A ∧ A.ConjInvariant) ∧
    ∀ A : HermLine (fun _ : Unit ↦ N), A.deg = 1 → LatticeMetricAgrees φ F A →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (v : Fin (r + 1) → K'), v ≠ 0 →
    ∀ τ : K' →+* AlgebraicClosure ℚ,
      height A (latticePoint φ (τ.comp (algebraMap K K')) fun j ↦ τ (v j)) = -F.lineDegree K' v
def PointVariety.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : Coord n → Ω), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
    ∃ P : ArithVariety n, P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y
def ChartLatSection.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (Ω : Type) [Field Ω] (y : Coord n → Ω)
    (P : ArithVariety n) (a : ι → ℤ) (τ : ℕ) (s : Ω), P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y →
    (s ∈ Geo.chartLat (ι := blockIdx n) y a τ ↔
      ∃ t : IntegralSection P (τ • a), P.Reads y (τ • a) s t.toFun)
def ChartLatNmSection.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (Ω : Type) [Field Ω] (y : Coord n → Ω)
    (P : ArithVariety n) (a : ι → ℤ) (τ : ℕ) (s : Ω), P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y →
    Geo.Birational (ι := blockIdx n) y →
    (s ∈ Geo.chartLatNm (ι := blockIdx n) y a τ ↔
      ∃ t : P.FunField, P.IsNormalSection (τ • a) t ∧ P.Reads y (τ • a) s t)
def ReadsMul.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (Ω : Type) [Field Ω] (y : Coord n → Ω)
    (P : ArithVariety n) (a b : ι → ℤ) (s s' : Ω) (t t' : P.FunField),
    P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y → P.IsOfDegree a t → P.IsOfDegree b t' →
    P.Reads y a s t → P.Reads y b s' t' → P.Reads y (a + b) (s * s') (t * t')
def AddBlockBridge.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (Ω : Type) [Field Ω] (y : Coord n → Ω)
    (P : ArithVariety n) (a : ι → ℤ) (m : ℕ) (x' : Fin (m + 1) → Ω),
    P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y →
    (∀ j, x' j ∈ Geo.chartLat (ι := blockIdx n) y a 1) →
    ArakelovGeometry.KH.GeneratesOn (ι := blockIdx n) y a x' →
    ∃ (D : AddBlockData P) (hm : D.size = m), D.deg = a ∧
      D.BlockReading y (x' ∘ Fin.cast (congrArg (· + 1) hm))
def YPlusArithVar.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (Ω : Type) [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) (E : ℕ), D.BlockReading y x' →
    Geo.IsArithVar (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) (E + 1) →
    Geo.IsArithVar (ι := blockIdx D.extSizes)
      (Geo.mCoordIdeal (ι := blockIdx D.extSizes) (D.plusCoord y x')) (E + 1)
def YPlusSec.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (Ω : Type) [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) (τ : ℕ),
    Geo.secM (ι := blockIdx D.extSizes) (D.plusCoord y x') (Pi.single none τ) =
      Geo.secM (ι := blockIdx fun _ : Unit ↦ D.size) (fun p ↦ x' p.2) (fun _ ↦ τ)
def YPlusMetric.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (Ω : Type) [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω) (N : HermLine n),
    D.BlockReading y x' → N.deg = D.deg → N.ConjInvariant →
    ∃ Ap : HermLine D.extSizes, Ap.deg = AddBlockData.newDeg ∧ Ap.ConjInvariant ∧
      D.InducesMetric y x' N.toGeo Ap.toGeo
def YPlusSmall.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (Ω : Type) [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω)
    (N : Geo.HermLine (blockIdx n)) (Ap : Geo.HermLine (blockIdx D.extSizes)) (τ : ℕ) (s : Ω),
    D.BlockReading y x' → N.a = D.deg → D.InducesMetric y x' N Ap →
    s ∈ Geo.secM (ι := blockIdx D.extSizes) (D.plusCoord y x') (Pi.single none τ) →
    IsSupSmallBlock (D.plusCoord y x') none Ap τ s →
    s ∈ Geo.chartLat (ι := blockIdx n) y N.a τ ∧
      Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) y N τ s
def YPlusSupSmall.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (D : AddBlockData P)
    (Ω : Type) [Field Ω] (y : Coord n → Ω) (x' : Fin (D.size + 1) → Ω)
    (N : Geo.HermLine (blockIdx n)) (Ap : Geo.HermLine (blockIdx D.extSizes)) (τ : ℕ) (s : Ω),
    D.BlockReading y x' → N.a = D.deg → D.InducesMetric y x' N Ap →
    s ∈ Geo.secM (ι := blockIdx D.extSizes) (D.plusCoord y x') (Pi.single none τ) →
    Geo.IsSmallH (ι := blockIdx n) (Geo.mCoordIdeal (ι := blockIdx n) y) y N τ s →
    IsSupSmallBlock (D.plusCoord y x') none Ap τ s
section Examples
variable {ι : Type} [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (k₀ : ι)
end Examples
end
end GroundTheory.Heights₂.Heights


