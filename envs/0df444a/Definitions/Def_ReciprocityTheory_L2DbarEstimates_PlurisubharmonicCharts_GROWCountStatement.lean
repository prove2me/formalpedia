-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
-- name    : ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:34.358287+00:00
-- url     : https://prove2.me/theorems/d52f24b3-84f6-4ad7-b9ae-a00a87a612b2
-- title:
--   GROWCount Statement
-- statement:
--   Definitions and structural lemmas for GROWCount Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/PlurisubharmonicCharts/GROWCountStatement.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
def HAll.{v} (n : ℕ) : Prop :=
  ∀ (M : Type v) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M], HStatement n M
def SAll.{v} (n : ℕ) : Prop :=
  ∀ (M : Type v) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M], SStatement n M
def NORMAll.{v} (n : ℕ) : Prop :=
  ∀ (M : Type v) [TopologicalSpace M], NORMStatement n M
def LSEAll.{v} (n : ℕ) : Prop :=
  ∀ (M : Type v) [TopologicalSpace M], LSEStatement n M
open WeightedAtlas
def InhStatement (n : ℕ) : Prop :=
  ∀ hn : 1 ≤ n, ∃ (A : WeightedAtlas n (V n) Unit ℤ) (w : Fin (n + 1) → Unit → V n → ℂ)
    (w0 : Unit → V n → ℂ) (s : Fin n → Unit → V n → ℂ),
    A.D0 1 w w0 s ∧ A.Flat w0 s 1 ∧ A.Flat w0 s (MvPolynomial.X ⟨0, hn⟩) ∧
    (∃ C : ℝ, ∀ y, A.sqn 1 w y ≤ C) ∧
    (∀ i y (ξ : Fin n → ℂ), ξ ≠ 0 → 0 < A.leviAt i (A.ph 1 i) y ξ) ∧
    A.IsFrameOn (A.kap + 1) (A.Mset w0 s 1) (fun _ _ => 1)
def HYStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (L la : La) (N : ℕ) (w : Fin N → ι → Y → ℂ)
    (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ)
    (σ : ι → Y → ℂ) (ps : Y → ℝ) (F0 : ι → Y → ℂ) (h : Y → ℝ≥0∞),
    A.D0 L w w0 s → A.Flat w0 s De → A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ →
    A.SmoothFn ps → A.Pos la ps → A.IsSSec (A.kap + la) F0 → Measurable h →
    (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      ENNReal.ofReal (‖A.dbarAt i F0 y ξ‖ ^ 2 * Real.exp (-A.ph (A.kap + la) i y)) ≤
        h y * ENNReal.ofReal (A.leviAt i (fun x => A.ph la i x + ps x) y ξ)) →
    ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧
      ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) (F0 - F) y * Real.exp (-ps y)) ∂A.mu ≤
        ∫⁻ y, h y * ENNReal.ofReal (Real.exp (-ps y)) ∂A.mu
def AStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (L la : La) (N : ℕ) (w : Fin N → ι → Y → ℂ)
    (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ)
    (σ : ι → Y → ℂ) (ps1 : Y → ℝ) (η : ℝ) (c : Y → ℂ),
    A.D0 L w w0 s → A.Flat w0 s De → A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ →
    (∃ C : ℝ, ∀ y, A.sqn L w y ≤ C) → A.Pos L (fun _ => 0) → A.SmoothFn ps1 → 0 < η →
    (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      2 * η * A.leviAt i (A.ph L i) y ξ ≤ A.leviAt i (fun x => A.ph (la - n • L) i x + ps1 x) y ξ) →
    (∃ U : Set Y, IsOpen U ∧ A.zeroSet s ⊆ U ∧ ∀ i y, y ∈ (A.chart i).source → y ∈ U →
      ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph L i) y ξ) →
    ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧
      ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) F y * Real.exp (-ps1 y) *
        A.sqn L w y ^ (-η)) ∂A.mu < ⊤ ∧
      ∀ P ∈ A.zeroSet s, F (A.pick P) P = c P
def AApproxStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (L la : La) (N : ℕ) (w : Fin N → ι → Y → ℂ)
    (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ)
    (σ : ι → Y → ℂ) (ps1 : Y → ℝ) (η : ℝ) (c : Y → ℂ) (ε : ℝ),
    A.D0 L w w0 s → A.Flat w0 s De → A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ →
    (∃ C : ℝ, ∀ y, A.sqn L w y ≤ C) → A.Pos L (fun _ => 0) → A.SmoothFn ps1 → 0 < η → 0 < ε →
    (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      2 * η * A.leviAt i (A.ph L i) y ξ ≤ A.leviAt i (fun x => A.ph (la - n • L) i x + ps1 x) y ξ) →
    (∃ U : Set Y, IsOpen U ∧ A.zeroSet s ⊆ U ∧ ∀ i y, y ∈ (A.chart i).source → y ∈ U →
      ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph L i) y ξ) →
    ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧
      ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) F y * Real.exp (-ps1 y) *
        A.sqn L w y ^ (-η)) ∂A.mu < ⊤ ∧
      ∀ P ∈ A.zeroSet s, ‖F (A.pick P) P - c P‖ ≤ ε
def APrimeStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*)
    [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (L la : La) (N : ℕ) (w : Fin N → ι → Y → ℂ)
    (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ)
    (σ : ι → Y → ℂ) (d m : ℕ) (r r' θ : ℝ) (B : Fin m → Set Y)
    (π : Fin m → Y → EuclideanSpace ℂ (Fin d)) (yA : Fin m → Y) (f : Fin m → ι → Y → ℂ)
    (ps1 : Y → ℝ),
    A.D0 L w w0 s → A.Flat w0 s De → A.IsFrameOn (A.kap + la) (A.Mset w0 s De) σ →
    1 ≤ d → 0 < r → r < r' → 0 < θ → θ < 1 →
    (∀ a, IsOpen (B a)) → Pairwise (Function.onFun Disjoint B) →
    (∀ a i, DifferentiableOn ℂ (π a ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' B a)) →
    (∀ a, ∀ y ∈ B a, Function.Surjective
      (fderiv ℂ (π a ∘ (A.chart (A.pick y)).symm) (A.chart (A.pick y) y))) →
    (∀ a, ∀ y ∈ B a, ‖π a y‖ < r') →
    (∀ a (K : Set (EuclideanSpace ℂ (Fin d))), IsCompact K → K ⊆ Metric.ball 0 r' →
      IsCompact (B a ∩ π a ⁻¹' K)) →
    (∀ a, yA a ∈ B a) → (∀ a, π a (yA a) = 0) →
    (∀ a, A.IsSecOn (A.kap + la) (B a) (f a)) →
    A.SmoothFn ps1 → A.Pos la ps1 →
    (∀ a i y, y ∈ (A.chart i).source → y ∈ B a → ‖π a y‖ ≤ r → ∀ ξ : Fin n → ℂ, ξ ≠ 0 →
      (d : ℝ) / (θ * r ^ 2) * A.leviAt i (fun x => ‖π a x‖ ^ 2) y ξ <
        A.leviAt i (fun x => A.ph la i x + ps1 x) y ξ) →
    ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧
      ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) F y * Real.exp (-ps1 y)) ∂A.mu < ⊤ ∧
      ∀ a, F (A.pick (yA a)) (yA a) = f a (A.pick (yA a)) (yA a)
def BStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (L mu0 : La) (N : ℕ) (w : Fin N → ι → Y → ℂ)
    (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ)
    (σ : ι → Y → ℂ) (T : ℕ) (f : ι → Y → ℂ),
    2 ≤ n → A.D0 L w w0 s → A.Flat w0 s De → (∃ i0 : Fin n, MvPolynomial.X i0 ∣ De) →
    A.IsFrameOn mu0 (A.Mset w0 s De) σ → A.Pos (mu0 - A.kap) (fun _ => 0) → n + 1 ≤ T →
    A.IsSec (mu0 + T • L) f →
    ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + T • L) f y * A.sqn L w y ^ (-(T : ℝ))) ∂A.mu < ⊤ →
    (∀ P ∈ A.zeroSet s, A.VanishOrd f P (T - n)) →
    ∃ hh : (Fin n → ℕ) → ι → Y → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple n (T - n), A.IsSec (mu0 + n • L) (hh α) ∧
        ∫⁻ y, ENNReal.ofReal (A.nsq (mu0 + n • L) (hh α) y * A.sqn L w y ^ (-(n : ℝ))) ∂A.mu
          < ⊤) ∧
      ∀ i y, y ∈ (A.chart i).source →
        f i y = ∑ α ∈ Finset.Nat.antidiagonalTuple n (T - n), (∏ k, s k i y ^ α k) * hh α i y
def IMMStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (L de : La) (N m : ℕ) (w : Fin N → ι → Y → ℂ)
    (a : ι → Y → ℂ),
    (∀ k, A.IsSec L (w k)) → (∀ y, ∃ k, w k (A.pick y) y ≠ 0) → 1 ≤ m →
    A.IsSec (m • de) a → (∃ y, a (A.pick y) y ≠ 0) →
    (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 →
      0 < A.leviAt i (A.ph (L - de) i) y ξ) →
    Tendsto (fun y => A.nsq (m • de) a y / A.sqn L w y ^ m) (cocompact Y) (𝓝 0) →
    ∃ y, ∀ ξ : Fin n → ℂ, ξ ≠ 0 →
      0 < A.leviAt (A.pick y) (fun x => Real.log (∑ k, ‖w k (A.pick y) x‖ ^ 2)) y ξ
def ZEROStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*)
    [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (L : La) (N : ℕ) (w : Fin N → ι → Y → ℂ)
    (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ) (m : ℕ)
    (Nsec : ι → Y → ℂ),
    ConnectedSpace Y → A.D0 L w w0 s → A.Flat w0 s De → MvPolynomial.constantCoeff De ≠ 0 →
    (∃ C : ℝ, ∀ y, A.sqn L w y ≤ C * (A.nsq L w0 y + A.sqn L s y)) →
    A.IsSec (m • L) Nsec → (∃ C : ℝ, ∀ y, A.nsq (m • L) Nsec y ≤ C * A.sqn L w y ^ m) →
    (∀ P ∈ A.zeroSet s, A.VanishOrd Nsec P (m + 1)) →
    ∀ i y, y ∈ (A.chart i).source → Nsec i y = 0
def ZERODimStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*)
    [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (L ε β : La) (N : ℕ) (w : Fin N → ι → Y → ℂ)
    (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ) (k e r : ℕ)
    (b : ι → Y → ℂ) (f : Fin r → ι → Y → ℂ),
    ConnectedSpace Y → A.D0 L w w0 s → A.Flat w0 s De → MvPolynomial.constantCoeff De ≠ 0 →
    (∃ C : ℝ, ∀ y, A.sqn L w y ≤ C * (A.nsq L w0 y + A.sqn L s y)) →
    1 ≤ k → k • ε + β = (k * e) • L → A.IsSec β b → (∃ y, b (A.pick y) y ≠ 0) →
    (∀ j, A.IsSec ε (f j)) →
    (∀ c : Fin r → ℂ, (∀ i y, y ∈ (A.chart i).source → ∑ j, c j * f j i y = 0) → c = 0) →
    (∀ c : Fin r → ℂ, ∃ C : ℝ, ∀ y,
      A.nsq ((k * e) • L) (fun i x => (∑ j, c j * f j i x) ^ k * b i x) y ≤
        C * A.sqn L w y ^ (k * e)) →
    r ≤ (A.zeroSet s).ncard * (e + n).choose n
def INDStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (L lam : La) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ)
    (S : Finset Y) (F : Y → ι → Y → ℂ) (j : ℕ) (c : Y → (Fin n → ℕ) → ℂ),
    A.IsSec L w0 → A.IsSSec L w0 → (∀ k, A.IsSec L (s k)) → (∀ k, A.IsSSec L (s k)) →
    (∀ P ∈ S, ∀ k, s k (A.pick P) P = 0) → (∀ P ∈ S, w0 (A.pick P) P ≠ 0) →
    (∀ P ∈ S, A.IsCoordAt w0 s P) →
    (∀ P ∈ S, A.IsSec lam (F P)) → (∀ P ∈ S, A.IsSSec lam (F P)) →
    (∀ P ∈ S, F P (A.pick P) P ≠ 0) → (∀ P ∈ S, ∀ P' ∈ S, P' ≠ P → F P (A.pick P') P' = 0) →
    (∀ P' ∈ S, A.VanishOrd (fun i y => ∑ P ∈ S, ∑ α ∈ multiLe n j,
      c P α * (∏ k, s k i y ^ α k) * w0 i y ^ (j - ∑ k, α k) * F P i y) P' (j + 1)) →
    ∀ P ∈ S, ∀ α ∈ multiLe n j, c P α = 0
def INDCountStatement : Prop :=
  ∀ n j : ℕ, (multiLe n j).card = (j + n).choose n
def CMPStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (la : La) (a b : Y → ℝ),
    A.SmoothFn a → A.SmoothFn b → A.Pos la a → A.Pos la b →
    Tendsto (fun y => b y - a y) (cocompact Y) atBot →
    ∫⁻ y, A.maDens la b y ∂A.mu ≤ ∫⁻ y, A.maDens la a y ∂A.mu
def CMPDegStatement (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*)
    [AddCommGroup La] : Prop :=
  ∀ (A : WeightedAtlas n Y ι La) (L : La) (N : ℕ) (w : Fin N → ι → Y → ℂ)
    (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (De : MvPolynomial (Fin n) ℂ),
    1 ≤ n → A.D0 L w w0 s → A.Flat w0 s De →
    ∫⁻ y in A.Mset w0 s De, ENNReal.ofReal
        ((A.hessAt (A.pick y) (fun x => Real.log (‖w0 (A.pick y) x‖ ^ 2 +
          ∑ k, ‖s k (A.pick y) x‖ ^ 2)) y).det.re * Real.exp (-A.ph A.kap (A.pick y) y)) ∂A.mu =
      ((A.zeroSet s).ncard : ℝ≥0∞) *
        ∫⁻ v : V n, ENNReal.ofReal ((1 + ‖v‖ ^ 2) ^ (-((n : ℝ) + 1)))
def GROWCountStatement.{u1, u2} : Prop :=
  ∀ (X : Type u1) [MeasurableSpace X] (μ : Measure X) (Γ : Type u2) [Group Γ] [MulAction Γ X]
    [Countable Γ] [MeasurableSpace Γ] [MeasurableSMul Γ X] [SMulInvariantMeasure Γ X μ]
    (D B : Set X) (φ : X → ℝ≥0∞) (m : ℕ),
    IsFundamentalDomain Γ D μ → MeasurableSet B → Measurable φ →
    (∀ (γ : Γ) x, φ (γ • x) = φ x) →
    (∀ T : Finset Γ, (∀ γ ∈ T, (γ • B ∩ B).Nonempty) → T.card ≤ m) →
    ∫⁻ x in B, φ x ∂μ ≤ m * ∫⁻ x in D, φ x ∂μ
def GROWStatement.{u1, u2} : Prop :=
  ∀ (X : Type u1) [MeasurableSpace X] (μ : Measure X) (Γ : Type u2) [Group Γ] [MulAction Γ X]
    [Countable Γ] [MeasurableSpace Γ] [MeasurableSMul Γ X] [SMulInvariantMeasure Γ X μ]
    (D B : Set X) (F : X → ℂ) (ps : X → ℝ) (x' : X) (C : ℝ≥0∞) (Sup : ℝ) (m : ℕ),
    IsFundamentalDomain Γ D μ → MeasurableSet B → Measurable F → Measurable ps →
    (∀ (γ : Γ) x, ‖F (γ • x)‖ ^ 2 * Real.exp (-ps (γ • x)) = ‖F x‖ ^ 2 * Real.exp (-ps x)) →
    (∀ T : Finset Γ, (∀ γ ∈ T, (γ • B ∩ B).Nonempty) → T.card ≤ m) →
    ENNReal.ofReal (‖F x'‖ ^ 2) ≤ C * ∫⁻ x in B, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ →
    (∀ x ∈ B, ps x ≤ Sup) →
    ENNReal.ofReal (‖F x'‖ ^ 2) ≤
      C * m * ENNReal.ofReal (Real.exp Sup) *
        ∫⁻ x in D, ENNReal.ofReal (‖F x‖ ^ 2 * Real.exp (-ps x)) ∂μ
def tube (f : ℕ) (Ω : Set (Fin f → ℝ)) : Set (Fin f → ℂ) :=
  {s | (fun k => (s k).im) ∈ Ω}
def fourCoeff {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ) (ν : Fin f → ℤ) : ℂ :=
  ∫ x in Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1),
    h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) *
      Complex.exp (-2 * Real.pi * Complex.I *
        ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I))
def FOURIndepStatement (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h : (Fin f → ℂ) → ℂ),
    IsOpen Ω → IsPreconnected Ω → DifferentiableOn ℂ h (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h (s + fun k => (m k : ℂ)) = h s) →
    ∀ b ∈ Ω, ∀ b' ∈ Ω, ∀ ν, fourCoeff h b ν = fourCoeff h b' ν
def FOURBoundStatement (f : ℕ) : Prop :=
  ∀ (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ) (ν : Fin f → ℤ) (C : ℝ),
    (∀ x : Fin f → ℝ, ‖h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I)‖ ≤ C) →
    ‖fourCoeff h b ν‖ * Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) ≤ C
def FOURSignStatement (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h : (Fin f → ℂ) → ℂ) (b0 κ : Fin f → ℝ) (C E : ℝ),
    IsOpen Ω → IsPreconnected Ω → DifferentiableOn ℂ h (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h (s + fun k => (m k : ℂ)) = h s) →
    (∀ t : ℝ, 0 ≤ t → b0 + t • κ ∈ Ω) →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Fin f → ℝ,
      ‖h (fun k => (x k : ℂ) + ((b0 + t • κ) k : ℂ) * Complex.I)‖ ≤ C * (1 + t) ^ E) →
    ∀ ν : Fin f → ℤ, fourCoeff h b0 ν ≠ 0 → 0 ≤ ∑ k, (ν k : ℝ) * κ k
def FOURSumStatement (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h : (Fin f → ℂ) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ h (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h (s + fun k => (m k : ℂ)) = h s) → (0 : Fin f → ℝ) ∈ Ω →
    Summable (fun ν : Fin f → ℤ => ‖fourCoeff h 0 ν‖) →
    ∀ x : Fin f → ℝ, HasSum (fun ν : Fin f → ℤ => fourCoeff h 0 ν *
      Complex.exp (2 * Real.pi * Complex.I * ∑ k, (ν k : ℂ) * (x k : ℂ))) (h (fun k => (x k : ℂ)))
def UNITrStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (γ : Matrix (Fin r) (Fin r) E) (g : ℤ),
    3 * (r : ℤ) < g →
    (∀ k, 1 ≤ k → k ≤ r → ∃ y : NumberField.RingOfIntegers E,
      (γ ^ k).trace - (r : E) = (g : E) * (y : E)) →
    (∀ k, 1 ≤ k → k ≤ r → ∀ τ : E →+* ℂ, ‖τ ((γ ^ k).trace)‖ ≤ r * Real.exp (1 / 3)) →
    IsNilpotent (γ - 1)
def UNIHSStatement : Prop :=
  ∀ (r : ℕ) (γ : Matrix (Fin r) (Fin r) ℂ), IsNilpotent (γ - 1) →
    (∀ v : Fin r → ℂ, ∑ i, ‖(γ *ᵥ v) i‖ ^ 2 ≤ Real.exp (2 / (3 * r)) * ∑ i, ‖v i‖ ^ 2) →
    ∑ i, ∑ j, ‖(γ - 1) i j‖ ^ 2 < 1
def gramDet {N s : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (b : Fin s → Fin N → ℤ) : ℝ :=
  (Matrix.of fun a c => ∑ i, ∑ j, (b a i : ℝ) * G i j * (b c j : ℝ)).det
def qf {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * G i j * x j
def UNILatStatement : Prop :=
  ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℝ) (R : Set (Matrix (Fin N) (Fin N) ℤ)) (κ c : ℝ)
    (φ : Matrix (Fin N) (Fin N) ℤ),
    G.PosDef → 0 < κ → 0 ≤ c → c < 1 →
    (∀ (s : ℕ) (b : Fin s → Fin N → ℤ), LinearIndependent ℤ b →
      (∀ ρ ∈ R, ∀ a, ρ *ᵥ b a ∈ Submodule.span ℤ (Set.range b)) → κ ^ s ≤ gramDet G b) →
    G.det = κ ^ N →
    (∀ ρ ∈ R, φ * ρ = ρ * φ) →
    (∀ x : Fin N → ℝ, qf G (φ.map (Int.cast : ℤ → ℝ) *ᵥ x) ≤ c ^ 2 * qf G x) →
    φ = 0
end
end ReciprocityTheory.L2DbarEstimates.Y


