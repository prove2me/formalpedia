-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementLE
-- name    : Formalism_HermitianCurvature_StatementLE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:35:53.670861+00:00
-- url     : https://prove2.me/theorems/cf73b33c-8a9f-49ca-908c-7c2bc49c9f1d
-- title:
--   Statement LE
-- statement:
--   Definitions and structural lemmas for Statement LE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementLE.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
def ld (p : ℕ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  iteratedDeriv p (fun u : ℝ => φ (Real.exp u)) (Real.log x)
def SmoothLog (φ : ℝ → ℝ) : Prop := ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => φ (Real.exp u))
def th (ε σ : ℝ) (x : ℝ) : ℝ := (x / (x + ε)) ^ σ
structure Cut where

  χ : ℝ → ℝ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ
  zero : ∀ x, x ≤ 1 / 2 → χ x = 0
  one : ∀ x, 1 ≤ x → χ x = 1
  nonneg : ∀ x, 0 ≤ χ x
  le_one : ∀ x, χ x ≤ 1
def Cut.sc (c : Cut) (ε : ℝ) (m : ℕ) (x : ℝ) : ℝ := c.χ (x / ε) ^ m
def ThetaForm : Prop :=
  ∀ ε σ : ℝ, 0 < ε → ∀ v : ℝ, th ε σ (Real.exp v) = (1 + ε * Real.exp (-v)) ^ (-σ)
def ThetaRange : Prop :=
  ∀ ε σ x : ℝ, 0 < ε → 0 ≤ σ → 0 < x → 0 < th ε σ x ∧ th ε σ x ≤ 1
def ThetaSmooth : Prop := ∀ ε σ : ℝ, 0 < ε → SmoothLog (th ε σ)
def ThetaBound : Prop :=
  E.CauchyTheta → ∀ σ ε : ℝ, 4 ≤ σ → 0 < ε → ∀ (p : ℕ) (x : ℝ), 0 < x →
    |ld p (th ε σ) x| ≤ Real.exp 1 * p.factorial * (4 * σ) ^ p * th ε σ x
def ThetaLimit : Prop :=
  ∀ (σ : ℝ) (p : ℕ) (x : ℝ), 0 < x →
    Tendsto (fun ε : ℝ => ld p (th ε σ) x) (𝓝[>] 0) (𝓝 (if p = 0 then 1 else 0))
def ThetaMono : Prop :=
  ∀ σ ε ε' x : ℝ, 0 ≤ σ → 0 < ε → ε ≤ ε' → 0 < x → th ε' σ x ≤ th ε σ x
def CutBound : Prop :=
  ∀ (c : Cut) (m p : ℕ), 1 ≤ m → ∃ C : ℝ, ∀ ε x : ℝ, 0 < ε → 0 < x →
    |ld p (c.sc ε m) x| ≤ C ∧ (x < ε / 2 → ld p (c.sc ε m) x = 0) ∧
      (ε < x → ld p (c.sc ε m) x = if p = 0 then 1 else 0)
def CutTheta : Prop :=
  E.CauchyTheta → ∀ (c : Cut) (σ ε : ℝ), 4 ≤ σ → 0 < ε → ∀ p : ℕ, ∃ C : ℝ,
    ∀ ε₂ x : ℝ, 0 < ε₂ → 0 < x →
      |ld p (fun y => c.sc ε₂ 1 y * th ε σ y) x| ≤ C * th ε σ x ∧
        (ε₂ < x → ld p (fun y => c.sc ε₂ 1 y * th ε σ y) x = ld p (th ε σ) x)
structure Base where

  Ω : Type
  [mΩ : MeasurableSpace Ω]

  μ : Measure Ω

  G : Ω → ℝ
  G_pos : ∀ ω, 0 < G ω
  G_meas : Measurable G
attribute [instance] Base.mΩ
abbrev Fn (B : Base) (A : Type) := B.Ω → A → ℂ
section ops
variable (B : Base) {A A' : Type}
def mulF (φ : ℝ → ℝ) (u : Fn B A) : Fn B A := fun ω a => (φ (B.G ω) : ℂ) * u ω a
def conjS (T : Fn B A → Fn B A') (u : Fn B A) (s : ℝ) : Fn B A' :=
  fun ω a => (((B.G ω) ^ (-s) : ℝ) : ℂ) * T (mulF B (fun x => x ^ s) u) ω a
def dS (T : Fn B A → Fn B A') (u : Fn B A) (p : ℕ) : Fn B A' :=
  fun ω a => iteratedDeriv p (fun s : ℝ => conjS B T u s ω a) 0
def sq [Fintype A] (wt : B.Ω → A → ℝ) (u : Fn B A) (ω : B.Ω) : ℝ := ∑ a, wt ω a * ‖u ω a‖ ^ 2
def pr [Fintype A] (wt : B.Ω → A → ℝ) (u v : Fn B A) (ω : B.Ω) : ℂ :=
  ∑ a, (wt ω a : ℂ) * u ω a * conj (v ω a)
def JetLocal (T : Fn B A → Fn B A') (u : Fn B A) : Prop :=
  ∃ (m : ℕ) (c : ℕ → Fn B A'), ∀ φ : ℝ → ℝ, SmoothLog φ → ∀ ω a,
    T (mulF B φ u) ω a = ∑ q ∈ range (m + 1), (ld q φ (B.G ω) : ℂ) * c q ω a
def PolyS (T : Fn B A → Fn B A') (u : Fn B A) (d : ℕ) : Prop :=
  ∃ c : ℕ → Fn B A', ∀ (s : ℝ) ω a, conjS B T u s ω a = ∑ q ∈ range (d + 1), (s : ℂ) ^ q * c q ω a
def WeightedL2 (wt : B.Ω → ℝ) (f : B.Ω → ℂ) : Prop :=
  AEStronglyMeasurable f B.μ ∧ Integrable (fun ω => wt ω * ‖f ω‖ ^ 2) B.μ
end ops
def Leibniz : Prop :=
  ∀ (B : Base) (A A' : Type) (T : Fn B A → Fn B A') (u : Fn B A) (d : ℕ),
    JetLocal B T u → PolyS B T u d → ∀ φ : ℝ → ℝ, SmoothLog φ → ∀ ω a,
      T (mulF B φ u) ω a = ∑ p ∈ range (d + 1), (ld p φ (B.G ω) : ℂ) * dS B T u p ω a / p.factorial
structure Step (B : Base) where

  ι : Type
  [fι : Fintype ι]

  r : ℕ

  X : Fn B ι

  dw : B.Ω → ι → ℝ

  g : ℝ → Fn B ι → Fn B (Bool × ι)

  gst : ℝ → Fn B (Bool × ι) → Fn B ι

  d : ℝ → B.Ω → Bool × ι → ℝ

  ee : ℝ → B.Ω → Matrix ι ι ℂ

  P : ℝ → ℝ

  a : ℝ

  L : ℝ
attribute [instance] Step.fι
namespace Step
variable {B : Base} (S : Step B)
def J : Set ℝ := Set.Icc S.a (S.a + S.L)
def gX (Y : ℝ) : Fn B (Bool × S.ι) := S.g Y S.X
def gs (Y s : ℝ) : Fn B (Bool × S.ι) := conjS B (S.g Y) S.X s
def ds (Y : ℝ) (p : ℕ) : Fn B (Bool × S.ι) := dS B (S.g Y) S.X p
def En (ε σ Y : ℝ) : ℝ := ∫ ω, th ε σ (B.G ω) * sq B (S.d Y) (S.gX Y) ω ∂B.μ
def Ens (ε σ Y s : ℝ) : ℝ := ∫ ω, th ε σ (B.G ω) * sq B (S.d Y) (S.gs Y s) ω ∂B.μ
def Dn (ε σ Y : ℝ) (p : ℕ) : ℝ := ∫ ω, th ε σ (B.G ω) * sq B (S.d Y) (S.ds Y p) ω ∂B.μ
def Eset (ε σ : ℝ) : Set ℝ := (fun Y => S.En ε σ Y / |S.P Y|) '' S.J
def Esup (ε σ : ℝ) : ℝ := sSup (S.Eset ε σ)
def A0 : ℝ := ∫ ω, sq B S.dw S.X ω ∂B.μ
def Ath (ε σ : ℝ) : ℝ := ∫ ω, th ε σ (B.G ω) * sq B S.dw S.X ω ∂B.μ
def term (ε σ Y : ℝ) (p : ℕ) : ℂ :=
  (∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * pr B (S.d Y) (S.gX Y) (S.ds Y p) ω ∂B.μ) / p.factorial
def Meas : Prop :=
  (∀ i, Measurable fun ω => S.X ω i) ∧ (∀ i, Measurable fun ω => S.dw ω i) ∧
    ∀ Y ∈ S.J, (∀ k, Measurable fun ω => S.d Y ω k) ∧ ∀ s k, Measurable fun ω => S.gs Y s ω k
def WPos : Prop := (∀ ω i, 0 < S.dw ω i) ∧ ∀ Y ∈ S.J, ∀ ω k, 0 < S.d Y ω k
def PReg : Prop := ContinuousOn S.P S.J ∧ ∀ Y ∈ S.J, S.P Y ≠ 0
def I3 : Prop :=
  ∀ Y ∈ S.J, ∀ ω i, S.gst Y (fun ω k => (S.d Y ω k : ℂ) * S.gX Y ω k) ω i = (|S.P Y| * S.dw ω i : ℝ) * S.X ω i
def AdjB (c : Cut) (σ : ℝ) : Prop :=
  ∀ Y ∈ S.J, ∀ ε ε₂ : ℝ, 0 < ε → 0 < ε₂ →
    ∫ ω, pr B (fun _ _ => 1) (S.gst Y (fun ω k => (S.d Y ω k : ℂ) * S.gX Y ω k))
        (mulF B (fun y => c.sc ε₂ 1 y * th ε σ y) S.X) ω ∂B.μ =
      ∫ ω, pr B (S.d Y) (S.gX Y) (S.g Y (mulF B (fun y => c.sc ε₂ 1 y * th ε σ y) S.X)) ω ∂B.μ
def Jet : Prop := ∀ Y ∈ S.J, JetLocal B (S.g Y) S.X
def I4 : Prop := ∀ Y ∈ S.J, PolyS B (S.g Y) S.X (S.r + 1)
def I4' (σ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (∀ Y ∈ S.J, ∀ s : ℝ, Integrable (fun ω => th ε σ (B.G ω) * sq B (S.d Y) (S.gs Y s) ω) B.μ) ∧
      ContinuousOn (S.En ε σ) S.J
def ShiftFormula : Prop :=
  ∀ Y s : ℝ, Y ∈ S.J → Y + s ∈ S.J → ∀ ω i,
    S.gs Y s ω (false, i) = S.gX (Y + s) ω (false, i) ∧
    S.gs Y s ω (true, i) = S.gX (Y + s) ω (true, i) +
      ∑ j, (S.ee Y ω i j - S.ee (Y + s) ω i j) * S.gX (Y + s) ω (false, j)
def Residues (CR : ℝ) : Prop :=
  ∀ Y s : ℝ, Y ∈ S.J → Y + s ∈ S.J → ∀ ω (v : S.ι → ℂ),
    ∑ i, S.d Y ω (true, i) * ‖∑ j, (S.ee Y ω i j - S.ee (Y + s) ω i j) * v j‖ ^ 2 ≤
      CR ^ 2 * ∑ i, S.d Y ω (false, i) * ‖v i‖ ^ 2
def WeightRatio (Cd : ℝ) : Prop :=
  ∀ Y s : ℝ, Y ∈ S.J → Y + s ∈ S.J → ∀ ω k, S.d Y ω k ≤ Cd * S.d (Y + s) ω k
def PRatio (CP : ℝ) : Prop := ∀ Y s : ℝ, Y ∈ S.J → Y + s ∈ S.J → |S.P (Y + s)| ≤ CP * |S.P Y|
def Imports (c : Cut) (σ CR Cd CP : ℝ) : Prop :=
  S.Meas ∧ S.WPos ∧ S.PReg ∧ S.I3 ∧ S.AdjB c σ ∧ S.Jet ∧ S.I4 ∧ S.I4' σ ∧ S.ShiftFormula ∧ S.Residues CR ∧
    S.WeightRatio Cd ∧ S.PRatio CP
def Star (σ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Y ∈ S.J, ((|S.P Y| * S.Ath ε σ : ℝ) : ℂ) = ∑ p ∈ range (S.r + 2), S.term ε σ Y p
def CoefInt (σ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Y ∈ S.J, ∀ p : ℕ,
    Integrable (fun ω => th ε σ (B.G ω) * sq B (S.d Y) (S.ds Y p) ω) B.μ
end Step
def C7 (CR Cd CP : ℝ) : ℝ := Cd * CP * (1 + CR) ^ 2
def TermZero : Prop :=
  ∀ (B : Base) (S : Step B) (ε σ Y : ℝ), S.term ε σ Y 0 = (S.En ε σ Y : ℂ)
def DsMeas : Prop :=
  ∀ (B : Base) (S : Step B), S.Meas → S.I4 → ∀ Y ∈ S.J, ∀ (p : ℕ) k, Measurable fun ω => S.ds Y p ω k
def CoefIntegrable : Prop :=
  ∀ (B : Base) (S : Step B) (σ : ℝ), 0 ≤ σ → S.Meas → S.WPos → S.I4 → S.I4' σ → S.CoefInt σ
def Adj : Prop :=
  E.CauchyTheta → Leibniz → CutTheta → CoefIntegrable → ThetaSmooth → ThetaRange →
  ∀ (B : Base) (S : Step B) (c : Cut) (σ : ℝ), 4 ≤ σ →
    S.Meas → S.WPos → S.I3 → S.AdjB c σ → S.Jet → S.I4 → S.I4' σ →
    Integrable (sq B S.dw S.X) B.μ → S.Star σ
def EFinite : Prop :=
  ∀ (B : Base) (S : Step B) (σ ε : ℝ), 0 < ε → S.PReg → S.I4' σ → BddAbove (S.Eset ε σ)
def CSTerm : Prop :=
  ThetaBound → E.CauchyTheta →
  ∀ (B : Base) (S : Step B) (σ ε : ℝ), 4 ≤ σ → 0 < ε → S.Meas → S.WPos → S.I4 → S.I4' σ → S.CoefInt σ →
    ∀ Y ∈ S.J, ∀ p : ℕ,
      ‖S.term ε σ Y p‖ ≤ Real.exp 1 * (4 * σ) ^ p * √(S.En ε σ Y) * √(S.Dn ε σ Y p)
def ShiftBound : Prop :=
  ∀ (B : Base) (S : Step B) (σ ε CR Cd CP : ℝ), 0 ≤ σ → 0 < ε → 0 ≤ CR → 0 ≤ Cd → 0 ≤ CP →
    S.Meas → S.WPos → S.PReg → S.I4' σ → S.ShiftFormula → S.Residues CR → S.WeightRatio Cd → S.PRatio CP →
    BddAbove (S.Eset ε σ) →
    ∀ Y s : ℝ, Y ∈ S.J → Y + s ∈ S.J → S.Ens ε σ Y s ≤ C7 CR Cd CP * S.Esup ε σ * |S.P Y|
def MarkovTerm : Prop :=
  E.MarkovVector →
  ∀ (B : Base) (S : Step B) (σ ε M : ℝ), 0 ≤ σ → 0 < ε → 0 < S.L → S.Meas → S.WPos → S.I4 → S.I4' σ →
    ∀ Y ∈ S.J, (∀ s : ℝ, Y + s ∈ S.J → S.Ens ε σ Y s ≤ M) →
      ∀ p : ℕ, S.Dn ε σ Y p ≤ (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ (2 * p) * M
def TermBound : Prop :=
  CSTerm → ShiftBound → MarkovTerm → CoefIntegrable → EFinite → ThetaBound → E.CauchyTheta → E.MarkovVector →
  ∀ (B : Base) (S : Step B) (c : Cut) (σ ε CR Cd CP : ℝ), 4 ≤ σ → 0 < ε → 0 ≤ CR → 0 ≤ Cd → 0 ≤ CP → 0 < S.L →
    S.Imports c σ CR Cd CP → ∀ Y ∈ S.J, ∀ p : ℕ,
      ‖S.term ε σ Y p‖ ≤ Real.exp 1 * √(C7 CR Cd CP) * S.Esup ε σ * |S.P Y| *
        (8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ p
def GeomSum : Prop :=
  ∀ (c x : ℝ) (R : ℕ), 0 ≤ c → 0 ≤ x → x ≤ 1 / (2 * (1 + 2 * Real.exp 1 * √c)) →
    ∑ p ∈ Icc 1 R, Real.exp 1 * √c * x ^ p ≤ 1 / 2
def EnergyStep : Prop :=
  TermZero → GeomSum → ThetaRange →
  ∀ (B : Base) (S : Step B) (c : Cut) (σ ε CR Cd CP : ℝ), 4 ≤ σ → 0 < ε → 0 ≤ CR → 0 ≤ Cd → 0 ≤ CP → 0 < S.L →
    16 * σ * ((S.r : ℝ) + 1) ^ 2 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) ≤ S.L →
    S.Imports c σ CR Cd CP → Integrable (sq B S.dw S.X) B.μ → S.Star σ →
    (∀ Y ∈ S.J, ∀ p : ℕ, ‖S.term ε σ Y p‖ ≤ Real.exp 1 * √(C7 CR Cd CP) * S.Esup ε σ * |S.P Y| *
        (8 * σ * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ p) →
    ∀ Y ∈ S.J, S.En ε σ Y / |S.P Y| ≤ S.A0 + S.Esup ε σ / 2
def Absorb : Prop :=
  ∀ (B : Base) (S : Step B) (σ ε A : ℝ), 0 ≤ S.L → BddAbove (S.Eset ε σ) →
    (∀ Y ∈ S.J, S.En ε σ Y / |S.P Y| ≤ A + S.Esup ε σ / 2) → S.Esup ε σ ≤ 2 * A
def Uniform (B : Base) (S : Step B) (σ CR Cd CP : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Y ∈ S.J, ∀ p : ℕ,
    S.Dn ε σ Y p ≤ 2 * C7 CR Cd CP * (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ (2 * p) * |S.P Y| * S.A0
def UniformBound : Prop :=
  Adj → TermBound → EnergyStep → Absorb → EFinite → ShiftBound → MarkovTerm → CSTerm → CoefIntegrable → TermZero →
  GeomSum → ThetaRange → ThetaSmooth → ThetaBound → Leibniz → CutTheta → E.CauchyTheta → E.MarkovVector →
  ∀ (B : Base) (S : Step B) (c : Cut) (σ CR Cd CP : ℝ), 4 ≤ σ → 0 ≤ CR → 0 ≤ Cd → 0 ≤ CP → 0 < S.L →
    16 * σ * ((S.r : ℝ) + 1) ^ 2 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) ≤ S.L →
    S.Imports c σ CR Cd CP → Integrable (sq B S.dw S.X) B.μ → Uniform B S σ CR Cd CP
def FatouStep : Prop :=
  ThetaRange → ThetaLimit →
  ∀ (B : Base) (A : Type) [Fintype A] (wt : B.Ω → A → ℝ) (v : Fn B A) (σ K : ℝ), 0 ≤ σ →
    (∀ ω a, 0 ≤ wt ω a) → (∀ a, Measurable fun ω => wt ω a) → (∀ a, Measurable fun ω => v ω a) →
    (∀ ε : ℝ, 0 < ε → Integrable (fun ω => th ε σ (B.G ω) * sq B wt v ω) B.μ) →
    (∀ ε : ℝ, 0 < ε → ∫ ω, th ε σ (B.G ω) * sq B wt v ω ∂B.μ ≤ K) →
      Integrable (sq B wt v) B.μ ∧ ∫ ω, sq B wt v ω ∂B.μ ≤ K
def DomConv : Prop :=
  ThetaRange → ThetaLimit → ThetaBound → TermZero → E.CauchyTheta →
  ∀ (B : Base) (S : Step B) (σ : ℝ), 4 ≤ σ → S.Meas → S.WPos → S.I4 → S.Star σ →
    Integrable (sq B S.dw S.X) B.μ →
    ∀ Y ∈ S.J, (∀ p : ℕ, Integrable (sq B (S.d Y) (S.ds Y p)) B.μ) →
      ∫ ω, sq B (S.d Y) (S.gX Y) ω ∂B.μ = |S.P Y| * S.A0
def StepClaim : Prop :=
  ∀ (B : Base) (S : Step B) (c : Cut) (σ CR Cd CP : ℝ), 4 ≤ σ → 0 ≤ CR → 0 ≤ Cd → 0 ≤ CP → 0 < S.L →
    16 * σ * ((S.r : ℝ) + 1) ^ 2 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) ≤ S.L →
    S.Imports c σ CR Cd CP → Integrable (sq B S.dw S.X) B.μ →
    ∀ Y ∈ S.J, Integrable (sq B (S.d Y) (S.gX Y)) B.μ ∧
      ∫ ω, sq B (S.d Y) (S.gX Y) ω ∂B.μ = |S.P Y| * S.A0
def StepClaimFromSteps : Prop :=
  E.CauchyTheta → E.MarkovVector → ThetaForm → ThetaRange → ThetaSmooth → ThetaBound → ThetaLimit → CutTheta →
  Leibniz → TermZero → CoefIntegrable → Adj → EFinite → CSTerm → ShiftBound → MarkovTerm → TermBound → GeomSum →
  EnergyStep → Absorb → UniformBound → FatouStep → DomConv → StepClaim
def InterpolationCoefficientsInL2 : Prop :=
  ∀ (B : Base) (N d : ℕ) (wt : B.Ω → ℝ) (m : (Fin N → ℝ) → B.Ω → ℂ)
    (c : (Fin N → Fin (d + 1)) → B.Ω → ℂ) (J : Fin N → Set ℝ),
    (∀ ω, 0 ≤ wt ω) → (∀ a, (J a).Infinite) →
    (∀ y ω, m y ω = ∑ κ : Fin N → Fin (d + 1), ((∏ a, (y a) ^ (κ a : ℕ) : ℝ) : ℂ) * c κ ω) →
    (∀ y, (∀ a, y a ∈ J a) → WeightedL2 B wt (m y)) → ∀ κ, WeightedL2 B wt (c κ)
structure Fam (B : Base) (N : ℕ) where

  R : Type
  [fR : Fintype R]

  ι : Type
  [fι : Fintype ι]

  r : ℕ

  u : Fn B R

  gw : (Fin N → ℝ) → Fn B R → Fn B ι

  Wt : B.Ω → ℝ

  cw : (Fin N → ℝ) → ι → ℝ

  mon : (Fin N → ℝ) → Fn B ι

  BN : (Fin N → ℝ) → B.Ω → Matrix ι ι ℂ

  J : Fin N → Set ℝ
attribute [instance] Fam.fR Fam.fι
namespace Fam
variable {B : Base} {N : ℕ} (F : Fam B N)
def dw (Y : Fin N → ℝ) : B.Ω → F.ι → ℝ := fun ω i => F.Wt ω ^ N * F.cw Y i
def On (Y : Fin N → ℝ) : Prop := ∀ a, Y a ∈ F.J a
def Meas : Prop :=
  Measurable F.Wt ∧ (∀ y i, Measurable fun ω => F.mon y ω i) ∧ ∀ Y i k, Measurable fun ω => F.BN Y ω i k
def Pos : Prop := (∀ ω, 0 < F.Wt ω) ∧ ∀ Y, F.On Y → ∀ i, 0 < F.cw Y i
def Factor : Prop :=
  ∀ Y, F.On Y → ∀ (s : ℝ) ω i,
    conjS B (F.gw Y) F.u s ω i = ∑ k, F.BN Y ω i k * F.mon (fun a => Y a + s) ω k
def BNBounded : Prop :=
  ∀ Y, F.On Y → ∃ (C : ℝ) (Binv : B.Ω → Matrix F.ι F.ι ℂ),
    (∀ ω i k, ‖F.BN Y ω i k‖ ≤ C ∧ ‖Binv ω i k‖ ≤ C) ∧ (∀ i k, Measurable fun ω => Binv ω i k) ∧
      ∀ ω (v : F.ι → ℂ) i, ∑ l, Binv ω i l * ∑ k, F.BN Y ω l k * v k = v i
def MonPoly : Prop :=
  ∃ c : (Fin N → Fin (F.r + 1 + 1)) → Fn B F.ι, ∀ y ω i,
    F.mon y ω i = ∑ κ : Fin N → Fin (F.r + 1 + 1), ((∏ a, (y a) ^ (κ a : ℕ) : ℝ) : ℂ) * c κ ω i
def Jet : Prop := ∀ Y, F.On Y → JetLocal B (F.gw Y) F.u
def Imports : Prop := F.Meas ∧ F.Pos ∧ F.Factor ∧ F.BNBounded ∧ F.MonPoly ∧ F.Jet
end Fam
def LimitA : Prop :=
  InterpolationCoefficientsInL2 →
  ∀ (B : Base) (N : ℕ) (F : Fam B N), (∀ a, (F.J a).Infinite) →
    F.Meas → F.Pos → F.Factor → F.BNBounded → F.MonPoly →
    (∀ Y, F.On Y → Integrable (sq B (F.dw Y) (F.gw Y F.u)) B.μ) →
    ∀ Y, F.On Y → PolyS B (F.gw Y) F.u (N * (F.r + 1)) ∧
      ∀ p : ℕ, (∀ i, Measurable fun ω => dS B (F.gw Y) F.u p ω i) ∧
        Integrable (sq B (F.dw Y) (dS B (F.gw Y) F.u p)) B.μ
def CutoffLimitInL2 : Prop :=
  Leibniz → CutBound →
  ∀ (B : Base) (A A' : Type) [Fintype A'] (T : Fn B A → Fn B A') (u : Fn B A) (wt : B.Ω → A' → ℝ) (c : Cut)
    (M m : ℕ), 1 ≤ m → (∀ ω a, 0 ≤ wt ω a) → (∀ a, Measurable fun ω => wt ω a) →
    JetLocal B T u → PolyS B T u M → (∀ p a, Measurable fun ω => dS B T u p ω a) →
    (∀ p : ℕ, Integrable (sq B wt (dS B T u p)) B.μ) →
    (∀ ε : ℝ, 0 < ε → Integrable (sq B wt (T (mulF B (c.sc ε m) u))) B.μ) ∧
    Tendsto (fun ε : ℝ => ∫ ω, sq B wt (fun ω a => T (mulF B (c.sc ε m) u) ω a - T u ω a) ω ∂B.μ)
      (𝓝[>] 0) (𝓝 0)
def PairLimit : Prop :=
  ∀ (B : Base) (A : Type) [Fintype A] (wt : B.Ω → A → ℝ) (v v' : Fn B A) (f f' : ℝ → Fn B A),
    (∀ ω a, 0 ≤ wt ω a) → (∀ a, Measurable fun ω => wt ω a) →
    (∀ a, Measurable fun ω => v ω a) → (∀ a, Measurable fun ω => v' ω a) →
    (∀ ε a, 0 < ε → Measurable fun ω => f ε ω a) → (∀ ε a, 0 < ε → Measurable fun ω => f' ε ω a) →
    Integrable (sq B wt v) B.μ → Integrable (sq B wt v') B.μ →
    (∀ ε, 0 < ε → Integrable (sq B wt (f ε)) B.μ) → (∀ ε, 0 < ε → Integrable (sq B wt (f' ε)) B.μ) →
    Tendsto (fun ε : ℝ => ∫ ω, sq B wt (fun ω a => f ε ω a - v ω a) ω ∂B.μ) (𝓝[>] 0) (𝓝 0) →
    Tendsto (fun ε : ℝ => ∫ ω, sq B wt (fun ω a => f' ε ω a - v' ω a) ω ∂B.μ) (𝓝[>] 0) (𝓝 0) →
    Tendsto (fun ε : ℝ => ∫ ω, pr B wt (f ε) (f' ε) ω ∂B.μ) (𝓝[>] 0) (𝓝 (∫ ω, pr B wt v v' ω ∂B.μ))
def LimitB : Prop :=
  LimitA → CutoffLimitInL2 → PairLimit → InterpolationCoefficientsInL2 → Leibniz → CutBound →
  ∀ (B : Base) (N : ℕ) (F : Fam B N) (c : Cut), (∀ a, (F.J a).Infinite) → F.Imports →
    (∀ Y, F.On Y → Integrable (sq B (F.dw Y) (F.gw Y F.u)) B.μ) →
    ∀ Y, F.On Y →
      Tendsto (fun ε : ℝ => ∫ ω, sq B (F.dw Y) (F.gw Y (mulF B (c.sc ε 1) F.u)) ω ∂B.μ) (𝓝[>] 0)
        (𝓝 (∫ ω, sq B (F.dw Y) (F.gw Y F.u) ω ∂B.μ))
def GridConvergence : Prop :=
  ∀ (N n : ℕ) (T : Type) (l : Filter T) (Q : T → MvPolynomial (Fin N) ℝ) (Q₀ : MvPolynomial (Fin N) ℝ)
    (grid : Fin N → Finset ℝ),
    (∀ t a, (Q t).degreeOf a ≤ n) → (∀ a, Q₀.degreeOf a ≤ n) → (∀ a, (grid a).card = n + 1) →
    (∀ Y : Fin N → ℝ, (∀ a, Y a ∈ grid a) →
      Tendsto (fun t => MvPolynomial.eval Y (Q t)) l (𝓝 (MvPolynomial.eval Y Q₀))) →
    ∀ Y : Fin N → ℝ, Tendsto (fun t => MvPolynomial.eval Y (Q t)) l (𝓝 (MvPolynomial.eval Y Q₀))
def ConstSign : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (α β : ℝ), (∀ s, -lam s ∉ Set.Icc α β) →
    ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ Y ∈ Set.Icc α β, |∏ s, (Y + lam s)| = sg * ∏ s, (Y + lam s)
def PRatioMiddle : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (α β L Y s : ℝ), α < β → (∀ t, -lam t ∉ Set.Ioo α β) → 0 ≤ L → n * L ≤ β - α →
    |s| ≤ L → α + (β - α) / 3 ≤ Y → Y ≤ β - (β - α) / 3 → α + (β - α) / 3 ≤ Y + s → Y + s ≤ β - (β - α) / 3 →
    |∏ t, (Y + lam t)| ≤ Real.exp 3 * |∏ t, (Y + s + lam t)|
def Constants : Prop :=
  ∀ (k r N : ℕ) (C₂ C₆ I : ℝ), r + 1 ≤ N → 0 < C₂ → 6 * C₂ ≤ C₆ →
    C₆ * ((k : ℝ) * N * ((r : ℝ) + 1) ^ 2 + (N : ℝ) ^ 2 * ((r : ℝ) + 1) ^ 2) ≤ I →
    (k : ℝ) * (C₂ * N * ((r : ℝ) + 1) ^ 2) ≤ I ∧
    ((k + 2 * r + 1 : ℕ) : ℝ) * (C₂ * N * ((r : ℝ) + 1) ^ 2) ≤ I ∧
    6 * (N : ℝ) * (C₂ * N * ((r : ℝ) + 1) ^ 2) ≤ I
def plus (w : List ℝ) : List (Bool × ℝ) := w.map fun Y => (true, Y)
structure Sys where

  B : Base

  c : Cut

  k : ℕ
  r : ℕ

  lam : Fin (k + 2 * r + 1) → ℝ

  α : ℝ
  β : ℝ

  Ntot : ℕ

  L : ℝ

  principalHermitianLattice : ℝ → List (Bool × ℝ) → ℝ

  step : List ℝ → Step B

  fam : (N : ℕ) → Fam B N
  step_r : ∀ w, (step w).r = r
  step_P : ∀ w Y, (step w).P Y = ∏ s, (Y + lam s)
  step_a : ∀ w, (step w).a = α + (β - α) / 3 + 2 * (w.length : ℝ) * L
  step_L : ∀ w, (step w).L = L

  step_new : ∀ w Y ω, sq B (step (Y :: w)).dw (step (Y :: w)).X ω = sq B ((step w).d Y) ((step w).gX Y) ω
  fam_r : ∀ N, (fam N).r = r
  fam_J : ∀ N (a : Fin N), (fam N).J a =
    Set.Icc (α + (β - α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * L) (α + (β - α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * L + L)

  fam_dens : ∀ (N : ℕ) (Y : Fin N → ℝ) ω, sq B (step (List.ofFn Y)).dw (step (List.ofFn Y)).X ω =
    sq B ((fam N).dw Y) ((fam N).gw Y (fam N).u) ω
namespace Sys
variable (S : Sys)
def P (Y : ℝ) : ℝ := ∏ s, (Y + S.lam s)
def box (a : ℕ) : Set ℝ :=
  Set.Icc (S.α + (S.β - S.α) / 3 + 2 * (a : ℝ) * S.L) (S.α + (S.β - S.α) / 3 + 2 * (a : ℝ) * S.L + S.L)
def OnBoxes : List ℝ → Prop
  | [] => True
  | Y :: w => Y ∈ S.box w.length ∧ OnBoxes w
def admitted (w : List (Bool × ℝ)) : Prop :=
  (∀ x ∈ w, x.2 ∈ Set.Icc S.α S.β) ∧ w.Pairwise fun x y => 2 < |x.2 - y.2|
def size (w : List (Bool × ℝ)) : ℝ := (w.map fun x => |S.P x.2|).prod
def dens (w : List ℝ) : S.B.Ω → ℝ := sq S.B (S.step w).dw (S.step w).X
def jn : ℝ := ∫ ω, S.dens [] ω ∂S.B.μ
def Claim (w : List ℝ) : Prop :=
  Integrable (S.dens w) S.B.μ ∧ ∫ ω, S.dens w ω ∂S.B.μ = S.size (plus w) * S.jn
def RootsOut : Prop := ∀ s, -S.lam s ∉ Set.Icc S.α S.β
def I1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, N ≤ S.Ntot → ∃ Q : MvPolynomial (Fin N) ℝ,
    (∀ a, Q.degreeOf a ≤ S.k + 2 * S.r + 1) ∧
    ∀ (sg : Fin N → Bool) (Y : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg a, Y a)) →
      S.principalHermitianLattice ε (List.ofFn fun a => (sg a, Y a)) = MvPolynomial.eval Y Q
def BaseDensityIntegrable : Prop := Integrable (S.dens []) S.B.μ
def jsq : ℝ := ∫ ω, ∑ a, ‖(S.fam 0).u ω a‖ ^ 2 ∂S.B.μ
def J0 : Prop := ∀ ω, S.dens [] ω = ∑ a, ‖(S.fam 0).u ω a‖ ^ 2
def ThmP : Prop :=
  ∀ (N : ℕ) (Y : Fin N → ℝ), N ≤ S.Ntot → S.OnBoxes (List.ofFn Y) → ∀ ε : ℝ, 0 < ε →
    S.principalHermitianLattice ε (plus (List.ofFn Y)) =
      ∫ ω, sq S.B ((S.fam N).dw Y) ((S.fam N).gw Y (mulF S.B (S.c.sc ε 1) (S.fam N).u)) ω ∂S.B.μ
def StepImports (σ CR Cd CP : ℝ) : Prop :=
  ∀ w : List ℝ, S.OnBoxes w → w.length < S.Ntot → (S.step w).Imports S.c σ CR Cd CP
def FamImports : Prop := ∀ N, N ≤ S.Ntot → (S.fam N).Imports
def EnergyLimit : Prop :=
  ∀ w : List (Bool × ℝ), S.admitted w → w.length ≤ S.Ntot →
    Tendsto (fun ε : ℝ => S.principalHermitianLattice ε w) (𝓝[>] 0) (𝓝 (S.size w * S.jn))
def BoxLimit : Prop :=
  ∀ w : List ℝ, S.OnBoxes w → w.length ≤ S.Ntot →
    Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (plus w)) (𝓝[>] 0) (𝓝 (S.size (plus w) * S.jn))
end Sys
def BoxesFit : Prop :=
  ∀ S : Sys, 2 < S.L → 6 * (S.Ntot : ℝ) * S.L ≤ S.β - S.α →
    (∀ a, a < S.Ntot → S.box a ⊆ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3)) ∧
    (∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x) ∧
    ∀ w : List ℝ, S.OnBoxes w → w.length ≤ S.Ntot → S.admitted (plus w)
def PImportsHold : Prop :=
  PRatioMiddle → BoxesFit →
  ∀ S : Sys, 2 < S.L → 6 * (S.Ntot : ℝ) * S.L ≤ S.β - S.α → ((S.k + 2 * S.r + 1 : ℕ) : ℝ) * S.L ≤ S.β - S.α →
    S.RootsOut → ∀ w : List ℝ, w.length < S.Ntot → (S.step w).PReg ∧ (S.step w).PRatio (Real.exp 3)
def ReduceToBoxes : Prop :=
  GridConvergence → ConstSign → BoxesFit →
  ∀ S : Sys, 2 < S.L → 6 * (S.Ntot : ℝ) * S.L ≤ S.β - S.α → S.RootsOut → S.I1 → S.BoxLimit → S.EnergyLimit
def ClaimInduction : Prop :=
  ∀ S : Sys, S.BaseDensityIntegrable →
    (∀ (w : List ℝ) (Y : ℝ), S.OnBoxes (Y :: w) → w.length < S.Ntot → Integrable (S.dens w) S.B.μ →
      Integrable (S.dens (Y :: w)) S.B.μ ∧ ∫ ω, S.dens (Y :: w) ω ∂S.B.μ = |S.P Y| * ∫ ω, S.dens w ω ∂S.B.μ) →
    ∀ w : List ℝ, S.OnBoxes w → w.length ≤ S.Ntot → S.Claim w
def ClaimAll : Prop :=
  StepClaim → ClaimInduction →
  ∀ (S : Sys) (σ CR Cd CP : ℝ), 4 ≤ σ → 0 ≤ CR → 0 ≤ Cd → 0 ≤ CP → 0 < S.L →
    16 * σ * ((S.r : ℝ) + 1) ^ 2 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) ≤ S.L →
    S.BaseDensityIntegrable → S.StepImports σ CR Cd CP → ∀ w : List ℝ, S.OnBoxes w → w.length ≤ S.Ntot → S.Claim w
def BoxLimitFromClaim : Prop :=
  LimitB → LimitA → CutoffLimitInL2 → PairLimit → InterpolationCoefficientsInL2 → Leibniz → CutBound →
  ∀ S : Sys, 0 < S.L → S.FamImports → S.ThmP →
    (∀ w : List ℝ, S.OnBoxes w → w.length ≤ S.Ntot → S.Claim w) → S.BoxLimit
def LemmaE : Prop :=
  ∀ CR Cd CP : ℝ, 0 ≤ CR → 0 ≤ Cd → 0 ≤ CP →
    ∀ C₂ : ℝ, 64 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) ≤ C₂ → ∀ C₆ : ℝ, 6 * C₂ ≤ C₆ →
    ∀ S : Sys, S.r + 1 ≤ S.Ntot → S.L = C₂ * S.Ntot * ((S.r : ℝ) + 1) ^ 2 →
      C₆ * ((S.k : ℝ) * S.Ntot * ((S.r : ℝ) + 1) ^ 2 + (S.Ntot : ℝ) ^ 2 * ((S.r : ℝ) + 1) ^ 2) ≤ S.β - S.α →
      S.RootsOut → S.I1 → S.BaseDensityIntegrable → S.ThmP → S.StepImports (4 * S.Ntot) CR Cd CP → S.FamImports →
      S.EnergyLimit
def LemmaEFromSteps : Prop :=
  Constants → ReduceToBoxes → GridConvergence → ConstSign → BoxesFit → ClaimAll → StepClaim → ClaimInduction →
  BoxLimitFromClaim → LimitB → LimitA → CutoffLimitInL2 → PairLimit → InterpolationCoefficientsInL2 → Leibniz → CutBound → LemmaE
def WeightedIntegrable : Prop :=
  ∀ (B : Base) (T : Type) [Fintype T] (f : B.Ω → ℝ) (v : T → B.Ω → ℂ) (C : ℝ) (p N : ℕ), N ≤ 2 * p →
    Measurable f → (∀ ω, 0 ≤ f ω) →
    (∀ ω, f ω ≤ C * (B.G ω) ^ ((2 * p : ℝ) - N) * ∑ t, ‖v t ω‖ ^ 2) →
    (∀ t, Integrable (fun ω => ‖v t ω‖ ^ 2) B.μ) → (∀ t, Integrable (fun ω => (B.G ω) ^ (2 * p) * ‖v t ω‖ ^ 2) B.μ) →
    Integrable f B.μ
structure EP (B : Base) where

  R : Type
  [fR : Fintype R]

  ι : Type
  [fι : Fintype ι]

  u : Fn B R

  gw : Fn B R → Fn B ι

  dw : B.Ω → ι → ℝ

  Cw : Fn B R → Fn B R
attribute [instance] EP.fR EP.fι
namespace EP
variable {B : Base} (X : EP B)
def beta (h h' : Fn B X.R) : ℂ := ∫ ω, pr B (fun _ _ => 1) h h' ω ∂B.μ
def Meas : Prop :=
  (∀ a, Measurable fun ω => X.u ω a) ∧ (∀ a, Measurable fun ω => X.Cw X.u ω a) ∧ (∀ i, Measurable fun ω => X.dw ω i) ∧
    ∀ p i, Measurable fun ω => dS B X.gw X.u p ω i
def PolarKK (c : Cut) : Prop :=
  ∀ (ε₁ ε₂ : ℝ) (m₁ m₂ : ℕ), 0 < ε₁ → 0 < ε₂ → 1 ≤ m₁ → 1 ≤ m₂ →
    X.beta (X.Cw (mulF B (c.sc ε₁ m₁) X.u)) (mulF B (c.sc ε₂ m₂) X.u) =
      ∫ ω, pr B X.dw (X.gw (mulF B (c.sc ε₁ m₁) X.u)) (X.gw (mulF B (c.sc ε₂ m₂) X.u)) ω ∂B.μ
def CwLocal (c : Cut) : Prop :=
  ∀ (ε₁ : ℝ) ω, 0 < ε₁ → ε₁ < B.G ω → ∀ a, X.Cw (mulF B (c.sc ε₁ 1) X.u) ω a = X.Cw X.u ω a
def BetaFinite : Prop :=
  Integrable (sq B (fun _ _ => 1) X.u) B.μ ∧ Integrable (sq B (fun _ _ => 1) (X.Cw X.u)) B.μ
def NF (p N : ℕ) : Prop :=
  ∀ q : ℕ, ∃ (n : ℕ) (v : Fin n → B.Ω → ℂ) (C : ℝ),
    (∀ ω, sq B X.dw (dS B X.gw X.u q) ω ≤ C * (B.G ω) ^ ((2 * p : ℝ) - N) * ∑ t, ‖v t ω‖ ^ 2) ∧
    (∀ t, Integrable (fun ω => ‖v t ω‖ ^ 2) B.μ) ∧ ∀ t, Integrable (fun ω => (B.G ω) ^ (2 * p) * ‖v t ω‖ ^ 2) B.μ
def CoefInt : Prop := ∀ q : ℕ, Integrable (sq B X.dw (dS B X.gw X.u q)) B.μ
end EP
def EpCoefInt : Prop :=
  WeightedIntegrable → ∀ (B : Base) (X : EP B) (p N : ℕ), N ≤ 2 * p → (∀ ω i, 0 ≤ X.dw ω i) → X.Meas → X.NF p N → X.CoefInt
def EpStep5 : Prop :=
  ∀ (B : Base) (X : EP B) (c : Cut), X.Meas → X.BetaFinite →
    Tendsto (fun ε : ℝ => X.beta (X.Cw X.u) (mulF B (c.sc ε 2) X.u)) (𝓝[>] 0) (𝓝 (X.beta (X.Cw X.u) X.u))
def EpStep6 : Prop :=
  CutBound →
  ∀ (B : Base) (X : EP B) (c : Cut), JetLocal B X.gw X.u → X.PolarKK c → X.CwLocal c → ∀ ε : ℝ, 0 < ε →
    X.beta (X.Cw X.u) (mulF B (c.sc ε 2) X.u) =
      ∫ ω, pr B X.dw (X.gw X.u) (X.gw (mulF B (c.sc ε 2) X.u)) ω ∂B.μ
def LemmaEprime : Prop :=
  ∀ (B : Base) (X : EP B) (c : Cut) (M : ℕ), (∀ ω i, 0 ≤ X.dw ω i) → X.Meas → JetLocal B X.gw X.u →
    PolyS B X.gw X.u M → X.CoefInt → X.PolarKK c → X.CwLocal c → X.BetaFinite →
    Integrable (sq B X.dw (X.gw X.u)) B.μ ∧
    ((∫ ω, sq B X.dw (X.gw X.u) ω ∂B.μ : ℝ) : ℂ) = X.beta (X.Cw X.u) X.u ∧
    Tendsto (fun ε : ℝ => X.beta (X.Cw (mulF B (c.sc ε 1) X.u)) (mulF B (c.sc ε 1) X.u)) (𝓝[>] 0)
      (𝓝 (X.beta (X.Cw X.u) X.u))
def LemmaEprimeFull : Prop :=
  ∀ (B : Base) (X : EP B) (c : Cut) (M p N : ℕ), N ≤ 2 * p → (∀ ω i, 0 ≤ X.dw ω i) → X.Meas →
    JetLocal B X.gw X.u → PolyS B X.gw X.u M → X.NF p N → X.PolarKK c → X.CwLocal c → X.BetaFinite →
    Integrable (sq B X.dw (X.gw X.u)) B.μ ∧
    ((∫ ω, sq B X.dw (X.gw X.u) ω ∂B.μ : ℝ) : ℂ) = X.beta (X.Cw X.u) X.u ∧
    Tendsto (fun ε : ℝ => X.beta (X.Cw (mulF B (c.sc ε 1) X.u)) (mulF B (c.sc ε 1) X.u)) (𝓝[>] 0)
      (𝓝 (X.beta (X.Cw X.u) X.u))
def LemmaEprimeFromSteps : Prop :=
  Leibniz → CutBound → CutoffLimitInL2 → PairLimit → EpStep5 → EpStep6 → LemmaEprime
def EstEJoint : Prop :=
  ∀ (E W : Type) [Field E] (D : TB.Data E W) (S : Fin D.f → Sys) (loc : W → Fin D.f → List (Bool × ℝ)),
    (∀ v, (S v).Ntot = D.Ntop) → (∀ v, (S v).RootsOut) →
    (∀ w ∈ D.Wall, ∀ v, (S v).admitted (loc w v) ∧ (loc w v).length ≤ D.cnt w) →
    (∀ w ∈ D.Wall, D.wt w = ∏ v, (S v).size (loc w v)) →
    (∀ ε : ℝ, 0 < ε → ∀ w ∈ D.Wall, (D.gram ε 0 w [] []).re = ∏ v, (S v).principalHermitianLattice ε (loc w v)) →
    (∀ v, (S v).J0) → (∀ v, (S v).EnergyLimit) → D.EstE (∏ v, (S v).jsq)
end
end Formalism.FourierDecayAlt.LE


