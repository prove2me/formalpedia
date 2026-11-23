-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
-- name    : Formalism_GL3MeanSquares_LegendreCoefficient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:51.659724+00:00
-- url     : https://prove2.me/theorems/5070dfae-6372-4ed9-8266-528e80a54795
-- title:
--   Legendre Coefficient
-- statement:
--   Definitions and structural lemmas for Legendre Coefficient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/LegendreCoefficient.lean

import Mathlib
import Definitions.Def_Formalism_FormalGroupWitt_ShiftSOneLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.ExpSeriesBivariate
open Finset
def expS {σ K : Type} [Field K] [Algebra ℚ K] (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst f (PowerSeries.exp K)
def InLam {σ K : Type} [NormedField K] [Algebra ℚ K] (f : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ Formalism.G.IntegralMv (expS f)
def LamGroup : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra ℚ K] (σ : Type)
    (f g : MvPowerSeries σ K),
    InLam (0 : MvPowerSeries σ K) ∧ (InLam f → InLam g → InLam (f + g)) ∧ (InLam f → InLam (-f))
def LamSubst : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra ℚ K] (σ τ : Type) [Finite σ]
    (f : MvPowerSeries σ K) (h : σ → MvPowerSeries τ K),
    InLam f → (∀ i, MvPowerSeries.constantCoeff (h i) = 0) → (∀ i, Formalism.G.IntegralMv (h i)) →
    InLam (MvPowerSeries.subst h f)
def LamZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [NormedField K] [IsUltrametricDist K] [NormedAlgebra ℚ_[p] K]
    [Algebra ℚ K] (σ : Type) (f : MvPowerSeries σ K) (c : ℤ_[p]),
    InLam f → InLam (MvPowerSeries.C (algebraMap ℚ_[p] K (c : ℚ_[p])) * f)
def LamClosed : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra ℚ K] (σ : Type)
    (F : ℕ → MvPowerSeries σ K) (f : MvPowerSeries σ K),
    (∀ n, Filter.Tendsto (fun k => MvPowerSeries.coeff n (F k)) Filter.atTop
      (nhds (MvPowerSeries.coeff n f))) →
    (∀ k, InLam (F k)) → InLam f
def LamDescent : Prop :=
  ∀ (K : Type) [Field K] [Algebra ℚ K] (K₀ : Subfield K) (σ : Type) (f : MvPowerSeries σ K),
    MvPowerSeries.constantCoeff f = 0 → (∀ n, MvPowerSeries.coeff n f ∈ K₀) →
    ∀ n, MvPowerSeries.coeff n (expS f) ∈ K₀
def LamDescentFull : Prop :=
  ∀ (K : Type) [NormedField K] [CharZero K] (K₀ : Subfield K) (σ : Type) (f₀ : MvPowerSeries σ K₀),
    InLam (MvPowerSeries.map K₀.subtype f₀) ↔ InLam f₀
def LamCoordinates : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra ℚ K] (σ τ : Type) [Finite σ] [Finite τ]
    (f : MvPowerSeries σ K) (h : σ → MvPowerSeries τ K) (h' : τ → MvPowerSeries σ K),
    (∀ i, MvPowerSeries.constantCoeff (h i) = 0) → (∀ i, Formalism.G.IntegralMv (h i)) →
    (∀ i, MvPowerSeries.constantCoeff (h' i) = 0) → (∀ i, Formalism.G.IntegralMv (h' i)) →
    (∀ i, MvPowerSeries.subst h' (h i) = MvPowerSeries.X i) →
    (InLam f ↔ InLam (MvPowerSeries.subst h f))
def IntegralInverse : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type) [Fintype σ] [DecidableEq σ]
    (T : σ → MvPowerSeries σ K) (J' : Matrix σ σ K),
    (∀ i, MvPowerSeries.constantCoeff (T i) = 0) → (∀ i, Formalism.G.IntegralMv (T i)) →
    (∀ i j, ‖J' i j‖ ≤ 1) →
    (Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (T i)) * J' = 1 →
    ∃ X' : σ → MvPowerSeries σ K, (∀ i, MvPowerSeries.constantCoeff (X' i) = 0) ∧
      (∀ i, Formalism.G.IntegralMv (X' i)) ∧ (∀ i, MvPowerSeries.subst X' (T i) = MvPowerSeries.X i) ∧
      ∀ i, MvPowerSeries.subst T (X' i) = MvPowerSeries.X i
def AbsorbExponential : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra ℚ K] (σ : Type)
    (Ph Be U₀ : MvPowerSeries σ K), MvPowerSeries.constantCoeff Ph = 0 →
    MvPowerSeries.constantCoeff Be = 0 → InLam (Ph - Be) → Formalism.G.IntegralMv U₀ →
    ∃ U : MvPowerSeries σ K, Formalism.G.IntegralMv U ∧ expS (-Ph) * U₀ = expS (-Be) * U
def LamControl : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ¬ InLam (MvPowerSeries.X () : MvPowerSeries Unit ℚ_[p]) ∧
    InLam (MvPowerSeries.C (p : ℚ_[p]) * MvPowerSeries.X () : MvPowerSeries Unit ℚ_[p])
def BridgeLowDegree : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (l : ℕ), 2 ≤ l → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) →
    ∀ (m : ℕ) [NeZero m] (ι : Type) [Fintype ι] [DecidableEq ι] (M : ZMod m → ι → K)
    (h : ZMod m → MvPowerSeries ι K), (∀ j, MvPowerSeries.constantCoeff (h j) = 0) →
      (∀ j, MvPowerSeries.subst h (Formalism.FG.shiftLogS K l ε m j) =
        ∑ r, MvPowerSeries.C (M j r) * Formalism.FG.ltLogS K l ε r) →
      (∀ j r, MvPowerSeries.coeff (Finsupp.single r 1) (h j) = M j r) ∧
      ∀ j (n : ι →₀ ℕ), 2 ≤ n.degree → n.degree < l ^ 2 → MvPowerSeries.coeff n (h j) = 0
def ShiftLowDegree : Prop :=
  ∀ (K : Type) [Field K] (l : ℕ), 2 ≤ l → ∀ (ε : ℤ) (m : ℕ) [NeZero m] (j : ZMod m)
    (n : ZMod m →₀ ℕ), n.degree < l ^ 2 →
    MvPowerSeries.coeff n (Formalism.FG.shiftLogS K l ε m j) = if n = Finsupp.single j 1 then 1 else 0
def FirstCoefficient : Prop :=
  ∀ (A : Type) [CommRing A] (l : ℕ), l.Prime → ∀ θ θ' : A, (l : A) ∣ θ' ^ (l ^ 2) - θ →
    (MvPolynomial.C (l : A) : MvPolynomial (Fin 2) A) ∣
      MvPolynomial.X 0 ^ (l ^ 2) + MvPolynomial.C θ * MvPolynomial.X 1 ^ (l ^ 2) -
        (MvPolynomial.X 0 + MvPolynomial.C θ' * MvPolynomial.X 1) ^ (l ^ 2)
def TwistLog : Prop :=
  ∀ (K : Type) [Field K] (l : ℕ), Odd l → ∀ ε : K, ε ^ (l ^ 2 - 1) = -1 →
    ∀ n : Unit →₀ ℕ,
      MvPowerSeries.coeff n (Formalism.FG.ltLogS K l (-1) ()) * ε ^ n.degree =
        ε * MvPowerSeries.coeff n (Formalism.FG.ltLogS K l 1 ())
def FrobeniusSign : Prop :=
  ∀ (d l : ℕ), 5 ≤ d → l.Prime → ¬ IsSquare (-(d : ZMod l)) →
    ∀ x y : ℤ, x ^ 2 + d * y ^ 2 = 4 * (l : ℤ) ^ 2 → y = 0 ∧ (x = 2 * l ∨ x = -(2 * l))
def LogShiftIntegral : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → (∀ m : ℕ, ¬ l ∣ m → ‖(m : K)‖ = 1) →
    ∀ (σ : Type) (a : ℕ → K), (∀ n : ℕ, ‖(n : K) * a n‖ ≤ 1) →
    ∀ P Q : MvPowerSeries σ K, Formalism.G.IntegralMv P → Formalism.G.IntegralMv Q →
      (∀ e, ‖MvPowerSeries.coeff e (P - Q)‖ ≤ ‖(l : K)‖) →
      ∀ (D : ℕ) e, ‖MvPowerSeries.coeff e (∑ n ∈ range (D + 1),
        MvPowerSeries.C (a n) * (P ^ n - Q ^ n))‖ ≤ ‖(l : K)‖
def LogFunEq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → (∀ m : ℕ, ¬ l ∣ m → ‖(m : K)‖ = 1) → ∀ π : K, (π = l ∨ π = -l) →
    ∀ lam g : PowerSeries K, PowerSeries.constantCoeff lam = 0 →
      (∀ n : ℕ, ‖(n : K) * PowerSeries.coeff n lam‖ ≤ 1) →
      PowerSeries.constantCoeff g = 0 → Formalism.G.IntegralPS g →
      (∀ n, ‖PowerSeries.coeff n (g - PowerSeries.X ^ (l ^ 2))‖ ≤ ‖(l : K)‖) →
      PowerSeries.subst g lam = PowerSeries.C π * lam →
      Formalism.G.IntegralPS (lam - PowerSeries.C π⁻¹ *
        PowerSeries.subst ((PowerSeries.X : PowerSeries K) ^ (l ^ 2)) lam)
def DiscModel : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (W.c₄ / 12) ^ 3 - 27 * (W.c₆ / 216) ^ 2 = W.Δ
def TwelfthRoot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ η : (WittVector l (AlgebraicClosure (ZMod l)))ˣ,
    ∃ ε : (WittVector l (AlgebraicClosure (ZMod l)))ˣ, ε ^ 12 = η
def FrobeniusOrder : Prop :=
  ∀ (G : Type) [CommGroup G] (c φ : G), c ^ 2 = 1 →
    (c ∉ Subgroup.zpowers φ →
      orderOf (QuotientGroup.mk φ : G ⧸ Subgroup.zpowers c) = orderOf φ) ∧
    ∀ π : G →* Multiplicative (ZMod 2), π φ ≠ 1 → Even (orderOf φ)
open Classical in

def HomFormTrace : Prop :=
  ∀ (E L L' ι : Type) [Field E] [StarRing E] [AddCommGroup L] [Module E L] [AddCommGroup L']
    [Module E L'] [Fintype ι] (hL : L → L → E) (hL' : L' → L' → E),
    (∀ x x' y, hL (x + x') y = hL x y + hL x' y) → (∀ (a : E) x y, hL (a • x) y = a * hL x y) →
    (∀ x y, hL x y = star (hL y x)) → (∀ x y, hL' x y = star (hL' y x)) →
    ∀ (b : Module.Basis ι E L) (bs : ι → L), (∀ a a', hL (b a) (bs a') = if a = a' then 1 else 0) →
    ∀ (A B : L →ₗ[E] L') (Bs : L' →ₗ[E] L), (∀ x y, hL' (B x) y = hL x (Bs y)) →
      LinearMap.trace E L (Bs ∘ₗ A) = ∑ a, hL' (A (b a)) (B (bs a))
def TraceUnimodular : Prop :=
  ∀ (K E V : Type) [CommRing K] [CommRing E] [StarRing E] [AddCommGroup V] [Module E V]
    (T : E →+ K) (OE : Set E) (O : Set K) (h : V → V → E) (Y : Set V),
    (∀ (a : E) x y, h x (star a • y) = a * h x y) →
    (∀ a ∈ OE, ∀ y ∈ Y, star a • y ∈ Y) →
    (∀ e : E, (∀ a ∈ OE, T (a * e) ∈ O) → e ∈ OE) →
    (∀ x : V, (∀ y ∈ Y, h x y ∈ OE) → x ∈ Y) →
    ∀ x : V, (∀ y ∈ Y, T (h x y) ∈ O) → x ∈ Y
open Classical in

def SplitOrthonormal : Prop :=
  ∀ (B L ι : Type) [CommRing B] [StarRing B] [AddCommGroup L] [Module B L] (e : B) (h : L → L → B),
    e + star e = 1 → e * star e = 0 →
    (∀ x x' y, h (x + x') y = h x y + h x' y) → (∀ (a : B) x y, h (a • x) y = a * h x y) →
    (∀ x y, h x y = star (h y x)) →
    ∀ (l ls : ι → L), (∀ a, e • l a = l a) → (∀ a, star e • ls a = ls a) →
      (∀ a a', h (l a) (ls a') = if a = a' then e else 0) →
      (∀ a a', h (l a) (l a') = 0) ∧ (∀ a a', h (ls a) (ls a') = 0) ∧
      ∀ a a', h (l a + ls a) (l a' + ls a') = if a = a' then 1 else 0
def EigenCoordinate : Prop :=
  ∀ (Ow W Λ ι : Type) [CommRing Ow] [CommRing W] [AddCommGroup Λ] [Module W Λ] [Fintype ι]
    (σ j : Ow →+* W) (ω : ι → Ow) (a : Ow) (am : ι → ι → Ow),
    (∀ r' r, σ (am r' r) = j (am r' r)) → (∀ r, a * ω r = ∑ r', am r' r * ω r') →
    ∀ lx : ι → Λ,
      ∑ r', σ (ω r') • ∑ r, j (am r' r) • lx r = σ a • ∑ r, σ (ω r) • lx r
open Classical in

def AdjointMatrix : Prop :=
  ∀ (O P P' ι : Type) [CommRing O] [StarRing O] [AddCommGroup P] [Module O P] [AddCommGroup P']
    [Module O P'] [Fintype ι] (h₁ : P → P' → O),
    (∀ p q p', h₁ (p + q) p' = h₁ p p' + h₁ q p') → (∀ (c : O) p p', h₁ (c • p) p' = c * h₁ p p') →
    (∀ p p' q', h₁ p (p' + q') = h₁ p p' + h₁ p q') →
    (∀ (c : O) p p', h₁ p (c • p') = star c * h₁ p p') →
    ∀ (ω : ι → P) (ωv : ι → P'), (∀ r r', h₁ (ω r) (ωv r') = if r = r' then 1 else 0) →
    ∀ (a : P → P) (abar : P' → P'), (∀ p p', h₁ (a p) p' = h₁ p (abar p')) →
    ∀ (am cm : ι → ι → O), (∀ r, a (ω r) = ∑ r', am r' r • ω r') →
      (∀ r', abar (ωv r') = ∑ r, cm r r' • ωv r) →
      ∀ r r', cm r r' = star (am r' r)
def MeanInvariant : Prop :=
  ∀ (Z S μ X : Type) [CommRing Z] [AddCommGroup S] [Module Z S] [Group μ] [Fintype μ]
    [MulAction μ X] (La : Submodule Z S) (ninv : Z), ninv * (Fintype.card μ : Z) = 1 →
    ∀ b : X → S, (∀ (u : μ) x, b (u • x) - b x ∈ La) →
      (∀ (u' : μ) x, ninv • ∑ u : μ, b (u • (u' • x)) = ninv • ∑ u : μ, b (u • x)) ∧
      ∀ x, ninv • ∑ u : μ, b (u • x) - b x ∈ La
def AxisVanish : Prop :=
  ∀ (R σ τ : Type) [CommRing R] [Finite σ] [Finite τ] (P : MvPowerSeries (σ ⊕ τ) R),
    MvPowerSeries.subst (fun i : σ ⊕ τ => Sum.elim
      (fun s => (MvPowerSeries.X (Sum.inl s) : MvPowerSeries (σ ⊕ τ) R)) (fun _ => 0) i) P = 0 →
    ∀ n : σ ⊕ τ →₀ ℕ, (∀ t, n (Sum.inr t) = 0) → MvPowerSeries.coeff n P = 0
def DivisionLemma : Prop :=
  ∀ (A σ : Type) [CommRing A] [IsDomain A] [Finite σ] (k : ℕ) (g : Fin k → MvPowerSeries σ A),
    Function.Injective g → (∀ i, MvPowerSeries.constantCoeff (g i) = 0) →
    ∀ D : MvPowerSeries (Option σ) A,
      (∀ i, MvPowerSeries.subst (fun o : Option σ => Option.elim o (g i) MvPowerSeries.X) D = 0) →
      ∃ D' : MvPowerSeries (Option σ) A,
        D = (∏ i, (MvPowerSeries.X none - MvPowerSeries.subst
          (fun s : σ => (MvPowerSeries.X (some s) : MvPowerSeries (Option σ) A)) (g i))) * D'
def DetLeading : Prop :=
  ∀ (R : Type) [CommRing R] (a b c : R),
    Matrix.det !![a ^ 3, a, -1; b ^ 3, b, -1; c ^ 3, c, -1] =
      (a - b) * (b - c) * (c - a) * (a + b + c)
def SigmaStarFormulas : Prop :=
  ∀ (R : Type) [CommRing R] (a₁ a₃ β x₁ y₁ x₂ y₂ x₃ y₃ a b c : R),
    Matrix.det !![1, x₁ + β, 2 * y₁ + a₁ * x₁ + a₃; 1, x₂ + β, 2 * y₂ + a₁ * x₂ + a₃;
        1, x₃ + β, 2 * y₃ + a₁ * x₃ + a₃] = 2 * Matrix.det !![1, x₁, y₁; 1, x₂, y₂; 1, x₃, y₃] ∧
    (a + b) ^ 2 + (a - b) ^ 2 - 2 * a ^ 2 - 2 * b ^ 2 = 0 ∧
    (a + b + c) ^ 2 + (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 - 3 * (a ^ 2 + b ^ 2 + c ^ 2) = 0
open Complex in

def Hf (A : ℝ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (A : ℂ)
def EF (A : ℝ) (z w : ℂ) : ℝ := (Hf A z w).im
def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)
def Uop (A : ℝ) (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => F (z + x) * Complex.exp (-Real.pi * Hf A z x - Real.pi * Hf A x x / 2)
def Fq (A : ℝ) (S : ℂ → ℂ) (y : ℂ) : ℂ → ℂ := fun z => Uop A y S z / S z
def UopNeg : Prop :=
  ∀ (A : ℝ) (x : ℂ) (F : ℂ → ℂ) (z : ℂ), Uop A x F (-z) = Uop A (-x) (fun w => F (-w)) z
def LegendreCoefficient : Prop :=
  ∀ (a b ω₁ ω₂ : ℂ) (A : ℝ), A = (ω₁ * (starRingEnd ℂ) ω₂).im → A ≠ 0 →
    (a * ω₂ + b * (starRingEnd ℂ) ω₂) * ω₁ - (a * ω₁ + b * (starRingEnd ℂ) ω₁) * ω₂ =
      2 * Real.pi * Complex.I →
    b = Real.pi / A
def TranslateModulus : Prop :=
  ∀ (A : ℝ) (S : ℂ → ℂ) (x ω ep : ℂ), (∀ z, Uop A ω S z = ep * S z) →
    (∀ z, Uop A (x + ω) S z = ep * ee (EF A x ω / 2) * Uop A x S z) ∧
    ∀ (m₀ : ℕ) (la : ℂ) (k : ℤ), ω = 2 * m₀ * la → ep = 1 → EF A (m₀ * x) la = k →
      ∀ z, Uop A (x + ω) S z = Uop A x S z
def FqPeriod : Prop :=
  ∀ (A : ℝ) (S : ℂ → ℂ) (y ω ep : ℂ), ep ≠ 0 → (∀ z, Uop A ω S z = ep * S z) →
    ∀ z, Fq A S y (z + ω) = ee (-EF A ω y) * Fq A S y z
def FqReflect : Prop :=
  ∀ (A : ℝ) (S : ℂ → ℂ) (y z : ℂ), (∀ w, S (-w) = -S w) →
    Fq A S y (-z) = Fq A S (-y) z ∧ (S z ≠ 0 → S (z - y) ≠ 0 → Fq A S y (-z) * Fq A S y (z - y) = 1)
def FqDouble : Prop :=
  ∀ (A : ℝ) (S : ℂ → ℂ) (y z : ℂ), S (z + y) ≠ 0 →
    Fq A S (2 * y) z = Fq A S y (z + y) * Fq A S y z
def QuadraticFormEF : Prop :=
  ∀ (A d : ℝ) (x : ℂ), 0 < d →
    EF A ((1 + Real.sqrt d * Complex.I) / 2 * x) x = ‖x‖ ^ 2 * Real.sqrt d / (2 * A) ∧
    ∀ n : ℝ, n ≠ 0 → A = n * Real.sqrt d / 2 →
      EF A ((1 + Real.sqrt d * Complex.I) / 2 * x) x = ‖x‖ ^ 2 / n
def Wop (A d : ℝ) (x : ℂ) (F : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ee (EF A ((1 + Real.sqrt d * Complex.I) / 2 * x) x / 2) * Uop A x F z
def WopCocycle : Prop :=
  ∀ (A d : ℝ) (x y : ℂ), 0 < d →
    ∀ (a₁ b : ℝ), Hf A y x * (Real.sqrt d / 2) = a₁ + b * ((1 + Real.sqrt d * Complex.I) / 2) →
      (∀ (F : ℂ → ℂ) (z : ℂ), Wop A d x (Wop A d y F) z = ee (-a₁) * Wop A d (x + y) F z) ∧
      ∀ (a₁' b' : ℝ),
        Hf A x y * (Real.sqrt d / 2) = a₁' + b' * ((1 + Real.sqrt d * Complex.I) / 2) →
        a₁ - a₁' = EF A x y
def HomFormInvariant : Prop :=
  ∀ (E n n' : Type) [CommRing E] [StarRing E] [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] (g : Matrix.unitaryGroup n E) (g' : Matrix.unitaryGroup n' E)
    (x y : Matrix n' n E),
    Matrix.trace (((g' : Matrix n' n' E) * x * ((g⁻¹ : Matrix.unitaryGroup n E) : Matrix n n E)) *
      ((g' : Matrix n' n' E) * y * ((g⁻¹ : Matrix.unitaryGroup n E) : Matrix n n E)).conjTranspose) =
      Matrix.trace (x * y.conjTranspose)
def BinaryFormOne : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ u₁ u₂ : ZMod p, u₁ ≠ 0 → u₂ ≠ 0 →
    ∃ a b : ZMod p, u₁ * a ^ 2 + u₂ * b ^ 2 = 1
def DetPhaseSquare : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (δ : Matrix.unitaryGroup n ℂ),
    Matrix.det (1 - ((δ⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)) ≠ 0 →
      ((‖Matrix.det (1 - ((δ⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ))‖ : ℂ) /
        Matrix.det (1 - ((δ⁻¹ : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ))) ^ 2 =
        (-1) ^ Fintype.card n * Matrix.det (δ : Matrix n n ℂ)
def InfinityTypeSquare : Prop :=
  ∀ (x : ℂ) (n : ℤ), x ≠ 0 → (x / (‖x‖ : ℂ)) ^ (2 * n) = (x / (starRingEnd ℂ) x) ^ n
def PowerUnit : Prop :=
  ∀ (K T : Type) [Field K] [Fintype T] (v : Kˣ →* Multiplicative ℚ) (c ζ : Kˣ) (t : T → Kˣ)
    (n : T → ℤ) (h k : ℕ), 0 < h → 0 < k → ζ ^ k = 1 → (∀ τ, v (t τ) = 1) →
    c ^ h = (∏ τ, t τ ^ (-n τ)) * ζ → v c = 1
def FockTranslate : Prop :=
  ∀ (A : ℝ) (x z : ℂ) (G φ : ℂ → ℂ),
    Uop A x G z * (starRingEnd ℂ) (Uop A x φ z) * Complex.exp (-Real.pi * Hf A z z) =
      G (z + x) * (starRingEnd ℂ) (φ (z + x)) * Complex.exp (-Real.pi * Hf A (z + x) (z + x))
def SignConvention : Prop :=
  ∀ (n d : ℝ) (x y : ℂ), 0 < n → 0 < d →
    0 < (-1 / ((n : ℂ) * (Real.sqrt d * Complex.I))).im ∧
    2 * ((-1 / ((n : ℂ) * (Real.sqrt d * Complex.I))) * (x * (starRingEnd ℂ) y)).re =
      -EF (n * Real.sqrt d / 2) x y
def TypesOfRho : Prop :=
  ∀ (H T : Type) [CommGroup H] [Fintype T] (t : T → H) (e : T → ℤ) (a a' : ℤ),
    (∏ τ, t τ ^ e τ)⁻¹ * (∏ τ, (t τ)⁻¹) ^ (-a') = ∏ τ, t τ ^ (-(e τ - a')) ∧
    (∏ τ, t τ ^ e τ) * (∏ τ, (t τ)⁻¹) ^ a = ∏ τ, t τ ^ (e τ - a)
def BridgeGenerators : Prop :=
  ∀ (K T : Type) [Field K] [Fintype T] (p : Kˣ) (δ : T → Kˣ) (cl s' : T → ℤ) (i : ℤ),
    (∏ τ, δ τ ^ s' τ = p ^ (i * ∑ τ, cl τ * s' τ) * ∏ τ, (p ^ (-i * cl τ) * δ τ) ^ s' τ) ∧
    (∀ (v : Kˣ → ℚ), (∀ x y, v (x * y) = v x + v y) → v p = 1 →
      ∀ (ρz ζ : Kˣ) (a : T → Kˣ) (h k : ℕ), 0 < h → 0 < k → ζ ^ k = 1 →
        (∀ τ, v (a τ) = h * cl τ) → ρz ^ h = (∏ τ, a τ ^ (-s' τ)) * ζ →
        v ρz = -∑ τ, (cl τ : ℚ) * s' τ ∧
        v ((ρz * p ^ (∑ τ, cl τ * s' τ)) ^ i) = 0 ∧
        ρz ^ i * ∏ τ, δ τ ^ s' τ =
          (ρz * p ^ (∑ τ, cl τ * s' τ)) ^ i * ∏ τ, (p ^ (-i * cl τ) * δ τ) ^ s' τ) ∧
    (∑ τ, cl τ = 0 → ∀ c : ℤ, ∏ τ, (p ^ (-i * cl τ) * δ τ) ^ c = ∏ τ, δ τ ^ c)
def OddRankExponent : Prop :=
  ∀ (a' : ℤ) (eV : ℚ) (N : ℤ), (4 * (a' : ℚ) = 2 * (-2 * eV + N)) →
    (a' : ℚ) = -eV + N / 2 ∧ ∃ m : ℤ, 2 * eV = m ∧ (Odd m ↔ Odd N)
end Formalism.HermitianLattices.ExpSeriesBivariate


