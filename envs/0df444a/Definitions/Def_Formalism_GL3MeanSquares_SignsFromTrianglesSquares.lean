-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_SignsFromTrianglesSquares
-- name    : Formalism_GL3MeanSquares_SignsFromTrianglesSquares
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:30.933082+00:00
-- url     : https://prove2.me/theorems/25d92d61-c8f7-409b-bb58-b18dac4ef147
-- title:
--   Signs From Triangles Squares
-- statement:
--   Definitions and structural lemmas for Signs From Triangles Squares, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/SignsFromTrianglesSquares.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.WeilRepresentation
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
def SelfDualTraceLattice : Prop :=
  ∀ (A K B L : Type) [CommRing A] [Field K] [CommRing B] [Field L] [Algebra A K] [Algebra B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsFractionRing A K] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsFractionRing B L] [IsDedekindDomain B]
    (c : L ≃+* L) (I J : FractionalIdeal (nonZeroDivisors B) L),
    (∀ x, c (c x) = x) → I ≠ 0 → (∀ x, x ∈ J ↔ c x ∈ I) →
    I * J = FractionalIdeal.dual A K 1 →
    ∀ y : L, (∀ x ∈ I, Algebra.trace K L (x * c y) ∈ (algebraMap A K).range) ↔ y ∈ I
def ImHGenusOne : Prop :=
  ∀ (d x0 x1 y0 y1 : ℝ), 0 < d →
    (((x0 : ℂ) + x1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2)) *
      (starRingEnd ℂ) ((y0 : ℂ) + y1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2))).im /
        (Real.sqrt d / 2) = x1 * y0 - x0 * y1 ∧
    2 * (((x0 : ℂ) + x1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2)) *
      (starRingEnd ℂ) ((y0 : ℂ) + y1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2))).re =
        2 * (x0 * y0 + x0 * y1 + (1 + d) / 4 * (x1 * y1)) + (x1 * y0 - x0 * y1)
def SupGenusOne : Prop :=
  ∀ (d : ℕ) (x0 x1 : ℤ), d % 4 = 3 → (x0 ≠ 0 ∨ x1 ≠ 0) →
    1 ≤ x0 ^ 2 + x0 * x1 + (((d + 1) / 4 : ℕ) : ℤ) * x1 ^ 2
def PerDifferentMean : Prop :=
  ∀ (DE d : ℝ) (f : ℕ), 0 < DE → 0 < d → 0 < f →
    (2 / (2 * (f : ℝ))) * ((1 / 2) * Real.log (DE / d ^ f)) =
      Real.log (DE ^ (1 / (2 * (f : ℝ)))) - Real.log (Real.sqrt d)
def Heisenberg₂ {V : Type} [AddCommGroup V] (H : V → V → ℂ) (x : V) (F : V → ℂ) (z : V) : ℂ :=
  F (z + x) * Complex.exp (-(Real.pi : ℂ) * H z x - Real.pi * H x x / 2)
def HeisenbergCocycle : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ (F : V → ℂ) (x y z : V),
      Heisenberg₂ H x (Heisenberg₂ H y F) z =
        Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H x y).im : ℂ))) * Heisenberg₂ H (x + y) F z
def HeisenbergNorm : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ (F : V → ℂ) (x z : V),
      ‖Heisenberg₂ H x F z‖ ^ 2 * Real.exp (-(Real.pi * (H z z).re)) =
        ‖F (z + x)‖ ^ 2 * Real.exp (-(Real.pi * (H (z + x) (z + x)).re))
def HeisenbergUnitary : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ) (δ : V ≃+ V), (∀ x y, H (δ x) (δ y) = H x y) →
    ∀ (F : V → ℂ) (x z : V),
      Heisenberg₂ H x F (δ.symm z) = Heisenberg₂ H (δ x) (fun w => F (δ.symm w)) z
def WCocycle : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ (F : V → ℂ) (x y z : V) (qx qy qxy a b : ℝ), (H x y).im = b → qxy = qx + qy + a →
      Complex.exp ((Real.pi : ℂ) * Complex.I * qx) *
          Heisenberg₂ H x (fun w => Complex.exp ((Real.pi : ℂ) * Complex.I * qy) * Heisenberg₂ H y F w) z =
        Complex.exp (-((Real.pi : ℂ) * Complex.I * (a + b))) *
          (Complex.exp ((Real.pi : ℂ) * Complex.I * qxy) * Heisenberg₂ H (x + y) F z)
def WCocycleTrace : Prop :=
  ∀ (E : Type) [Field E] [CharZero E] [StarRing E] (s a b : E), s ≠ 0 → star s = -s →
    star a = a → star b = b →
    ((1 + s) / 2 * ((a + b * s) / 2) / s) + star ((1 + s) / 2 * ((a + b * s) / 2) / s) = (a + b) / 2
def ProjectorNorm : Prop :=
  ∀ (T : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] (A : Type) [CommGroup A] [Fintype A]
    (ρ : A →* (T ≃ₗᵢ[ℂ] T)) (F : T),
    (∀ x : A, x ≠ 1 → inner ℂ (ρ x F) F = 0) →
    ‖((Fintype.card A : ℂ)⁻¹) • ∑ x : A, ρ x F‖ ^ 2 = ‖F‖ ^ 2 / Fintype.card A
def SigmaStarMultiplier : Prop :=
  ∀ (s2 z om : ℂ) (A : ℝ),
    (s2 * om + Real.pi * (starRingEnd ℂ) om / A) * (z + om / 2) - s2 * ((z + om) ^ 2 - z ^ 2) / 2 =
      Real.pi * (z * (starRingEnd ℂ) om / A) + Real.pi * (om * (starRingEnd ℂ) om / A) / 2
def SecondCoefficientFormula : Prop :=
  ∀ (s2 al alb S : ℂ), al ≠ 0 → al ≠ alb → -(s2 * al ^ 2) = -(al * alb * s2) - S →
    s2 = -S / (al * (alb - al))
def ThetaNormGaussian : Prop :=
  ∀ y : ℝ, 0 < y →
    y⁻¹ * (∫ t : ℝ, Real.exp (-(2 * Real.pi * t ^ 2 / y))) = (2 * y) ^ (-(1 / 2) : ℝ)
def ThetaNorm : Prop :=
  ∀ τ : ℂ, 0 < τ.im →
    (∫ t in (0 : ℝ)..τ.im, (∫ x in (0 : ℝ)..1, ‖jacobiTheta₂ ((x : ℂ) + (t : ℂ) * Complex.I) τ‖ ^ 2) *
        Real.exp (-(2 * Real.pi * t ^ 2 / τ.im))) / τ.im = (2 * τ.im) ^ (-(1 / 2) : ℝ)
def ThConstantHalf : Prop :=
  ∀ (d γ Λ rd L : ℝ), 0 < d → 0 ≤ γ → Real.sqrt d ≤ rd / 2 → Real.log (rd / 2) + |Λ| ≤ L →
    -(1 / 2) * (Real.log 2 + (γ - Real.log (2 * Real.sqrt d) - Λ)) =
        (1 / 2) * (Real.log (Real.sqrt d) - γ + Λ) ∧
      (1 / 2) * (Real.log (Real.sqrt d) - γ + Λ) ≤ L / 2
def WeberTwoTorsion : Prop :=
  ∀ (P η ta tb tc u w : ℂ), η ≠ 0 → tc ≠ 0 → ta * tb * tc = 2 * η ^ 3 → (2 * P) ^ 12 * η ^ 24 = 1 →
    u = P ^ 2 * ta ^ 4 → w = P ^ 2 * tb ^ 4 → (u * w) ^ 3 * (tc / η) ^ 12 = 1
def TraceDiagonal : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (tr : O → Z),
    (∀ α, algebraMap Z O (tr α) = star α + α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (z : Z) a b, cob φ a (algebraMap Z O z • b) = z • cob φ a b) →
    (∀ x : Q, x + x = 0 → x = 0) →
    ∀ (γ : O) (u : M), (∀ a b, cob φ (star γ • a) b = cob φ a (γ • b)) →
      φ ((2 : O) • u) = (4 : Z) • φ u → cob φ u (γ • u) = tr γ • φ u
def TranslateProduct : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ (s : V → ℂ) (w : V → V → ℂ), (∀ a b, s (a + b) * s (a - b) = w a b * s a ^ 2 * s b ^ 2) →
    ∀ P Q z : V, Heisenberg₂ H (P + Q) s z * Heisenberg₂ H (P - Q) s z =
      (Heisenberg₂ H Q s 0) ^ 2 * w (z + P) Q * (Heisenberg₂ H P s z) ^ 2
def ParallelogramTwo : Prop :=
  ∀ (T : Type) [AddCommGroup T] [Fintype T] (M0 m : T → ℝ),
    (∀ P Q, Q ≠ 0 → M0 (P + Q) + M0 (P - Q) - 2 * M0 P = 2 * m Q) → M0 0 = 0 →
    (∀ Q, Q ≠ 0 → m Q = 0) ∧ ∀ P, M0 P = 0
def TwoVanish : Prop :=
  ∀ (Z M Q : Type) [CommRing Z] [AddCommGroup M] [Module Z M] [AddCommGroup Q] [Module Z Q]
    (φ : M → Q) (b bbar : Z),
    (∀ (z : Z) x y, cob φ (z • x) y = z • cob φ x y) →
    (∀ u, φ (b • u) = (b * bbar) • φ u) →
    ((∀ x y, cob φ x y = 0) → ∀ (z : Z) u, φ (z • u) = z • φ u) →
    IsUnit b → IsUnit (b - bbar) → IsUnit (1 - bbar) →
    (∀ x y, cob φ x y = 0) ∧ ∀ u, φ u = 0
def SumExpansion : Prop :=
  ∀ (M Q : Type) [AddCommGroup M] [AddCommGroup Q] (φ : M → Q),
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    ∀ (k : ℕ) (a : Fin k → M),
      φ (∑ j, a j) =
        (∑ j, φ (a j)) + ∑ j, ∑ j' ∈ univ.filter (fun j' => j < j'), cob φ (a j) (a j')
def GramExpansion : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n : Type) [Fintype n] (k : ℕ) (A : n → Fin k → O) (u : Fin k → M),
      ∑ i, φ (∑ j, A i j • u j) =
        (∑ j, (∑ i, nm (A i j)) • φ (u j)) +
          ∑ j, ∑ j' ∈ univ.filter (fun j' => j < j'),
            cob φ ((∑ i, star (A i j') * A i j) • u j) (u j')
def JetsOfExp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (f E : PowerSeries K),
    (∀ n : ℕ, 1 ≤ n → (n.factorial : K) * PowerSeries.coeff n f ∈ R) →
    PowerSeries.constantCoeff E = 1 →
    PowerSeries.derivative K E = PowerSeries.derivative K f * E →
    ∀ n : ℕ, (n.factorial : K) * PowerSeries.coeff n E ∈ R
def JetsOfLogUnitInv : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (σ ι : Type)
    (D : ι → Derivation K (MvPowerSeries σ K) (MvPowerSeries σ K)) (U f : MvPowerSeries σ K),
    (∀ i g, (∀ m, MvPowerSeries.coeff m g ∈ R) → ∀ m, MvPowerSeries.coeff m (D i g) ∈ R) →
    (∀ m, MvPowerSeries.coeff m U ∈ R) → MvPowerSeries.constantCoeff U = 1 →
    (∀ i, D i f * U = D i U) →
    ∀ (i : ι) (w : List ι) m, MvPowerSeries.coeff m (w.foldr (fun j g => D j g) (D i f)) ∈ R
def HyperbolicFromNorm : Prop :=
  ∀ (O : Type) [CommRing O] [StarRing O] [Invertible (2 : O)] (κ : O), star κ * κ = -1 →
    star (1 : O) * 1 + star κ * κ = 0 ∧
    star (⅟2 : O) * ⅟2 + star (-(⅟2 * κ)) * (-(⅟2 * κ)) = 0 ∧
    star (1 : O) * ⅟2 + star κ * (-(⅟2 * κ)) = 1
def KernelTranslate : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ y w z : V, Heisenberg₂ H y (fun u => Complex.exp (Real.pi * H u w)) z =
      Complex.exp (Real.pi * H y w - Real.pi * H y y / 2) * Complex.exp (Real.pi * H z (w - y))
def LemmaCDecay : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ) (a : V → V),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    (∀ x y, H (a x) (a y) = H x y) →
    ∀ x z : V, ‖Heisenberg₂ H x (fun u => Complex.exp (Real.pi * H u z)) (a z) *
        Complex.exp (-(Real.pi * H z z))‖ =
      Real.exp (-(Real.pi / 2 * (H (x - (z - a z)) (x - (z - a z))).re))
def GaussianIntegralC : Prop :=
  ∀ lam u v : ℂ, 0 < lam.re →
    (∫ z : ℂ, Complex.exp (-(Real.pi * lam * ((‖z‖ ^ 2 : ℝ) : ℂ)) + Real.pi * u * (starRingEnd ℂ) z +
        Real.pi * (starRingEnd ℂ) v * z)) =
      lam⁻¹ * Complex.exp (Real.pi * u * (starRingEnd ℂ) v / lam)
def CayleyOperator : Prop :=
  ∀ (R : Type) [Ring R] [StarRing R] [Invertible (2 : R)] (a B : R),
    star a * a = 1 → a * star a = 1 → (1 - a) * B = 1 → B * (1 - a) = 1 →
    star B = 1 - B ∧ star (B - ⅟2) = -(B - ⅟2) ∧ ⅟2 + a * B = B - ⅟2
def LemmaCQuadratic : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ) (C B : V → V) (al : V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    (∀ x y, C (x + y) = C x + C y) → (∀ x y, H (C x) y = -H x (C y)) →
    (∀ x y, H (B x) y = H (C x) y + H x y / 2) →
    ∀ x x' : V,
      al (x + x') = al x * al x' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H x x').im : ℂ))) →
      al (x + x') * Complex.exp (-(Real.pi * H (C (x + x')) (x + x'))) =
        (al x * Complex.exp (-(Real.pi * H (C x) x))) *
          (al x' * Complex.exp (-(Real.pi * H (C x') x'))) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((H (B x) x').im : ℂ)))
def CocycleEighth : Prop :=
  ∀ (c r G D : ℂ) (g : ℕ), c = r * G → r ^ 2 = (-1) ^ g * D → G ^ 8 = 1 →
    c ^ 2 = (-1) ^ g * D * G ^ 2 ∧ c ^ 8 = D ^ 4
def GaussSumModulus : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Fintype M] (φ : M → ℂ) (B : M → M → ℂ),
    (∀ x, ‖φ x‖ = 1) → (∀ x y, φ (x + y) = φ x * φ y * B x y) →
    (∀ x x' y, B (x + x') y = B x y * B x' y) →
    (∀ x, x ≠ 0 → ∃ y, B x y ≠ 1) →
    ‖∑ x, φ x‖ ^ 2 = Fintype.card M
def QuadraticFromEven : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [CommGroup H] (Φ : G → H) (B : G → G → H),
    (∀ x y, Φ (x + y) = Φ x * Φ y * B x y) → (∀ x x' y, B (x + x') y = B x y * B x' y) →
    (∀ x, Φ (-x) = Φ x) →
    (∀ y, Φ y ^ 2 = B y y) ∧ ∀ (k : ℤ) (y : G), Φ (k • y) = Φ y ^ (k ^ 2)
def GaussSumRadical : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] (Φ : G → ℂ) (B : G → G → ℂ),
    (∀ x y, Φ (x + y) = Φ x * Φ y * B x y) → ∑ y, Φ y ≠ 0 →
    ∀ r : G, (∀ y, B r y = 1) → Φ r = 1
def OddOrderDetermined : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [Fintype G] [CommGroup H] (Φ Φ' : G → H) (B : G → G → H),
    Odd (Fintype.card G) →
    (∀ x y, Φ (x + y) = Φ x * Φ y * B x y) → (∀ x y, Φ' (x + y) = Φ' x * Φ' y * B x y) →
    (∀ x, Φ (-x) = Φ x) → (∀ x, Φ' (-x) = Φ' x) → ∀ x, Φ x = Φ' x
def TraceZeroConj : Prop :=
  ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (X : S →ₗ[ℂ] S)
    (Y : S ≃ₗ[ℂ] S) (c : ℂ), c ≠ 1 →
    (Y : S →ₗ[ℂ] S) ∘ₗ X ∘ₗ (Y.symm : S →ₗ[ℂ] S) = c • X → LinearMap.trace ℂ S X = 0
def SplitLagrangian : Prop :=
  ∀ (M : Type) [AddCommGroup M] (B : M → M → ℂ) (P P' : AddSubgroup M),
    (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y y', B x (y + y') = B x y * B x y') →
    (∀ x, (∀ y, B x y = 1) → x = 0) → P ⊔ P' = ⊤ →
    (∀ x ∈ P, ∀ y ∈ P, B x y = 1) → (∀ x ∈ P', ∀ y ∈ P', B x y = 1) →
    ∀ x, (∀ y ∈ P, B x y = 1) → x ∈ P
def InertGaussSumLength : Prop :=
  ∀ (p a : ℕ) [Fact p.Prime] (t n : ℤ), (∀ z : ZMod p, z ^ 2 - (t : ZMod p) * z + (n : ZMod p) ≠ 0) →
    ∀ ψ : AddChar (ZMod (p ^ a)) ℂ, ψ.IsPrimitive →
      ∑ x : ZMod (p ^ a), ∑ y : ZMod (p ^ a),
        ψ (x ^ 2 + (t : ZMod (p ^ a)) * x * y + (n : ZMod (p ^ a)) * y ^ 2) = (-(p : ℂ)) ^ a
def SignsFromTrianglesSquares : Prop :=
  ∀ (X X' : Type) [Nonempty X] [Nonempty X'] (s1 : X → X → X' → ℤˣ) (s2 : X → X' → X' → ℤˣ),
    (∀ L L1 L2 L', s1 L L1 L' * s1 L1 L2 L' = s1 L L2 L') →
    (∀ L L' L'' L''', s2 L L' L'' * s2 L L'' L''' = s2 L L' L''') →
    (∀ L L1 L' L'', s1 L L1 L' * s2 L1 L' L'' = s2 L L' L'' * s1 L L1 L'') →
    ∃ ε : X → X' → ℤˣ, (∀ L L1 L', ε L L' * s1 L L1 L' = ε L1 L') ∧
      ∀ L L' L'', ε L L' * s2 L L' L'' = ε L L''
def CommutatorBimult : Prop :=
  ∀ (G : Type) [Group G] (a b c : G), (∀ g : G, g * (b * c * b⁻¹ * c⁻¹) = (b * c * b⁻¹ * c⁻¹) * g) →
    (a * b) * c * (a * b)⁻¹ * c⁻¹ = (a * c * a⁻¹ * c⁻¹) * (b * c * b⁻¹ * c⁻¹)
def SL2NoSignCharacter : Prop :=
  ∀ (F : Type) [Field F], (2 : F) ≠ 0 →
    ∀ (t : Matrix.SpecialLinearGroup (Fin 2) F →* ℤˣ) (g : Matrix.SpecialLinearGroup (Fin 2) F),
      t g = 1
def DiscriminantFactorization : Prop :=
  ∀ (dt1 D : ℂ) (f N M' : ℕ), dt1 ≠ 0 → Even f →
    ((‖dt1‖ : ℂ) / dt1) ^ 2 = (-1) ^ (f * N) * D →
    ((‖dt1 ^ (2 * M')‖ : ℝ) : ℂ) / dt1 ^ (2 * M') = D ^ M'
def ModelCocycleTwoSwapped : Prop :=
  ∀ δ a b : ℚ_[2], δ ≠ 0 →
    ((-(1 + δ)) / (2 * δ)) * ((a + b * δ) / 2) + ((1 - δ) / (2 * δ)) * ((a - b * δ) / 2) =
      -((a + b) / 2)
def HalfIntegerParity : Prop :=
  ∀ (d : ℕ) (a b : ℤ), d % 4 = 3 → ((4 : ℤ) ∣ a ^ 2 + d * b ^ 2 ↔ (2 : ℤ) ∣ a - b)
def KappaValuation : Prop :=
  ∀ h y : ℚ, h ≠ 0 → h * (-y / (2 * h)) + y / 2 = 0 ∧ -h * (-y / (2 * h)) + -y / 2 = 0
def ChiExistsAllEmbeddings : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] (Ψ : Finset (E →+* ℂ))
    (A : Type) [CommGroup A] (ι : unitary E →* A) (K : Subgroup A),
    (∀ (τ : E →+* ℂ) (x : E), τ (star x) = (starRingEnd ℂ) (τ x)) →
    Even Ψ.card →
    (∀ z : unitary E, ι z ∈ K → (z : E) = 1 ∨ (z : E) = -1) →
    ∃ χ : A →* ℂˣ, (∀ k ∈ K, χ k = 1) ∧
      (∀ z : unitary E, ((χ (ι z) : ℂˣ) : ℂ) = ∏ τ ∈ Ψ, (τ (z : E))⁻¹) ∧
      ∀ (t : A) (s : ℂ →+* ℂ), ‖s ((χ t : ℂˣ) : ℂ)‖ = 1
def QuadExpJetsDvd : Prop :=
  ∀ (n : ℕ) (k : Fin n → Fin n → ℕ),
    (∏ i, ∏ j ∈ univ.filter (fun j => i ≤ j), (k i j).factorial) ∣
      ∏ i, ((∑ j ∈ univ.filter (fun j => i ≤ j), k i j) +
        ∑ j ∈ univ.filter (fun j => j ≤ i), k j i).factorial
def FourSquaresPadic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (u : ℤ_[p]), ∃ T : Matrix (Fin 4) (Fin 4) ℤ_[p],
    T.transpose * T = u • (1 : Matrix (Fin 4) (Fin 4) ℤ_[p])
def IntegrationLemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (X r : A) (k : ℕ),
    ∃ s : A, (X + (p : A) * r) ^ (k + 1) - X ^ (k + 1) = ((k + 1 : ℕ) : A) * ((p : A) * s)
def DworkLemma : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : Subring K) (σ : K →+* K) (p : ℕ) (hp : p.Prime),
    (∀ a ∈ W, ∃ b ∈ W, σ a - a ^ p = (p : K) * b) →
    ∀ (ι : Type) (f : MvPowerSeries ι K), MvPowerSeries.constantCoeff f = 1 →
      ((∀ m, MvPowerSeries.coeff m f ∈ W) ↔
        ∃ h : MvPowerSeries ι K, (∀ m, MvPowerSeries.coeff m h ∈ W) ∧
          MvPowerSeries.constantCoeff h = 0 ∧
          MvPowerSeries.expand p hp.ne_zero (MvPowerSeries.map σ f) =
            f ^ p * (1 + MvPowerSeries.C (p : K) * h))
def DworkCorollary : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : Subring K) (σ : K →+* K) (p : ℕ) (hp : p.Prime), p ≠ 2 →
    (∀ a ∈ W, ∃ b ∈ W, σ a - a ^ p = (p : K) * b) → (∀ n : ℕ, ¬ p ∣ n → ((n : K))⁻¹ ∈ W) →
    ∀ (ι : Type) (H : MvPowerSeries ι K), MvPowerSeries.constantCoeff H = 0 →
      ((∀ m, MvPowerSeries.coeff m (PowerSeries.subst H (PowerSeries.exp K)) ∈ W) ↔
        ∀ m, ∃ w ∈ W, MvPowerSeries.coeff m
          (MvPowerSeries.expand p hp.ne_zero (MvPowerSeries.map σ H) - MvPowerSeries.C (p : K) * H) =
            (p : K) * w)
def VarpiExponent : Prop :=
  ∀ q j : ℕ, 2 ≤ q → 2 ≤ j → q - 1 + j ≤ ∑ i ∈ range j, q ^ i
def ModuleShift : Prop :=
  ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] (p : K) (h r : A) (i : ℕ), p ≠ 0 →
    (p⁻¹) ^ i • (h + p • r) ^ i =
      ∑ k ∈ range (i + 1), (i.choose k : A) * ((p⁻¹) ^ k • h ^ k) * r ^ (i - k)
def StepVICoordinates : Prop :=
  ∀ (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p] (n : ℕ) [NeZero n], Even n →
    ∀ (u ζ : ZMod n → A), (∀ e, u (e + 1) = u e ^ p) → ∀ L : ℕ,
      ∑ l ∈ range L, (-1) ^ l *
          (∑ s ∈ univ.filter (fun s : ZMod n => s.val % 2 = 0), u s * ζ s) ^ ((p ^ 2) ^ l) =
        ∑ e ∈ univ.filter (fun e : ZMod n => e.val % 2 = 0),
          u e * ∑ l ∈ range L, (-1) ^ l * ζ (e - 2 * (l : ZMod n)) ^ ((p ^ 2) ^ l)
def StepVI : Prop :=
  ∀ (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime] [CharP A p] (n : ℕ) [NeZero n], Even n →
    ∀ (ι : Type) [Fintype ι] (u v : ZMod n → ι → A) (s : ZMod n → A),
      (∀ e r, u (e + 1) r = u e r ^ p) → (∀ e r, v (e + 1) r = v e r ^ p) →
      (∀ a b : ZMod n, a.val % 2 = b.val % 2 → ∑ r, u a r * v b r = if a = b then 1 else 0) →
      ∑ r, ((∑ e ∈ univ.filter (fun e : ZMod n => e.val % 2 = 0), u e r * s e) *
              (∑ e ∈ univ.filter (fun e : ZMod n => e.val % 2 = 1), v e r * s e) ^ p +
            (∑ e ∈ univ.filter (fun e : ZMod n => e.val % 2 = 0), u e r * s e) ^ p *
              (∑ e ∈ univ.filter (fun e : ZMod n => e.val % 2 = 1), v e r * s e)) =
        ∑ e : ZMod n, s e ^ p * s (e + 1)
def StrRationality : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* K) (p : ℕ) (c ε : K), 1 ≤ p → σ c = -c → σ ε = ε ^ p →
    ε ^ (p ^ 2 - 1) = -1 → σ (c * (ε ^ (p + 1))⁻¹) = c * (ε ^ (p + 1))⁻¹
end Formalism.HermitianLattices.WeilRepresentation


