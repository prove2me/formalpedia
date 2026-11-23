-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
-- name    : Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:54.444997+00:00
-- url     : https://prove2.me/theorems/6024ed09-9e42-497a-9442-c93852ce06b7
-- title:
--   Biadditive In Single Variables
-- statement:
--   Definitions and structural lemmas for Biadditive In Single Variables, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BiadditiveInSingleVariables.lean

import Definitions.Def_Formalism_DropLevelBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
def Ereal (l i : ℕ) : ℝ := 1 + ((l : ℝ) ^ i - l) * rho l
def r1 (l i : ℕ) : ℝ := rho l + 1 / (2 * (l : ℝ) ^ i)
def r2 (l : ℕ) : ℝ := rho l + 1 / 2
def del (l i : ℕ) : ℝ := 1 / (8 * (l : ℝ) ^ i)
def EInt : Prop := ∀ l i : ℕ, 2 ≤ l → Odd i → gam l = l * rho l ∧ (expE l i : ℝ) = Ereal l i
def I1 : Prop := ∀ l i : ℕ, 2 ≤ l →
  (l : ℝ) ^ i * r1 l i + r2 l = ((l : ℝ) ^ i + 1) * rho l + 1 ∧
    ((l : ℝ) ^ i + 1) * rho l + 1 = Ereal l i + 1 / ((l : ℝ) - 1)
def I2 : Prop := ∀ l i : ℕ, 2 ≤ l → 1 ≤ i →
  (l : ℝ) ^ i / ((l : ℝ) - 1) - Ereal l i = ((l : ℝ) ^ i + 1) * gam l - 1 ∧
    0 ≤ ((l : ℝ) ^ i + 1) * gam l - 1
def ValOther : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 →
    ∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0
def HM1 {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (l i n0 : ℕ)
    (h1 : MvPowerSeries (PVar n0) C) : Prop :=
  ∀ m : PVar n0 →₀ ℕ,
    (((1 / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ) ≤
      v (MvPowerSeries.coeff m h1) +
        (((degL m : ℝ) * (r1 l i - del l i) + (degR m : ℝ) * (r2 l - del l i) : ℝ) : WithTop ℝ)
def HM2 {C : Type} [Field C] {n0 : ℕ} (h1 : MvPowerSeries (PVar n0) C) : Prop :=
  ∀ m : PVar n0 →₀ ℕ, MvPowerSeries.coeff m h1 ≠ 0 → 1 ≤ degR m
def HSeparatedRowSum {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (l n0 : ℕ)
    (h1 : MvPowerSeries (PVar n0) C) : Prop :=
  ∃ hb : Fin n0 → MvPowerSeries (PVar n0) C, h1 = ∑ b, hb b ∧
    (∀ b (m : PVar n0 →₀ ℕ), MvPowerSeries.coeff m (hb b) ≠ 0 → ∀ x ∈ m.support, rowOf x = b) ∧
    ∀ b (m : PVar n0 →₀ ℕ), degL m < l ^ 2 → degR m < l → 0 ≤ v (MvPowerSeries.coeff m (hb b))
def WeightConditionIff : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (l i n0 : ℕ)
    (h1 : MvPowerSeries (PVar n0) C), HM1 v l i n0 h1 ↔ WeightCond v l i n0 h1
def bdP (l i n0 n y : ℕ) : ℝ :=
  (n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1)
def F1 : Prop := CayleyId
def CapacityFactorialProduct : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 x : ℕ),
    jetAt0 (detL C n0 ^ x) ((detL C n0 ^ x : MvPolynomial (PVar n0) C) : MvPowerSeries (PVar n0) C) =
        ((∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n0, (t + c) : ℕ) : C) ∧
      (∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n0, (t + c)) = capNat n0 x ∧
      (∀ c, c.factorial ∣ (x + c).factorial) ∧ capNat n0 x ≠ 0
def F2 : Prop :=
  ∀ l : ℕ, l.Prime →
    (∀ N : ℕ, (padicValNat l N.factorial : ℝ) = ((N : ℝ) - (Nat.digits l N).sum) / ((l : ℝ) - 1)) ∧
    (∀ N : ℕ, 1 ≤ N → ((Nat.digits l N).sum : ℝ) ≤ ((l : ℝ) - 1) * ((⌊Real.logb l N⌋₊ : ℝ) + 1)) ∧
    (∀ (σ : Type) [Fintype σ] (A : σ →₀ ℕ), 1 ≤ A.degree →
      (A.degree : ℝ) / ((l : ℝ) - 1) - (Fintype.card σ : ℝ) * (Real.logb l A.degree + 1) ≤
          (padicValNat l (mfact A) : ℝ) ∧
        (padicValNat l (mfact A) : ℝ) ≤ (A.degree : ℝ) / ((l : ℝ) - 1)) ∧
    (∀ N : ℕ, N < l ^ 2 → padicValNat l N.factorial = N / l)
def F3 : Prop :=
  ∀ l : ℕ, l.Prime → ∀ n0 n x : ℕ, 1 ≤ n → n0 ≤ n →
    (padicValNat l (capNat n0 x) : ℝ) ≤
        (n0 : ℝ) * x / ((l : ℝ) - 1) + n0 * (Real.logb l n0 + 1) ∧
      (n0 : ℝ) * x / ((l : ℝ) - 1) + n0 * (Real.logb l n0 + 1) ≤
        (n0 : ℝ) * x / ((l : ℝ) - 1) + n * (Real.logb l n + 1)
def detM (C : Type) [CommRing C] (n0 : ℕ) : MvPolynomial (Fin n0 × Fin n0) C :=
  Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (b, c))
def actM {C : Type} [CommRing C] {n0 : ℕ} (g1 g2 : Matrix (Fin n0) (Fin n0) C) :
    MvPolynomial (Fin n0 × Fin n0) C →ₐ[C] MvPolynomial (Fin n0 × Fin n0) C :=
  MvPolynomial.aeval fun x : Fin n0 × Fin n0 =>
    ∑ b' : Fin n0, ∑ c' : Fin n0,
      MvPolynomial.C (g1 b' x.1 * g2 c' x.2) * MvPolynomial.X (b', c')
def F4 : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 N : ℕ)
    (lam : MvPolynomial (Fin n0 × Fin n0) C →ₗ[C] C),
    (∀ Q : MvPolynomial (Fin n0 × Fin n0) C, Q.IsHomogeneous N →
      ∀ g1 g2 : Matrix (Fin n0) (Fin n0) C, g1.det = 1 → g2.det = 1 → lam (actM g1 g2 Q) = lam Q) →
    (n0 ∣ N → ∃ c : C, ∀ Q : MvPolynomial (Fin n0 × Fin n0) C, Q.IsHomogeneous N →
        lam Q = c * jetAt0 (detM C n0 ^ (N / n0)) (Q : MvPowerSeries (Fin n0 × Fin n0) C)) ∧
      (¬ n0 ∣ N → ∀ Q : MvPolynomial (Fin n0 × Fin n0) C, Q.IsHomogeneous N → lam Q = 0)
def F5 : Prop :=
  (∀ (y : ℤ) (s : ℕ), ((Ring.choose y s : ℤ) : ℚ) =
      (∏ j ∈ Finset.range s, ((y : ℚ) - j)) / (s.factorial : ℚ)) ∧
    (∀ (y : ℤ) (s : ℕ), Ring.choose (y + 1) (s + 1) - Ring.choose y (s + 1) = Ring.choose y s) ∧
    (∀ y : ℤ, Ring.choose (y + 1) 0 - Ring.choose y 0 = 0) ∧
    (∀ s : ℕ, Ring.choose (0 : ℤ) s = if s = 0 then 1 else 0)
def S0 (l i n0 : ℕ) : ℕ := ⌈64 * (n0 : ℝ) ^ 2 * ((i : ℝ) + 3 + 3 * Real.logb l ((n0 : ℝ) + 1))⌉₊
def ThmP : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → ∀ i : ℕ, Odd i → ∀ n n0 : ℕ, 1 ≤ n → n0 ≤ n →
    ∀ h1 : MvPowerSeries (PVar n0) C, HM1 v l i n0 h1 → HM2 h1 →
      (1 ≤ n0 → ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧ y < Y0 + S0 l i n0 ∧
        v (LamP C l i n0 h1 y) ≤ ((bdP l i n0 n y : ℝ) : WithTop ℝ)) ∧
      (n0 = 0 → ∀ y : ℕ, LamP C l i n0 h1 y = 1)
def CoefficientExpansionLambda : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → ∀ i : ℕ, Odd i → ∀ n0 : ℕ,
    ∀ h1 : MvPowerSeries (PVar n0) C, HM1 v l i n0 h1 → HM2 h1 →
      ∃ a : ℕ → C, a 0 = 1 ∧
        (∀ y : ℕ, LamP C l i n0 h1 y =
          (-((l : C) ^ (expE l i))⁻¹) ^ (n0 * y) * (capNat n0 (l ^ i * y) : C) *
            ∑ s ∈ Finset.range (y + 1), ((Nat.choose y s : ℕ) : C) * a s) ∧
        ∀ s : ℕ, 1 ≤ s →
          ((((s : ℝ) / 8 - (n0 : ℝ) ^ 2 *
            (3 * Real.logb l n0 + 2 * Real.logb l s + i + 3)) : ℝ) : WithTop ℝ) ≤ v (a s)
def NewtonBoundPositive : Prop :=
  ∀ l : ℕ, 5 ≤ l → ∀ i n0 s : ℕ, 1 ≤ i → 1 ≤ n0 → S0 l i n0 ≤ s →
    0 < (s : ℝ) / 8 - (n0 : ℝ) ^ 2 * (3 * Real.logb l n0 + 2 * Real.logb l s + i + 3)
def P7 : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : ℕ) (a : ℕ → C), 1 ≤ S →
    a 0 = 1 → (∀ s : ℕ, S ≤ s → 0 < v (a s)) → ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧ y < Y0 + S ∧
      v (∑ s ∈ Finset.range (y + 1), ((Nat.choose y s : ℕ) : C) * a s) ≤ 0
def minorK (C : Type) [CommRing C] (N N' k : ℕ) : MvPolynomial (Fin N × Fin N') C :=
  if h : k ≤ N ∧ k ≤ N' then
    (Matrix.of fun b c : Fin k =>
      (MvPolynomial.X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') C)).det
  else 1
def monP (C : Type) [CommRing C] (N N' : ℕ) (e : ℕ → ℕ) : MvPolynomial (Fin N × Fin N') C :=
  ∏ k ∈ Finset.Icc 1 (min N N'), minorK C N N' k ^ e k
def monAl (N N' : ℕ) (e : ℕ → ℕ) (ρ : ℕ) : ℕ := ∑ k ∈ Finset.Icc (ρ + 1) (min N N'), e k
def monDeg (N N' : ℕ) (e : ℕ → ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 (min N N'), k * e k
def TangentId {C : Type} [CommRing C] {σ : Type} (t : σ → MvPowerSeries σ C) : Prop :=
  ∀ (x : σ) (m : σ →₀ ℕ), m.degree ≤ 1 →
    MvPowerSeries.coeff m (t x) = MvPowerSeries.coeff m (MvPowerSeries.X x : MvPowerSeries σ C)
def monG {C : Type} [CommRing C] {σ : Type} (N N' : ℕ) (e : ℕ → ℕ)
    (t : Fin N × Fin N' → MvPowerSeries σ C) : MvPowerSeries σ C :=
  ∏ ρ : Fin N, if h : ρ.val < N' then t (ρ, ⟨ρ.val, h⟩) ^ monAl N N' e ρ.val else 1
def MON : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (N N' : ℕ) (e : ℕ → ℕ)
    (t : Fin N × Fin N' → MvPowerSeries (Fin N × Fin N') C), TangentId t →
    jetAt0 (monP C N N' e) (monG N N' e t) = ((∏ ρ : Fin N, (monAl N N' e ρ.val).factorial : ℕ) : C) ∧
      ∑ ρ : Fin N, monAl N N' e ρ.val = monDeg N N' e ∧
      ∀ (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 →
        v ((∏ ρ : Fin N, (monAl N N' e ρ.val).factorial : ℕ) : C) ≤
            (((monDeg N N' e : ℝ) / ((l : ℝ) - 1) : ℝ) : WithTop ℝ) ∧
          ((∀ ρ : Fin N, monAl N N' e ρ.val < l) →
            v ((∏ ρ : Fin N, (monAl N N' e ρ.val).factorial : ℕ) : C) = 0)
def MONTypes : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (B : Type) [Fintype B] [DecidableEq B] (N : ℕ) (N' : B → ℕ)
    (e : B → ℕ → ℕ)
    (t : (Σ b : B, Fin N × Fin (N' b)) → MvPowerSeries (Σ b : B, Fin N × Fin (N' b)) C),
    TangentId t →
    jetAt0 (∏ b : B, MvPolynomial.rename (fun x => (⟨b, x⟩ : Σ b : B, Fin N × Fin (N' b)))
          (monP C N (N' b) (e b)))
        (∏ b : B, monG N (N' b) (e b) fun x => t ⟨b, x⟩) =
      ((∏ b : B, ∏ ρ : Fin N, (monAl N (N' b) (e b) ρ.val).factorial : ℕ) : C)
def InRow {C : Type} [Field C] {n : ℕ} (ρ : Fin n) (G : MvPowerSeries (PVar n) C) : Prop :=
  ∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m G ≠ 0 → ∀ x ∈ m.support, rowOf x = ρ
def DiagCoord {C : Type} [Field C] {n : ℕ} (w : Fin n → PVar n) (ρ : Fin n)
    (t : MvPowerSeries (PVar n) C) : Prop :=
  (∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m t ≠ 0 → ∀ x ∈ m.support, ∃ c, x = w c) ∧
    ∀ m : PVar n →₀ ℕ, m.degree ≤ 1 →
      MvPowerSeries.coeff m t = MvPowerSeries.coeff m (MvPowerSeries.X (w ρ) : MvPowerSeries (PVar n) C)
structure BiHyp {C : Type} [Field C] (l i n0 n : ℕ) (hn : n0 ≤ n)
    (hr t t' : Fin n → MvPowerSeries (PVar n) C) (h1 : MvPowerSeries (PVar n0) C) : Prop where
  biadditive_in_single_variables : ∀ ρ, InRow ρ (hr ρ)
  constantCoeff_biadditive_zero : ∀ ρ, MvPowerSeries.constantCoeff (hr ρ) = 0
  diagonal_coordinate_left : ∀ ρ : Fin n, n0 ≤ ρ.val → DiagCoord (fun c => Sum.inl (ρ, c)) ρ (t ρ)
  diagonal_coordinate_right : ∀ ρ : Fin n, n0 ≤ ρ.val → DiagCoord (fun c => Sum.inr (ρ, c)) ρ (t' ρ)
  R3 : restr hn (∑ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => ρ.val < n0), hr ρ) =
    hP C l i n0 h1
def BiF {C : Type} [Field C] (l i n0 n y : ℕ) (hr t t' : Fin n → MvPowerSeries (PVar n) C) :
    MvPowerSeries (PVar n) C :=
  ∏ ρ : Fin n, (if ρ.val < n0 then 1 else t ρ ^ (l ^ i * y) * t' ρ ^ y) * mvExp (hr ρ)
def BiValue : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (l i n0 n : ℕ) (hn : n0 ≤ n)
    (hr t t' : Fin n → MvPowerSeries (PVar n) C) (h1 : MvPowerSeries (PVar n0) C),
    BiHyp l i n0 n hn hr t t' h1 → ∀ y : ℕ,
      jetAt0 (detL C n ^ (l ^ i * y) * detR C n ^ y) (BiF l i n0 n y hr t t') =
        ((((l ^ i * y).factorial * y.factorial) ^ (n - n0) : ℕ) : C) * LamP C l i n0 h1 y
def BiContent : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → ∀ i n n0 y : ℕ, Odd i → 1 ≤ n → n0 ≤ n → ∀ Λ : C,
      v Λ ≤ ((bdP l i n0 n y : ℝ) : WithTop ℝ) →
      v (((((l ^ i * y).factorial * y.factorial) ^ (n - n0) : ℕ) : C) * Λ) ≤
        (((bdP l i n n y + ((n : ℝ) - n0) * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ)
def BiWindow : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → ∀ i : ℕ, Odd i → ∀ (n0 n m : ℕ) (hn : n0 ≤ n), 1 ≤ n0 →
    n - n0 ≤ (i + 1) * m →
    ∀ (hr t t' : Fin n → MvPowerSeries (PVar n) C) (h1 : MvPowerSeries (PVar n0) C),
    BiHyp l i n0 n hn hr t t' h1 → HM1 v l i n0 h1 → HM2 h1 →
      ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧ y < Y0 + S0 l i n0 ∧
        v (jetAt0 (detL C n ^ (l ^ i * y) * detR C n ^ y) (BiF l i n0 n y hr t t')) ≤
          (((bdP l i n n y + ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y / ((l : ℝ) - 1)) : ℝ) :
            WithTop ℝ)
def UBCong : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → ∀ n n0 y : ℕ, 1 ≤ n → n0 ≤ n → y + n ≤ l - 1 →
    ∀ h1 : MvPowerSeries (PVar n0) C, HM1 v l 1 n0 h1 → HM2 h1 → HSeparatedRowSum v l n0 h1 →
      1 ≤ v (LamP C l 1 n0 h1 y - (capNat n0 y : C))
def UB : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → ∀ n n0 y : ℕ, 1 ≤ n → n0 ≤ n → y + n ≤ l - 1 →
    ∀ h1 : MvPowerSeries (PVar n0) C, HM1 v l 1 n0 h1 → HM2 h1 → HSeparatedRowSum v l n0 h1 →
      ¬ l ∣ capNat n0 y ∧ v (LamP C l 1 n0 h1 y) = 0 ∧
        v (((((l * y).factorial * y.factorial) ^ (n - n0) : ℕ) : C) * LamP C l 1 n0 h1 y) =
          ((((n : ℝ) - n0) * y : ℝ) : WithTop ℝ)
end Formalism.L2.FormalSeriesBounds


