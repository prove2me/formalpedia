-- Prove2me | Definitions.Def_Formalism_IncomingBounds_DefsThmP
-- name    : Formalism_IncomingBounds_DefsThmP
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:48.699568+00:00
-- url     : https://prove2.me/theorems/fe44bd71-1356-4926-80f8-aa6c4d5528c9
-- title:
--   Defs Thm P
-- statement:
--   Definitions and structural lemmas for Defs Thm P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/DefsThmP.lean

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_LemmaMNumerics
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
namespace Formalism.IncomingBounds
variable {C : Type} [Field C]
def lpart {n0 : ℕ} (m : PVar n0 →₀ ℕ) : PVar n0 →₀ ℕ := m.filter (fun x => x.isLeft = true)
def rpart {n0 : ℕ} (m : PVar n0 →₀ ℕ) : PVar n0 →₀ ℕ := m.filter (fun x => x.isRight = true)
def IsL {n0 : ℕ} (P : MvPolynomial (PVar n0) C) : Prop := ∀ a ∈ P.support, rpart a = 0
def IsR {n0 : ℕ} (P : MvPolynomial (PVar n0) C) : Prop := ∀ a ∈ P.support, lpart a = 0
def pp {n0 : ℕ} (Q : MvPolynomial (PVar n0) C) (G : MvPowerSeries (PVar n0) C) :
    MvPowerSeries (PVar n0) C :=
  fun m => if rpart m = 0 then
    ∑ a ∈ Q.support, if lpart a ≤ m then
      MvPolynomial.coeff a Q * (mfact (rpart a) : C) *
        MvPowerSeries.coeff (m - lpart a + rpart a) G
    else 0
  else 0
def shiftR {n0 : ℕ} (ζ : Fin n0 × Fin n0 → MvPolynomial (PVar n0) C) :
    MvPolynomial (PVar n0) C →ₐ[C] MvPolynomial (PVar n0) C :=
  MvPolynomial.aeval (Sum.elim (fun x => MvPolynomial.X (Sum.inl x))
    (fun x => MvPolynomial.X (Sum.inr x) + ζ x))
def zetaP (C : Type) [Field C] (l i n0 : ℕ) (x : Fin n0 × Fin n0) : MvPolynomial (PVar n0) C :=
  -((l : C) ^ (expE l i))⁻¹ • MvPolynomial.X (Sum.inl x) ^ (l ^ i)
def psZ (l i n0 : ℕ) : MvPolynomial (PVar n0) ℤ :=
  Matrix.det (Matrix.of fun b c : Fin n0 =>
      MvPolynomial.X (Sum.inl (b, c)) ^ (l ^ i) -
        (l : MvPolynomial (PVar n0) ℤ) ^ (expE l i) * MvPolynomial.X (Sum.inr (b, c))) -
    Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inl (b, c))) ^ (l ^ i)
def psC (C : Type) [Field C] (l i n0 : ℕ) : MvPolynomial (PVar n0) C :=
  MvPolynomial.map (Int.castRingHom C) (psZ l i n0)
def aP (C : Type) [Field C] (l i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) C) (s : ℕ) : C :=
  jetAt0 (detL C n0 ^ (l ^ i * s)) (pp (psC C l i n0 ^ s) (mvExp h1)) /
    (capNat n0 (l ^ i * s) : C)
def wP {n0 : ℕ} (l i : ℕ) (m : PVar n0 →₀ ℕ) : ℝ :=
  (degL m : ℝ) * (rho l + ((l : ℝ) ^ i)⁻¹ / 2 - ((l : ℝ) ^ i)⁻¹ / 8) +
    (degR m : ℝ) * (rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8)
def windowLength (n i : ℕ) : ℕ := ⌈200 * (n : ℝ) ^ 2 * ((i : ℝ) + 3 + Real.log n)⌉₊
def ValNat : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime →
    v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ N : ℕ, N ≠ 0 → v (N : C) = (((padicValNat l N : ℕ) : ℝ) : WithTop ℝ)
def Adjoint : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (σ : Type) (P R : MvPolynomial σ C)
    (G : MvPowerSeries σ C),
    jetAt0 P ((R : MvPowerSeries σ C) * G) = jetAt0 (diffOp R P) G
def ExpAdd : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (σ : Type) (a b : MvPowerSeries σ C),
    MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      mvExp (a + b) = mvExp a * mvExp b
def ExpWeight : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime →
    v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ (σ : Type) (w : (σ →₀ ℕ) → ℝ), (∀ m m', w (m + m') = w m + w m') →
    ∀ h : MvPowerSeries σ C, MvPowerSeries.constantCoeff h = 0 →
      (∀ m, (((1 / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ) ≤
        v (MvPowerSeries.coeff m h) + ((w m : ℝ) : WithTop ℝ)) →
      ∀ m, (0 : WithTop ℝ) ≤ v (MvPowerSeries.coeff m (mvExp h)) + ((w m : ℝ) : WithTop ℝ)
def SplitPair : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 : ℕ) (P Q : MvPolynomial (PVar n0) C)
    (G : MvPowerSeries (PVar n0) C), IsL P → IsR Q → jetAt0 (P * Q) G = jetAt0 P (pp Q G)
def PpAlg : Prop :=
  ∀ (C : Type) [Field C] (n0 : ℕ) (G : MvPowerSeries (PVar n0) C),
    (∀ R Q : MvPolynomial (PVar n0) C, IsL R →
      pp (R * Q) G = (R : MvPowerSeries (PVar n0) C) * pp Q G) ∧
    (∀ Q Q' : MvPolynomial (PVar n0) C, pp (Q + Q') G = pp Q G + pp Q' G) ∧
    (∀ (c : C) (Q : MvPolynomial (PVar n0) C), pp (c • Q) G = c • pp Q G)
def ExpShift : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 : ℕ) (ζ : Fin n0 × Fin n0 → MvPolynomial (PVar n0) C),
    (∀ x, IsL (ζ x)) → ∀ Q : MvPolynomial (PVar n0) C, IsR Q → ∀ G : MvPowerSeries (PVar n0) C,
      pp Q (mvExp (∑ x, (ζ x : MvPowerSeries (PVar n0) C) * MvPowerSeries.X (Sum.inr x)) * G) =
        pp (shiftR ζ Q) G
def DetShift : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (l i n0 : ℕ), l.Prime →
    shiftR (zetaP C l i n0) (detR C n0) =
      (-((l : C) ^ (expE l i))⁻¹) ^ n0 • (detL C n0 ^ (l ^ i) + psC C l i n0)
def PsDiv : Prop :=
  ∀ l : ℕ, l.Prime → ∀ (i n0 s : ℕ) (a : PVar n0 →₀ ℕ),
    (l : ℤ) ^ (expE l i * degR a + (s - degR a)) ∣ MvPolynomial.coeff a (psZ l i n0 ^ s) ∧
      (MvPolynomial.coeff a (psZ l i n0 ^ s) ≠ 0 → degL a + l ^ i * degR a = l ^ i * n0 * s)
def SizeA : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ),
    l.Prime → 5 ≤ l → v (l : C) = 1 → (∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) →
    ∀ i : ℕ, Odd i → ∀ (n0 : ℕ) (g : MvPowerSeries (PVar n0) C),
      (∀ m, (0 : WithTop ℝ) ≤ v (MvPowerSeries.coeff m g) + ((wP l i m : ℝ) : WithTop ℝ)) →
      ∀ s : ℕ, 1 ≤ s →
        ((((n0 : ℝ) * (l : ℝ) ^ i * s / ((l : ℝ) - 1) + (s : ℝ) / 8 -
            (n0 : ℝ) ^ 2 * (Real.logb l ((n0 : ℝ) * (l : ℝ) ^ i * s) + 1) -
            (n0 : ℝ) ^ 2 * (Real.logb l ((n0 : ℝ) * s) + 1)) : ℝ) : WithTop ℝ) ≤
          v (jetAt0 (detL C n0 ^ (l ^ i * s)) (pp (psC C l i n0 ^ s) g))
def Numerics : Prop :=
  ∀ l : ℕ, l.Prime → 5 ≤ l → ∀ i : ℕ, 1 ≤ i → ∀ n n0 : ℕ, 1 ≤ n → n0 ≤ n →
    (∀ s : ℕ, windowLength n i ≤ s →
      0 < (s : ℝ) / 8 - (n0 : ℝ) ^ 2 * (Real.logb l ((n0 : ℝ) * (l : ℝ) ^ i * s) + 1) -
        (n0 : ℝ) ^ 2 * (Real.logb l ((n0 : ℝ) * s) + 1) - (n : ℝ) * (Real.logb l n + 1)) ∧
    (windowLength n i : ℝ) < 1000 * (n : ℝ) ^ 2 * ((i : ℝ) + Real.log ((n : ℝ) + 1))
def NewtonPick : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S0 : ℕ) (a : ℕ → C),
    a 0 = 1 → (∀ s : ℕ, S0 ≤ s → 0 < v (a s)) → ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧ y < Y0 + S0 ∧
      v (∑ s ∈ Finset.range (y + 1), ((Nat.choose y s : ℕ) : C) * a s) ≤ 0
def LamIdentity : Prop :=
  CayleyId →
  ∀ (C : Type) [Field C] [CharZero C] (l i n0 : ℕ), l.Prime →
    ∀ h1 : MvPowerSeries (PVar n0) C, MvPowerSeries.constantCoeff h1 = 0 →
      aP C l i n0 h1 0 = 1 ∧
      ∀ y : ℕ, LamP C l i n0 h1 y =
        (-((l : C) ^ (expE l i))⁻¹) ^ (n0 * y) * (capNat n0 (l ^ i * y) : C) *
          ∑ s ∈ Finset.range (y + 1), ((Nat.choose y s : ℕ) : C) * aP C l i n0 h1 s
end Formalism.IncomingBounds


