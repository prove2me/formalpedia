-- Prove2me | Definitions.Def_Formalism_TwistFamilyExistence_Statement
-- name    : Formalism_TwistFamilyExistence_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:39:59.907737+00:00
-- url     : https://prove2.me/theorems/17b646ec-d156-4d11-807d-eaa381d9cbe0
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TwistFamilyExistence/Statement.lean

import Definitions.Def_Formalism_JacobiWeightFamilies_LFunctionOnePositive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.TwistFamilyExistence₂
open Formalism Formalism.CMTypeGaloisData Formalism.WT
def Lc {N : ℕ} (χ : DirichletCharacter ℂ N) : ℂ :=
  if h : N = 0 then 0 else
    haveI : NeZero N := ⟨h⟩; DirichletCharacter.LFunction χ 1
def Ldc {N : ℕ} (χ : DirichletCharacter ℂ N) : ℂ :=
  if h : N = 0 then 0 else
    haveI : NeZero N := ⟨h⟩; deriv (DirichletCharacter.LFunction χ) 1
def chiT {q : ℕ} (d : ℕ) (ψ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ((jacobiSym (n : ℤ) d : ℤ) : ℂ) * ψ (n : ZMod q)
def IsTwistFamily {q : ℕ} (S : Finset ℕ) (ψ : DirichletCharacter ℂ q)
    (χ : (d : ℕ) → DirichletCharacter ℂ (d * q)) : Prop :=
  ∀ d ∈ S, ∀ n : ℕ, χ d (n : ZMod (d * q)) = chiT d ψ n
def TwistFamilyExists : Prop :=
  ∀ (q : ℕ) (ψ : DirichletCharacter ℂ q) (S : Finset ℕ), (∀ d ∈ S, Odd d) →
    ∃ χ : (d : ℕ) → DirichletCharacter ℂ (d * q), IsTwistFamily S ψ χ
def GT (χ : ℕ → ℂ) (Lv Ld : ℂ) (y : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ n * ((y / n - 1 : ℝ) : ℂ)) + (y : ℂ) * (Ld / Lv)
def primesUpTo (y0 : ℝ) : Finset ℕ := (range (⌊y0⌋₊ + 1)).filter Nat.Prime
def Mo (χ : ℕ → ℂ) (y0 : ℝ) (K : ℕ) : ℂ :=
  ∑ S ∈ (primesUpTo y0).powerset.filter (fun S => S.card ≤ K),
    (-1 : ℂ) ^ S.card * χ (∏ p ∈ S, p) / (((∏ p ∈ S, p : ℕ) : ℝ) : ℂ)
def Wsc (D z : ℝ) (M : ℕ) : ℝ := Lcount D / (8 * M) * Vz (Pz z M)
def rho (A : ℕ) (D z : ℝ) : ℝ :=
  (Real.exp (-(Real.log D / (10 * Real.log z))) + Real.log D / z) * Real.log D ^ A
def bndG (A : ℕ) (D z : ℝ) (M : ℕ) (y : ℝ) : ℝ :=
  y * Real.log D ^ A + (Real.log (2 * M) * Real.log y) ^ 2 * Real.log D ^ A + y ^ 2 * rho A D z
def bndMo (A : ℕ) (D z : ℝ) (M : ℕ) (y0 : ℝ) : ℝ :=
  Real.log (2 * M * y0) ^ A / y0 + rho A D z
def TParams (D : ℝ) (M r a M1 : ℕ) : Prop :=
  Odd M ∧ Squarefree M ∧ r % 4 = 3 ∧ Nat.Coprime r M ∧
    (∀ p : ℕ, p.Prime → p ∣ M → jacobiSym (p : ℤ) r = 1) ∧
    M1 ∣ M ∧ ((2 ^ a * M : ℕ) : ℝ) ≤ D ^ ((1 : ℝ) / 20)
def WeightMoments : Prop :=
  ∃ (C : ℝ) (A : ℕ) (D0 : ℝ), 1 ≤ C ∧ ∀ D : ℝ, D0 ≤ D → ∀ z : ℝ, 2 ≤ z → ∀ (M r a M1 : ℕ),
    TParams D M r a M1 →
    ∀ (ψ : DirichletCharacter ℂ (2 ^ a * M1)) (χ : (d : ℕ) → DirichletCharacter ℂ (d * (2 ^ a * M1))),
      IsTwistFamily (DD D z M r) ψ χ →
      (∀ y : ℝ, 2 ≤ y → y ≤ D ^ ((1 : ℝ) / 70) →
        (∑ d ∈ DD D z M r, ‖Lc (χ d) * GT (chiT d ψ) (Lc (χ d)) (Ldc (χ d)) y‖ ^ 2)
          ≤ C * Wsc D z M * bndG A D z M y) ∧
      (∀ (y0 : ℝ) (K : ℕ), 2 ≤ y0 → y0 ^ K ≤ D ^ ((1 : ℝ) / 20) → Real.log y0 ^ 2 ≤ K →
        (∑ d ∈ DD D z M r, ‖Lc (χ d) * Mo (chiT d ψ) y0 K - 1‖ ^ 2)
            ≤ C * Wsc D z M * bndMo A D z M y0 ∧
        ∀ d ∈ DD D z M r, ‖Mo (chiT d ψ) y0 K‖ ≤ C * Real.log y0) ∧
      ∀ d ∈ DD D z M r, ‖Ldc (χ d)‖ ≤ C * Real.log D ^ 2
def PrimeShare (κ : ℝ) (PP : Finset ℕ) (D z : ℝ) (M r : ℕ) : Prop :=
  PP ⊆ DD D z M r ∧ (∀ d ∈ PP, d.Prime) ∧ κ * Wsc D z M ≤ (PP.card : ℝ)
def WeightPrimeCor : Prop :=
  ∃ (C : ℝ) (A : ℕ) (D0 : ℝ), 1 ≤ C ∧ ∀ D : ℝ, D0 ≤ D → ∀ z : ℝ, 2 ≤ z → ∀ (M r a M1 : ℕ),
    TParams D M r a M1 →
    ∀ (Ps : Finset (DirichletCharacter ℂ (2 ^ a * M1)))
      (χ : DirichletCharacter ℂ (2 ^ a * M1) → (d : ℕ) → DirichletCharacter ℂ (d * (2 ^ a * M1))),
      (∀ ψ ∈ Ps, IsTwistFamily (DD D z M r) ψ (χ ψ)) →
    ∀ (y0 : ℝ) (K : ℕ), 2 ≤ y0 → y0 ^ K ≤ D ^ ((1 : ℝ) / 20) → Real.log y0 ^ 2 ≤ K →
    ∀ (YY : Finset ℝ) (B : ℝ → ℝ), (∀ y ∈ YY, 2 ≤ y ∧ y ≤ D ^ ((1 : ℝ) / 70) ∧ 0 < B y) →
    ∀ (κ : ℝ) (PP : Finset ℕ), PrimeShare κ PP D z M r →
      (Ps.card : ℝ) * (4 * C * bndMo A D z M y0 + ∑ y ∈ YY, C * bndG A D z M y / B y ^ 2) < κ →
      ∃ d ∈ PP, ∀ ψ ∈ Ps,
        1 / (2 * C * Real.log y0) ≤ ‖Lc (χ ψ d)‖ ∧
        ‖Ldc (χ ψ d) / Lc (χ ψ d)‖ ≤ 2 * C ^ 2 * Real.log D ^ 2 * Real.log y0 ∧
        ∀ y ∈ YY, ‖GT (chiT d ψ) (Lc (χ ψ d)) (Ldc (χ ψ d)) y‖ ≤ 2 * C * Real.log y0 * B y
end Formalism.TwistFamilyExistence₂


