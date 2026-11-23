-- Prove2me | Definitions.Def_Formalism_PairingDivisors_StatementN
-- name    : Formalism_PairingDivisors_StatementN
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:17:33.81869+00:00
-- url     : https://prove2.me/theorems/028b3969-d3fb-4fc7-a1d0-b48163c46099
-- title:
--   Statement N
-- statement:
--   Definitions and structural lemmas for Statement N, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PairingDivisors/StatementN.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.PairingDivisionLocalBalance
def PairingDiv : Prop :=
  ∀ (O H : Type) [CommRing O] [AddCommGroup H] [Module O H] (B : H →ₗ[O] H →ₗ[O] O) (e f : H) (D : O),
    (∃ h, B e h = 1) →
    (∀ h : H, ∃ (u : O) (r : H), D • h = u • f + r ∧ B e r = 0) →
    B e f ∣ D
def DetDiv : Prop :=
  ∀ (O : Type) [CommRing O] (f : ℕ) (A B : Matrix (Fin f) (Fin f) O) (D : O),
    B * A = D • (1 : Matrix (Fin f) (Fin f) O) → A.det ∣ D ^ f
def DivPow : Prop :=
  (∀ l m : ℕ, l.Prime → l ≠ 2 → 1 ≤ m →
    padicValNat l m.factorial + 1 ≤ m ∧ 2 * padicValNat l m.factorial ≤ m) ∧
  (∀ m : ℕ, 1 ≤ m → padicValNat 2 m.factorial + 1 ≤ m) ∧
  (∀ j : ℕ, padicValNat 2 (2 ^ j).factorial + 1 = 2 ^ j)
def nl (kf κs c t : ℝ) : ℝ := kf * c + κs * (2 * c + 1 + t)
def NlEstimate : Prop :=
  ∀ (Φ : Type) [Fintype Φ] (k : ℕ) (κ : Φ → ℕ) (c cE t2 td vu0 vg : ℝ) (vp : Φ → ℝ),
    vu0 ≤ Fintype.card Φ * c →
    -cE - (∑ τ, (κ τ : ℝ)) * (c + 1 + t2) ≤ vg →
    (∀ τ, vp τ ≤ c + td) →
    -cE - nl ((k : ℝ) * Fintype.card Φ) (∑ τ, (κ τ : ℝ)) c (t2 + td) ≤
      -(k : ℝ) * vu0 + vg - ∑ τ, (κ τ : ℝ) * vp τ
def NlBounds : Prop :=
  ∀ (kf κs : ℝ), 0 ≤ kf → 0 ≤ κs →
    (∀ δ : ℝ, 0 ≤ δ → nl kf κs δ 1 ≤ (κs + kf) * (2 + 2 * δ)) ∧
    nl kf κs (1 / 2) 0 = kf / 2 + 2 * κs ∧ nl kf κs (1 / 2) 0 ≤ 2 * (κs + kf) ∧
    nl kf κs (1 / 2) (1 / 2) = kf / 2 + 5 / 2 * κs ∧ nl kf κs (1 / 2) (1 / 2) ≤ 5 / 2 * (κs + kf) ∧
    (∀ a0 : ℝ, 1 ≤ a0 → nl kf κs a0 0 ≤ 3 * a0 * (κs + kf))
def NlSum : Prop :=
  ∀ (kf κs δ2 f q1 d : ℝ) (R : Finset ℕ) (a0 : ℕ → ℝ), 0 ≤ kf → 0 ≤ κs → 1 ≤ f → 1 ≤ q1 → 1 ≤ d →
    0 ≤ δ2 → δ2 ≤ Real.logb 2 f → (∀ l ∈ R, 1 ≤ l ∧ 1 ≤ a0 l ∧ a0 l ≤ 2) →
    nl kf κs δ2 1 * Real.log 2 + nl kf κs (1 / 2) 0 * Real.log q1
        + nl kf κs (1 / 2) (1 / 2) * Real.log d + ∑ l ∈ R, nl kf κs (a0 l) 0 * Real.log l ≤
      (κs + kf) * (2 * Real.log (2 * f) + 2 * Real.log q1 + 5 / 2 * Real.log d
        + 6 * ∑ l ∈ R, Real.log l)
def mE (l n : ℕ) : ℕ :=
  if l = 2 then 2 + padicValNat 2 n else if (l - 1) ∣ n then 1 + padicValNat l n else 0
def MinVal : Prop :=
  ∀ l n : ℕ, l.Prime → 2 ≤ n → Even n →
    ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ padicValNat l (a ^ n - 1) = mE l n
def CESum : Prop :=
  ∀ (f X : ℕ) (S : Finset ℕ), 16 ≤ X → 2 * f ≤ X → (∀ l ∈ S, l.Prime) →
    ∑ l ∈ S, ((f * padicValNat l 2 + mE l X : ℕ) : ℝ) * Real.log l ≤ X * Real.log (X + 1)
def TotalSizeBound : Prop :=
  ∀ (SE Sn kf κs f q1 d sR x L b Cκ Cx Cg : ℝ),
    1 ≤ x → 1 ≤ L → 1 ≤ b → 1 ≤ f → 0 ≤ Cκ → 0 ≤ Cx → 0 ≤ Cg → 0 ≤ kf → 0 ≤ κs →

    SE ≤ f * b →
    Sn ≤ (κs + kf) * (2 * Real.log (2 * f) + 2 * Real.log q1 + 5 / 2 * Real.log d + 6 * sR) →

    kf ≤ f * b → κs ≤ Cκ * f * b → Real.log (2 * f) ≤ Cx * (L + Real.log x) →
    Real.log q1 ≤ L → Real.log d ≤ L → sR ≤ Cg * L → 0 ≤ Real.log q1 → 0 ≤ Real.log d → 0 ≤ sR →
    SE + Sn ≤ (1 + (Cκ + 1) * (2 * Cx + 9 / 2 + 6 * Cg)) * f * b * (L + Real.log x)
end Formalism.PairingDivisionLocalBalance


