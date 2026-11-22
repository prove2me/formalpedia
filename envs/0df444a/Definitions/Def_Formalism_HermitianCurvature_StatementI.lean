-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementI
-- name    : Formalism_HermitianCurvature_StatementI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:09.359484+00:00
-- url     : https://prove2.me/theorems/43e99b17-0783-4f63-9c6c-4e7a51d668b5
-- title:
--   Statement I
-- statement:
--   Definitions and structural lemmas for Statement I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementI.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.I
open Finset Polynomial
noncomputable section
def Interlaces (k : ℕ) (u u' ρ : ℕ → ℝ) : Prop :=
  ∀ i ∈ Icc 1 (k - 1), ρ i + 1/2 ≤ u i ∧ ρ i + 1/2 ≤ u' i ∧
    u (i + 1) + 1/2 ≤ ρ i ∧ u' (i + 1) + 1/2 ≤ ρ i
def OnCut (u u' : ℕ → ℝ) (l : ℕ) (Y : ℝ) : Prop :=
  ((u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) ∨ (u' l + 2 ≤ -Y ∧ -Y ≤ u l - 2))
def xpoly (k : ℕ) (ρ : ℕ → ℝ) (Y : ℝ) : ℝ := ∏ i ∈ Icc 1 (k - 1), (Y + ρ i)
def qpoly (k : ℕ) (T T' : ℝ) (u u' : ℕ → ℝ) (Y : ℝ) : ℝ :=
  -(T * T') * ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i))
def InterlaceSign : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k → Interlaces k u u' ρ →
    OnCut u u' l Y → ∀ e ∈ ({-1, 0, 1} : Finset ℝ), 0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e)
def QPositive : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y T T' : ℝ), 1 ≤ l → l ≤ k → Interlaces k u u' ρ →
    OnCut u u' l Y → 0 < T → 0 < T' → 0 < qpoly k T T' u u' Y
def InterlaceRatio : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k → Interlaces k u u' ρ →
    OnCut u u' l Y →
    xpoly k ρ (Y + 1) ^ 2 * (|Y + 1/2 + u l| * |Y + 1/2 + u' l|) ≤
      |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))|
def orderR {F : Type} [Field F] (o : Subring F) (q : F) : Set (F × F) :=
  {a | a.1 ∈ o ∧ a.2 ∈ o ∧ ∃ t ∈ o, a.1 - a.2 = q * t}
def SelfDualG : Prop :=
  ∀ (F : Type) [Field F] (o : Subring F) (q : F), q ∈ o → q ≠ 0 → ∀ a : F × F,
    (∀ b ∈ orderR o q, (a.1 * b.1 - a.2 * b.2) / q ∈ o) ↔ a ∈ orderR o q
noncomputable def Tpoly {A : Type} [Ring A] (p c ci : A) : Matrix (Fin 2) (Fin 2) A[X] :=
  !![X + C p, -C c; C ci, 0]
noncomputable def TpolyProd {A : Type} [Ring A] (n : ℕ) (p c ci : ℕ → A) :
    Matrix (Fin 2) (Fin 2) A[X] :=
  ((List.ofFn (fun l : Fin n => Tpoly (p (l + 1)) (c (l + 1)) (ci (l + 1)))).reverse).prod
def TProdMonic : Prop :=
  ∀ (A : Type) [Ring A] [Nontrivial A] (n : ℕ) (p c ci : ℕ → A),
    (TpolyProd n p c ci 0 0).Monic ∧ (TpolyProd n p c ci 0 0).natDegree = n ∧
      (TpolyProd n p c ci 1 0).degree < n
end
end Formalism.FourierDecayAlt.I


