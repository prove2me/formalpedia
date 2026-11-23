-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_CurveCl
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_CurveCl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:53.392806+00:00
-- url     : https://prove2.me/theorems/cab0d9fc-f2ea-4fd9-95bd-525b4eb2481c
-- title:
--   Curve Cl
-- statement:
--   Definitions and structural lemmas for Curve Cl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/CurveCl.lean

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.DegreeFormula
noncomputable section
namespace GlobalTheory.FlagPoly
abbrev Pol (ι : Type) (N : ℕ) : Type := MvPolynomial (ι × Fin N) ℝ
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
def pSum (τ : ι) (k : ℕ) : Pol ι N := ∑ i : Fin N, X (τ, i) ^ k
def pLow (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ k
def pHigh (j : ℕ) (τ : ι) (k : ℕ) : Pol ι N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), X (τ, i) ^ k
def shF (j : ℕ) (τ : ι) (F : Pol ι N) : ℝ :=
  degFl ι N (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), pderiv (τ, i) F)
def totF (τ : ι) (F : Pol ι N) : ℝ := degFl ι N (∑ i : Fin N, pderiv (τ, i) F)
def swapAt (τ : ι) (a b : Fin N) : ι × Fin N → ι × Fin N :=
  fun x => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x
def AntiL (j : ℕ) (P : Pol ι N) : Prop :=
  ∀ (τ : ι) (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) ≠ j → rename (swapAt τ a b) P = -P
def delPol (ι : Type) [Fintype ι] (N : ℕ) : Pol ι N :=
  ∏ τ : ι, ∏ a : Fin N, ∏ b : Fin N, if a < b then X (τ, a) - X (τ, b) else 1
def invForm (j : ℕ) (al be : ι → ℝ) : Pol ι N :=
  ∑ τ : ι, (C (al τ) * pLow j τ 1 + C (be τ) * pHigh j τ 1)
def ev (lam : ι → Fin N → ℝ) (P : Pol ι N) : ℝ := eval (fun x => lam x.1 x.2) P
def CoefLe (P : Pol ι N) (c : ℝ) : Prop := ∀ m, |P.coeff m| ≤ c
def Dom (lam : ι → Fin N → ℝ) : Prop := ∀ τ (a b : Fin N), a ≤ b → lam τ b ≤ lam τ a
def RegDom (lam : ι → Fin N → ℝ) : Prop := ∀ τ (a b : Fin N), a < b → lam τ b < lam τ a
def GapZero (j : ℕ) (τ : ι) (lam : ι → Fin N → ℝ) : Prop :=
  ∀ a b : Fin N, (b : ℕ) = a + 1 → (b : ℕ) = j → lam τ a = lam τ b
def wallSet (j : ℕ) (τ₀ : ι) (c₀ : ℝ) : Set (ι → Fin N → ℝ) :=
  {lam | (∀ τ i, |lam τ i| ≤ 1 / 2) ∧ GapZero j τ₀ lam ∧
    ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → ¬ (τ = τ₀ ∧ (b : ℕ) = j) → c₀ ≤ lam τ a - lam τ b}
def lamA (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := ∑ τ : ι, (pHigh j τ 1 - pLow j τ 1)
def fibPt (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N :=
  ∏ x : ι × Fin N, (-X x) ^ (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ))
def dimGr (ι : Type) [Fintype ι] (N j : ℕ) : ℕ := Fintype.card ι * (j * (N - j))
def curveCl (ι : Type) [Fintype ι] (N j : ℕ) : Pol ι N := lamA ι N j ^ (dimGr ι N j - 1) * fibPt ι N j
end GlobalTheory.FlagPoly


