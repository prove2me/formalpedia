-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
-- name    : Formalism_FormalDegreeBessel_StatementDS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:38.385528+00:00
-- url     : https://prove2.me/theorems/62f447c5-47d3-4e29-9137-0a264e039020
-- title:
--   Statement DS
-- statement:
--   Definitions and structural lemmas for Statement DS, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/StatementDS.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
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
namespace Formalism.QuantumDeterminants
open Formalism.REAL
def IsHCParam {n : ℕ} (lam : Fin n → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)
def lowK {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : Fin n → ℝ := lam + rhoN ε - rhoC ε
def GapAtLeast {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) : Prop :=
  ∀ a b : Fin n, ε a ≠ ε b → h ≤ |lam a - lam b|
def fdegHC {n : ℕ} (lam : Fin n → ℝ) : ℝ :=
  (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |lam a - lam b|) /
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))
def rhoStd (n : ℕ) : Fin n → ℝ := fun a => ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)
def capP {n : ℕ} (lam : Fin n → ℂ) (Y : ℂ) : ℂ := ∏ s : Fin n, (Y + lam s)
def epsHol (n : ℕ) : Fin (n + 1) → Bool := fun i => decide (i ≠ 0)
def lamHol (n : ℕ) (a b : ℝ) : Fin (n + 1) → ℝ := fun i =>
  if i = 0 then b - (n : ℝ) / 2 else a + (n : ℝ) / 2 + 1 - ((i : ℕ) : ℝ)
def ncBetween {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ℕ :=
  (univ.filter fun c : Fin n => a < c ∧ c < b ∧ ε c ≠ ε a).card
def LowKInt : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    (∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) →
    ∀ a, ∃ m : ℤ, lowK ε lam a = (m : ℝ)
def LowKDiff : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (a b : Fin n), a < b → ε a = ε b →
    lowK ε lam a - lowK ε lam b =
      (lam a - lam b) - (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) + 2 * (ncBetween ε a b : ℝ)
def LowKDom : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam →
    ∀ a b : Fin n, a < b → ε a = ε b → 2 * (ncBetween ε a b : ℝ) ≤ lowK ε lam a - lowK ε lam b
def FdegPos : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), Function.Injective lam → 0 < fdegHC lam
def FdegPerm : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), fdegHC (lam ∘ σ) = fdegHC lam
def FdegVand : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), StrictAnti lam →
    ((fdegHC lam : ℝ) : ℂ) = vand (fun a => (lam a : ℂ)) / vand (fun a => (rhoStd n a : ℂ))
def FdegWeyl : Prop :=
  ∀ (n : ℕ) (m : Fin n → ℤ), Antitone m →
    fdegHC (fun a => (m a : ℝ) + rhoStd n a) =
      ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
        (((m a : ℝ) - (m b : ℝ) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) / (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)))
def FdegRatio : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℝ) (s : Fin n), Function.Injective μ →
    (∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) → Function.Injective (μ + Pi.single s 1) →
    fdegHC (μ + Pi.single s 1) / fdegHC μ = ∏ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s')
def FormalDegreeTwoByTwo : Prop :=
  ∀ k : ℝ, 1 ≤ k → fdegHC ![(k - 1) / 2, -((k - 1) / 2)] = k - 1
def HolLowK : Prop :=
  ∀ (n : ℕ) (a b : ℝ), lowK (epsHol n) (lamHol n a b) = fun i => if i = 0 then b else a
def HolHC : Prop :=
  ∀ (n : ℕ) (a b : ℤ), (n : ℤ) < b - a → IsHCParam (lamHol n (a : ℝ) (b : ℝ))
def HolFdeg : Prop :=
  ∀ (n : ℕ) (a b : ℝ), (n : ℝ) ≤ b - a →
    fdegHC (lamHol n a b) = (∏ j ∈ Icc 1 n, (b - a - (j : ℝ))) / (n.factorial : ℝ)
def CapelliHW : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
    ∀ Y : ℂ, qdet E (Y + ((n : ℂ) - 1) / 2) v = capP (fun s => ν s + (rhoStd n s : ℂ)) Y • v
def CapPPerm : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (Y : ℂ), capP (lam ∘ σ) Y = capP lam Y
end Formalism.QuantumDeterminants


