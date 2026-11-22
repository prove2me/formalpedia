-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_HolDimLowK
-- name    : Formalism_FormalDegreeBessel_HolDimLowK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:38:43.020603+00:00
-- url     : https://prove2.me/theorems/4487cf8c-bf36-471a-ab4b-1778a4f79cc2
-- title:
--   Hol Dim Low K
-- statement:
--   Definitions and structural lemmas for Hol Dim Low K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/HolDimLowK.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
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
def dimLowK {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : ℝ :=
  ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b ∧ ε a = ε b),
    (((lowK ε lam + rhoC ε) a - (lowK ε lam + rhoC ε) b) / (rhoC ε a - rhoC ε b))
def cBetween {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) : ℕ :=
  (univ.filter fun c : Fin n => a < c ∧ c < b ∧ ε c = ε a).card
def FdegFactorial : Prop :=
  ∀ n : ℕ, (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) =
    ∏ i ∈ range n, (i.factorial : ℝ)
def FdegDimV : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), StrictAnti lam →
    fdegHC lam = (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b)) /
      ∏ i ∈ range n, (i.factorial : ℝ)
def FdegVV : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ), StrictAnti lam →
    fdegHC lam * (∏ i ∈ range n, (i.factorial : ℝ)) =
      ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (lam a - lam b)
def RhoCGap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a b : Fin n), a < b → ε a = ε b →
    rhoC ε a - rhoC ε b = 1 + (cBetween ε a b : ℝ)
def DimLowKPos : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → 0 < dimLowK ε lam
def DimLowKNat : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → ∃ d : ℕ, dimLowK ε lam = (d : ℝ)
def HolDimLowK : Prop :=
  ∀ (n : ℕ) (a b : ℝ), dimLowK (epsHol n) (lamHol n a b) = 1
end Formalism.QuantumDeterminants


