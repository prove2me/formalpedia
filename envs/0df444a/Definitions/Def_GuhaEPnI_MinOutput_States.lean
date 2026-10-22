-- Prove2me | Definitions.Def_GuhaEPnI_MinOutput_States
-- name    : GuhaEPnI_MinOutput_States
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:15.985983+00:00
-- url     : https://prove2.me/theorems/20842ac8-f0e4-4c9b-af21-de5f3a1727b2
-- title:
--   Eq. (10), pp. 2–3 — thermal, vacuum, pure, and zero-mean-field states
-- statement:
--   For $n$ bosonic modes, a thermal state of mean photon number $N$ in every mode is the tensor product of single-mode states with number-basis weights $N^m/(N+1)^{m+1}$. The vacuum has only its zero-photon matrix entry equal to one. A pure state is the projector onto a unit Fock vector. A zero-mean-field state has zero annihilation-operator expectation in every mode, with convergence included in the condition.
--
--   These predicates express the input classes in Minimum Output Entropy Conjectures 1 and 2, using the same state and beam-splitter model as the referenced EPnI.
--
--   **Formalization Note** The thermal formula is used only for $N\ge 0$ in the theorems. Number-basis matrix entries encode density operators; the zero-mean-field condition uses a convergent series.
-- source:
--   Guha, Erkmen & Shapiro, The Entropy Photon-Number Inequality and its Consequences, arXiv:0710.5666v2, pp. 2–3, Eq. (10), Minimum Output Entropy Conjectures 1–2

import Mathlib
import Definitions.Def_EntropyPhotonNumber

namespace GuhaEPnI.MinOutput

open OAI.EntropyPhotonNumber
open scoped ComplexConjugate

/-- Eq. (10), n-mode product of thermal photon-number weights. -/
def IsThermal {n : ℕ} (N : ℝ) (ρ : State n) : Prop :=
  ∀ k l : NumberIndex n, entry ρ.op k l =
    if k = l then ((∏ j, N ^ (k j) / (N + 1) ^ (k j + 1) : ℝ) : ℂ) else 0

/-- The n-mode vacuum as a density operator. -/
def IsVacuum {n : ℕ} (ρ : State n) : Prop :=
  ∀ k l : NumberIndex n, entry ρ.op k l = if k = 0 ∧ l = 0 then 1 else 0

/-- A rank-one density operator from a unit Fock vector. -/
def IsPure {n : ℕ} (ρ : State n) : Prop :=
  ∃ ψ : Fock n, ‖ψ‖ = 1 ∧ ∀ k l : NumberIndex n, entry ρ.op k l = ψ k * conj (ψ l)

/-- Every mode's annihilation expectation is a convergent series with sum zero. -/
def IsZeroMeanField {n : ℕ} (ρ : State n) : Prop :=
  ∀ j : Fin n, HasSum (fun k : NumberIndex n =>
    (Real.sqrt ((k j : ℝ) + 1) : ℂ) * entry ρ.op (Function.update k j (k j + 1)) k) 0

end GuhaEPnI.MinOutput


