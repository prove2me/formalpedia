-- Prove2me | Definitions.Def_CountKSatRate_Interfaces
-- name    : CountKSatRate_Interfaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:09:21.974813+00:00
-- url     : https://prove2.me/theorems/9b3b86c7-9666-495a-8d90-56582819e72a
-- title:
--   Interfaces
-- statement:
--   Definitions and structural lemmas for Interfaces, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSatRate/Interfaces.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatStatement
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_CountKSatRate_Defs
import Definitions.Def_PaddedDescent_F_Interfaces
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace CountKSatRate
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta bsum leafC)
def StTreeK : Prop := ∀ (k τ n : ℕ), 1 ≤ k → k ^ 2 ≤ τ → ∀ ψ : PFml, (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
  (leaves (stepC (theta τ) k) (bsum τ k * n) (rootC (List.replicate n (), ψ))).length ≤ ∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j ∧
  (∀ x ∈ leaves (stepC (theta τ) k) (bsum τ k * n) (rootC (List.replicate n (), ψ)),
    stepC (theta τ) k x = none ∧ (leafF x).length ≤ (leafC τ k + 2) * n ∧
      (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (Mark.occ x.1 v).length ≤ leafC τ k) ∧
      ∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧
  cntN n ψ = ((leaves (stepC (theta τ) k) (bsum τ k * n) (rootC (List.replicate n (), ψ))).map fun x => cntN n (leafF x)).sum ∧
  ∀ i, ((round (stepC (theta τ) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1.length ≤ bsum τ k * n + 1 ∧
    ∀ x ∈ ((round (stepC (theta τ) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1,
      x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n
def StRoundS : Prop := ∀ (σ : Type) (step : σ → Option (σ × σ)) (val : σ → ℕ) (i : ℕ) (st out : List σ),
  (roundS step val)^[i] (st, (out.map val).sum) = (((round step)^[i] (st, out)).1, (((round step)^[i] (st, out)).2.map val).sum)
def StRoundSEnd : Prop := ∀ (σ : Type) (step : σ → Option (σ × σ)) (val : σ → ℕ) (d : ℕ) (s : σ),
  (∀ x ∈ leaves step d s, step x = none) → ∀ R : ℕ, 2 * (leaves step d s).length - 1 ≤ R →
  (roundS step val)^[R] ([s], 0) = ([], ((leaves step d s).map val).sum)
def StWalkS : Prop := ∀ (k : ℕ) (pad : U) (τ : ℕ) (val : CNode → ℕ) (r : CNode) (d : ℕ),
  (∀ x ∈ leaves (stepC (theta τ) k) d r, stepC (theta τ) k x = none) → 2 * (leaves (stepC (theta τ) k) d r).length ≤ pad.length + 1 →
  (∀ i, len ((roundS (stepC (theta τ) k) val)^[i] ([r], 0)) ≤ pad.length) →
  walkS k pad τ val r = ((leaves (stepC (theta τ) k) d r).map val).sum
def StStateLen : Prop := ∀ (k τ n m c : ℕ) (st : List CNode), st.length ≤ bsum τ k * n + 1 →
  (∀ x ∈ st, x.1.length ≤ m * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) →
  c < 2 ^ (n + 1) → len (st, c) ≤ stackLenC k τ n m
def StBruteC : Prop := ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → SatK.IsKCNF k φ → ∀ w : U, 2 ^ n ≤ w.length → bruteN k (SatK.enc k φ, w) = SatK.numSat φ
def StCertWalkS : Prop := ∀ (k : ℕ) (α : Type) [Enc α] (pad : α → U) (τ : α → ℕ) (val : α → CNode → ℕ) (r : α → CNode),
  PolyT pad → PolyT τ → (PolyT fun p : α × CNode => val p.1 p.2) → PolyT r → PolyT fun t => walkS k (pad t) (τ t) (val t) (r t)
def StPaddedW : Prop := ∀ (e : List Bool → ℕ) (B : List Bool × List Unit → List Bool), PolyT e → PolyT B →
  ∃ (N : Turing.TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
    ∀ x : List Bool, Nonempty (Turing.TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
      (some ((B (x, pad (e x))).map N.outputAlphabet.invFun)) (q * (x.length + 2 ^ e x + 1) ^ q))
end CountKSatRate


