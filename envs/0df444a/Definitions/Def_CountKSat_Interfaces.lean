-- Prove2me | Definitions.Def_CountKSat_Interfaces
-- name    : CountKSat_Interfaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:43:20.231077+00:00
-- url     : https://prove2.me/theorems/4b54ac26-71b2-4cc2-abcf-d3b901447111
-- title:
--   Interfaces
-- statement:
--   Definitions and structural lemmas for Interfaces, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Interfaces.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatStatement
import Definitions.Def_CountKSat_Defs
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_WidthK_Decode
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_GridLoop
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_ToTuring_PolyT
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_takeWhile
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.takeWhile


set_option autoImplicit false
section
section
namespace CountKSat
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog
def decU (k : ℕ) (x : List Bool) : List Unit × Fml := (List.replicate (x.takeWhile id).length (), (DecodeK.decK k x).2)
def StDecU : Prop := ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → (∀ C ∈ φ, C.length ≤ k) →
  decU k (SatK.enc k φ) = (List.replicate n (), Decode.toN φ)
def StCertDecU : Prop := ∀ k : ℕ, PolyT (decU k)
def StCntToN : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), cntN n (Decode.toN φ) = SatK.numSat φ
def StCountValue : Prop := ∀ (g K k : ℕ) (δ b : ℝ) (NE : NetEvaluator), 0 < δ → δ ≤ 1 → 1 ≤ k → 0 < g → 0 ≤ b → 8 * b * k / δ ≤ K →
  NE.Correct g K (δ / (8 * k)) b →
  ∃ A : ℕ, ∀ φ : Fml, (∀ C ∈ φ, C.length ≤ k) →
    ∃ T : ℕ, (NE.app (satP g k)).Runs φ T (A * size φ ^ A) (Count.wordNet g k φ).value ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ * φ.length)
def StStepCount : Prop := ∀ (θ : ℕ → ℕ) (k n : ℕ) (x l h : CNode), stepC θ k x = some (l, h) →
  cntN n (leafF x) = cntN n (leafF l) + cntN n (leafF h)
def StRootCount : Prop := ∀ (n : ℕ) (ψ : Fml), cntN n (leafF (rootC (List.replicate n (), ψ))) = cntN n ψ
def StSumLeaves : Prop := ∀ (σ : Type) (step : σ → Option (σ × σ)) (G : σ → ℕ → ℕ → Prop) (q : ℕ),
  (∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q)) → ∀ f : σ → ℕ,
  (∀ s p t l h, G s p t → step s = some (l, h) → f s = f l + f h) →
  ∀ (d : ℕ) (s : σ) (p t : ℕ), G s p t → f s = ((leaves step d s).map f).sum
def SparsifiesC (k : ℕ) (ε : ℝ) (step : CNode → Option (CNode × CNode)) (Dd Bl Sk : ℕ) : Prop :=
  ∀ (n : ℕ) (ψ : Fml), (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
    ((leaves step (Dd * n) (rootC (List.replicate n (), ψ))).length : ℝ) ≤ (2 : ℝ) ^ (ε * n) ∧
    (∀ x ∈ leaves step (Dd * n) (rootC (List.replicate n (), ψ)), step x = none ∧ (leafF x).length ≤ Bl * n ∧
      (∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ i < n, ∃ C ∈ leafF x, ∃ l ∈ C, l.1 = i) ∧
    cntN n ψ = ((leaves step (Dd * n) (rootC (List.replicate n (), ψ))).map fun x => cntN n (leafF x)).sum ∧
    ∀ i, ((round step)^[i] ([rootC (List.replicate n (), ψ)], [])).1.length ≤ Dd * n + 1 ∧
      ∀ x ∈ ((round step)^[i] ([rootC (List.replicate n (), ψ)], [])).1, (leafF x).length ≤ (ψ.length + n) * Sk ∧
        ∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n
def StProgC : Prop := ∀ (τ k : ℕ) (ε : ℝ), 1 ≤ τ → ((k : ℝ) / τ) * Real.logb 2 (Real.exp 1 * τ * bsum τ k) ≤ ε →
  SparsifiesC k ε (stepC (theta τ) k) (bsum τ k) (leafC τ k + k * bsum τ k + 1) (2 ^ k + k * bsum τ k + 1)
def StCertStepC : Prop := ∀ (θ : ℕ → ℕ) (k : ℕ), PolyT (stepC θ k)
def StWalkSum : Prop := ∀ (α ν : Type) [HasSize ν] (step : ν → Option (ν × ν)) (root : α → ν) (T : Stepped ν ℕ) (d : ℕ) (a : α),
  (∀ x ∈ leaves step d (root a), step x = none) → ∀ (v : ν → ℕ) (t Sm Sx B : ℕ),
  (∀ x ∈ leaves step d (root a), T.Runs x t Sm (v x)) → (∀ i, size ((round step)^[i] ([root a], [])).1 ≤ Sx) →
  ((leaves step d (root a)).map v).sum < 2 ^ B →
  (walkSum step root T).Runs a ((leaves step d (root a)).length * (t + 2)) (Sx + (B + 1 + (Sm + 1)) + 1) ((leaves step d (root a)).map v).sum
def StHostW : Prop := ∀ (M : Stepped (List Bool) (List Bool)) [IsPolyT M],
  ∃ (N : Turing.TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
    ∀ (x : List Bool) (T S : ℕ) (w : List Bool), M.Runs x T S w →
      Nonempty (Turing.TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some (w.map N.outputAlphabet.invFun))
        (q * (T + 1) * (x.length + S + 1) ^ q))
end CountKSat


