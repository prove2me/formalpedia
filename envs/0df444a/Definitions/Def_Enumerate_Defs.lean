-- Prove2me | Definitions.Def_Enumerate_Defs
-- name    : Enumerate_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:25:19.797815+00:00
-- url     : https://prove2.me/theorems/86f6bad6-d16f-40c6-8514-29d7a766ed6d
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Enumerate/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Mach_Defs
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_SparsifyWidthK_DefsProg
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace Enumerate
open Finset Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK PaddedDescent SparsificationLemma SparsificationLemma.Geo SparsificationLemma.Mach Turing
def rule (τ : ℕ) : CNode → Option (CNode × CNode) := stepC (thetaU τ) 3
def start (n : ℕ) (φ : PFml) : CNode := rootC (List.replicate n (), φ)
def depth (τ n : ℕ) : ℕ := bsumU τ 3 * n
def produced (τ n : ℕ) (φ : PFml) : List PFml := (leaves (rule τ) (depth τ n) (start n φ)).map SparsificationLemma.out
structure Enumerates (ε : ℝ) (M τ : ℕ) : Prop where
  /-- the walk comes to an end: the procedure has stopped at every leaf -/
  stops : ∀ (n : ℕ) (φ : PFml), IsKCNF 3 n φ → ∀ x ∈ leaves (rule τ) (depth τ n) (start n φ), rule τ x = none
  /-- «at most 2^{εn}» -/
  few : ∀ (n : ℕ) (φ : PFml), IsKCNF 3 n φ → ((produced τ n φ).length : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ))
  /-- «3-CNFs on the same variables, each with at most M(ε)·n clauses»; no clause is written twice -/
  sparse : ∀ (n : ℕ) (φ : PFml), IsKCNF 3 n φ → ∀ Φ ∈ produced τ n φ, IsKCNF 3 n Φ ∧ Φ.Nodup ∧ Φ.length ≤ M * n
  /-- φ is satisfiable if and only if at least one of them is (weaker than the paper's «an
  assignment satisfies φ if and only if it satisfies at least one of them») -/
  sat : ∀ (n : ℕ) (φ : PFml), IsKCNF 3 n φ → ((∃ b, SparsificationLemma.Sat b φ) ↔ ∃ Φ ∈ produced τ n φ, ∃ b, SparsificationLemma.Sat b Φ)
  /-- «in time 2^{εn} times a polynomial in n», first half: the walk makes two moves for each
  formula that it produces (one less in all); this holds for every tree, and is a bound on the time
  only together with `few` -/
  moves : ∀ (n : ℕ) (φ : PFml), (visits (rule τ) (depth τ n) (start n φ) []).length + 1 = 2 * (produced τ n φ).length
  /-- second half: a move, and the passage from a leaf to its output, take polynomial time … -/
  rule_poly : PolyT (rule τ)
  out_poly : PolyT SparsificationLemma.out
  /-- … in the size of the stack, which is polynomial: at most τ⁶·n + 1 nodes, each with at most
  8·|φ| + 2n clauses of at most 3 literals on the same variables -/
  stack : ∀ (n : ℕ) (φ : PFml), IsKCNF 3 n φ → ∀ i, ((Sparsify.round (rule τ))^[i] ([start n φ], [])).1.length ≤ depth τ n + 1 ∧
    ∀ x ∈ ((Sparsify.round (rule τ))^[i] ([start n φ], [])).1,
      x.1.length ≤ φ.length * 2 ^ 3 ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ 3 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n
def StProducedIsList : Prop := ∀ (τ n : ℕ) (φ : PFml), produced τ n φ = outTau 3 n τ φ
def StSameTree : Prop := ∀ (τ n : ℕ) (φ : PFml), leaves (stepK (thetaU τ) 3) (depth τ n) (rootP φ) = (leaves (rule τ) (depth τ n) (start n φ)).map Prod.fst
def StEnumeratesTau : Prop := ∀ (τ : ℕ) (ε : ℝ), 24 ≤ τ → ((3 : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsumU τ 3 : ℝ)) ≤ ε → Enumerates ε (τ ^ 6) τ
def StEnumeration : Prop := ∀ ε : ℝ, 0 < ε → ∃ M τ : ℕ, 1 ≤ M ∧ Enumerates ε M τ
def StNamed : Prop := ∃ Mm : TM2ComputableAux Bool Bool, (∀ i, Finite (Mm.tm.Γ i)) ∧
  ∀ ε : ℝ, 0 < ε → ∃ Mε s c : ℕ, 1 ≤ Mε ∧ Enumerates ε Mε (tauOf s) ∧
    ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → [] ∉ φ →
      ∃ T : ℕ, Nonempty (TM2OutputsInTime Mm.tm ((encIn s 3 φ).map Mm.inputAlphabet.invFun) (some ((code (produced (tauOf s) n (Decode.toN φ))).map Mm.outputAlphabet.invFun)) T) ∧
        (T : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) * ((c : ℝ) * ((n : ℝ) + 1) ^ c)
def StNamedOf : Prop := Prints → StProducedIsList → StEnumeratesTau → StNamed
def StNamedGives : Prop := StNamed → LemSparsification ∧ StEnumeration
end Enumerate


