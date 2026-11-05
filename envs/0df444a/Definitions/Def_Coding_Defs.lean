-- Prove2me | Definitions.Def_Coding_Defs
-- name    : Coding_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:56:22.241717+00:00
-- url     : https://prove2.me/theorems/45b996bf-9493-436f-a4bd-97f0813f45b7
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsiDefs
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_ThmEveryDeltaStatement
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
namespace Coding
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping
structure PaddingOf {g : ℕ} (N₀ N : Net g) (pad : Fin g → List Bool → List Bool) : Prop where
  /-- a setting of N₀ is written by a setting of N, and different settings by different ones -/
  maps : ∀ a, ∀ z ∈ N₀.S a, pad a z ∈ N.S a
  inj : ∀ a, ∀ z ∈ N₀.S a, ∀ z' ∈ N₀.S a, pad a z = pad a z' → z = z'
  /-- a setting of N that writes no setting of N₀ has W = 0 -/
  off : ∀ a, ∀ y ∈ N.S a, (∀ z ∈ N₀.S a, pad a z ≠ y) → N.W a y = 0
  W : ∀ a, ∀ z ∈ N₀.S a, N.W a (pad a z) = N₀.W a z
  Ψ : ∀ a b, a ≠ b → ∀ z ∈ N₀.S a, ∀ z' ∈ N₀.S b, N.Ψ a b (pad a z) (pad b z') = N₀.Ψ a b z z'
  c : ∀ a b, a ≠ b → N.c a b = N₀.c a b
  f : ∀ a b, a ≠ b → ∀ z ∈ N₀.S a, ∀ θ ∈ words (N₀.c a b), N.f a b (pad a z) θ = N₀.f a b z θ
def StPaddingValue : Prop := ∀ (g : ℕ) (N₀ N : Net g) (pad : Fin g → List Bool → List Bool), PaddingOf N₀ N pad → N.value = N₀.value ∧ N.U = N₀.U
section Occurrences
variable (g : ℕ) (Φ : Fml)
def occIn (e₀ r : ℕ) : List (ℕ × ℕ) := (List.range' e₀ r).flatMap fun e => (List.range (Φ.getD e []).length).map fun j => (e, j)
def occOf (a : ℕ) : List (ℕ × ℕ) := occIn Φ (a * mu g Φ) (mu g Φ)
def occAll : List (ℕ × ℕ) := occIn Φ 0 Φ.length
def litOf (o : ℕ × ℕ) : ℕ × Bool := (Φ.getD o.1 []).getD o.2 (0, false)
def clusterOf (o : ℕ × ℕ) : ℕ := o.1 / mu g Φ
def tests : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (occAll Φ ×ˢ occAll Φ).filter fun p =>
    decide ((occAll Φ).idxOf p.1 < (occAll Φ).idxOf p.2) && decide ((litOf Φ p.1).1 = (litOf Φ p.2).1) &&
      (occAll Φ).all fun o => !(decide ((occAll Φ).idxOf p.1 < (occAll Φ).idxOf o) && decide ((occAll Φ).idxOf o < (occAll Φ).idxOf p.2) && decide ((litOf Φ o).1 = (litOf Φ p.1).1))
def testsBetween (a b : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (tests Φ).filter fun p => (clusterOf g Φ p.1 == a && clusterOf g Φ p.2 == b) || (clusterOf g Φ p.1 == b && clusterOf g Φ p.2 == a)
def bitAt (a : ℕ) (z : List Bool) (o : ℕ × ℕ) : Bool := z.getD ((occOf g Φ a).idxOf o) false
def isTrue (a : ℕ) (z : List Bool) (o : ℕ × ℕ) : Bool := bitAt g Φ a z o == (litOf Φ o).2
def restrict (a b : ℕ) (z : List Bool) : List Bool := (testsBetween g Φ a b).map fun p => bitAt g Φ a z (if clusterOf g Φ p.1 = a then p.1 else p.2)
def occNet : Net g where
  len a := (occOf g Φ a.val).length
  S a := words (occOf g Φ a.val).length
  W a z := if ((List.range' (a.val * mu g Φ) (mu g Φ)).all fun e => !(decide (e < Φ.length)) || (List.range (Φ.getD e []).length).any fun j => isTrue g Φ a.val z (e, j)) &&
      ((testsBetween g Φ a.val a.val).all fun p => bitAt g Φ a.val z p.1 == bitAt g Φ a.val z p.2) then 1 else 0
  Ψ a b z z' := if restrict g Φ a.val b.val z = restrict g Φ b.val a.val z' then 1 else 0
  c a b := (testsBetween g Φ a.val b.val).length
  f a b z θ := if restrict g Φ a.val b.val z = θ then 1 else 0
def padOcc (a : Fin g) (z : List Bool) : List Bool :=
  (List.range (mu g Φ * 3)).map fun i => decide (i % 3 < (Φ.getD (a.val * mu g Φ + i / 3) []).length) && bitAt g Φ a.val z (a.val * mu g Φ + i / 3, i % 3)
end Occurrences
def StOccNet : Prop := ∀ (g : ℕ) (Φ : Fml), 0 < g → (∀ C ∈ Φ, C.length ≤ 3) → PaddingOf (occNet g Φ) (satNet g 3 Φ) (padOcc g Φ)
def StOccNetIs : Prop := ∀ (g : ℕ) (Φ : Fml), 0 < g → Φ ≠ [] → (∀ C ∈ Φ, C.length ≤ 3) → (occNet g Φ).Is (6 * mu g Φ) 1
def StOccNetSmall : Prop := ∀ (g : ℕ) (Φ : Fml), (∀ C ∈ Φ, C.length ≤ 3) →
  (∀ a : Fin g, (occNet g Φ).len a ≤ 3 * mu g Φ) ∧ (∀ (a : Fin g) z, (occNet g Φ).W a z = 0 ∨ (occNet g Φ).W a z = 1) ∧
  (∀ (a b : Fin g) z z', (occNet g Φ).Ψ a b z z' = 0 ∨ (occNet g Φ).Ψ a b z z' = 1) ∧ ∀ (a b : Fin g) z θ, (occNet g Φ).f a b z θ = 0 ∨ (occNet g Φ).f a b z θ = 1
def StOccNetCounts : Prop := ∀ (g : ℕ) (Φ : Fml), 0 < g → (∀ C ∈ Φ, C.length ≤ 3) → (occNet g Φ).value = (Eight.numSat Φ : ℤ) ∧ (0 < (occNet g Φ).value ↔ Φ.Sat)
def StOccNetCountsOf : Prop := StOccNet → StPaddingValue → StOccNetCounts
def StTests : Prop := ∀ Φ : Fml, Φ ≠ [] → (∀ C ∈ Φ, C ≠ [] ∧ C.length ≤ 3) →
  (∀ o ∈ occAll Φ, ((tests Φ).filter fun p => p.1 == o || p.2 == o).length ≤ 2) ∧
  (tests Φ).length + ((occAll Φ).map fun o => (litOf Φ o).1).toFinset.card = (occAll Φ).length ∧ (tests Φ).length ≤ 3 * Φ.length - 1
def sixExample : Fml := [[(0, true), (1, true), (2, true)], [(0, false), (1, true), (2, true)], [(0, true), (1, false), (2, true)]]
def StRowSumReached : Prop := mu 3 sixExample = 1 ∧ ∑ b ∈ univ.erase (1 : Fin 3), (occNet 3 sixExample).c 1 b = 6 * mu 3 sixExample ∧
  ∑ b ∈ univ.erase (1 : Fin 3), (satNet 3 3 sixExample).c 1 b = 6 * mu 3 sixExample
structure ThreeCNF (n : ℕ) where
  clauses : Finset (Finset (Sat3.Lit n))
  nonempty : ∀ E ∈ clauses, E.Nonempty
  width : ∀ E ∈ clauses, E.card ≤ 3
def ThreeCNF.Satisfiable {n : ℕ} (Φ : ThreeCNF n) : Prop := ∃ a : Fin n → Bool, ∀ E ∈ Φ.clauses, ∃ l ∈ E, a l.1 = l.2
def Writes {n : ℕ} (φ : Sat3.CNF n) (Φ : ThreeCNF n) : Prop := (∀ C ∈ φ, C.Nodup) ∧ (φ.map List.toFinset).Nodup ∧ (φ.map List.toFinset).toFinset = Φ.clauses
def StWrites : Prop := ∀ (n : ℕ) (Φ : ThreeCNF n), (∃ φ, Writes φ Φ) ∧
  ∀ φ, Writes φ Φ → Sat3.Is3CNF φ ∧ φ.length = Φ.clauses.card ∧ [] ∉ φ ∧ (Sat3.Satisfiable φ ↔ Φ.Satisfiable)
def StSetForm : Prop := ∀ δ : ℝ, 0 < δ → ∃ (M : Turing.TM2ComputableAux Bool Bool) (c : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
  ∀ (n : ℕ) (Φ : ThreeCNF n) (φ : Sat3.CNF n), Writes φ Φ → ∃ (b : Bool) (t : ℕ), (b = true ↔ Φ.Satisfiable) ∧ (t : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) ∧ Sat3.HaltsWith M φ b t
def StSetFormOf : Prop := StWrites → Sat3.ThmEveryDelta → StSetForm
def StCubic : Prop := ∀ (n : ℕ) (Φ : ThreeCNF n), Φ.clauses.card ≤ 14 * n ^ 3
end Coding


