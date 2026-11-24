-- Prove2me | Definitions.Def_ValiantBorder_thinTrees
-- name    : ValiantBorder_thinTrees
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:12:47.331069+00:00
-- url     : https://prove2.me/theorems/22039ed4-025b-4be3-b50f-4d0835040265
-- title:
--   Thin exchange trees and their size bounds
-- statement:
--   A thin exchange tree evaluates a product of equality constraints by local exchanges. Its conditions bound the number of nodes, the sizes of the intermediate boundaries, and the cost of describing the tree.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Tree.lean).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Tree.lean.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_tapePieces
/-! Based on Claude (Anthropic), *VP ≠ VNP over every field*, Theorems onecut and cut,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp .
This arrangement refactors the single-cut hypothesis from its quantitative amplification.
The upstream Lean source is copyright 2026 Anthropic, PBC and released under Apache 2.0,
https://www.apache.org/licenses/LICENSE-2.0. -/
namespace Unc
open Nc.Cut
variable {Inp ι : Type} {D : ℕ}
def SlpN (inp : ι → Inp → Fin D) (p : ℕ) (H : Set (Inp → ℕ)) : Prop :=
  ∃ fn : ℕ → Inp → Fin D, (∀ k < p, IsSlpStep inp fn k) ∧ ∀ h ∈ H, ∃ k < p, ∀ x, (fn k x : ℕ) = h x

/-- The indicator of a property. -/
noncomputable def ind (P : Inp → Prop) : Inp → ℕ := by
  classical exact fun x => if P x then 1 else 0


end Unc
namespace Paper
open Finset
theorem laws_over_algebras {A : Type} [CommRing A] (L : Nc.G.Law A) (R : Type) [CommRing R] [Algebra A R]
    (X : L.Ro → L.Sl → Bool) : (if ∀ e, X (L.a e) e = X (L.b e) e then (1 : R) else 0) =
      ∑ i, ∑ y : ∀ ν, Fin (L.len i ν) → Bool,
        ∏ p, algebraMap A R (L.tab p i (fun e => X p e) (fun ν => y ν)) := by
  simpa only [apply_ite (algebraMap A R), map_one, map_zero, map_sum, map_prod] using
    congrArg (algebraMap A R) (L.law X)


end Paper
namespace Paper
open Finset Nc Nc.G
/-- The units of a network with n a c units from a to c. -/
abbrev NetUnit {AA : ℕ} (n : Fin AA → Fin AA → ℕ) := Σ a c : Fin AA, Fin (n a c)

/-- A table of the node a, with values in R, of the contents of the units at a. -/
abbrev NodeTable (R : Type) {AA : ℕ} (n : Fin AA → Fin AA → ℕ) (ℓ : ℕ) (a : Fin AA) :=
  ({u : NetUnit n // u.1 = a ∨ u.2.1 = a} → Fin ℓ → Bool) → R

/-- The value of a network: the sum over all contents of the units of the product of the tables. -/
def netValue {R : Type} [CommRing R] {AA ℓ : ℕ} {n : Fin AA → Fin AA → ℕ} (tab : ∀ a, NodeTable R n ℓ a) : R :=
  ∑ w : NetUnit n → Fin ℓ → Bool, ∏ a, tab a fun u => w u.1

/-- A law over A is a law over every A-algebra. -/
noncomputable def lawMap {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (L : G.Law A) : G.Law R where
  Ro := L.Ro
  Sl := L.Sl
  Cn := L.Cn
  I := L.I
  a := L.a
  b := L.b
  ab := L.ab
  c := L.c
  d := L.d
  cd := L.cd
  lam := L.lam
  lab := L.lab
  lab_inj := L.lab_inj
  len := L.len
  tab p i s y := f (L.tab p i s y)
  law X := @laws_over_algebras A _ L R _ f.toAlgebra X
  conn := L.conn


end Paper
namespace Paper
open Finset Nc Nc.G
variable {R : Type} [CommRing R] {AA A' E N ℓ : ℕ}
/-- The tables with which the moves start: every node of the network has its table, applied to the units at it, and
every other node the table 1. -/
noncomputable def startTab (S : Sys R (AA + A') E) (U1 : ℕ) (n : Fin AA → Fin AA → Fin (N + 1))
    (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) : Fin (AA + A') → (Uid AA N S.N U1 → UW ℓ) → R :=
  Fin.addCases (motive := fun _ => (Uid AA N S.N U1 → UW ℓ) → R)
    (fun a y => if ∀ u : {u : NetUnit (fun a c => (n a c).1) // u.1 = a ∨ u.2.1 = a},
        y (.init u.1.1 u.1.2.1 (Fin.castLE (Nat.le_of_lt_succ (n u.1.1 u.1.2.1).2) u.1.2.2)) ≠ none then
        tab a fun u => (y (.init u.1.1 u.1.2.1 (Fin.castLE (Nat.le_of_lt_succ (n u.1.1 u.1.2.1).2) u.1.2.2))).getD
          fun _ => false
      else 0)
    (fun _ _ => 1)


end Paper
namespace Paper
open Finset Nc Nc.G Nc.Tow Unc
open NS1 (lg)
open Classical in
/-- The networks on trees of Theorem thm:tree, for networks on AA nodes with units of ℓ bits, at most N units at a
node and at most M nodes, over R, with the exponent C, the gain γ and the integer G₁ of the test for good outcomes.
The nodes are the parties 0, ..., AA + A' − 1. For numbers n of units and outcomes o the units of the tree are those
that are current at the end, plan.cur. A unit from a node to itself is allowed; it stays at its node, whose value sums
over it. -/
structure ThinTrees (R : Type) [CommRing R] (laws : List (G.Law R)) (AA N ℓ M b G₁ C : ℕ) (γ : ℝ) where
  /-- the number of further nodes -/
  A' : ℕ
  /-- the number of moves -/
  E : ℕ
  /-- a bound for outcomes -/
  U1 : ℕ
  U1_pos : 0 < U1
  /-- the moves -/
  sys : Sys R (AA + A') E
  /-- the units given in the moves, their numbers, and the good outcomes -/
  plan : Plan sys N U1
  /-- a bound for the units of one move -/
  cap : ℕ
  /-- the plan is causal and gives only current units between the ends of their slots -/
  ok : plan.Ok cap
  /-- the stage of a node -/
  stage : Fin (AA + A') → ℕ
  /-- the depth of the tree -/
  depth : ℕ
  /-- the root -/
  root : Fin (AA + A')
  /-- the parent of a node -/
  par : (Fin AA → Fin AA → Fin (N + 1)) → (sys.N → Fin U1) → Fin (AA + A') → Fin (AA + A')
  /-- the number of units between a node and its parent, as the program bounds it: the load at the node -/
  up : (Fin AA → Fin AA → Fin (N + 1)) → (sys.N → Fin U1) → Fin (AA + A') → ℕ
  /-- the dead units -/
  dead : (sys.N → Fin U1) → Finset (Uid AA N sys.N U1)
  /-- is the move a law move? -/
  isLaw : Fin E → Bool
  depth_le : depth ≤ lg M ^ C
  stage_le : ∀ p, stage p ≤ depth
  stage_given : ∀ a, stage (Fin.castAdd A' a) = 0
  stage_root : ∀ p, stage p = depth ↔ p = root
  stage_par : ∀ n o p, p ≠ root → stage (par n o p) = stage p + 1
  children_le : ∀ n o q, q ≠ root → (univ.filter fun p => p ≠ root ∧ par n o p = q).card ≤ b
  root_children_le : ∀ n o, (univ.filter fun p => p ≠ root ∧ par n o p = root).card ≤ C
  dead_le : ∀ o, (dead o).card ≤ M ^ C
  kinds : ∀ x, if isLaw x then sys.kind x ∈ laws else sys.kind x = relay R
  law_stage : ∀ r : sys.R, isLaw r.1 = true → 0 < stage (sys.rp r)
  /-- what good means -/
  good_iff : ∀ n o x, plan.good n o x ↔ if isLaw x then
      b * ∑ ν : (sys.kind x).Cn, (o ⟨x, ν⟩).val ^ 2 ≤ G₁ * plan.num n o x ^ 2 ∧
        ∀ ν : (sys.kind x).Cn, plan.num n o x ≤ o ⟨x, ν⟩
    else ∀ ν : (sys.kind x).Cn, (o ⟨x, ν⟩).val = plan.num n o x
  /-- every possible outcome is good -/
  poss_good : ∀ n o x, plan.Poss n o ℓ x → plan.good n o x
  edge : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∀ u ∈ cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E \ dead o),
      ∃ p, p ≠ root ∧ s(hold0 sys.np u, hold1 sys.np u) = s(p, par n o p)
  node_le : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∀ p, (((cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E \ dead o)).filter
        (Holds (hold0 sys.np) (hold1 sys.np) p)).card : ℝ) ≤
      (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2)
  total_le : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    (cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E \ dead o)).card ≤ lg M ^ C * M * (N + M ^ 2)
  between_le : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) → ∀ p, p ≠ root →
    ((cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E \ dead o)).filter
      (fun u => s(hold0 sys.np u, hold1 sys.np u) = s(p, par n o p))).card ≤ up n o p
  up_node : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∀ p, ((up n o p + ∑ q ∈ univ.filter (fun q => q ≠ root ∧ par n o q = p), up n o q : ℕ) : ℝ) ≤
      (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2)
  up_total : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∑ p, up n o p ≤ lg M ^ C * M * (N + M ^ 2)
  layers_le : ∀ n o, (∀ x, plan.good n o x) → ∀ p,
    ∑ r ∈ univ.filter (fun r : sys.R => sys.rp r = p ∧ isLaw r.1 = true), plan.num n o r.1 ≤
      ((Plan.seenAt n o E).filter (Holds (hold0 sys.np) (hold1 sys.np) p)).card
  /-- copies: what a node ever holds, with the zeros in slots and the counts of the moves, against the units that it
  has in the end -/
  copies_le : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) → ∀ p,
    ((Plan.seenAt n o E).filter (Holds (hold0 sys.np) (hold1 sys.np) p)).card +
        ∑ r ∈ univ.filter (fun r : sys.R => sys.rp r = p),
          (1 + Fintype.card ((sys.kind r.1).SlAt r.2)) * plan.num n o r.1 ≤
      C * (up n o p + ∑ q ∈ univ.filter (fun q => q ≠ root ∧ par n o q = p), up n o q) +
        (if (p : ℕ) < AA then lg M ^ C * N else 0) +
        C * ((dead o).filter (Holds (hold0 sys.np) (hold1 sys.np) p)).card
  value : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) →
    ∀ tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a,
      netValue tab = ∑ o : sys.N → Fin U1, if ∀ x, plan.good n o x then
        ∑ w ∈ Common (none : UW ℓ) (cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E)), ∏ p,
          groupVal (hold0 sys.np) (hold1 sys.np) none (Plan.seenAt n o E) (plan.cur n o E) id
            (fun a => partyTab plan n o (startTab sys U1 n tab a) a) p w
        else 0
  computed : ∃ (D steps : ℕ) (inp : (Fin AA × Fin AA) ⊕ sys.N → (Fin AA → Fin AA → Fin (N + 1)) × (sys.N → Fin U1) → Fin D)
      (H : Set ((Fin AA → Fin AA → Fin (N + 1)) × (sys.N → Fin U1) → ℕ)),
    D ≤ (M * N) ^ C ∧ steps ≤ (M * N) ^ C ∧ AA + A' ≤ (M * N) ^ C ∧ E ≤ (M * N) ^ C ∧ U1 ≤ (M * N) ^ C ∧
    Fintype.card (Uid AA N sys.N U1) ≤ (M * N) ^ C ∧
    (∀ a c x, (inp (.inl (a, c)) x : ℕ) = x.1 a c) ∧ (∀ ν x, (inp (.inr ν) x : ℕ) = x.2 ν) ∧ SlpN inp steps H ∧
    (∀ p q, (ind fun x => par x.1 x.2 p = q) ∈ H) ∧ (∀ u, (ind fun x => u ∈ plan.cur x.1 x.2 E) ∈ H) ∧
    (∀ z u, (ind fun x => u ∈ plan.cons x.1 x.2 z) ∈ H) ∧ (∀ y, (fun x => plan.num x.1 x.2 y) ∈ H) ∧
    (∀ p, (fun x => up x.1 x.2 p) ∈ H) ∧ ∀ y, (ind fun x => plan.good x.1 x.2 y) ∈ H


end Paper


