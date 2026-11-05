-- Prove2me | Definitions.Def_Exits_Defs
-- name    : Exits_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T16:45:37.989566+00:00
-- url     : https://prove2.me/theorems/4b2fc37e-c148-4054-9c07-9686289b13ae
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_ToTuring_PolyT
set_option autoImplicit false
section
section
namespace Exits
open Finset Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
section Loops
variable {α β γ τ ν : Type}
def foldUntil [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ) (M : Stepped τ β) (g : γ → τ → β → γ) (stop : γ → Bool) (c₀ : α → γ) : Stepped α γ where
  σ := (τ × γ × M.σ) ⊕ γ
  init a := foldGo M (c₀ a) (start a)
  step s := match s with
    | .inl p => match M.out p.2.2 with
      | some b => foldGo M (g p.2.1 p.1 b) (if stop (g p.2.1 p.1 b) then none else nxt p.1)
      | none => .inl (p.1, p.2.1, M.step p.2.2)
    | .inr c => .inr c
  out s := match s with | .inl _ => none | .inr c => some c
def firstUntil [HasSize α] (N : α → ℕ) (M : Stepped (α × ℕ) β) (p : β → Bool) : Stepped α (Option ℕ) :=
  foldUntil (rangeStart N) (rangeNext N) M (rangeG (firstG p)) Option.isSome noneC
def walkUntil [HasSize ν] (step : ν → Option (ν × ν)) (root : α → ν) (T : Stepped ν Bool) : Stepped α Bool :=
  foldUntil (fun a => some [root a]) (walkNext step) (Stepped.guard (walkSel step) T false) (fun c _ b => c || b) id fun _ => false
end Loops
def met {τ γ : Type} (f : γ → τ → γ) (stop : γ → Bool) : γ → List τ → List τ
  | _, [] => []
  | c, x :: xs => if stop (f c x) then [x] else x :: met f stop (f c x) xs
def StFoldUntil : Prop := ∀ (α β γ τ : Type) [HasSize τ] [HasSize γ] (start : α → Option τ) (nxt : τ → Option τ) (M : Stepped τ β) (g : γ → τ → β → γ) (stop : γ → Bool) (c₀ : α → γ)
  (a : α) (xs : List τ), Orbit nxt (start a) xs → ∀ (t : τ → ℕ) (v : τ → β) (Sx Sc Sm : ℕ),
  (∀ x ∈ met (fun c x => g c x (v x)) stop (c₀ a) xs, M.Runs x (t x) Sm (v x)) → (∀ x ∈ met (fun c x => g c x (v x)) stop (c₀ a) xs, size x ≤ Sx) →
  (∀ l, l <+: met (fun c x => g c x (v x)) stop (c₀ a) xs → size (l.foldl (fun c x => g c x (v x)) (c₀ a)) ≤ Sc) →
  (foldUntil start nxt M g stop c₀).Runs a ((met (fun c x => g c x (v x)) stop (c₀ a) xs).map fun x => t x + 1).sum (Sx + (Sc + Sm) + 1)
    ((met (fun c x => g c x (v x)) stop (c₀ a) xs).foldl (fun c x => g c x (v x)) (c₀ a))
def reach (q : ℕ → Bool) (n : ℕ) : ℕ := match (List.range n).find? q with | some i => i + 1 | none => n
def StFirstUntil : Prop := ∀ (α β : Type) [HasSize α] (N : α → ℕ) (M : Stepped (α × ℕ) β) (p : β → Bool) (a : α) (t : ℕ → ℕ) (v : ℕ → β) (Sm : ℕ),
  (∀ y < reach (fun y => p (v y)) (N a), M.Runs (a, y) (t y) Sm (v y)) →
  (firstUntil N M p).Runs a (∑ y ∈ range (reach (fun y => p (v y)) (N a)), (t y + 1)) (size a + size (N a) + (size (N a) + 1 + Sm) + 1) ((List.range (N a)).find? fun y => p (v y))
def tested {ν : Type} (v : ν → Bool) (ls : List ν) : List ν := ls.take (ls.findIdx v + 1)
def StWalkUntil : Prop := ∀ (α ν : Type) [HasSize ν] (step : ν → Option (ν × ν)) (root : α → ν) (T : Stepped ν Bool) (k : ℕ) (a : α),
  (∀ x ∈ leaves step k (root a), step x = none) → ∀ (v : ν → Bool) (t Sm Sx : ℕ),
  (∀ x ∈ tested v (leaves step k (root a)), T.Runs x t Sm (v x)) → (∀ i, size ((Sparsify.round step)^[i] ([root a], [])).1 ≤ Sx) →
  (walkUntil step root T).Runs a ((tested v (leaves step k (root a))).length * (t + 2) + k) (Sx + (1 + (Sm + 1)) + 1) ((leaves step k (root a)).any v)
def StFoldUntilPoly : Prop := ∀ (α β γ τ : Type) [HasSize τ] [HasSize γ] [Enc α] [Enc β] [Enc γ] [Enc τ] [Carried γ] [Carried τ]
  (start : α → Option τ) (nxt : τ → Option τ) (M : Stepped τ β) [IsPolyT M] (g : γ → τ → β → γ) (stop : γ → Bool) (c₀ : α → γ),
  PolyT start → PolyT nxt → (PolyT fun p : γ × τ × β => g p.1 p.2.1 p.2.2) → PolyT stop → PolyT c₀ → Nonempty (IsPolyT (foldUntil start nxt M g stop c₀))
def StFirstUntilOf : Prop := StFoldUntil → StFirstUntil
def StWalkUntilOf : Prop := StFoldUntil → StWalkUntil
end Exits


