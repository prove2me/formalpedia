-- Prove2me | Definitions.Def_AppVariablesStatement
-- name    : AppVariablesStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:16:39.968574+00:00
-- url     : https://prove2.me/theorems/8e43af69-9bc1-4d7b-982f-8948170f28de
-- title:
--   App Variables Statement
-- statement:
--   Definitions and structural lemmas for App Variables Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/AppVariablesStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Log
set_option autoImplicit false
section
section
namespace AppVariables
open Finset
section StepParity
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
def allEven (V : X → Finset E) (L : List (Finset E)) (ξ : X) : ℤ := (L.map fun Λ => ParityChecks.ev #(Λ ∩ V ξ)).prod
def Fsum (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) : ℤ := ∑ ξ, ParityChecks.eta V nb ξ * allEven V L ξ
def Xsum (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) : ℤ := ∑ ξ, ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ
def tup (V : X → Finset E) (L : List (Finset E)) (M' : ℕ) (ξ : X) : Finset (Fin L.length → Finset E) :=
  ParityChecks.tuples V L.length (fun j => L.getD j ∅) univ M' ξ
def ProductStmt : Prop := ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ) (L : List (Finset E)),
  Xsum V nb L = 0 → Fsum V nb L = #{ξ | V ξ = ∅}
def EmptyListStmt : Prop := ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ),
  Fintype.card E ≤ nb → Xsum V nb [] = 0
def LemCutoff : Prop := ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (L : List (Finset E)) (φ : X → ℤ) (ν M' : ℕ),
  1 ≤ ν → ν - 1 + L.length ≤ M' →
  ∑ ξ, φ ξ * allEven V L ξ ≡ ∑ ξ, φ ξ * ∑ S ∈ tup V L M' ξ, ∏ j, ParityChecks.sig #(S j) [ZMOD 2 ^ ν]
def XFStmt : Prop := ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) (β n M : ℕ),
  1 ≤ β → β - 1 + L.length ≤ M → n + L.length ≤ M →
  (Xsum V nb L ≡ ∑ ξ, ∑ _S₀ ∈ (V ξ).powerset with #_S₀ = nb + 1, ∑ S ∈ tup V L M ξ, ∏ j, ParityChecks.sig #(S j) [ZMOD 2 ^ β]) ∧
  (Fsum V nb L ≡ ∑ ξ, ∑ S₀ ∈ (V ξ).powerset with #S₀ ≤ nb, (-1) ^ #S₀ * ∑ S ∈ tup V L M ξ, ∏ j, ParityChecks.sig #(S j) [ZMOD 2 ^ (n + 1)])
def ResiduesStmt : Prop := ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) (n : ℕ),
  Fintype.card X ≤ 2 ^ n →
  (0 ≤ Xsum V nb L ∧ Xsum V nb L ≤ 2 ^ n * (Fintype.card E).choose (nb + 1) ∧
    (2 : ℤ) ^ n * (Fintype.card E).choose (nb + 1) ≤ 2 ^ (n + Nat.clog 2 ((Fintype.card E).choose (nb + 1)))) ∧
  (Xsum V nb L = 0 → 0 ≤ Fsum V nb L ∧ Fsum V nb L ≤ 2 ^ n)
end StepParity
structure IsFamily {E ι : Type} [Fintype E] [DecidableEq E] (v : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) : Prop where
  a : ∀ u ∈ Ω, v * #(Γ u) ≤ 16 * Fintype.card E
  b : ∀ e : E, 15 * v * #{u ∈ Ω | e ∈ Γ u} ≤ 16 * #Ω
  c : ∀ V : Finset E, v < #V → #Ω ≤ 4 * #{u ∈ Ω | Odd #(Γ u ∩ V)}
section Family
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
def ip {s : ℕ} (x y : Fin s → ZMod 2) : ZMod 2 := ∑ i, x i * y i
def Gam {m s : ℕ} (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (u : F × F × F × F) : Finset (Fin m) :=
  univ.filter fun E => (∀ i : Fin s, i.val < a - 1 → bits (u.1 * ϑ E + u.2.1) i = 0) ∧ ip (bits (u.2.2.1 ^ E.val)) (bits u.2.2.2) = 1
def Om {m s : ℕ} (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) : Finset (F × F × F × F) :=
  univ.filter fun u => 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m
end Family
def LemFamily : Prop := ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] (m s a : ℕ) (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F),
  1 ≤ a → 2 ^ a ≤ m → 16 * m ≤ 2 ^ s → 2 ^ s < 32 * m →
  0 < #(Om bits ϑ a) ∧ #(Om bits ϑ a) < (32 * m) ^ 4 ∧ IsFamily (2 ^ a) (Om bits ϑ a) (Gam bits ϑ a)
def IsNb (n Δ nb : ℕ) : Prop := (∃ a, nb = 2 ^ a) ∧ (2 * Δ) ^ nb ≤ 2 ^ n ∧ 2 ^ n < (2 * Δ) ^ (2 * nb)
def beta (n m nb : ℕ) : ℕ := n + Nat.clog 2 (m.choose (nb + 1)) + 1
def IsRb (β rb : ℕ) : Prop := 3 ^ rb * 2 ^ β < 4 ^ rb ∧ ∀ j < rb, ¬ 3 ^ j * 2 ^ β < 4 ^ j
def Mb (β rb : ℕ) : ℕ := rb + β - 1
def pp (nb : ℕ) : ℚ := 16 / (15 * nb)
def IsTb (m nb rb tb : ℕ) : Prop := (m : ℚ) * (1 + pp nb) ^ rb ≤ 2 ^ tb ∧ ∀ c < tb, ¬ (m : ℚ) * (1 + pp nb) ^ rb ≤ 2 ^ c
section StepChoice
variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]
def load (L : List (Finset E)) (e : E) : ℕ := (L.filter fun Λ => e ∈ Λ).length
def Ups (V : X → Finset E) (nb β rb tb : ℕ) (L : List (Finset E)) : ℚ :=
  (4 / 3) ^ L.length * (Xsum V nb L : ℚ) / 2 ^ (β - 1) + (1 + pp nb) ^ (rb - L.length) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e
inductive Reached (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) : List (Finset E) → Prop
  | nil : Reached V nb β rb tb Ω Γ []
  | step (L : List (Finset E)) (u : ι) : Reached V nb β rb tb Ω Γ L → 0 < Xsum V nb L → u ∈ Ω →
      (∀ u' ∈ Ω, Ups V nb β rb tb (L ++ [Γ u]) ≤ Ups V nb β rb tb (L ++ [Γ u'])) → Reached V nb β rb tb Ω Γ (L ++ [Γ u])
structure StepChoice : Prop where
  /-- for a family as in Lemma 13 with v = n̄: the average of X(𝓛, Γ_u) over u ∈ Ω is at most
  (3/4)·X(𝓛) -/
  avgX : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    IsFamily nb Ω Γ → 4 * ∑ u ∈ Ω, Xsum V nb (L ++ [Γ u]) ≤ 3 * #Ω * Xsum V nb L
  /-- for n̄ ≥ 1 and a family as in Lemma 13 with v = n̄: the average of 2^[E ∈ Γ_u] over u ∈ Ω is
  at most 1 + p -/
  avgCol : ∀ (E ι : Type) [Fintype E] [DecidableEq E] (nb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (e : E), 1 ≤ nb →
    IsFamily nb Ω Γ → ∑ u ∈ Ω, (2 : ℚ) ^ (if e ∈ Γ u then 1 else 0) ≤ (1 + pp nb) * #Ω
  /-- for n̄ ≥ 1, a family as in Lemma 13 with v = n̄, any β, r̄, t̄ and a list of r < r̄ checks:
  the average of Υ(𝓛, Γ_u) over u ∈ Ω is at most Υ(𝓛) -/
  avgUps : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    1 ≤ nb → IsFamily nb Ω Γ → L.length < rb → ∑ u ∈ Ω, Ups V nb β rb tb (L ++ [Γ u]) ≤ #Ω * Ups V nb β rb tb L
  /-- for at most 2^n assignments, n̄ ≥ 1, β, r̄, t̄ as in the paper and a family as in Lemma 13
  with v = n̄: every list that is reached has at most r̄ checks and Υ ≤ 2 -/
  ups_le : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    Fintype.card X ≤ 2 ^ n → 1 ≤ nb → IsRb (beta n (Fintype.card E) nb) rb → IsTb (Fintype.card E) nb rb tb → IsFamily nb Ω Γ →
    Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L → L.length ≤ rb ∧ Ups V nb (beta n (Fintype.card E) nb) rb tb L ≤ 2
  /-- under the hypotheses of `ups_le`: every reached list has X(𝓛) ≤ (3/4)^r·2^β -/
  x_le : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    Fintype.card X ≤ 2 ^ n → 1 ≤ nb → IsRb (beta n (Fintype.card E) nb) rb → IsTb (Fintype.card E) nb rb tb → IsFamily nb Ω Γ →
    Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L → 4 ^ L.length * Xsum V nb L ≤ 3 ^ L.length * 2 ^ beta n (Fintype.card E) nb
  /-- for any β, r̄, t̄ and any sets Γ_u, if Ω is not empty: a reached list with X(𝓛) > 0 has a
  reached extension (𝓛, Γ_u), u ∈ Ω -/
  progress : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    Ω.Nonempty → Reached V nb β rb tb Ω Γ L → 0 < Xsum V nb L → ∃ u ∈ Ω, Reached V nb β rb tb Ω Γ (L ++ [Γ u])
  /-- under the hypotheses of `ups_le`: a reached list of r̄ checks has X = 0; with `ups_le`, the
  loop ends after at most r̄ rounds with X(𝓛) = 0 -/
  ends : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)),
    Fintype.card X ≤ 2 ^ n → 1 ≤ nb → IsRb (beta n (Fintype.card E) nb) rb → IsTb (Fintype.card E) nb rb tb → IsFamily nb Ω Γ →
    Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L → L.length = rb → Xsum V nb L = 0
  /-- the bounds at the end of Step 2, under the hypotheses of `ups_le`: every list whose X or F is
  needed (a reached list, or one with X > 0 and one more Γ_u, u ∈ Ω) has r ≤ r̄, |Λ_j| ≤ s̄ =
  16m/n̄, load(E) ≤ t̄ + 2 -/
  structure_ : ∀ (X E ι : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L L' : List (Finset E)),
    Fintype.card X ≤ 2 ^ n → 1 ≤ nb → IsRb (beta n (Fintype.card E) nb) rb → IsTb (Fintype.card E) nb rb tb → IsFamily nb Ω Γ →
    Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L → (L' = L ∨ (0 < Xsum V nb L ∧ ∃ u ∈ Ω, L' = L ++ [Γ u])) →
    L'.length ≤ rb ∧ (∀ Λ ∈ L', nb * #Λ ≤ 16 * Fintype.card E) ∧ ∀ e : E, load L' e ≤ tb + 2
end StepChoice
end AppVariables


