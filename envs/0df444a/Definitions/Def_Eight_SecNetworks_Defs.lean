-- Prove2me | Definitions.Def_Eight_SecNetworks_Defs
-- name    : Eight_SecNetworks_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:56:32.58268+00:00
-- url     : https://prove2.me/theorems/c96bc3cf-9397-46d3-b8dc-562dceac44d3
-- title:
--   Sec Networks Defs
-- statement:
--   Definitions and structural lemmas for Sec Networks Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Networks
import Theorems.Thm_Groundwork_Colouring_cheb
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace Eight.SecNetworks
open Groundwork Groundwork.Prog Finset
structure Net (g : ℕ) where
  len : Fin g → ℕ
  S : Fin g → Finset (List Bool)
  W : Fin g → List Bool → ℤ
  Ψ : Fin g → Fin g → List Bool → List Bool → ℤ
  c : Fin g → Fin g → ℕ
  f : Fin g → Fin g → List Bool → List Bool → ℤ
namespace Net
variable {g : ℕ} (N : Net g)
def value : ℤ := ∑ z ∈ Fintype.piFinset N.S, (∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)
def U : ℕ := ∑ a, ∑ b ∈ univ.erase a, N.c a b
structure Is (P B : ℕ) : Prop where
  P_pos : 1 ≤ P
  B_pos : 1 ≤ B
  /-- the settings of a are bit strings of one fixed length P_a ≤ P -/
  len_S : ∀ a, ∀ z ∈ N.S a, z.length = N.len a
  len_le : ∀ a, N.len a ≤ P
  /-- Ψ_{b,a}(z_b, z_a) = Ψ_{a,b}(z_a, z_b) -/
  Ψ_symm : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, N.Ψ b a z' z = N.Ψ a b z z'
  c_symm : ∀ a b, N.c a b = N.c b a
  /-- (f_{a,b}, f_{b,a}) is a factorization of Ψ_{a,b} through c_{a,b} bits -/
  fact : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, N.Ψ a b z z' = ∑ θ ∈ words (N.c a b), N.f a b z θ * N.f b a z' θ
  /-- (i) -/
  i : ∀ a, ∑ b ∈ univ.erase a, N.c a b ≤ P
  /-- (ii) -/
  ii_W : ∀ a, ∀ z ∈ N.S a, |N.W a z| < 2 ^ B
  ii_Ψ : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, |N.Ψ a b z z'| < 2 ^ B
  ii_f : ∀ a b, a ≠ b → ∀ z ∈ N.S a, ∀ θ ∈ words (N.c a b), |N.f a b z θ| < 2 ^ B
end Net
abbrev PsiQ : Type := (ℕ × ℕ) × (List Bool × List Bool)
structure Procs (C : Type) : Type 1 where
  P : C → ℕ
  B : C → ℕ
  len : C → ℕ → ℕ
  cap : C → ℕ → ℕ → ℕ
  mem : Stepped (C × WQ) Bool
  W : Stepped (C × WQ) ℤ
  Ψ : Stepped (C × PsiQ) ℤ
  f : Stepped (C × FQ) ℤ
structure Procs.Give {C : Type} (Np : Procs C) (c : C) {g : ℕ} (N : Net g) (P B τ S : ℕ) : Prop where
  P_eq : Np.P c = P
  B_eq : Np.B c = B
  len_eq : ∀ a : Fin g, Np.len c a = N.len a
  cap_eq : ∀ a b : Fin g, a ≠ b → Np.cap c a b = N.c a b
  mem_runs : ∀ (a : Fin g) (z : List Bool), z.length = N.len a → Np.mem.Runs (c, (a.val, z)) τ S (decide (z ∈ N.S a))
  W_runs : ∀ (a : Fin g), ∀ z ∈ N.S a, Np.W.Runs (c, (a.val, z)) τ S (N.W a z)
  Ψ_runs : ∀ (a b : Fin g), a ≠ b → ∀ z ∈ N.S a, ∀ z' ∈ N.S b, Np.Ψ.Runs (c, ((a.val, b.val), (z, z'))) τ S (N.Ψ a b z z')
  f_runs : ∀ (a b : Fin g), a ≠ b → ∀ z ∈ N.S a, ∀ θ ∈ words (N.c a b), Np.f.Runs (c, ((a.val, b.val), (z, θ))) τ S (N.f a b z θ)
structure IsNetwork {C : Type} {g : ℕ} (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ) : Prop where
  is : N.Is P B
  τ_pos : 1 ≤ τ
  given : Np.Give c N P B τ S
structure NetAlg : Type 2 where
  app : {C : Type} → [HasSize C] → Procs C → Stepped C ℤ
structure Procs.Keeps {C : Type} [Enc C] (Np : Procs C) : Prop where
  len : Unary fun p : C × ℕ => Np.len p.1 p.2
  cap : Unary fun p : C × ℕ × ℕ => Np.cap p.1 p.2.1 p.2.2
  mem : Nonempty (IsPolyT Np.mem)
  W : Nonempty (IsPolyT Np.W)
  Ψ : Nonempty (IsPolyT Np.Ψ)
  f : Nonempty (IsPolyT Np.f)
def place (w w' : ℕ) : ℕ := if w' < w then w' else w' - 1
def copyAt (lam : ℕ) (w w' : ℕ) (z : List Bool) : List Bool := (z.drop (place w w' * lam)).take lam
def clique (K lam : ℕ) (W : Fin K → List Bool → ℤ) : Net K where
  len _ := (K - 1) * lam
  S _ := words ((K - 1) * lam)
  W := W
  Ψ w w' z z' := if copyAt lam w w' z = copyAt lam w' w z' then 1 else 0
  c _ _ := lam
  f w w' z θ := if copyAt lam w w' z = θ then 1 else 0
def Y {g K : ℕ} (c : Fin g → Fin g → ℕ) (χ : Fin g → Fin K) (γ γ' : Fin K) : ℕ := ∑ a with χ a = γ, ∑ b with χ b = γ', c a b
structure Good {g K : ℕ} (c : Fin g → Fin g → ℕ) (P : ℕ) (χ : Fin g → Fin K) : Prop where
  G1 : ∀ γ, K * #{a | χ a = γ} ≤ 2 * g
  G2 : ∀ γ γ', γ ≠ γ' → K ^ 3 * Y c χ γ γ' ≤ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P
structure GroupingFacts : Prop where
  /-- by Chebyshev, Pr(Y_{γ,γ'} > U/K² + gP/K³) ≤ 4K⁶/g = 4/(3K²) -/
  cheb : ∀ (K P : ℕ) (c : Fin (3 * K ^ 8) → Fin (3 * K ^ 8) → ℕ), 2 ≤ K → (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∀ γ γ' : Fin K, γ ≠ γ' →
    3 * K ^ 2 * #{χ : Fin (3 * K ^ 8) → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} ≤ 4 * K ^ (3 * K ^ 8)
  /-- some pair violates this bound with probability less than 2/3 -/
  pairs : ∀ (K P : ℕ) (c : Fin (3 * K ^ 8) → Fin (3 * K ^ 8) → ℕ), 2 ≤ K → (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) →
    3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ (3 * K ^ 8)
  /-- a group exceeds 2g/K with probability at most K/g -/
  group : ∀ K : ℕ, 2 ≤ K → ∀ γ : Fin K, 3 * K ^ 8 * #{χ : Fin (3 * K ^ 8) → Fin K | 2 * (3 * K ^ 8) < K * #{a | χ a = γ}} ≤ K * K ^ (3 * K ^ 8)
  /-- some group does so with probability less than 1/3 (the paper: at most K²/g < 1/3) -/
  groups : ∀ K : ℕ, 2 ≤ K → 3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}} < K ^ (3 * K ^ 8)
  /-- so a good grouping exists -/
  exists_good : ∀ (K P : ℕ) (c : Fin (3 * K ^ 8) → Fin (3 * K ^ 8) → ℕ), 2 ≤ K → (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∃ χ : Fin (3 * K ^ 8) → Fin K, Good c P χ
end Eight.SecNetworks


