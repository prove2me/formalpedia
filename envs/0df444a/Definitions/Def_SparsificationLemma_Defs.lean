-- Prove2me | Definitions.Def_SparsificationLemma_Defs
-- name    : SparsificationLemma_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:50:22.627884+00:00
-- url     : https://prove2.me/theorems/93bd710f-295d-4ec2-bb42-f3c5065330d5
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsificationLemma/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_UniformInK_Tree_Defs
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_any
import Theorems.Thm_Groundwork_PolyT_contains
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_mul
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_TM_Run_one
import Theorems.Thm_Groundwork_Unary_mul
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)
def IsKCNF (k n : ℕ) (ψ : PFml) : Prop := ∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n
def Sat (b : ℕ → Bool) (ψ : PFml) : Prop := ∀ C ∈ ψ, ∃ l ∈ C, b l.1 = l.2
def ExactlyOne (b : ℕ → Bool) (ψ : PFml) (Φ : List PFml) : Prop :=
  (Sat b ψ → ∃! i : Fin Φ.length, Sat b (Φ.get i)) ∧ (¬ Sat b ψ → ∀ Ψ ∈ Φ, ¬ Sat b Ψ)
def occN (ψ : PFml) (v : ℕ) : ℕ := (occ ψ v).length
def noTaut (ψ : PFml) : PFml := ψ.filter fun C => !(C.any fun l => C.contains (l.1, !l.2))
def root (ψ : PFml) : CNode := (rootP ψ, [])
def tree (θ : ℕ → ℕ) (k D : ℕ) (ψ : PFml) : List CNode := leaves (stepC θ k) D (root ψ)
def out (x : CNode) : PFml := (leafM x).dedup
def outputs (θ : ℕ → ℕ) (k D : ℕ) (ψ : PFml) : List PFml := (tree θ k D ψ).map out
def StExactlyOne : Prop := ∀ (θ : ℕ → ℕ) (k D : ℕ) (ψ : PFml) (b : ℕ → Bool), ExactlyOne b ψ (outputs θ k D ψ)
def StCountOfExactlyOne : Prop := ∀ (n : ℕ) (ψ : PFml) (Φ : List PFml), (∀ b, ExactlyOne b ψ Φ) → cntN n ψ = (Φ.map (cntN n)).sum
def StSide : Prop := ∀ (θ : ℕ → ℕ) (k D : ℕ) (r X : PFml),
  leaves (stepC θ k) D (r, X) = (leaves (stepC θ k) D (r, [])).map fun x => (x.1, x.2 ++ X)
def StUnchanged : Prop := ∀ (θ : ℕ → ℕ) (k D : ℕ) (r X : PFml), (leaves (stepC θ k) D (r, X)).map Prod.fst = leaves (stepK θ k) D r
def StOutputsSame : Prop := ∀ (θ : ℕ → ℕ) (k D n : ℕ) (ψ : PFml),
  (leaves (stepC θ k) D (rootC (List.replicate n (), ψ))).map out = outputs θ k D ψ
def StNodup : Prop := ∀ (θ : ℕ → ℕ) (k D : ℕ) (ψ : PFml), ∀ Φ ∈ outputs θ k D ψ, Φ.Nodup
def StLenOfOcc : Prop := ∀ (k n Δ : ℕ) (Φ : PFml), IsKCNF k n Φ → (∀ v, occN Φ v ≤ Δ) → Φ.length ≤ Δ * n
def StNoTaut : Prop := ∀ ψ : PFml, (∀ b, Sat b (noTaut ψ) ↔ Sat b ψ) ∧ (∀ k n, IsKCNF k n ψ → IsKCNF k n (noTaut ψ)) ∧
  ∀ C ∈ noTaut ψ, ∀ l ∈ C, (l.1, !l.2) ∉ C
structure ThrC (k τ : ℕ) (θ β : ℕ → ℕ) : Prop where
  pos : ∀ i, 0 < θ i
  one : 2 ≤ β 1
  step : ∀ i, 2 ≤ i → i < k → 4 * θ (i - 1) + ∑ i' ∈ range i, 2 * θ (i - i') * β i' ≤ β i
  mul : ∀ r, τ * β r ≤ θ r
def StThrOfU : Prop := ∀ (k τ : ℕ) (θ β : ℕ → ℕ), 2 ≤ β 1 → ThrU k τ θ β → ThrC k τ θ β
def StBoundC : Prop := ∀ (α : Type) [DecidableEq α] (θ β : ℕ → ℕ) (k τ n : ℕ) (φ F : Finset (Finset α)) (U : Finset α) (p t : ℕ),
  ThrC k τ θ β → U.card ≤ 2 * n → (∀ C ∈ φ, C ⊆ U) → NodeU θ k τ φ F p t → p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ (k - 1) * n
def StIfaceC : Prop := ∀ (k τ n D : ℕ) (θ β : ℕ → ℕ), ThrC k τ θ β → (∑ i ∈ range k, β i) * n ≤ D →
  Iface θ k D ((k - 1) * n) τ ((2 * ∑ j ∈ range k, θ j) * n) (ProgMain.Ok k n) (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU θ k τ F₀ F p t)
def StGen : Prop := ∀ (k τ n D : ℕ) (θ β : ℕ → ℕ), 1 ≤ k → 1 ≤ τ → ThrC k τ θ β → (∑ i ∈ range k, β i) * n ≤ D → ∀ ψ : PFml, IsKCNF k n ψ →
  (∀ x ∈ tree θ k D ψ, stepC θ k x = none) ∧
  (outputs θ k D ψ).length ≤ ∑ j ∈ range ((k - 1) * n / τ + 1), D.choose j ∧
  (∀ Φ ∈ outputs θ k D ψ, IsKCNF k n Φ ∧ ∀ v, occN Φ v ≤ 2 * (∑ j ∈ range k, θ j) + 2) ∧
  ∀ x ∈ tree θ k D ψ, x.1.length ≤ ψ.length
def StTreeG : Prop := ∀ (k τ n D : ℕ) (θ β : ℕ → ℕ), 1 ≤ k → k ^ 2 ≤ τ → ThrC k τ θ β → (∑ i ∈ range k, β i) * n ≤ D → ∀ ψ : PFml, IsKCNF k n ψ →
  (leaves (stepC θ k) D (rootC (List.replicate n (), ψ))).length ≤ ∑ j ∈ range ((k - 1) * n / τ + 1), D.choose j ∧
  (∀ x ∈ leaves (stepC θ k) D (rootC (List.replicate n (), ψ)),
    stepC θ k x = none ∧ (leafF x).length ≤ (2 * (∑ j ∈ range k, θ j) + 2) * n ∧
      (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (occ x.1 v).length ≤ 2 * ∑ j ∈ range k, θ j) ∧
      ∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧
  cntN n ψ = ((leaves (stepC θ k) D (rootC (List.replicate n (), ψ))).map fun x => cntN n (leafF x)).sum ∧
  ∀ i, ((round (stepC θ k))^[i] ([rootC (List.replicate n (), ψ)], [])).1.length ≤ D + 1 ∧
    ∀ x ∈ ((round (stepC θ k))^[i] ([rootC (List.replicate n (), ψ)], [])).1,
      x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n
end SparsificationLemma


