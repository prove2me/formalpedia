-- Prove2me | Definitions.Def_Value_Defs
-- name    : Value_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:58:21.743071+00:00
-- url     : https://prove2.me/theorems/3eb49a6b-00f0-4f6d-8754-2f6c0273e6db
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Display
import Theorems.Thm_Groundwork_PolyT_idxOf
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
def edgeStrings (K lam : ℕ) : Finset (Fin K × Fin K → List Bool) := tuples (fun p : Fin K × Fin K => p.1 < p.2) (fun _ => words lam) []
def CopiesAgree {K : ℕ} (lam : ℕ) (z : Fin K → List Bool) : Prop := ∀ p ∈ pairs (Fin K), copyAt lam p.1 p.2 (z p.1) = copyAt lam p.2 p.1 (z p.2)
def cliqueTerm {K : ℕ} (lam : ℕ) (W : Fin K → List Bool → ℤ) (z : Fin K → List Bool) : ℤ :=
  (∏ w, W w (z w)) * ∏ p ∈ pairs (Fin K), if copyAt lam p.1 p.2 (z p.1) = copyAt lam p.2 p.1 (z p.2) then 1 else 0
def StSumOverSettings : Prop := ∀ (K lam : ℕ) (W : Fin K → List Bool → ℤ),
  (clique K lam W).value = ∑ z ∈ Fintype.piFinset (fun _ : Fin K => words ((K - 1) * lam)), cliqueTerm lam W z
def StCopiesMustAgree : Prop := ∀ (K lam : ℕ) (W : Fin K → List Bool → ℤ) (z : Fin K → List Bool),
  (¬ CopiesAgree lam z → cliqueTerm lam W z = 0) ∧ (CopiesAgree lam z → cliqueTerm lam W z = ∏ w, W w (z w))
def StOneStringPerEdge : Prop := ∀ (K lam : ℕ),
  (∀ Λ ∈ edgeStrings K lam, ∃! z : Fin K → List Bool, z ∈ Fintype.piFinset (fun _ : Fin K => words ((K - 1) * lam)) ∧ ∀ w w' : Fin K, w' ≠ w → copyAt lam w w' (z w) = star Λ w w') ∧
  ∀ z ∈ Fintype.piFinset (fun _ : Fin K => words ((K - 1) * lam)), CopiesAgree lam z → ∃ Λ ∈ edgeStrings K lam, ∀ w w' : Fin K, w' ≠ w → copyAt lam w w' (z w) = star Λ w w'
def StCliqueValue : Prop := ∀ (K lam : ℕ) (W : Paper.Tables K),
  (clique K lam (tablesOn lam W)).value = ∑ Λ ∈ edgeStrings K lam, ∏ w, W w (star Λ w)
def StCliqueValueOf : Prop := StSumOverSettings → StCopiesMustAgree → StOneStringPerEdge → StCliqueValue
section Groups
variable {C : Type} [HasSize C] {g K : ℕ}
def groupClique (Np : Procs C) (c : C) (N : Net g) (hK0 : 0 < K) (x L : ℕ) : Net K := clique K L (tablesOn L (display Np c N hK0 x))
abbrev Across (χ : Fin g → Fin K) (p : Fin g × Fin g) : Prop := p.1 < p.2 ∧ χ p.1 ≠ χ p.2
def blockStrings (N : Net g) (χ : Fin g → Fin K) : Finset (Fin g × Fin g → List Bool) := tuples (Across χ) (fun p => words (N.c p.1 p.2)) []
def readBlocks (Np : Procs C) (c : C) (hK0 : 0 < K) (x : ℕ) (Λ : Fin K × Fin K → List Bool) : Fin g × Fin g → List Bool :=
  fun p => if Across (Paper.grouping hK0 x) p then thetaAt Np.toPaperNetwork c hK0 x (star Λ (Paper.grouping hK0 x p.1)) p.1 p.2 else []
def AppendedZero (g : ℕ) (Np : Procs C) (c : C) (x : ℕ) (Λ : Fin K × Fin K → List Bool) : Prop :=
  ∀ γ γ' : Fin K, γ' ≠ γ → ∀ bit ∈ appendedBits (g := g) Np.toPaperNetwork c x γ γ' (star Λ γ γ'), bit = false
def jointTerm (N : Net g) (χ : Fin g → Fin K) (z : Fin g → List Bool) (θ : Fin g × Fin g → List Bool) : ℤ :=
  (∏ a, N.W a (z a)) * (∏ p ∈ pairs (Fin g) with χ p.1 = χ p.2, N.Ψ p.1 p.2 (z p.1) (z p.2)) *
    ∏ p ∈ pairs (Fin g) with χ p.1 ≠ χ p.2, N.f p.1 p.2 (z p.1) (θ p) * N.f p.2 p.1 (z p.2) (θ p)
end Groups
def StLayout : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (Np : Procs C) (c : C) (hK0 : 0 < K) (x : ℕ) (Θ : Fin K → List Bool) (a b : Fin g), Paper.grouping hK0 x a < Paper.grouping hK0 x b →
  (thetaAt Np.toPaperNetwork c hK0 x Θ a b =
      ((Θ (Paper.grouping hK0 x b)).drop (((lbLens K g Np.toPaperNetwork c x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).take ((prs K g x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).idxOf (a.val, b.val))).sum)).take (Np.cap c a.val b.val)) ∧
  (thetaAt Np.toPaperNetwork c hK0 x Θ b a =
      ((Θ (Paper.grouping hK0 x a)).drop (((lbLens K g Np.toPaperNetwork c x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).take ((prs K g x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).idxOf (a.val, b.val))).sum)).take (Np.cap c a.val b.val)) ∧
  ∀ θ : List Bool, appendedBits (g := g) Np.toPaperNetwork c x (Paper.grouping hK0 x a) (Paper.grouping hK0 x b) θ = θ.drop (lbLens K g Np.toPaperNetwork c x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).sum
def StSameBlock : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (Np : Procs C) (c : C) (hK0 : 0 < K) (x : ℕ) (Λ : Fin K × Fin K → List Bool) (a b : Fin g),
  Paper.grouping hK0 x a ≠ Paper.grouping hK0 x b →
    thetaAt Np.toPaperNetwork c hK0 x (star Λ (Paper.grouping hK0 x a)) a b = thetaAt Np.toPaperNetwork c hK0 x (star Λ (Paper.grouping hK0 x b)) b a
def StAppendedZero : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (Np : Procs C) (c : C) (N : Net g) (hK0 : 0 < K) (x : ℕ) (Λ : Fin K × Fin K → List Bool),
  ¬ AppendedZero g Np c x Λ → ∏ γ, display Np c N hK0 x γ (star Λ γ) = 0
def StBlocks : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (hK0 : 0 < K) (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∀ x L : ℕ, (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    (∀ Λ ∈ edgeStrings K L, AppendedZero g Np c x Λ → readBlocks Np c hK0 x Λ ∈ blockStrings N (Paper.grouping hK0 x)) ∧
    ∀ θ ∈ blockStrings N (Paper.grouping hK0 x), ∃! Λ : Fin K × Fin K → List Bool, Λ ∈ edgeStrings K L ∧ AppendedZero g Np c x Λ ∧ readBlocks Np c hK0 x Λ = θ
def StSumsInside : Prop := ∀ (g K : ℕ) (χ : Fin g → Fin K) (S : Fin g → Finset (List Bool)) (F : Fin K → (Fin g → List Bool) → ℤ),
  ∏ γ, ∑ z ∈ tuples (fun a => χ a = γ) S [], F γ z = ∑ z ∈ Fintype.piFinset S, ∏ γ, F γ fun a => if χ a = γ then z a else []
def StJointSum : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (hK0 : 0 < K) (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∀ x L : ℕ, (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ∑ Λ ∈ edgeStrings K L, ∏ γ, display Np c N hK0 x γ (star Λ γ)
      = ∑ z ∈ Fintype.piFinset N.S, ∑ θ ∈ blockStrings N (Paper.grouping hK0 x), jointTerm N (Paper.grouping hK0 x) z θ
def StSumOut : Prop := ∀ (g K P B : ℕ) (N : Net g), N.Is P B → ∀ (χ : Fin g → Fin K), ∀ z ∈ Fintype.piFinset N.S,
  ∑ θ ∈ blockStrings N χ, jointTerm N χ z θ = (∏ a, N.W a (z a)) * ∏ p ∈ pairs (Fin g), N.Ψ p.1 p.2 (z p.1) (z p.2)
def StValueEqualsZ : Prop := ∀ (C : Type) [HasSize C] (g K : ℕ) (hK0 : 0 < K) (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
  ∀ x L : ℕ, (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) → (groupClique Np c N hK0 x L).value = N.value
def StJointSumOf : Prop := StSameBlock → StAppendedZero → StBlocks → StSumsInside → StJointSum
def StValueEqualsZOf : Prop := StCliqueValue → StJointSum → StSumOut → StValueEqualsZ
def StValueOf : Prop := StCliqueValue → StValueEqualsZ → Eight.ViaGrouping.StValue
end Value


