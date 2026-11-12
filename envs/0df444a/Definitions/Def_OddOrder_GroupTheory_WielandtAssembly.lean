-- Prove2me | Definitions.Def_OddOrder_GroupTheory_WielandtAssembly
-- name    : OddOrder_GroupTheory_WielandtAssembly
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:39:39.602864+00:00
-- url     : https://prove2.me/theorems/1ec3ef80-b0ae-4c71-bd30-65fadb30081a
-- title:
--   Peterfalvi (9.1): the chief-series assembly of Wielandt's fixed-point formula
-- statement:
--   The chief-series induction reducing the group-level Wielandt fixed-point identity to the per-chief-factor identity. The predicate `WielandtPerFactor L U E` packages the per-chief-factor identity uniformly over all finite groups $H$ carrying an $L$-action.
--
--   The main declaration: `WielandtPerFactor`.
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/WielandtAssembly.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/WielandtAssembly.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_CoprimeFixedPoints
import Definitions.Def_OddOrder_GroupTheory_MinimalInvariantNormal

namespace OddOrder.GroupTheory

open OddOrder.Isaacs.Ch03 (IsAInvariant)

local notation3 "quotMulAut " hN => OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom hN

/-- The **per-chief-factor Wielandt identity**, uniformly over all finite groups `H` carrying an
`L`-action and all elementary-abelian `L`-invariant normal subgroups `N ◁ H` (of *prime* exponent
`p`).  This is the single representation-theoretic input to the chief-series assembly
(`wielandt_formula_of_perfactor`); it is the cardinality form of the elementary-abelian dimension
identity `finrank_elab_identity`, discharged from that identity in `wielandtPerFactor_of_dim`.

The exponent `p` is required to be *prime* (not merely an exponent): this is what makes `↥N` an
`𝔽_p`-vector space, the form in which the dimension identity (⋆) lives.  Primality is not
recoverable
from `IsElementaryAbelian p ↥N` alone (e.g. `IsElementaryAbelian 6 (ZMod 2)` holds), so it is
carried
explicitly. -/
def WielandtPerFactor (L : Type*) [Group L] (U E : Subgroup L) : Prop :=
  ∀ (H : Type*) [Group H] [Finite H] (φ : L →* MulAut H) (N : Subgroup H) [N.Normal],
    Nat.Coprime (Nat.card L) (Nat.card H) →
    IsAInvariant φ N → (∃ p : ℕ, p.Prime ∧ IsElementaryAbelian p ↥N) →
    Nat.card ↥(fixedSubgroup φ ⊤ ⊓ N) ^ Nat.card ↥E * Nat.card ↥N =
      Nat.card ↥(fixedSubgroup φ E ⊓ N) ^ Nat.card ↥E * Nat.card ↥(fixedSubgroup φ U ⊓ N)

/-- **Peterfalvi (9.1), the chief-series assembly.**  Given the per-chief-factor identity
(`hpf : WielandtPerFactor L U E`), the group-level Wielandt fixed-point identity holds for every
coprime solvable action `φ : L →* MulAut H`:
`|C_H(UE)|^{|E|} · |H| = |C_H(E)|^{|E|} · |C_H(U)|` (with `C_H(UE) = fixedSubgroup φ ⊤`).

Proved by strong induction on `|H|`: the trivial group is the base case; otherwise an
elementary-abelian `L`-invariant normal subgroup `N`
(`exists_aInvariant_normal_isElementaryAbelian`)
splits the problem via `wielandt_step`, with the per-factor identity on `N` from `hpf` and the
induction hypothesis on the smaller quotient `H/N`. -/
theorem wielandt_formula_of_perfactor.{u} {L : Type*} [Group L] [Finite L] {U E : Subgroup L}
    (hpf : WielandtPerFactor.{_, u} L U E) :
    ∀ (H : Type u) [Group H] [Finite H] [Group.IsSolvable H] (φ : L →* MulAut H),
      Nat.Coprime (Nat.card L) (Nat.card H) →
      Nat.card ↥(fixedSubgroup φ ⊤) ^ Nat.card ↥E * Nat.card H =
        Nat.card ↥(fixedSubgroup φ E) ^ Nat.card ↥E * Nat.card ↥(fixedSubgroup φ U) := by
  suffices key : ∀ n : ℕ, ∀ (H : Type u) [Group H] [Finite H] [Group.IsSolvable H]
      (φ : L →* MulAut H),
      Nat.Coprime (Nat.card L) (Nat.card H) → Nat.card H = n →
      Nat.card ↥(fixedSubgroup φ ⊤) ^ Nat.card ↥E * Nat.card H =
        Nat.card ↥(fixedSubgroup φ E) ^ Nat.card ↥E * Nat.card ↥(fixedSubgroup φ U) by
    intro H _ _ _ φ hcop
    exact key (Nat.card H) H φ hcop rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H _ _ _ φ hcop hcard
    rcases eq_or_ne (Nat.card H) 1 with h1 | h1
    · -- Base case: `H` is trivial, so every fixed-point count is `1`.
      have : Subsingleton H := Nat.card_eq_one_iff_unique.mp h1 |>.1
      have hsub : ∀ K : Subgroup H, Nat.card ↥K = 1 := fun K =>
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨1⟩⟩
      simp only [hsub, h1, one_pow, mul_one]
    · -- Inductive step: peel off an elementary-abelian `L`-invariant normal subgroup `N`.
      have : Nontrivial H :=
        Finite.one_lt_card_iff_nontrivial.mp (by have := Nat.card_pos (α := H); omega)
      obtain ⟨N, p, hp, hN_ne, hN_normal, hN_inv, hN_elab⟩ :=
        exists_aInvariant_normal_isElementaryAbelian (φ := φ)
      have : N.Normal := hN_normal
      -- Coprimality and the quotient action descend to `H / N`.
      have hcopN : Nat.Coprime (Nat.card L) (Nat.card (H ⧸ N)) :=
        hcop.coprime_dvd_right (Subgroup.card_dvd_of_surjective _ (QuotientGroup.mk'_surjective N))
      have hlt : Nat.card (H ⧸ N) < n := by
        rw [← hcard]; exact Subgroup.card_quotient_lt_of_ne_bot hN_ne
      -- Induction hypothesis on the quotient.
      have hIH := ih (Nat.card (H ⧸ N)) hlt (H ⧸ N) (quotMulAut hN_inv) hcopN rfl
      -- Per-factor identity on the elementary-abelian `N` (coprimality `|L| ⟂ |H|` available).
      have hfac := hpf H φ N hcop hN_inv ⟨p, hp, hN_elab⟩
      exact wielandt_step hN_inv hcop hfac hIH

end OddOrder.GroupTheory


