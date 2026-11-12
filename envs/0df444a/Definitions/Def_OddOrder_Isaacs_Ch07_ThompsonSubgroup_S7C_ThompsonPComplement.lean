-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
-- name    : OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7C_ThompsonPComplement
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:53:12.605812+00:00
-- url     : https://prove2.me/theorems/611e8f40-afec-4ddd-b992-8f97584c3db6
-- title:
--   Isaacs FGT Ch. 7 §7C: Thompson's normal $p$-complement theorem
-- statement:
--   Isaacs, *Finite Group Theory*, Chapter 7, §7C, pp. 215-219. This file contains the quotient identifications and the minimal-counterexample assembly for Thompson's normal $p$-complement theorem (Isaacs Theorem 7.1).
--
--   Main definitions: `HasThompsonLocalPComplements` (the Theorem 7.1 hypotheses at a $p$-subgroup), `HasThompsonPComplementHypothesis` (the two local hypotheses at every suitable subgroup), `IsBadNormalizerPSubgroup` (a nontrivial $p$-subgroup whose normalizer has no normal $p$-complement) and `normalizerPPart` (the order of a Sylow $p$-subgroup of $N_G(U)$).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7C_ThompsonPComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement

namespace OddOrder.Isaacs.Ch07

open scoped Pointwise

variable {G : Type*} [Group G]

section LocalHypothesisTransport

/-- **Isaacs Theorem 7.1 hypotheses at a `p`-subgroup.**

Both the centralizer of the ambient copy of `Z(P)` and the normalizer of `J(P)`
have normal `p`-complements.  The theorem applies this condition to Sylow
subgroups; accepting an arbitrary subgroup makes its transport API reusable in
the minimum-counterexample argument. -/
def HasThompsonLocalPComplements (p : ℕ) (P : Subgroup G) : Prop :=
  OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.centralizer
        (((Subgroup.center ↥P).map P.subtype : Subgroup G) : Set G)) ∧
    OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer ((Subgroup.thompsonJ P p : Subgroup G) : Set G))

/-- The intrinsic form of the two local hypotheses in Isaacs Theorem 7.1:
they hold at every Sylow `p`-subgroup. -/
def HasThompsonPComplementHypothesis (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ P : Sylow p G, HasThompsonLocalPComplements p (P : Subgroup G)

end LocalHypothesisTransport

section MinimalCounterexampleStepOne

/-- A nontrivial `p`-subgroup whose normalizer has no normal `p`-complement. -/
def IsBadNormalizerPSubgroup (p : ℕ) (U : Subgroup G) : Prop :=
  U ≠ ⊥ ∧ IsPGroup p U ∧
    ¬ OddOrder.Isaacs.Ch05.HasNormalPComplement p
      ↥(Subgroup.normalizer (U : Set G))

/-- The order of a Sylow `p`-subgroup of `N_G(U)`, expressed intrinsically as
the `p`-part of `|N_G(U)|`. -/
noncomputable def normalizerPPart (p : ℕ) (U : Subgroup G) : ℕ :=
  p ^ (Nat.card ↥(Subgroup.normalizer (U : Set G))).factorization p

end MinimalCounterexampleStepOne

end OddOrder.Isaacs.Ch07


