-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_TwoFamilies
-- name    : OddOrder_Peterfalvi_S09_NonexistenceCertain_TwoFamilies
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:43:41.786564+00:00
-- url     : https://prove2.me/theorems/b52c950b-afbe-4ed4-abd7-8a66072a5b91
-- title:
--   Peterfalvi (7.9): two-family non-orthogonality and orthogonal integer decomposition
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §7, (7.9) and (7.10): the non-orthogonality of two coherence setups, and the Frobenius-family hypothesis.
--
--   Main definitions: `Hypothesis79` (the (7.9) hypothesis interface, two instances of the (7.8) setup), `firstZetaImage` and `secondZetaImage` (images of the distinguished $\zeta$'s), `conclusion` (the two cross inner products cannot both vanish) and `FrobeniusFamily` (the (7.10) hypothesis, a family of $k$ Frobenius subgroups of $G$).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_NonexistenceCertain/TwoFamilies.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/TwoFamilies.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_CoherenceFormula

namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

section Section_7_9

/-- **Peterfalvi (7.9) hypothesis interface.**  Two instances of the (7.8)
coherence/norm setup over the same odd-order group, with disjoint Dade supports
`A₁^{τ₁}` and `A₂^{τ₂}` as in Hypothesis (7.4) for `I = {1,2}`. -/
structure Hypothesis79 (G : Type*) [Group G] [Fintype G]
    (A₁ : Set G) (L₁ : Subgroup G) [Fintype L₁]
    [Invertible (Nat.card L₁ : ℂ)]
    (A₂ : Set G) (L₂ : Subgroup G) [Fintype L₂]
    [Invertible (Nat.card L₂ : ℂ)]
    [Invertible (Nat.card G : ℂ)] where
  /-- The ambient group has odd order. -/
  odd_card : Odd (Nat.card G)
  /-- The first coherent normal-subgroup setup. -/
  first : Hypothesis78 G A₁ L₁
  /-- The second coherent normal-subgroup setup. -/
  second : Hypothesis78 G A₂ L₂
  /-- The Dade supports `A₁^{τ₁}` and `A₂^{τ₂}` are disjoint. -/
  dadeSupport_disjoint :
    Disjoint first.hyp76.hyp71.hyp.dadeSupport second.hyp76.hyp71.hyp.dadeSupport

namespace Hypothesis79

variable {G : Type*} [Group G] [Fintype G]

variable {A₁ : Set G} {L₁ : Subgroup G} [Fintype L₁]

variable [Invertible (Nat.card L₁ : ℂ)]

variable {A₂ : Set G} {L₂ : Subgroup G} [Fintype L₂]

variable [Invertible (Nat.card L₂ : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- The image `ζ₁^{ν₁}` of the distinguished first `ζ`. -/
noncomputable def firstZetaImage (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    ClassFunction G ℂ :=
  H79.first.nu (H79.first.hyp76.zeta H79.first.zetaDistinct)

/-- The image `ζ₂^{ν₂}` of the distinguished second `ζ`. -/
noncomputable def secondZetaImage (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) :
    ClassFunction G ℂ :=
  H79.second.nu (H79.second.hyp76.zeta H79.second.zetaDistinct)

/-- **Peterfalvi (7.9) conclusion.**  The two cross inner products cannot both
vanish: `(β₁, ζ₂^{ν₂}) ≠ 0` or `(β₂, ζ₁^{ν₁}) ≠ 0`. -/
def conclusion (H79 : Hypothesis79 G A₁ L₁ A₂ L₂) : Prop :=
  ClassFunction.inner H79.first.beta H79.secondZetaImage ≠ 0 ∨
    ClassFunction.inner H79.second.beta H79.firstZetaImage ≠ 0

end Hypothesis79

end Section_7_9

/-- **Peterfalvi (7.10) hypothesis.** A family of `k` Frobenius subgroups of `G`
whose kernels are pairwise-coprime TI-subsets.

This bundles conditions (a)-(c) of (7.10):
* `(a)` each `L i` is a Frobenius group with kernel `H i` (`isFrobenius`);
* `(b)` `H i` is `L i`-normal with `L i = N_G(H i)`, and `(H i)^#` is a TI-subset
  of `G` with normalizer `L i` (`normalizer_eq`, `isTI`);
* `(c)` the kernel orders `|H i|` are pairwise coprime (`coprime_kernel`),
together with `k ≥ 2` (`two_le`).  Condition (d) — the definition of `G₀` — is
recorded separately as `FrobeniusFamily.G0`. -/
structure FrobeniusFamily (G : Type*) [Group G] (k : ℕ) where
  /-- The Frobenius subgroups `L_i ≤ G`. -/
  L : Fin k → Subgroup G
  /-- The Frobenius kernels `H_i ⊴ L_i`. -/
  H : Fin k → Subgroup G
  /-- (7.10): the family has at least two members. -/
  two_le : 2 ≤ k
  /-- Each kernel sits inside its host. -/
  kernel_le : ∀ i, H i ≤ L i
  /-- (7.10)(a): each `L_i` is a Frobenius group with kernel `H_i`, for some
  Frobenius complement `C`. -/
  isFrobenius : ∀ i, ∃ C : Subgroup ↥(L i),
    IsFrobeniusGroup ↥(L i) ((H i).subgroupOf (L i)) C
  /-- (7.10)(b), host part: `L_i` is the normalizer of `H_i` in `G`. -/
  normalizer_eq : ∀ i, L i = Subgroup.normalizer (H i : Set G)
  /-- (7.10)(b), TI part: `H_i^#` is a TI-subset of `G` with normalizer `L_i`. -/
  isTI : ∀ i, IsTISubset ((H i : Set G) \ {1}) (L i)
  /-- (7.10)(c): the kernel orders are pairwise coprime. -/
  coprime_kernel : ∀ ⦃i j⦄, i ≠ j → Nat.Coprime (Nat.card (H i)) (Nat.card (H j))

end OddOrder.Peterfalvi.S09


