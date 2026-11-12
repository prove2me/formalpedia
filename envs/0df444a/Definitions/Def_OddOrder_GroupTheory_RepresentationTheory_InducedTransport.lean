-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedTransport
-- name    : OddOrder_GroupTheory_RepresentationTheory_InducedTransport
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:08:05.414394+00:00
-- url     : https://prove2.me/theorems/ef867643-4273-4ff4-bb67-7aefc326bb4d
-- title:
--   Transport lemmas for induced class functions
-- statement:
--   Generic group-theoretic transport lemmas for induced class functions: the constituent decomposition of an induced character, $\mathrm{Ind}^M_N\varphi=\sum_{\theta\in\mathrm{Irr}\,M}\langle\varphi,\mathrm{Res}_N\theta\rangle\theta$ (Fourier expansion plus Frobenius reciprocity), and invariance of the class-function inner product under pullback along a group isomorphism.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/InducedTransport.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/InducedTransport.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality

namespace OddOrder.RepresentationTheory

/-- **Constituent decomposition of an induced character**.  For any class function `φ` of a
subgroup `N ≤ M`, the induced character expands in the `Irr M` basis with coefficients the
Frobenius multiplicities: `Ind^M_N φ = ∑_{θ ∈ Irr M} ⟨φ, Res_N θ⟩ • θ`.  Fourier expansion
(`sum_inner_irreducibleCharacter_smul`) plus Frobenius reciprocity
(`inner_induce_eq_inner_restrict`) on each coefficient. -/
theorem induce_eq_sum_inner_restrict_smul {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {N : Subgroup M} [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (φ : ClassFunction ↥N ℂ) :
    ClassFunction.induce N φ
      = ∑ θ : IrreducibleCharacter M,
        ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
          • (θ : ClassFunction M ℂ) := by
  conv_lhs => rw [← sum_inner_irreducibleCharacter_smul (ClassFunction.induce N φ)]
  exact Finset.sum_congr rfl
    (fun θ _ => by rw [ClassFunction.inner_induce_eq_inner_restrict])

/-- **The class-function inner product is preserved by pullback along a group isomorphism.**  For a
`MulEquiv e : H ≃* G` and `a, b ∈ CF(G)`, `⟨a ∘ e, b ∘ e⟩_H = ⟨a, b⟩_G`: reindexing the inner sum
`∑_{h ∈ H} a(e h)·\overline{b(e h)} = ∑_{g ∈ G} a(g)·\overline{b(g)}` along the bijection `e` (and
`|H| = |G|`). -/
theorem inner_compHom_of_mulEquiv {G' H' : Type*} [Group G'] [Group H'] [Fintype G'] [Fintype H']
    [Invertible (Nat.card G' : ℂ)] [Invertible (Nat.card H' : ℂ)]
    (e : H' ≃* G') (a b : ClassFunction G' ℂ) :
    ClassFunction.inner (ClassFunction.compHom e.toMonoidHom a)
        (ClassFunction.compHom e.toMonoidHom b) = ClassFunction.inner a b := by
  have hcard : (Nat.card H' : ℂ) = (Nat.card G' : ℂ) := by rw [Nat.card_congr e.toEquiv]
  have hsum : (∑ h : H', (ClassFunction.compHom e.toMonoidHom a) h *
        star ((ClassFunction.compHom e.toMonoidHom b) h))
      = ∑ g : G', a g * star (b g) := by
    simp only [ClassFunction.compHom_apply]
    exact Equiv.sum_comp e.toEquiv (fun g => a g * star (b g))
  have hinv : ⅟(Nat.card H' : ℂ) = ⅟(Nat.card G' : ℂ) :=
    invOf_eq_right_inv (by rw [hcard, mul_invOf_self])
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum,
    ClassFunction.innerSum, ClassFunction.innerSum, hsum, hinv]

/-- **Induction in stages**.  For nested subgroups `K ≤ H ≤ M`, inducing a class function `ψ` of
`K` to `M` in one step agrees with inducing first to `H` (of `ψ` transported to `K.subgroupOf H`)
and then to `M`: `Ind^M_H (Ind^H_{K.subgroupOf H} (ψ ∘ e)) = Ind^M_K ψ`, where
`e : K.subgroupOf H ≃* K`.

Proved by completeness (`classFunction_eq_zero_of_orthogonal`): for every `χ ∈ Irr M`, double
Frobenius reciprocity reduces `⟨LHS, χ⟩` to `⟨ψ∘e, Res_{K.subgroupOf H}(Res_H χ)⟩`, the restriction
`Res_{K.subgroupOf H}(Res_H χ) = (Res_K χ)∘e` is the same `M`-value, and `inner_compHom_of_mulEquiv`
strips the transport to give `⟨ψ, Res_K χ⟩ = ⟨Ind^M_K ψ, χ⟩` (Frobenius). -/
theorem induce_induce_subgroupOf {M : Type*} [Group M] [Fintype M] [Invertible (Nat.card M : ℂ)]
    {K H : Subgroup M} (hKH : K ≤ H)
    [Fintype ↥H] [Finite ↥K] [Finite ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (ψ : ClassFunction ↥K ℂ) :
    ClassFunction.induce H (ClassFunction.induce (K.subgroupOf H)
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom ψ))
      = ClassFunction.induce K ψ := by
  have : Fintype ↥K := Fintype.ofFinite _
  have : Fintype ↥(K.subgroupOf H) := Fintype.ofFinite _
  set e := Subgroup.subgroupOfEquivOfLe hKH with he
  have hres : ∀ χ : IrreducibleCharacter M,
      ClassFunction.restrict (K.subgroupOf H)
          (ClassFunction.restrict H (χ : ClassFunction M ℂ))
        = ClassFunction.compHom e.toMonoidHom (ClassFunction.restrict K (χ : ClassFunction M ℂ)) :=
            by
    intro χ; ext y
    rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply, ClassFunction.compHom_apply,
      ClassFunction.restrict_apply]
    congr 1
  refine sub_eq_zero.mp (classFunction_eq_zero_of_orthogonal _ (fun χ => ?_))
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_induce_eq_inner_restrict, hres χ, inner_compHom_of_mulEquiv,
    ClassFunction.inner_induce_eq_inner_restrict, sub_self]

end OddOrder.RepresentationTheory


