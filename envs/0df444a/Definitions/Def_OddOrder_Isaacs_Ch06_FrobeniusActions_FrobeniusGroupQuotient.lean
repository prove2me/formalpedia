-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroupQuotient
-- name    : OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroupQuotient
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:35:18.133811+00:00
-- url     : https://prove2.me/theorems/4bf9ba0b-4c8e-4881-9824-62e5a9fea9fd
-- title:
--   Transport of Frobenius groups across isomorphisms
-- statement:
--   A group isomorphism $e:G\simeq H$ carries the whole Frobenius structure of $G=N\rtimes A$ (`IsFrobeniusGroup G N A`) onto its image: `IsFrobeniusGroup H (N.map e) (A.map e)`, with kernel $e(N)$ and complement $e(A)$. Every defining datum (normality, the complement relation, and so on) transports.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroupQuotient.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroupQuotient.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup

namespace OddOrder.Isaacs.Ch06

variable {G H : Type*} [Group G] [Group H]

/-- **Frobenius groups transport across isomorphisms.**  If `G = N ⋊ A` is a Frobenius group
(`IsFrobeniusGroup G N A`) and `e : G ≃* H` is a group isomorphism, then `H = e(N) ⋊ e(A)` is a
Frobenius group with kernel `e(N)` and complement `e(A)`.

Each Frobenius datum is carried along `e`: normality of `e(N)` (image of a normal subgroup under a
surjective hom), the complement relation (`e` is a bounded-lattice isomorphism on subgroups, so it
preserves `⊓ = ⊥` and `⊔ = ⊤`), the nontriviality of the two parts (an isomorphism sends `⊥` to
`⊥`), and the conjugation-Frobenius condition (transported pointwise using that `e` is a
homomorphism: `e a · e n · (e a)⁻¹ = e (a n a⁻¹)`). -/
theorem isFrobeniusGroup_map_equiv {N A : Subgroup G} (h : IsFrobeniusGroup G N A) (e : G ≃* H) :
    IsFrobeniusGroup H (N.map e.toMonoidHom) (A.map e.toMonoidHom) := by
  have := h.isNormal
  refine ⟨?isNormal, ?isComplement, ?ne_bot_kernel, ?ne_bot_complement, ?conj⟩
  case isNormal =>
    -- image of a normal subgroup under the *surjective* `e`.
    exact h.isNormal.map e.toMonoidHom e.surjective
  case isComplement =>
    -- `e(N)` and `e(A)` are complements: disjoint image + product-is-top.
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · -- `e(N) ⊓ e(A) = ⊥`, from `N ⊓ A = ⊥` via `map_inf` (`e` injective).
      rw [disjoint_iff, ← Subgroup.map_inf _ _ e.toMonoidHom e.injective,
        disjoint_iff.mp h.isComplement.disjoint, Subgroup.map_bot]
    · -- `e(N) * e(A) = ⊤` (as sets), from `N ⊔ A = ⊤` via `map_sup` + `e` surjective.
      have hsup : N.map e.toMonoidHom ⊔ A.map e.toMonoidHom = ⊤ := by
        rw [← Subgroup.map_sup, h.isComplement.sup_eq_top, ← MonoidHom.range_eq_map,
          MonoidHom.range_eq_top.mpr e.surjective]
      have : (N.map e.toMonoidHom).Normal := h.isNormal.map e.toMonoidHom e.surjective
      have hmul := Subgroup.normal_mul (N.map e.toMonoidHom) (A.map e.toMonoidHom)
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  case ne_bot_kernel =>
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
    exact h.ne_bot_kernel
  case ne_bot_complement =>
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
    exact h.ne_bot_complement
  case conj =>
    -- transport `a·n·a⁻¹ ≠ n` pointwise: preimages under `e` witness a violation upstream.
    intro a haA ha n hnN hn hfix
    -- `a = e a₀`, `n = e n₀` with `a₀ ∈ A`, `n₀ ∈ N`.
    obtain ⟨a₀, ha₀A, rfl⟩ := Subgroup.mem_map.mp haA
    obtain ⟨n₀, hn₀N, rfl⟩ := Subgroup.mem_map.mp hnN
    have ha₀ : a₀ ≠ 1 := fun h1 => ha (by rw [h1, map_one])
    have hn₀ : n₀ ≠ 1 := fun h1 => hn (by rw [h1, map_one])
    -- `e (a₀ n₀ a₀⁻¹) = e n₀` ⇒ `a₀ n₀ a₀⁻¹ = n₀` (injectivity), contradicting Frobenius on `G`.
    apply h.conj_frobenius a₀ ha₀A ha₀ n₀ hn₀N hn₀
    apply e.injective
    rw [map_mul, map_mul, map_inv]
    exact hfix

/-- **Frobenius groups transport across isomorphisms** (dot-notation form of
`isFrobeniusGroup_map_equiv`): `h.mapEquiv e : IsFrobeniusGroup H (e(N)) (e(A))`. -/
theorem IsFrobeniusGroup.mapEquiv {N A : Subgroup G} (h : IsFrobeniusGroup G N A) (e : G ≃* H) :
    IsFrobeniusGroup H (N.map e.toMonoidHom) (A.map e.toMonoidHom) :=
  isFrobeniusGroup_map_equiv h e

end OddOrder.Isaacs.Ch06


