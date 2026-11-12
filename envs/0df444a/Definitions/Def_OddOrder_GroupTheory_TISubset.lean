-- Prove2me | Definitions.Def_OddOrder_GroupTheory_TISubset
-- name    : OddOrder_GroupTheory_TISubset
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:09.559998+00:00
-- url     : https://prove2.me/theorems/ee005fdf-c758-447a-933a-7499223e2cbd
-- title:
--   Trivial-intersection (TI) subsets
-- statement:
--   Formalizes TI-subsets (trivial intersection subsets) of a finite group, a concept used throughout Peterfalvi, *Character Theory for the Odd Order Theorem*, §4–§8 and §11–§16. A subset $A\subseteq G$ is TI when distinct conjugates meet trivially: whenever $A^g\cap A\ne\emptyset$, $g$ normalizes $A$. The normalizer is taken as a parameter $L$, matching Peterfalvi's typical set-up $A=H\setminus\{1\}$ with $L=N_G(H)$.
--
--   Main definitions: `IsTISubset A L` (a TI-subset with normalizer-bound $L$) and `IsTI` (a subgroup $H$ is TI when $H\setminus\{1\}$ is a TI-subset).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/TISubset.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/TISubset.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- A subset `A ⊆ G` is a **TI-subset** with normalizer-bound `L ≤ G` iff every
element `g : G` that produces an overlap between `A` and the conjugate
`g · A · g⁻¹` must already lie in `L`.

Formally: `∀ g : G, (∃ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ L`.

The intended use is `L = N_G(A)`, in which case the TI condition states that
distinct conjugates of `A` (by elements outside `L`) are mutually disjoint.

Peterfalvi §4-§8 全節共有の predicate. -/
def IsTISubset (A : Set G) (L : Subgroup G) : Prop :=
  ∀ g : G, (∃ a ∈ A, g * a * g⁻¹ ∈ A) → g ∈ L

namespace IsTISubset

variable {A : Set G} {L : Subgroup G}

/-- 部分集合に絞っても TI: `A' ⊆ A` なら `A'` も同じ `L` で TI. -/
theorem subset {A' : Set G} (hA : IsTISubset A L) (hA' : A' ⊆ A) :
    IsTISubset A' L :=
  fun g ⟨a, ha', hga'⟩ => hA g ⟨a, hA' ha', hA' hga'⟩

/-- もし `A` が `L`-bound の TI-subset で `x ∈ A` なら, `x` の `G`-中心化群全体が `L`
に収まる: `c ∈ C_G(x)` は `x = c x c⁻¹ ∈ A` を固定するので, TI 条件が `c ∈ L` を強制
する. BG Thm II の "`C_G(x) ⊄ M` ⇒ `x ∈ M_σ`" 論法で使う汎用 infra. -/
theorem centralizer_le (hA : IsTISubset A L) {x : G} (hx : x ∈ A) :
    Subgroup.centralizer ({x} : Set G) ≤ L := by
  intro c hc
  have hcomm : x * c = c * x :=
    Subgroup.mem_centralizer_iff.mp hc x (Set.mem_singleton x)
  have hfix : c * x * c⁻¹ ∈ A := by
    have hxx : c * x * c⁻¹ = x := by rw [← hcomm, mul_inv_cancel_right]
    rwa [hxx]
  exact hA c ⟨x, hx, hfix⟩

/-- **TI transport along an `M`-conjugacy saturation.**  If `T` is a TI-subset with
normalizer-bound `Z ≤ M`, and every element of `A` is `M`-conjugate to an element of `T`
(i.e. `A` lies inside the `M`-conjugacy saturation `⋃_{m ∈ M} m·T·m⁻¹`), then `A` is itself a
TI-subset with normalizer-bound `M`.

This is the abstract content behind BG Theorem B(5) and C(9): the sets `A(M) − M_σ` and
`A_0(M) − A(M)` are contained in `M`-conjugacy saturations of TI-sets (the `σ`-singular pieces,
resp. `Ẑ = Z − (K ∪ K*)`), so they inherit TI-ness with normalizer `M`.

Proof: for `a, g·a·g⁻¹ ∈ A`, write `a = m₁·t₁·m₁⁻¹` and `g·a·g⁻¹ = m₂·t₂·m₂⁻¹` with `mᵢ ∈ M`,
`tᵢ ∈ T`.  Then `h := m₂⁻¹·g·m₁` conjugates `t₁` to `t₂ ∈ T`, so `h ∈ Z ≤ M` by the TI property
of `T`, whence `g = m₂·h·m₁⁻¹ ∈ M`. -/
theorem of_subset_conj_of_isTISubset {T : Set G} {Z M : Subgroup G}
    (hT : IsTISubset T Z) (hZM : Z ≤ M)
    (hsub : ∀ a ∈ A, ∃ m ∈ M, ∃ t ∈ T, a = m * t * m⁻¹) :
    IsTISubset A M := by
  intro g ⟨a, ha, hga⟩
  obtain ⟨m₁, hm₁, t₁, ht₁, ha₁⟩ := hsub a ha
  obtain ⟨m₂, hm₂, t₂, ht₂, ha₂⟩ := hsub _ hga
  -- `h := m₂⁻¹ * g * m₁` conjugates `t₁` to `t₂ ∈ T`.
  have hconj : (m₂⁻¹ * g * m₁) * t₁ * (m₂⁻¹ * g * m₁)⁻¹ = t₂ := by
    have e : (m₂⁻¹ * g * m₁) * t₁ * (m₂⁻¹ * g * m₁)⁻¹
        = m₂⁻¹ * (g * (m₁ * t₁ * m₁⁻¹) * g⁻¹) * m₂ := by group
    rw [e, ← ha₁, ha₂]; group
  -- The TI property of `T` then places `h` in `Z ≤ M`, and `g = m₂ · h · m₁⁻¹ ∈ M`.
  have hhZ : m₂⁻¹ * g * m₁ ∈ Z := hT _ ⟨t₁, ht₁, by rw [hconj]; exact ht₂⟩
  have hgM : m₂ * (m₂⁻¹ * g * m₁) * m₁⁻¹ ∈ M :=
    M.mul_mem (M.mul_mem hm₂ (hZM hhZ)) (M.inv_mem hm₁)
  have hg_eq : m₂ * (m₂⁻¹ * g * m₁) * m₁⁻¹ = g := by group
  rwa [hg_eq] at hgM

end IsTISubset

end OddOrder.GroupTheory

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup `H ≤ G` is **TI** iff its non-identity part `H \ {1}` is a
TI-subset (in the `OddOrder.GroupTheory.IsTISubset` sense) relative to the
normalizer `N_G(H)`.

これは古典的な「Trivial Intersection 部分群」の概念: 異なる共役
`g H g⁻¹` (g ∉ N_G(H)) は `H` と `{1}` のみで交わる.

Peterfalvi §8 (6.7), (6.8) で `P` Sylow `p`-部分群 + `L = N_G(P)`, `P^#` TI
の形で多用. -/
def IsTI (H : Subgroup G) : Prop :=
  OddOrder.GroupTheory.IsTISubset ((H : Set G) \ {1}) (Subgroup.normalizer (H : Set G))

end Subgroup


