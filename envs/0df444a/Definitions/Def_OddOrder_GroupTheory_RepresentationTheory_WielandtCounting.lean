-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_WielandtCounting
-- name    : OddOrder_GroupTheory_RepresentationTheory_WielandtCounting
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:32.264562+00:00
-- url     : https://prove2.me/theorems/db4063f4-ec46-465b-815c-5422ba6cfdfe
-- title:
--   Wielandt's fixed-point formula: the module-level counting (Peterfalvi (9.1))
-- statement:
--   Builds the elementary-abelian (vector-space) core of Peterfalvi (9.1), Wielandt's fixed-point formula. The eventual target is $|C_H(UE)|^{|E|}\cdot|H|=|C_H(E)|^{|E|}\cdot|C_H(U)|$ for a Frobenius group $L=U\rtimes E$ acting coprimely on $H$; this file does the module-level counting. It consists of lemmas only.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/WielandtCounting.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/WielandtCounting.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OddOrder.GroupTheory.WielandtCounting

open Module Representation

variable {k : Type*} [Field k] {G : Type*} [Group G]

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- **Coprime decomposition, dimension form.**  When `|G|` is invertible in `k`, the averaging
map `averageMap ρ` is a projection onto the invariants `V^G`, so `V = V^G ⊕ [V,G]` with
`[V,G] = ker (averageMap ρ)`.  Taking dimensions:
`dim V^G + dim [V,G] = dim V`. -/
theorem finrank_invariants_add_finrank_ker_averageMap
    (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)]
    [FiniteDimensional k V] :
    finrank k ρ.invariants + finrank k (LinearMap.ker ρ.averageMap) = finrank k V := by
  have hrange : LinearMap.range ρ.averageMap = ρ.invariants := (isProj_averageMap ρ).range
  rw [← hrange, LinearMap.finrank_range_add_finrank_ker]

/-- Explicit form of the averaging projection: `averageMap ρ v = ⅟|G| • ∑_g ρ g v`. -/
theorem averageMap_apply (ρ : Representation k G V) [Fintype G]
    [Invertible (Fintype.card G : k)] (v : V) :
    ρ.averageMap v = ⅟(Fintype.card G : k) • ∑ g : G, ρ g v := by
  simp only [averageMap, GroupAlgebra.average, map_smul, map_sum, MonoidAlgebra.of_apply,
    asAlgebraHom_single_one, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]

/-- The two summands of the coprime decomposition meet trivially: a `G`-invariant vector lying
in the augmentation submodule `[V,G] = ker (averageMap ρ)` is zero.  (This is `[V,G]^G = 0`, used
to collapse the el-ab identity to the kernel-FPF case.) -/
theorem eq_zero_of_mem_ker_averageMap_of_mem_invariants
    (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)]
    {v : V} (hker : v ∈ LinearMap.ker ρ.averageMap) (hinv : v ∈ ρ.invariants) : v = 0 := by
  rw [LinearMap.mem_ker] at hker
  exact (averageMap_id ρ v hinv).symm.trans hker

/-- The coprime decomposition `V = V^G ⊕ [V,G]`: the invariants and the augmentation submodule
`[V,G] = ker (averageMap ρ)` are complementary. -/
theorem isCompl_invariants_ker_averageMap
    (ρ : Representation k G V) [Fintype G] [Invertible (Fintype.card G : k)] :
    IsCompl ρ.invariants (LinearMap.ker ρ.averageMap) :=
  (isProj_averageMap ρ).isCompl

/-- If subgroups `H₁, H₂` generate `G` (`H₁ ⊔ H₂ = ⊤`), then the invariants of `ρ` are the
intersection of the invariants of the restrictions `ρ|_{H₁}` and `ρ|_{H₂}`: being fixed by a
generating set forces being fixed by the whole group.  Specialised to `⟨U,E⟩ = L`, this is
`V^{UE} = V^U ⊓ V^E`. -/
theorem invariants_eq_inf_of_sup_eq_top (ρ : Representation k G V) {H₁ H₂ : Subgroup G}
    (hsup : H₁ ⊔ H₂ = ⊤) :
    ρ.invariants = invariants (ρ.comp H₁.subtype) ⊓ invariants (ρ.comp H₂.subtype) := by
  apply le_antisymm
  · exact le_inf (fun v hv s => hv _) (fun v hv s => hv _)
  · intro v hv
    rw [Submodule.mem_inf, mem_invariants, mem_invariants] at hv
    obtain ⟨hv1, hv2⟩ := hv
    -- the stabiliser `{g | ρ g v = v}` is a subgroup containing `H₁` and `H₂`, hence `⊤`.
    let S : Subgroup G :=
      { carrier := {g | ρ g v = v}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq] at *
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_ofPred_eq] at *
          have h := congrArg (ρ a⁻¹) ha
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] at h
          exact h.symm }
    have hStop : S = ⊤ :=
      top_le_iff.mp (hsup ▸ sup_le (fun g hg => hv1 ⟨g, hg⟩) (fun g hg => hv2 ⟨g, hg⟩))
    exact fun g => (hStop ▸ Subgroup.mem_top g : g ∈ S)

/-- **Fixed points split along an invariant decomposition.**  If `V = A ⊕ B` with both `A`
and `B` stable under every `ρ g`, then the `G`-invariants decompose accordingly:
`dim V^G = dim (A ⊓ V^G) + dim (B ⊓ V^G)`.  (Used with `A = V^U`, `B = [V,U]`, `G = E` to
get `dim V^E = dim V^{UE} + dim ([V,U])^E` in the el-ab identity (⋆).) -/
theorem finrank_invariants_eq_of_isCompl_invariant
    (ρ : Representation k G V) [FiniteDimensional k V]
    {A B : Submodule k V} (hAB : IsCompl A B)
    (hA : ∀ g : G, ∀ a ∈ A, ρ g a ∈ A) (hB : ∀ g : G, ∀ b ∈ B, ρ g b ∈ B) :
    finrank k ρ.invariants =
      finrank k ↥(A ⊓ ρ.invariants) + finrank k ↥(B ⊓ ρ.invariants) := by
  have hdisj : (A ⊓ ρ.invariants) ⊓ (B ⊓ ρ.invariants) = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf inf_le_left inf_le_left) hAB.disjoint.le_bot)
  have hsup : (A ⊓ ρ.invariants) ⊔ (B ⊓ ρ.invariants) = ρ.invariants := by
    refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (codisjoint_iff.mp hAB.codisjoint ▸
      Submodule.mem_top (x := v))
    -- `a` and `b` are each `G`-fixed, by uniqueness of the `A ⊕ B` decomposition.
    have hainv : a ∈ ρ.invariants := by
      rw [mem_invariants]
      intro g
      have key : ρ g a + ρ g b = a + b := by rw [← map_add]; exact hv g
      have hba : ρ g a - a = b - ρ g b :=
        sub_eq_sub_iff_add_eq_add.mpr (key.trans (add_comm a b))
      have hmemB : ρ g a - a ∈ B := by rw [hba]; exact B.sub_mem hb (hB g b hb)
      have hzero : ρ g a - a = 0 := by
        rw [← Submodule.mem_bot k, ← hAB.inf_eq_bot]
        exact ⟨A.sub_mem (hA g a ha) ha, hmemB⟩
      exact sub_eq_zero.mp hzero
    have hbinv : b ∈ ρ.invariants := by
      have h := ρ.invariants.sub_mem hv hainv
      rwa [add_sub_cancel_left] at h
    exact Submodule.mem_sup.mpr ⟨a, ⟨ha, hainv⟩, b, ⟨hb, hbinv⟩, rfl⟩
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq
    (A ⊓ ρ.invariants) (B ⊓ ρ.invariants)
  rw [hsup, hdisj, finrank_bot, add_zero] at hrank
  exact hrank

/-- For a normal subgroup `U ◁ G`, the averaging projection over `U` commutes with `ρ g` for any
`g : G`: conjugation by `g` permutes `U`, fixing `∑_{u∈U} ρ u`. -/
theorem ρ_comp_averageMap_comm (ρ : Representation k G V) (U : Subgroup G) [U.Normal]
    [Fintype U] [Invertible (Fintype.card U : k)] (g : G) (v : V) :
    ρ g (averageMap (ρ.comp U.subtype) v) = averageMap (ρ.comp U.subtype) (ρ g v) := by
  rw [averageMap_apply, averageMap_apply, map_smul]
  congr 1
  rw [map_sum]
  refine Fintype.sum_equiv (MulAut.conjNormal g : MulAut U).toEquiv _ _ (fun u => ?_)
  change ρ g (ρ (u : G) v) = ρ (↑(MulAut.conjNormal g u) : G) (ρ g v)
  rw [MulAut.conjNormal_apply]
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- For `U ◁ G`, the augmentation submodule `[V,U] = ker (averageMap ρ|_U)` is `ρ g`-invariant
for every `g : G`. -/
theorem ker_averageMap_comp_invariant (ρ : Representation k G V) (U : Subgroup G) [U.Normal]
    [Fintype U] [Invertible (Fintype.card U : k)] (g : G) :
    ∀ x ∈ LinearMap.ker (averageMap (ρ.comp U.subtype)),
      ρ g x ∈ LinearMap.ker (averageMap (ρ.comp U.subtype)) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← ρ_comp_averageMap_comm ρ U g x, hx, map_zero]

/-- **The elementary-abelian identity (⋆)** for Peterfalvi (9.1), in dimension form, modulo the
kernel-FPF fact (†) supplied as `htag`.  For `ρ` a representation of `G = U ⋊ E` (with `U ◁ G`,
`⟨U,E⟩ = G`) over a field with `|U|` invertible:
`|E|·dim V^{UE} + dim V = |E|·dim V^E + dim V^U`,
provided `dim [V,U] = |E|·dim ([V,U] ⊓ V^E)`  (this is (†), discharged later via Maschke +
the modular Brauer permutation lemma).  Here `V^{UE} = ρ.invariants` since `⟨U,E⟩ = G`. -/
theorem finrank_elab_identity (ρ : Representation k G V) (U E : Subgroup G) [U.Normal]
    [Fintype U] [Fintype E] [Invertible (Fintype.card U : k)] [FiniteDimensional k V]
    (hUE : U ⊔ E = ⊤)
    (htag : finrank k ↥(LinearMap.ker (averageMap (ρ.comp U.subtype))) =
      Fintype.card E * finrank k ↥(LinearMap.ker (averageMap (ρ.comp U.subtype)) ⊓
        invariants (ρ.comp E.subtype))) :
    Fintype.card E * finrank k ↥ρ.invariants + finrank k V =
      Fintype.card E * finrank k ↥(invariants (ρ.comp E.subtype)) +
        finrank k ↥(invariants (ρ.comp U.subtype)) := by
  have hdaf := finrank_invariants_add_finrank_ker_averageMap (ρ.comp U.subtype)
  have hb : finrank k ↥(invariants (ρ.comp E.subtype)) =
      finrank k ↥(invariants (ρ.comp U.subtype) ⊓ invariants (ρ.comp E.subtype)) +
      finrank k ↥(LinearMap.ker (averageMap (ρ.comp U.subtype)) ⊓
        invariants (ρ.comp E.subtype)) := by
    refine finrank_invariants_eq_of_isCompl_invariant (ρ.comp E.subtype)
      (isCompl_invariants_ker_averageMap (ρ.comp U.subtype)) ?_ ?_
    · intro e x hx
      have := le_comap_invariants ρ U (e : G) hx
      rwa [Submodule.mem_comap] at this
    · exact fun e x hx => ker_averageMap_comp_invariant ρ U (e : G) x hx
  rw [invariants_eq_inf_of_sup_eq_top ρ hUE, hb, ← hdaf, htag]
  ring

end OddOrder.GroupTheory.WielandtCounting


