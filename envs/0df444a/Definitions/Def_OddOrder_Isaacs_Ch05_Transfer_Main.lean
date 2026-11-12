-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
-- name    : OddOrder_Isaacs_Ch05_Transfer_Main
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:28:58.919244+00:00
-- url     : https://prove2.me/theorems/77f25a83-0884-45ae-8a33-21c20ef83a9b
-- title:
--   Isaacs Ch. 5: Sylow subgroups controlling their own fusion (tail)
-- statement:
--   The tail of the Chapter 5 (Transfer) formalization of Isaacs, *Finite Group Theory*.
--
--   Declarations: `Sylow.ControlsOwnFusion` (a Sylow $p$-subgroup $P$ controls its own $G$-fusion: elements of $P$ conjugate in $G$ are conjugate by an element of $N_G(P)$) and `centralizer_subgroupOf_normalizer_normal` ($C_G(X)$ is normal in $N_G(X)$, as the kernel of the normalizer action).
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch05_Transfer/Main.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch05_Transfer/Main.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Nilpotent

open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- "Sylow `p`-subgroup `P` controls its own G-fusion": for any two elements `x, y ∈ P`
that are conjugate in `G`, they are already conjugate by some element of `P`.

Isaacs §5C-§5E で頻出. mathlib 未収載のため新規定義. -/
def _root_.Sylow.ControlsOwnFusion {p : ℕ} {G : Type*} [Group G] (P : Sylow p G) : Prop :=
  (P : Subgroup G).ControlsFusionIn (P : Subgroup G)

/-- **Isaacs Lem 5.27 part 1 (1 ⇒ 2, strong form)**: G が normal p-complement を持つなら,
任意の subgroup `H ≤ G` も normal p-complement を持つ.

`H` の p-complement は `N.subgroupOf H = N ⊓ H` viewed inside `H` (witness).

**証明** (Isaacs p.174): `N` は `G` で normal なので `N.subgroupOf H` は `H` で normal
(`Normal.subgroupOf`). Cardinality:

* 任意 Sylow `P₀ : Sylow p G` で `IsComplement' N P₀` ⇒ `N.index = |P₀| = p^v_p(|G|)`,
  `|N|` coprime to `p` (Sylow `not_dvd_index` + `IsComplement'.index_eq_card`).
* `(N.subgroupOf H).index ∣ N.index` (`relIndex_dvd_index_of_normal`) ⇒ p-power.
* `|N.subgroupOf H| = |M.map H.subtype| = |N ⊓ H| ∣ |N|` ⇒ coprime to `p`.
* 任意 Sylow `Q : Sylow p ↥H` で `|Q| = p^v_p(|H|)` (`Sylow.card_eq_multiplicity`).
* Lagrange + `Nat.factorization_mul` で `v_p(|H|) = a` (M.index = p^a の指数).
  ⇒ `|Q| = p^a = M.index`, よって `|N.subgroupOf H| * |Q| = |H|` + Coprime.
* `Subgroup.isComplement'_of_coprime` 適用. -/
theorem hasNormalPComplement_of_subgroup [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : HasNormalPComplement p G) (H : Subgroup G) :
    HasNormalPComplement p ↥H := by
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  have : N.Normal := hN_normal
  refine ⟨N.subgroupOf H, hN_normal.subgroupOf H, fun Q => ?_⟩
  set M : Subgroup ↥H := N.subgroupOf H with hM_def
  -- Get any Sylow P₀ in G
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p G))
  -- |P₀| = p^v_p(|G|)
  have hP₀_card : Nat.card ↥(P₀ : Subgroup G) = p ^ (Nat.card G).factorization p :=
    P₀.card_eq_multiplicity
  -- N.index = |P₀|
  have hN_idx_eq_P₀ : N.index = Nat.card ↥(P₀ : Subgroup G) :=
    (hN_compl P₀).symm.index_eq_card
  -- ¬ p ∣ |N|
  have h_p_ndvd_N : ¬ p ∣ Nat.card ↥N := by
    rw [← (hN_compl P₀).index_eq_card]; exact P₀.not_dvd_index
  -- |M| ∣ |N|: M ≃ N ⊓ H ≤ N via H.subtype
  have hM_card_dvd_N : Nat.card ↥M ∣ Nat.card ↥N := by
    have h_inj : Function.Injective (H.subtype : ↥H → G) := Subtype.coe_injective
    have h_card_eq : Nat.card ↥M = Nat.card ↥(M.map H.subtype) :=
      Nat.card_congr (Subgroup.equivMapOfInjective M H.subtype h_inj).toEquiv
    rw [h_card_eq, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  -- ¬ p ∣ |M|
  have h_p_ndvd_M : ¬ p ∣ Nat.card ↥M := fun h => h_p_ndvd_N (h.trans hM_card_dvd_N)
  -- M.index ∣ N.index (relIndex_dvd_index_of_normal)
  have hM_idx_dvd_Nidx : M.index ∣ N.index :=
    Subgroup.relIndex_dvd_index_of_normal N H
  -- M.index = p^a for some a ≤ v_p(|G|)
  obtain ⟨a, _, hM_idx_pow⟩ : ∃ a ≤ (Nat.card G).factorization p, M.index = p ^ a :=
    (Nat.dvd_prime_pow Fact.out).mp ((hN_idx_eq_P₀.trans hP₀_card) ▸ hM_idx_dvd_Nidx)
  -- |Q| = p^v_p(|H|)
  have hQ_card : Nat.card ↥(Q : Subgroup ↥H) = p ^ (Nat.card ↥H).factorization p :=
    Q.card_eq_multiplicity
  -- |H| = |M| * M.index (Lagrange)
  have hL_M : Nat.card ↥M * M.index = Nat.card ↥H := by
    rw [mul_comm]; exact M.index_mul_card
  -- v_p(|H|) = a (from |M| * p^a = |H|, |M| coprime to p ⇒ v_p(|M|) = 0)
  have h_va : (Nat.card ↥H).factorization p = a := by
    have h_card_eq : Nat.card ↥M * p ^ a = Nat.card ↥H := by
      rw [← hM_idx_pow]; exact hL_M
    have hp_pos : 0 < p := (Fact.out (p := p.Prime)).pos
    have hM_ne : Nat.card ↥M ≠ 0 := Nat.card_pos.ne'
    have hpa_ne : p ^ a ≠ 0 := pow_ne_zero a hp_pos.ne'
    rw [← h_card_eq, Nat.factorization_mul hM_ne hpa_ne, Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd h_p_ndvd_M,
        Nat.factorization_pow_self Fact.out, zero_add]
  -- |Q| = M.index
  have hQ_card_eq : Nat.card ↥(Q : Subgroup ↥H) = M.index := by
    rw [hQ_card, h_va, ← hM_idx_pow]
  -- |M| * |Q| = |H|
  have h_mul_eq : Nat.card ↥M * Nat.card ↥(Q : Subgroup ↥H) = Nat.card ↥H := by
    rw [hQ_card_eq]; exact hL_M
  -- Coprime |M| |Q|: |M| coprime to p ⇒ Coprime |M| p ⇒ Coprime |M| p^a
  have h_coprime : Nat.Coprime (Nat.card ↥M) (Nat.card ↥(Q : Subgroup ↥H)) := by
    rw [hQ_card, h_va]
    exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h_p_ndvd_M).symm).pow_right a
  exact Subgroup.isComplement'_of_coprime h_mul_eq h_coprime

/-- `(C_G(X)).subgroupOf (N_G(X))` は `N_G(X)` で normal (kernel of `normalizerMonoidHom`).
mathlib `normalizerMonoidHom_ker` 経由で機械的に得られるが、typeclass resolution が
直接行かないので明示 instance 化. -/
instance centralizer_subgroupOf_normalizer_normal (X : Subgroup G) :
    ((Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))).Normal := by
  rw [← X.normalizerMonoidHom_ker]
  infer_instance

end

end OddOrder.Isaacs.Ch05


