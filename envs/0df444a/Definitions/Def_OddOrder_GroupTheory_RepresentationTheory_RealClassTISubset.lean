-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_RealClassTISubset
-- name    : OddOrder_GroupTheory_RepresentationTheory_RealClassTISubset
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:08:37.813897+00:00
-- url     : https://prove2.me/theorems/90a71d22-6156-48b2-85bf-d02ac6af7d54
-- title:
--   Real classes under a TI Sylow setup: the Peterfalvi (6.7.3) real-class atom
-- statement:
--   Discharges the real-class atom of Peterfalvi (6.7.3) (§4.8, p. 33). In the (6.7) setup, with $P$ a Sylow $p$-subgroup of $G$, $L=N_G(P)$ of odd order, and $P^\#=P\setminus\{1\}$ a TI-subset with normalizer-bound $L$, a nontrivial $z\in P$ is not $G$-conjugate to its inverse. This is the opening line of Peterfalvi's proof of (6.7.3): since $|L|$ is odd, $z^{-1}$ is not conjugate to $z$ in $G$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/RealClassTISubset.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/RealClassTISubset.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutation
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_TISubset

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **Peterfalvi (6.7.3), real-class atom (TI-reduction).** In the (6.7) setup — `P ∈ Syl_p(G)`,
`L = N_G(P)` of odd order, and `P^# = P ∖ {1}` a TI-subset of `G` with normalizer-bound `L` — a
nontrivial `z ∈ P` is **not** `G`-conjugate to its inverse.

This is Peterfalvi's "since `|L|` is odd, `z⁻¹` is not conjugate to `z` in `G`".

Proof.  Both `z, z⁻¹ ∈ P^#`.  A `G`-conjugator `c` with `c z⁻¹ c⁻¹ = z` carries `z⁻¹ ∈ P^#` to
`z ∈ P^#`, so by the TI property `c ∈ L`.  As `P ≤ L`, also `z ∈ L`; reading the conjugacy inside
the finite group `L` of odd order, `z` is `L`-conjugate to `z⁻¹`, so
`ConjClasses.eq_one_of_isConj_inv_of_odd_card` forces `z = 1`, contradicting `z ≠ 1`. -/
theorem not_isConj_inv_of_isTISubset {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hodd : Odd (Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G))))
    (hti : IsTISubset ((P : Set G) \ {1}) (Subgroup.normalizer (P : Subgroup G)))
    {z : G} (hzP : z ∈ (P : Subgroup G)) (hz1 : z ≠ 1) :
    ¬ IsConj z⁻¹ z := by
  intro hconj
  -- Bind `L = N_G(P)` once; `hodd`/`hti` fold onto it.
  set L : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G) with hL
  -- `L` is finite: its order is odd, hence nonzero.
  have hcard_ne : Nat.card L ≠ 0 := by rcases hodd with ⟨k, hk⟩; omega
  have : Finite L := (Nat.card_ne_zero.mp hcard_ne).2
  -- `z, z⁻¹ ∈ P^# = P ∖ {1}`.
  have hzA : z ∈ (P : Set G) \ {1} := ⟨hzP, by simpa using hz1⟩
  have hzinvA : z⁻¹ ∈ (P : Set G) \ {1} :=
    ⟨inv_mem hzP, by simpa using inv_ne_one.mpr hz1⟩
  -- A `G`-conjugator: `c z⁻¹ c⁻¹ = z`.
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  -- `c` carries `z⁻¹ ∈ P^#` to `z ∈ P^#`, so the TI property puts `c ∈ L`.
  have hcL : c ∈ L := hti c ⟨z⁻¹, hzinvA, by rw [hc]; exact hzA⟩
  -- `P ≤ L`, so `z ∈ L` (and `z⁻¹ ∈ L` as `(⟨z, hzL⟩ : L)⁻¹`).
  have hzL : z ∈ L := by rw [hL]; exact (P : Subgroup G).le_normalizer hzP
  -- Read the conjugacy inside `L`: `IsConj (⟨z, _⟩⁻¹) ⟨z, _⟩`.
  have hconjL : IsConj (⟨z, hzL⟩ : L)⁻¹ ⟨z, hzL⟩ := by
    rw [isConj_iff]
    refine ⟨⟨c, hcL⟩, ?_⟩
    apply Subtype.ext
    change c * z⁻¹ * c⁻¹ = z
    exact hc
  -- Odd order ⇒ `⟨z, _⟩ = 1`, i.e. `z = 1`, contradicting `z ≠ 1`.
  have hz1' : (⟨z, hzL⟩ : L) = 1 :=
    ConjClasses.eq_one_of_isConj_inv_of_odd_card hodd hconjL
  exact hz1 (by simpa using congrArg Subtype.val hz1')

end OddOrder.RepresentationTheory


