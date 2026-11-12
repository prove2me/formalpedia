-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch09_MoreSubnormality_SylowSubnormal
-- name    : OddOrder_Isaacs_Ch09_MoreSubnormality_SylowSubnormal
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:33.158734+00:00
-- url     : https://prove2.me/theorems/6f2005ec-9522-4d4d-9f37-a955ff14422c
-- title:
--   Isaacs Lemma 9.31: Sylow subgroups meet subnormal subgroups in Sylow subgroups
-- statement:
--   Formalizes Isaacs, *Finite Group Theory*, §9D, Lemma 9.31 (p. 291): if $S$ is subnormal in $G$ and $P\in\mathrm{Syl}_p(G)$ then $P\cap S\in\mathrm{Syl}_p(S)$. The hypothesis is subnormality (confirmed against the printed page), not normality. The content reduces to the index being coprime to $p$, stated as $p\nmid[S:P\cap S]$.
--
--   The main definition is `sylowInfOfIsSubnormal`, the bundled Sylow subgroup $P\cap S$ of $S$.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch09_MoreSubnormality/SylowSubnormal.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch09_MoreSubnormality/SylowSubnormal.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.GroupTheory.IsSubnormal
import Mathlib.GroupTheory.Sylow

namespace OddOrder.Isaacs.Ch09

variable {G : Type*} [Group G]

section

/-- **Isaacs Lemma 9.31 の normal 段**: `N ⊴ G`, `P ∈ Syl_p(G)` ⇒ `|N : N ∩ P|` は `p` と互いに素.

第二同型定理の指数版. `J = N ⊔ P` とおくと
`|N : N ∩ P| · |J : N| = |J : N ∩ P| = |P : N ∩ P| · |J : P|` で,
`|J : N| = |P : N ∩ P|` (`relIndex_sup_left`, `N` 正規) を約せば
`|N : N ∩ P| = |J : P|`. これは `|G : P|` を割るので `p` と互いに素. -/
theorem not_dvd_relIndex_inf_of_normal [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (P : Sylow p G) :
    ¬ p ∣ ((P : Subgroup G) ⊓ N).relIndex N := by
  set Q : Subgroup G := (P : Subgroup G) with hQ
  set J : Subgroup G := N ⊔ Q with hJ
  -- (Q ⊓ N).relIndex N = J.relIndex Q, then divide |G : Q|.
  have hNJ : N ≤ J := le_sup_left
  have hQJ : Q ≤ J := le_sup_right
  have hinfN : (Q ⊓ N) ≤ N := inf_le_right
  have hinfQ : (Q ⊓ N) ≤ Q := inf_le_left
  -- Chain 1: |Q ⊓ N : ?| through N.
  have c1 : (Q ⊓ N).relIndex N * N.relIndex J = (Q ⊓ N).relIndex J :=
    Subgroup.relIndex_mul_relIndex _ _ _ hinfN hNJ
  -- Chain 2: through Q.
  have c2 : (Q ⊓ N).relIndex Q * Q.relIndex J = (Q ⊓ N).relIndex J :=
    Subgroup.relIndex_mul_relIndex _ _ _ hinfQ hQJ
  -- Second isomorphism theorem, index form: |J : N| = |Q : Q ⊓ N|.
  have hsup : N.relIndex J = N.relIndex Q := by
    rw [hJ]; exact Subgroup.relIndex_sup_left Q N
  have hinf : (Q ⊓ N).relIndex Q = N.relIndex Q := Subgroup.inf_relIndex_left Q N
  rw [hsup] at c1
  rw [hinf] at c2
  -- Cancel the common (nonzero) factor N.relIndex Q.
  have hne : N.relIndex Q ≠ 0 := by
    have : N.relIndex Q ∣ Nat.card Q := Subgroup.relIndex_dvd_card N Q
    exact fun h0 => (Nat.card_pos (α := Q)).ne' (Nat.eq_zero_of_zero_dvd (h0 ▸ this))
  have key : (Q ⊓ N).relIndex N = Q.relIndex J := by
    have := c1.trans c2.symm
    -- (Q ⊓ N).relIndex N * (N.relIndex Q) = (N.relIndex Q) * (Q.relIndex J)
    rw [mul_comm (N.relIndex Q)] at this
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) this
  rw [key]
  exact fun hdvd => P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hQJ))

/-- **Isaacs Lemma 9.31** (p. 291): `S ◁◁ G` (subnormal), `P ∈ Syl_p(G)` ⇒
`|S : S ∩ P|` は `p` と互いに素 (すなわち `P ∩ S ∈ Syl_p(S)`).

`Subgroup.IsSubnormal` の構造帰納. `top` 段は `Sylow.not_dvd_index` そのもの,
`step` 段は帰納法の仮定で得た `↥K` の Sylow に normal 段を適用する. -/
theorem not_dvd_relIndex_inf_of_isSubnormal [Finite G] {p : ℕ} [Fact p.Prime]
    {S : Subgroup G} (hS : S.IsSubnormal) (P : Sylow p G) :
    ¬ p ∣ ((P : Subgroup G) ⊓ S).relIndex S := by
  induction hS with
  | top =>
    simpa [Subgroup.relIndex_top_right] using P.not_dvd_index
  | step H K hle hKsub hHnorm ih =>
    -- Inside ↥K: `Q := (P ⊓ K).subgroupOf K` is a Sylow p-subgroup (ih gives the index).
    have hQ_pg : IsPGroup p ↥(((P : Subgroup G) ⊓ K).subgroupOf K) := by
      have : IsPGroup p ↥((P : Subgroup G) ⊓ K) :=
        P.isPGroup'.of_injective (Subgroup.inclusion inf_le_left)
          (Subgroup.inclusion_injective _)
      exact this.comap_subtype
    have hQ_idx : ¬ p ∣ (((P : Subgroup G) ⊓ K).subgroupOf K).index := ih
    set Q : Sylow p ↥K := hQ_pg.toSylow hQ_idx with hQdef
    have hQ_coe : (Q : Subgroup ↥K) = ((P : Subgroup G) ⊓ K).subgroupOf K :=
      hQ_pg.toSylow_coe hQ_idx
    -- Apply the normal step inside ↥K to the normal subgroup `H.subgroupOf K`.
    have : (H.subgroupOf K).Normal := hHnorm
    have hnormal := not_dvd_relIndex_inf_of_normal (H.subgroupOf K) Q
    rw [hQ_coe] at hnormal
    -- Identify `(P ⊓ K).subgroupOf K ⊓ H.subgroupOf K` with `(P ⊓ H).subgroupOf K`.
    have hmeet : ((P : Subgroup G) ⊓ K).subgroupOf K ⊓ H.subgroupOf K
        = ((P : Subgroup G) ⊓ H).subgroupOf K := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hle h.2⟩, h.2⟩⟩
    rw [hmeet, Subgroup.relIndex_subgroupOf hle] at hnormal
    exact hnormal

/-- **Isaacs Lemma 9.31** (束ねた形): `S ◁◁ G`, `P ∈ Syl_p(G)` ⇒ `P ∩ S` は `S` の
Sylow `p`-部分群. -/
noncomputable def sylowInfOfIsSubnormal [Finite G] {p : ℕ} [Fact p.Prime]
    {S : Subgroup G} (hS : S.IsSubnormal) (P : Sylow p G) : Sylow p ↥S :=
  (show IsPGroup p ↥(((P : Subgroup G) ⊓ S).subgroupOf S) from
    (P.isPGroup'.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)).comap_subtype).toSylow
    (not_dvd_relIndex_inf_of_isSubnormal hS P)

@[simp]
theorem sylowInfOfIsSubnormal_coe [Finite G] {p : ℕ} [Fact p.Prime]
    {S : Subgroup G} (hS : S.IsSubnormal) (P : Sylow p G) :
    (sylowInfOfIsSubnormal hS P : Subgroup ↥S) = ((P : Subgroup G) ⊓ S).subgroupOf S :=
  IsPGroup.toSylow_coe _ _

end

end OddOrder.Isaacs.Ch09


