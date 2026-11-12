-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04d_GorThm415
-- name    : OddOrder_BG_Ch1_Preliminary_S04d_GorThm415
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:55:18.55325+00:00
-- url     : https://prove2.me/theorems/badea173-dc29-4a53-9c45-cdc0e96ba742
-- title:
--   Gorenstein, *Finite Groups*, Lemma 4.14: the engine of $d_n(P)\le2\Rightarrow d(P)\le2$
-- statement:
--   Gorenstein, *Finite Groups* (2nd ed.), Lemma 4.14, referenced by Bender–Glauberman §4 (Lemma 4.13 depends on it): for a finite $p$-group $P$ with $p$ odd and $A$ a maximal abelian normal subgroup of maximal rank $m(A)=d_n(P)$ the lemma relates $\Omega_1(P)$ and the centralizer of $\Omega_1(A)$ (`omega1_centralizer_omega1_eq_omega1_of_maximal_rank`).
--
--   The bundle consists of lemmas only: `omega1_centralizer_omega1_eq_omega1_of_maximal_rank` (Lemma 4.14), `commutator_centralizes_of_stabilize` (Lemma 4.13, element form) and helpers on `omega1Map`.
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04d_GorThm415.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04d_GorThm415.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04c_Prop411
import Definitions.Def_OddOrder_GroupTheory_CriticalSubgroup
import Definitions.Def_OddOrder_GroupTheory_SCN
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_GroupTheory_FrattiniPGroup

open scoped commutatorElement Pointwise

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

/-- **Gorenstein "Finite Groups" Lemma 4.12.** If `x, y` are elements of a `p`-group
with `⟨x, y⟩` noncyclic, then `⟨y, ˣy⟩ ⊊ ⟨x, y⟩` (here `ˣy = x y x⁻¹`).

Proof (Gorenstein, mmd L4185): set `Q = ⟨y, x y x⁻¹⟩`, `P₀ = ⟨x, y⟩`. Clearly `Q ≤ P₀`.
If `Q = P₀`, then since `⁅x, y⁆ = (x y x⁻¹) · y⁻¹ ∈ Q` the coset `Φ(Q) y` generates
`Q/Φ(Q)` (because `x y x⁻¹ = ⁅x, y⁆ · y` and `⁅x, y⁆ ∈ Q' ≤ Φ(Q)`); so `Q/Φ(Q)` is
cyclic and hence `Q` is cyclic (Frattini non-generating), contradicting noncyclicity
of `P₀ = Q`. -/
private theorem lt_closure_conj_of_noncyclic (hP : IsPGroup p P) {x y : P}
    (hncyc : ¬ IsCyclic ↥(Subgroup.closure ({x, y} : Set P))) :
    Subgroup.closure ({y, x * y * x⁻¹} : Set P) < Subgroup.closure ({x, y} : Set P) := by
  set Q := Subgroup.closure ({y, x * y * x⁻¹} : Set P) with hQ
  set P₀ := Subgroup.closure ({x, y} : Set P) with hP₀
  -- `y, x y x⁻¹ ∈ P₀`.
  have hyP₀ : y ∈ P₀ := Subgroup.subset_closure (by simp)
  have hxP₀ : x ∈ P₀ := Subgroup.subset_closure (by simp)
  have hcyP₀ : x * y * x⁻¹ ∈ P₀ :=
    P₀.mul_mem (P₀.mul_mem hxP₀ hyP₀) (P₀.inv_mem hxP₀)
  -- `Q ≤ P₀`.
  have hQle : Q ≤ P₀ := by
    rw [hQ, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hyP₀
    · exact hcyP₀
  refine lt_of_le_of_ne hQle (fun hQeq => hncyc ?_)
  -- Suppose `Q = P₀`; show `P₀` is cyclic. Generators `y, x y x⁻¹ ∈ Q`, and `x ∈ Q` (as `Q = P₀`).
  have hyQ : y ∈ Q := Subgroup.subset_closure (by simp)
  have hcyQ : x * y * x⁻¹ ∈ Q := Subgroup.subset_closure (by simp)
  have hxQ : x ∈ Q := hQeq ▸ hxP₀
  -- Subtype lifts.
  set y₀ : Q := ⟨y, hyQ⟩ with hy₀
  set x₀ : Q := ⟨x, hxQ⟩ with hx₀
  set c₀ : Q := ⟨x * y * x⁻¹, hcyQ⟩ with hc₀
  -- `Q` is a `p`-group (subgroup of the `p`-group `P`).
  have hQpg : IsPGroup p Q := hP.to_subgroup Q
  -- **Frattini argument in `Q`**: `zpowers y₀ ⊔ Φ(Q) = ⊤`, hence `zpowers y₀ = ⊤`.
  -- `c₀ = ⁅x₀, y₀⁆ * y₀ ∈ Φ(Q) ⊔ zpowers y₀`.
  have hc₀_mem : c₀ ∈ Subgroup.zpowers y₀ ⊔ frattini Q := by
    have hcomm : ⁅x₀, y₀⁆ ∈ frattini Q := hQpg.commutator_mem_frattini x₀ y₀
    have heq : c₀ = ⁅x₀, y₀⁆ * y₀ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, commutatorElement_def]
      push_cast [hc₀, hx₀, hy₀]
      group
    rw [heq]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left (Subgroup.mem_zpowers y₀))
  have hsup_top : Subgroup.zpowers y₀ ⊔ frattini Q = ⊤ := by
    rw [eq_top_iff, ← Subgroup.map_subtype_le_map_subtype, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    -- `Q = closure {y, x y x⁻¹} ≤ (zpowers y₀ ⊔ Φ(Q)).map Q.subtype`.
    refine le_trans (le_of_eq hQ) ?_
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨y₀, Subgroup.mem_sup_left (Subgroup.mem_zpowers y₀), rfl⟩
    · exact ⟨c₀, hc₀_mem, rfl⟩
  have hzeq : Subgroup.zpowers y₀ = ⊤ := frattini_nongenerating hsup_top
  have : IsCyclic Q := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨y₀, hzeq⟩
  exact isCyclic_of_surjective (MulEquiv.subgroupCongr hQeq).toMonoidHom
    (MulEquiv.subgroupCongr hQeq).surjective

/-- If `K ◁ G`, `H ≤ K`, and `H` (viewed inside `K` as `H.subgroupOf K`) is
characteristic in `K`, then `H ◁ G`. (Conjugation by any `g : G` restricts to an
automorphism `MulAut.conjNormal g` of `K`, which fixes the characteristic
`H.subgroupOf K`.) -/
private theorem normal_of_characteristic_subgroupOf {G : Type*} [Group G] {K : Subgroup G}
    [K.Normal] {H : Subgroup G} (hHK : H ≤ K)
    (hchar : (H.subgroupOf K).Characteristic) : H.Normal where
  conj_mem := by
    intro n hn g
    have hnK : n ∈ K := hHK hn
    -- `⟨n, hnK⟩ ∈ H.subgroupOf K`.
    have hmem : (⟨n, hnK⟩ : K) ∈ H.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]; exact hn
    -- `conjNormal g` fixes `H.subgroupOf K`.
    have hfix : (H.subgroupOf K).map (MulAut.conjNormal g).toMonoidHom = H.subgroupOf K :=
      Subgroup.characteristic_iff_map_eq.mp hchar (MulAut.conjNormal g)
    have himg : MulAut.conjNormal g ⟨n, hnK⟩ ∈ H.subgroupOf K := by
      rw [← hfix]; exact Subgroup.mem_map_of_mem _ hmem
    rw [Subgroup.mem_subgroupOf, MulAut.conjNormal_apply] at himg
    exact himg

/-- If a group `M` is generated by two abelian normal subgroups `X, Y`
(`X ⊔ Y = ⊤`), then `M` has class `≤ 2`: `⁅M, M⁆ ≤ Z(M)`.

Proof: `⁅X, Y⁆ ≤ X ⊓ Y` (commutator of normals) is centralized by both `X` and `Y`,
hence (as `X ⊔ Y = ⊤`) lies in `Z(M)`. And `M / ⁅X, Y⁆` is abelian — it is generated
by the images of `X` and `Y`, which are abelian and commute (their commutator is killed)
— so `⁅M, M⁆ ≤ ⁅X, Y⁆ ≤ Z(M)`. -/
private theorem class_le_two_of_two_abelian_normal {M : Type*} [Group M]
    {X Y : Subgroup M} [X.Normal] [Y.Normal]
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hY : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (hsup : X ⊔ Y = ⊤) :
    _root_.commutator M ≤ Subgroup.center M := by
  have hXc : IsMulCommutative X := ⟨⟨fun a b => Subtype.ext (hX a a.2 b b.2)⟩⟩
  have hYc : IsMulCommutative Y := ⟨⟨fun a b => Subtype.ext (hY a a.2 b b.2)⟩⟩
  -- `⁅X, Y⁆ ≤ Z(M)`.
  have hXY_central : ⁅X, Y⁆ ≤ Subgroup.center M := by
    -- `⁅X, Y⁆ ≤ X ⊓ Y`.
    have h1 : ⁅X, Y⁆ ≤ X ⊓ Y := Subgroup.commutator_le_inf X Y
    refine le_trans h1 ?_
    -- `z ∈ X ⊓ Y` commutes with `X` and `Y`, hence with `⊤ = X ⊔ Y`.
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hgmem : g ∈ X ⊔ Y := hsup ▸ Subgroup.mem_top g
    -- Induct on membership of `g` in `X ⊔ Y = closure (↑X ∪ ↑Y)`.
    rw [Subgroup.sup_eq_closure] at hgmem
    refine Subgroup.closure_induction (p := fun g _ => g * z = z * g) ?_ ?_ ?_ ?_ hgmem
    · rintro w (hwX | hwY)
      · exact hX w hwX z (Subgroup.mem_inf.mp hz).1
      · exact hY w hwY z (Subgroup.mem_inf.mp hz).2
    · simp
    · intro a b _ _ ha hb
      rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    · intro a _ ha
      have : Commute a z := ha
      exact this.inv_left.eq
  -- `M / ⁅X, Y⁆` is commutative ⇒ `⁅M, M⁆ ≤ ⁅X, Y⁆`.
  have hMM_le : _root_.commutator M ≤ ⁅X, Y⁆ := by
    set N := ⁅X, Y⁆ with hN
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    -- The quotient is generated by the (commuting, abelian) images of `X` and `Y`.
    refine ⟨⟨fun p q => ?_⟩⟩
    obtain ⟨p', rfl⟩ := QuotientGroup.mk'_surjective N p
    obtain ⟨q', rfl⟩ := QuotientGroup.mk'_surjective N q
    -- `p', q' ∈ ⊤ = X ⊔ Y = X * Y`, so `p' = ux vx`, `q' = uy vy`.
    have hp'mem : p' ∈ (↑(X ⊔ Y) : Set M) := by rw [hsup]; trivial
    have hq'mem : q' ∈ (↑(X ⊔ Y) : Set M) := by rw [hsup]; trivial
    rw [Subgroup.normal_mul] at hp'mem hq'mem
    obtain ⟨ux, hux, vx, hvx, rfl⟩ := hp'mem
    obtain ⟨uy, huy, vy, hvy, rfl⟩ := hq'mem
    -- All cross commutators of `X`- and `Y`-elements vanish in the quotient.
    have key : ∀ (a : M), a ∈ X → ∀ (b : M), b ∈ Y →
        Commute (QuotientGroup.mk' N a) (QuotientGroup.mk' N b) := by
      intro a ha b hb
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul]
      -- `⁅a, b⁆ ∈ N` gives `mk (a*b) = mk (b*a)`.
      have hmem : ⁅a, b⁆ ∈ N := Subgroup.commutator_mem_commutator ha hb
      have : (QuotientGroup.mk' N) ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    -- like-subgroup commutators vanish (`X`, `Y` abelian).
    have keyX : ∀ (a : M), a ∈ X → ∀ (b : M), b ∈ X →
        Commute (QuotientGroup.mk' N a) (QuotientGroup.mk' N b) := fun a ha b hb => by
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hX a ha b hb]
    have keyY : ∀ (a : M), a ∈ Y → ∀ (b : M), b ∈ Y →
        Commute (QuotientGroup.mk' N a) (QuotientGroup.mk' N b) := fun a ha b hb => by
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hY a ha b hb]
    -- Assemble: `Commute (mk ux * mk vx) (mk uy * mk vy)`.
    change Commute (QuotientGroup.mk' N (ux * vx)) (QuotientGroup.mk' N (uy * vy))
    rw [map_mul, map_mul]
    have cux : Commute (QuotientGroup.mk' N ux) (QuotientGroup.mk' N uy * QuotientGroup.mk' N vy) :=
      (keyX ux hux uy huy).mul_right (key ux hux vy hvy)
    have cvx : Commute (QuotientGroup.mk' N vx) (QuotientGroup.mk' N uy * QuotientGroup.mk' N vy) :=
      (key uy huy vx hvx).symm.mul_right (keyY vx hvx vy hvy)
    exact cux.mul_left cvx
  exact le_trans hMM_le hXY_central

omit [Finite P] in
/-- **Gorenstein "Finite Groups" Lemma 4.13** (element form). Let `A` be a normal
subgroup of `P` and `H ≤ A` an abelian subgroup. If two elements `g₁, g₂` each
"stabilize" the series `A ⊇ H ⊇ 1` — i.e. their conjugation displaces every `a ∈ A`
into `H` (`g⁻¹ a g a⁻¹ ∈ H`) and they centralize `H` — then their commutator
`⁅g₂, g₁⁆` centralizes `A`.

This is the element-level version of Gorenstein's stability-group lemma (the
stabilizer of a two-step normal series with abelian top is abelian, mmd L4195,
eq. (4.11)). Concretely, with `s = g₁⁻¹ a g₁ a⁻¹`, `t = g₂⁻¹ a g₂ a⁻¹ ∈ H`, one
computes `⁅g₂, g₁⁆ a ⁅g₂, g₁⁆⁻¹ = (s t s⁻¹ t⁻¹) a = a`, the last step because
`s, t ∈ H` commute. -/
theorem commutator_centralizes_of_stabilize {A H : Subgroup P} [A.Normal]
    (hH_le : H ≤ A) (hH_comm : ∀ s ∈ H, ∀ t ∈ H, s * t = t * s) {g₁ g₂ : P}
    (hdisp₁ : ∀ a ∈ A, g₁⁻¹ * a * g₁ * a⁻¹ ∈ H)
    (hdisp₂ : ∀ a ∈ A, g₂⁻¹ * a * g₂ * a⁻¹ ∈ H)
    (hfix₁ : ∀ w ∈ H, g₁ * w = w * g₁) (hfix₂ : ∀ w ∈ H, g₂ * w = w * g₂) :
    ∀ a ∈ A, ⁅g₂, g₁⁆ * a = a * ⁅g₂, g₁⁆ := by
  intro a ha
  -- Displacement elements `s, t ∈ H`.
  set s := g₁⁻¹ * a * g₁ * a⁻¹ with hs_def
  set t := g₂⁻¹ * a * g₂ * a⁻¹ with ht_def
  have hsH : s ∈ H := hdisp₁ a ha
  have htH : t ∈ H := hdisp₂ a ha
  -- `s, t ∈ A`.
  have hsA : s ∈ A := hH_le hsH
  have htA : t ∈ A := hH_le htH
  -- `g₁⁻¹ a g₁ = s * a` and `g₂⁻¹ a g₂ = t * a`.
  have hconj₁ : g₁⁻¹ * a * g₁ = s * a := by rw [hs_def]; group
  have hconj₂ : g₂⁻¹ * a * g₂ = t * a := by rw [ht_def]; group
  -- `g₁ a g₁⁻¹ = s⁻¹ * a`: from `g₁` fixing `s ∈ H`, `g₁ s g₁⁻¹ = s`, hence
  -- `a g₁ a⁻¹ g₁⁻¹ = s`, so `g₁ a g₁⁻¹ = s⁻¹ a` (using `A` abelian via `H`-fix? no — direct).
  have hg1s : g₁ * s = s * g₁ := hfix₁ s hsH
  have hg2t : g₂ * t = t * g₂ := hfix₂ t htH
  -- `s⁻¹ = g₁ a g₁⁻¹ a⁻¹`: conjugate `hconj₁` by `g₁`.
  -- Conjugation-fix helpers: if `g` commutes with `w`, then `g w g⁻¹ = w` and `g⁻¹ w g = w`.
  have fixR : ∀ (g w : P), g * w = w * g → g * w * g⁻¹ = w := fun g w hgw => by
    rw [hgw]; group
  have fixL : ∀ (g w : P), g * w = w * g → g⁻¹ * w * g = w := fun g w hgw => by
    rw [mul_assoc, ← hgw]; group
  have hconj₁' : g₁ * a * g₁⁻¹ = s⁻¹ * a := by
    -- From `g₁⁻¹ a g₁ = s a` we get `a = (g₁ s g₁⁻¹)(g₁ a g₁⁻¹) = s (g₁ a g₁⁻¹)`.
    have h1 : a = s * (g₁ * a * g₁⁻¹) := by
      have h := congrArg (fun z => g₁ * z * g₁⁻¹) hconj₁
      rw [show g₁ * (g₁⁻¹ * a * g₁) * g₁⁻¹ = a by group,
        show g₁ * (s * a) * g₁⁻¹ = (g₁ * s * g₁⁻¹) * (g₁ * a * g₁⁻¹) by group,
        fixR g₁ s hg1s] at h
      exact h
    refine mul_left_cancel (a := s) ?_
    rw [← h1]; group
  -- Similarly `g₂ a g₂⁻¹ = t⁻¹ * a`.
  have hconj₂' : g₂ * a * g₂⁻¹ = t⁻¹ * a := by
    have h1 : a = t * (g₂ * a * g₂⁻¹) := by
      have h := congrArg (fun z => g₂ * z * g₂⁻¹) hconj₂
      rw [show g₂ * (g₂⁻¹ * a * g₂) * g₂⁻¹ = a by group,
        show g₂ * (t * a) * g₂⁻¹ = (g₂ * t * g₂⁻¹) * (g₂ * a * g₂⁻¹) by group,
        fixR g₂ t hg2t] at h
      exact h
    refine mul_left_cancel (a := t) ?_
    rw [← h1]; group
  -- `s, t` commute (both in abelian `H`); also `s⁻¹ ∈ H`, fixed by `g₂`.
  have hst : s * t = t * s := hH_comm s hsH t htH
  -- Auxiliary fixings.
  have hg2s : g₂ * s = s * g₂ := hfix₂ s hsH
  have hg1t : g₁ * t = t * g₁ := hfix₁ t htH
  have hg2si : g₂ * s⁻¹ = s⁻¹ * g₂ := hfix₂ s⁻¹ (H.inv_mem hsH)
  -- Conjugation of `a` by `⁅g₂, g₁⁆` is trivial.
  have hconj : ⁅g₂, g₁⁆ * a * (⁅g₂, g₁⁆)⁻¹ = a := by
    rw [commutatorElement_def]
    calc g₂ * g₁ * g₂⁻¹ * g₁⁻¹ * a * (g₂ * g₁ * g₂⁻¹ * g₁⁻¹)⁻¹
        = g₂ * g₁ * g₂⁻¹ * (g₁⁻¹ * a * g₁) * g₂ * g₁⁻¹ * g₂⁻¹ := by group
      _ = g₂ * g₁ * g₂⁻¹ * (s * a) * g₂ * g₁⁻¹ * g₂⁻¹ := by rw [hconj₁]
      _ = g₂ * g₁ * (g₂⁻¹ * s * g₂) * (g₂⁻¹ * a * g₂) * g₁⁻¹ * g₂⁻¹ := by group
      _ = g₂ * g₁ * s * (t * a) * g₁⁻¹ * g₂⁻¹ := by
            rw [hconj₂, fixL g₂ s hg2s]
      _ = g₂ * ((g₁ * s * g₁⁻¹) * (g₁ * t * g₁⁻¹) * (g₁ * a * g₁⁻¹)) * g₂⁻¹ := by group
      _ = g₂ * (s * t * (s⁻¹ * a)) * g₂⁻¹ := by
            rw [hconj₁', fixR g₁ s hg1s, fixR g₁ t hg1t]
      _ = (g₂ * s * g₂⁻¹) * (g₂ * t * g₂⁻¹) * (g₂ * s⁻¹ * g₂⁻¹) * (g₂ * a * g₂⁻¹) := by group
      _ = s * t * s⁻¹ * (t⁻¹ * a) := by
            rw [hconj₂', fixR g₂ s hg2s, fixR g₂ t hg2t, fixR g₂ s⁻¹ hg2si]
      _ = (s * t * s⁻¹ * t⁻¹) * a := by group
      _ = a := by
            rw [show s * t * s⁻¹ * t⁻¹ = 1 by
              rw [hst]; group]
            group
  -- Convert conjugation-trivial to commuting.
  have := hconj
  rw [mul_inv_eq_iff_eq_mul] at this
  rw [this]

omit [Finite P] in
omit [Fact (Nat.Prime p)] in
/-- `omega1Map M p = ⟨{n ∈ M : n^p = 1}⟩` as a subgroup of the ambient group. -/
private theorem omega1Map_eq_closure (M : Subgroup P) :
    omega1Map M p = Subgroup.closure {n : P | n ∈ M ∧ n ^ p = 1} := by
  rw [omega1Map, Omega, MonoidHom.map_closure]
  congr 1
  ext n
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype, pow_one]
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m.2, ?_⟩
    have : ((m ^ p : M) : P) = ((1 : M) : P) := by rw [hm]
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  · rintro ⟨hnM, hnp⟩
    refine ⟨⟨n, hnM⟩, ?_, rfl⟩
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hnp

omit [Finite P] in
omit [Fact (Nat.Prime p)] in
/-- If conjugation by `g` preserves `M` (`g M g⁻¹ = M`, as the membership equivalence
`hM`), then it preserves `omega1Map M p`. -/
private theorem conj_mem_omega1Map {M : Subgroup P} {g n : P}
    (hM : ∀ m : P, m ∈ M → g * m * g⁻¹ ∈ M) (hn : n ∈ omega1Map M p) :
    g * n * g⁻¹ ∈ omega1Map M p := by
  rw [omega1Map_eq_closure] at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem w hw =>
    refine Subgroup.subset_closure ⟨hM w hw.1, ?_⟩
    rw [conj_pow, hw.2, mul_one, mul_inv_cancel]
  | one => simp
  | mul a b _ _ ha hb =>
    rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ha

/-- **Gorenstein "Finite Groups" Lemma 4.14, PART 1** (stabilization step).
For a finite `p`-group `P` (`p` odd) with `A ◁ P` abelian, an element `x` of order
dividing `p` that centralizes `Ω₁(A)` also centralizes `A/Ω₁(A)`: for every `a ∈ A`,
`x⁻¹ a x a⁻¹ ∈ Ω₁(A)`.

Proof (Gorenstein, mmd L4207–4211): with `H = Ω₁(A)` and `B₁ = ⟨H, x⟩`, one shows
`B₁ ◁ ⟨A, x⟩` by descending induction along an index-`p` chain: at each maximal step
`M`, the group `M = (A ⊓ M)·⟨x⟩` has class `≤ 2`, so its order-`p` elements all lie in
`B₁`, identifying `B₁ = Ω₁(M)`, characteristic in `M`. Normality of `B₁` then yields
`a x a⁻¹ ∈ B₁`, whence `⁅a, x⁆ = h·x^{k-1}` with `h ∈ H`; as `⁅a, x⁆ ∈ A` and
`(x^{k-1})^p = 1`, we get `x^{k-1} ∈ H`, so `⁅a, x⁆ ∈ H`. -/
private theorem stabilizes_of_order_p_centralizing (hp_odd : Odd p) (hP : IsPGroup p P)
    {A : Subgroup P} [A.Normal] (hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {x : P}
    (hx_cent : ∀ w ∈ omega1OfAbelian P A p hA_comm, x * w = w * x) (hxp : x ^ p = 1) :
    ∀ a ∈ A, x⁻¹ * a * x * a⁻¹ ∈ omega1OfAbelian P A p hA_comm := by
  classical
  set H := omega1OfAbelian P A p hA_comm with hH_def
  -- `H ≤ A` and `H ◁ P` (characteristic in `A`).
  have hH_le_A : H ≤ A := omega1OfAbelian_le
  have hHA_comm : ∀ s ∈ H, ∀ t ∈ H, s * t = t * s :=
    fun s hs t ht => hA_comm s (hH_le_A hs) t (hH_le_A ht)
  -- `G = ⟨A, x⟩` and `B₁ = ⟨H, x⟩`.
  set G := A ⊔ Subgroup.zpowers x with hG_def
  set B₁ := H ⊔ Subgroup.zpowers x with hB₁_def
  have hxG : x ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxB₁ : x ∈ B₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hA_le_G : A ≤ G := le_sup_left
  have hB₁_le_G : B₁ ≤ G := sup_le (le_trans hH_le_A hA_le_G) le_sup_right
  -- `H ◁ P`: `H = {g ∈ A : g^p = 1}`, preserved by conjugation (`A ◁ P`).
  have hH_normal : H.Normal := by
    refine { conj_mem := ?_ }
    intro h hh g
    have hh' : h ∈ A ∧ h ^ p = 1 := hh
    refine (mem_omega1OfAbelian).mpr ⟨(inferInstance : A.Normal).conj_mem h hh'.1 g, ?_⟩
    calc (g * h * g⁻¹) ^ p = g * h ^ p * g⁻¹ := conj_pow
      _ = 1 := by rw [hh'.2, mul_one, mul_inv_cancel]
  have hH_norm_inst : H.Normal := hH_normal
  -- `↑B₁ = ↑H * ↑⟨x⟩` (as sets), so elements of `B₁` are `h·x^k`.
  have hB₁_mul : (↑B₁ : Set P) = (↑H : Set P) * (↑(Subgroup.zpowers x) : Set P) := by
    rw [hB₁_def]; exact Subgroup.normal_mul H (Subgroup.zpowers x)
  have hmem_B₁ : ∀ {b : P}, b ∈ B₁ → ∃ h ∈ H, ∃ k : ℤ, b = h * x ^ k := by
    intro b hb
    have hb' : b ∈ (↑H : Set P) * (↑(Subgroup.zpowers x) : Set P) := by
      rw [← hB₁_mul]; exact hb
    obtain ⟨h, hh, z, hz, rfl⟩ := hb'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨h, hh, k, rfl⟩
  -- `B₁` is abelian: `H` abelian, `x` centralizes `H`, `⟨x⟩` abelian.
  have hB₁_comm : ∀ b ∈ B₁, ∀ b' ∈ B₁, b * b' = b' * b := by
    intro b hb b' hb'
    obtain ⟨h, hh, k, rfl⟩ := hmem_B₁ hb
    obtain ⟨h', hh', k', rfl⟩ := hmem_B₁ hb'
    -- `x^k` commutes with `h'` (x centralizes H) and `h` with `h'`.
    have hxkh' : x ^ k * h' = h' * x ^ k := by
      have hxh' : x * h' = h' * x := hx_cent h' hh'
      exact (Commute.zpow_left (h := hxh') k).eq
    have hxk'h : x ^ k' * h = h * x ^ k' := by
      have : x * h = h * x := hx_cent h hh
      exact (Commute.zpow_left (h := this) k').eq
    have hhh' : h * h' = h' * h := hHA_comm h hh h' hh'
    calc h * x ^ k * (h' * x ^ k') = h * (x ^ k * h') * x ^ k' := by group
      _ = h * (h' * x ^ k) * x ^ k' := by rw [hxkh']
      _ = (h * h') * (x ^ k * x ^ k') := by group
      _ = (h' * h) * (x ^ k' * x ^ k) := by rw [hhh', ← zpow_add, ← zpow_add, add_comm]
      _ = h' * (h * x ^ k') * x ^ k := by group
      _ = h' * (x ^ k' * h) * x ^ k := by rw [hxk'h]
      _ = h' * x ^ k' * (h * x ^ k) := by group
  -- `G' ≤ G = A ⊔ ⟨x⟩`, so each `m ∈ G'` is `a·x^k` with `a ∈ A`.
  have hmem_G : ∀ {m : P}, m ∈ G → ∃ a ∈ A, ∃ k : ℤ, m = a * x ^ k := by
    intro m hm
    have hm' : m ∈ (↑A : Set P) * (↑(Subgroup.zpowers x) : Set P) := by
      rw [← Subgroup.normal_mul A (Subgroup.zpowers x)]; exact hm
    obtain ⟨a, haA, z, hz, rfl⟩ := hm'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ⟨a, haA, k, rfl⟩
  -- **Induction**: `B₁ ◁ G'` for every `B₁ ≤ G' ≤ G`, by strong induction on `|G'|`.
  have hnorm_all : ∀ n : ℕ, ∀ G' : Subgroup P, Nat.card ↥G' = n → B₁ ≤ G' → G' ≤ G →
      ∀ b ∈ B₁, ∀ g ∈ G', g * b * g⁻¹ ∈ B₁ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G' hcard hB₁G' hG'G b hb g hg
      rcases eq_or_lt_of_le hB₁G' with hEq | hLt
      · -- `G' = B₁`: `g ∈ B₁`, `b ∈ B₁` ⇒ `g b g⁻¹ ∈ B₁` (subgroup closed).
        have hgB₁ : g ∈ B₁ := hEq ▸ hg
        exact B₁.mul_mem (B₁.mul_mem hgB₁ hb) (B₁.inv_mem hgB₁)
      · -- `B₁ < G'`: descend to a maximal `M` with `B₁ ≤ M < G'`.
        have hG'pg : IsPGroup p ↥G' := hP.to_subgroup G'
        have : Finite ↥G' := inferInstance
        -- `B₁.subgroupOf G' < ⊤`.
        have hsub_lt : B₁.subgroupOf G' < ⊤ := by
          rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
          exact fun hle => absurd (le_antisymm hB₁G' hle) (ne_of_lt hLt)
        -- A coatom `M'` of `↥G'` above `B₁.subgroupOf G'`.
        obtain ⟨M', hM'_coat, hM'_ge⟩ :=
          (IsCoatomic.eq_top_or_exists_le_coatom (B₁.subgroupOf G')).resolve_left
            (ne_of_lt hsub_lt)
        set M : Subgroup P := M'.map G'.subtype with hM_def
        -- `M ≤ G'`, `B₁ ≤ M`, `x ∈ M`.
        have hM_le_G' : M ≤ G' := by rw [hM_def]; exact Subgroup.map_subtype_le M'
        have hB₁_le_M : B₁ ≤ M := by
          rw [hM_def]
          intro y hy
          rw [Subgroup.mem_map]
          exact ⟨⟨y, hB₁G' hy⟩, hM'_ge (by rw [Subgroup.mem_subgroupOf]; exact hy), rfl⟩
        have hxM : x ∈ M := hB₁_le_M hxB₁
        have hM_le_G : M ≤ G := le_trans hM_le_G' hG'G
        -- `M ◁ G'` (coatom in `p`-group): element-wise.
        have hM'_normal : M'.Normal := hM'_coat.normal_of_isPGroup hG'pg
        have hM_normal_in_G' : ∀ m ∈ M, ∀ g' ∈ G', g' * m * g'⁻¹ ∈ M := by
          intro m hm g' hg'
          rw [hM_def, Subgroup.mem_map] at hm ⊢
          obtain ⟨m₀, hm₀, rfl⟩ := hm
          refine ⟨(⟨g', hg'⟩ : ↥G') * m₀ * (⟨g', hg'⟩ : ↥G')⁻¹,
            hM'_normal.conj_mem m₀ hm₀ ⟨g', hg'⟩, ?_⟩
          rfl
        -- `M < G'`, so `|M| < |G'|`.
        have hM_lt_G' : M < G' := by
          rw [hM_def]
          refine lt_of_le_of_ne (Subgroup.map_subtype_le M') (fun heq => ?_)
          -- `M = G'` ⇒ `M' = ⊤`, contradicting `M'` coatom.
          apply hM'_coat.1
          have htop_map : (⊤ : Subgroup ↥G').map G'.subtype = G' :=
            (MonoidHom.range_eq_map G'.subtype).symm.trans G'.range_subtype
          exact Subgroup.map_injective G'.subtype_injective (heq.trans htop_map.symm)
        have hcard_lt : Nat.card ↥M < Nat.card ↥G' := by
          have hssub : (M : Set P) ⊂ (G' : Set P) := hM_lt_G'
          have h1 : Nat.card ↥M = (M : Set P).ncard := by
            rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
          have h2 : Nat.card ↥G' = (G' : Set P).ncard := by
            rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
          rw [h1, h2]
          exact Set.ncard_lt_ncard hssub
        -- IH applied to `M`.
        have hIH : ∀ b ∈ B₁, ∀ g ∈ M, g * b * g⁻¹ ∈ B₁ :=
          ih (Nat.card ↥M) (hcard ▸ hcard_lt) M rfl hB₁_le_M hM_le_G
        -- `X = B₁.subgroupOf M`, `Y = A.subgroupOf M`: abelian normal in `↥M`, sup `= ⊤`.
        set X : Subgroup ↥M := B₁.subgroupOf M with hX_def
        set Y : Subgroup ↥M := A.subgroupOf M with hY_def
        have hY_normal : Y.Normal := by
          rw [hY_def]; exact (inferInstance : A.Normal).comap M.subtype
        have hX_normal : X.Normal := by
          refine { conj_mem := ?_ }
          intro w hw g
          rw [hX_def, Subgroup.mem_subgroupOf] at hw ⊢
          have hconj := hIH (w : P) hw (g : P) g.2
          rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
          exact hconj
        have hX_comm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
          intro a ha b hb
          rw [hX_def, Subgroup.mem_subgroupOf] at ha hb
          exact Subtype.ext (hB₁_comm (a : P) ha (b : P) hb)
        have hY_comm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
          intro a ha b hb
          rw [hY_def, Subgroup.mem_subgroupOf] at ha hb
          exact Subtype.ext (hA_comm (a : P) ha (b : P) hb)
        have hXY_top : X ⊔ Y = ⊤ := by
          rw [eq_top_iff]
          intro m _
          obtain ⟨a, haA, k, hk⟩ := hmem_G (hM_le_G m.2)
          -- `a = m·x^{-k} ∈ M`, and `x^k ∈ B₁ ⊓ M`.
          have haM : a ∈ M := by
            have : a = (m : P) * (x ^ k)⁻¹ := by rw [hk]; group
            rw [this]; exact M.mul_mem m.2 (M.inv_mem (M.zpow_mem hxM k))
          have hxkM : x ^ k ∈ M := M.zpow_mem hxM k
          have hxkB₁ : x ^ k ∈ B₁ := B₁.zpow_mem hxB₁ k
          -- `m = ⟨a⟩ * ⟨x^k⟩` with `⟨a⟩ ∈ Y`, `⟨x^k⟩ ∈ X`.
          have hmem_a : (⟨a, haM⟩ : ↥M) ∈ Y := by rw [hY_def, Subgroup.mem_subgroupOf]; exact haA
          have hmem_xk : (⟨x ^ k, hxkM⟩ : ↥M) ∈ X := by
            rw [hX_def, Subgroup.mem_subgroupOf]; exact hxkB₁
          have hsplit : m = (⟨a, haM⟩ : ↥M) * ⟨x ^ k, hxkM⟩ := by
            apply Subtype.ext; rw [Subgroup.coe_mul]; exact hk
          rw [hsplit]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmem_a) (Subgroup.mem_sup_left hmem_xk)
        -- `cl(M) ≤ 2`.
        have hcl_M : _root_.commutator ↥M ≤ Subgroup.center ↥M :=
          class_le_two_of_two_abelian_normal hX_comm hY_comm hXY_top
        -- `B₁ = omega1Map M p`.
        have hB₁_eq : B₁ = omega1Map M p := by
          rw [omega1Map_eq_closure]
          apply le_antisymm
          · -- `B₁ ≤ closure {n ∈ M : n^p = 1}`: generators `H ∪ {x}` qualify.
            have hH_le_M : H ≤ M := le_trans le_sup_left hB₁_le_M
            rw [hB₁_def]
            apply sup_le
            · intro h hh
              exact Subgroup.subset_closure ⟨hH_le_M hh, ((mem_omega1OfAbelian).mp hh).2⟩
            · rw [Subgroup.zpowers_le]
              exact Subgroup.subset_closure ⟨hxM, hxp⟩
          · -- `closure {n ∈ M : n^p = 1} ≤ B₁`: each order-`p` element of `M` is in `B₁`.
            rw [Subgroup.closure_le]
            rintro n ⟨hnM, hnp⟩
            obtain ⟨a, haA, k, hk⟩ := hmem_G (hM_le_G hnM)
            have haM : a ∈ M := by
              have : a = n * (x ^ k)⁻¹ := by rw [hk]; group
              rw [this]; exact M.mul_mem hnM (M.inv_mem (M.zpow_mem hxM k))
            have hxkM : x ^ k ∈ M := M.zpow_mem hxM k
            -- In `↥M`: `a' = n' * (x^k)'⁻¹` has order `| p` (class ≤ 2).
            have hxkpP : (x ^ k) ^ p = 1 := by
              rw [← zpow_natCast (x ^ k) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp,
                one_zpow]
            have hap : a ^ p = 1 := by
              have hnp' : (⟨n, hnM⟩ : ↥M) ^ p = 1 := by
                apply Subtype.ext
                rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, Subgroup.coe_mk]; exact hnp
              have hxkp' : ((⟨x ^ k, hxkM⟩ : ↥M)⁻¹) ^ p = 1 := by
                apply Subtype.ext
                rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, InvMemClass.coe_inv,
                  Subgroup.coe_mk, inv_pow, hxkpP, inv_one]
              have hmul := mul_pow_prime_eq_one_of_class_le_two hp_odd hcl_M hnp' hxkp'
              -- `(n' * xk'⁻¹ : P) = n * (x^k)⁻¹ = a`.
              have hcoe : (((⟨n, hnM⟩ : ↥M) * (⟨x ^ k, hxkM⟩ : ↥M)⁻¹ : ↥M) : P) = a := by
                simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
                rw [hk]; group
              have hfin : ((((⟨n, hnM⟩ : ↥M) * (⟨x ^ k, hxkM⟩ : ↥M)⁻¹) ^ p : ↥M) : P)
                  = ((1 : ↥M) : P) := by rw [hmul]
              rwa [SubmonoidClass.coe_pow, hcoe, OneMemClass.coe_one] at hfin
            -- `a ∈ Ω₁(A) = H`, so `n = a x^k ∈ B₁`.
            have haH : a ∈ H := (mem_omega1OfAbelian).mpr ⟨haA, hap⟩
            have haB₁ : a ∈ B₁ := by rw [hB₁_def]; exact Subgroup.mem_sup_left haH
            rw [hk]
            exact B₁.mul_mem haB₁ (B₁.zpow_mem hxB₁ k)
        -- Finally, `g b g⁻¹ ∈ B₁` via conjugation preserving `omega1Map M p`.
        rw [hB₁_eq] at hb ⊢
        exact conj_mem_omega1Map (fun m hm => hM_normal_in_G' m hm g hg) hb
  -- Apply the induction with `G' = G`.
  have hB₁_normal_in_G : ∀ b ∈ B₁, ∀ g ∈ G, g * b * g⁻¹ ∈ B₁ :=
    hnorm_all (Nat.card ↥G) G rfl hB₁_le_G le_rfl
  -- **Extraction**: for `a ∈ A`, `a x a⁻¹ ∈ B₁`, so `⁅a, x⁆ ∈ H`, hence the conclusion.
  intro a ha
  have haxa : a * x * a⁻¹ ∈ B₁ := hB₁_normal_in_G x hxB₁ a (hA_le_G ha)
  obtain ⟨h, hh, k, hk⟩ := hmem_B₁ haxa
  -- `⁅a, x⁆ = a x a⁻¹ x⁻¹ = h x^{k-1}`.
  have hcomm_eq : a * x * a⁻¹ * x⁻¹ = h * x ^ (k - 1) := by
    rw [hk, zpow_sub, zpow_one]; group
  -- `⁅a, x⁆ ∈ A`.
  have hcomm_A : a * x * a⁻¹ * x⁻¹ ∈ A := by
    have h1 : x * a⁻¹ * x⁻¹ ∈ A := (inferInstance : A.Normal).conj_mem a⁻¹ (A.inv_mem ha) x
    have : a * (x * a⁻¹ * x⁻¹) ∈ A := A.mul_mem ha h1
    rwa [show a * (x * a⁻¹ * x⁻¹) = a * x * a⁻¹ * x⁻¹ by group] at this
  -- `x^{k-1} = h⁻¹ * ⁅a, x⁆ ∈ A`.
  have hxk_A : x ^ (k - 1) ∈ A := by
    have : x ^ (k - 1) = h⁻¹ * (a * x * a⁻¹ * x⁻¹) := by rw [hcomm_eq]; group
    rw [this]; exact A.mul_mem (A.inv_mem (hH_le_A hh)) hcomm_A
  -- `(x^{k-1})^p = 1`, so `x^{k-1} ∈ H`.
  have hxk_pow : (x ^ (k - 1)) ^ p = 1 := by
    rw [← zpow_natCast (x ^ (k - 1)) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp,
      one_zpow]
  have hxk_H : x ^ (k - 1) ∈ H := (mem_omega1OfAbelian).mpr ⟨hxk_A, hxk_pow⟩
  -- `⁅a, x⁆ = h * x^{k-1} ∈ H`.
  have hcomm_H : a * x * a⁻¹ * x⁻¹ ∈ H := by rw [hcomm_eq]; exact H.mul_mem hh hxk_H
  -- `x⁻¹ a x a⁻¹ = x⁻¹ ⁅a,x⁆ x ∈ H` (`H ◁ P`).
  have hconj_mem : x⁻¹ * (a * x * a⁻¹ * x⁻¹) * (x⁻¹)⁻¹ ∈ H :=
    hH_normal.conj_mem _ hcomm_H x⁻¹
  have heq : x⁻¹ * a * x * a⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹) * (x⁻¹)⁻¹ := by group
  rw [heq]; exact hconj_mem

/-- **Gorenstein "Finite Groups" Lemma 4.14, PART 2** (`D` exponent `p`).
With `C = C_P(Ω₁(A))`, the order-`p` elements of `C` are closed under products: if
`u, v ∈ C` with `u^p = v^p = 1` then `(u v)^p = 1`.

Proof (Gorenstein, mmd L4213): minimal counterexample on `|⟨u, v⟩|`. If `⟨u, v⟩` is
cyclic it is abelian, done. Otherwise `⟨u, v⟩` would have class `≥ 3` (else
`mul_pow_prime_eq_one_of_class_le_two`); but Lemma 4.12 gives `⟨v, vᵘ⟩ ⊊ ⟨u, v⟩`, so
by minimality `⁅v, u⁆ = v⁻¹ vᵘ` has order dividing `p`. Both `u, v` stabilize
`A ⊇ Ω₁(A)` (PART 1), so `⁅v, u⁆` centralizes `A` (Lemma 4.13); as `C_P(A) = A`
(Lemma 3.12), `⁅v, u⁆ ∈ Ω₁(A)`, whence it is central in `⟨u, v⟩` (which centralizes
`Ω₁(A)`), forcing class `≤ 2` — a contradiction. -/
private theorem omega1_centralizer_mul_pow (hp_odd : Odd p) (hP : IsPGroup p P)
    {A : Subgroup P} [A.Normal] (hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA_maxAb : ∀ N : Subgroup P, N.Normal →
      (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → A ≤ N → N = A) :
    ∀ u v : P, u ∈ Subgroup.centralizer (↑(omega1OfAbelian P A p hA_comm) : Set P) →
      v ∈ Subgroup.centralizer (↑(omega1OfAbelian P A p hA_comm) : Set P) →
      u ^ p = 1 → v ^ p = 1 → (u * v) ^ p = 1 := by
  classical
  set H := omega1OfAbelian P A p hA_comm with hH_def
  set C := Subgroup.centralizer (↑H : Set P) with hC_def
  have hp : p.Prime := Fact.out
  have hH_le_A : H ≤ A := omega1OfAbelian_le
  have hHA_comm : ∀ s ∈ H, ∀ t ∈ H, s * t = t * s :=
    fun s hs t ht => hA_comm s (hH_le_A hs) t (hH_le_A ht)
  -- `C_P(A) = A` (Lemma 3.12).
  have hCA : Subgroup.centralizer (↑A : Set P) = A :=
    centralizer_eq_self_of_maximal_abelian_normal hP hA_comm hA_maxAb
  -- An element of `C` of order `| p` lies in `Ω₁(A)` iff it lies in `A`.
  -- Strong induction on `|⟨u, v⟩|`.
  have key : ∀ n : ℕ, ∀ u v : P, u ∈ C → v ∈ C → u ^ p = 1 → v ^ p = 1 →
      Nat.card ↥(Subgroup.closure ({u, v} : Set P)) = n → (u * v) ^ p = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro u v huC hvC hup hvp hcard
      -- The conjugate `vᵘ = u v u⁻¹` is in `C` (both `u, v` centralize `Ω₁(A)`).
      have hconj_C : u * v * u⁻¹ ∈ C := by
        rw [hC_def, Subgroup.mem_centralizer_iff]
        intro w hw
        have hxw : Commute w u := (Subgroup.mem_centralizer_iff.mp huC) w hw
        have hyw : Commute w v := (Subgroup.mem_centralizer_iff.mp hvC) w hw
        exact ((hxw.mul_right hyw).mul_right hxw.inv_right).eq
      -- Class `≤ 2` of `⟨u, v⟩` would finish; otherwise derive a contradiction.
      set K := Subgroup.closure ({u, v} : Set P) with hK_def
      have huK : u ∈ K := Subgroup.subset_closure (by simp)
      have hvK : v ∈ K := Subgroup.subset_closure (by simp)
      by_cases hcl : _root_.commutator ↥K ≤ Subgroup.center ↥K
      · -- `cl ≤ 2`: `(u v)^p = 1` directly.
        have hup' : (⟨u, huK⟩ : ↥K) ^ p = 1 := by
          apply Subtype.ext; rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, Subgroup.coe_mk]
          exact hup
        have hvp' : (⟨v, hvK⟩ : ↥K) ^ p = 1 := by
          apply Subtype.ext; rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, Subgroup.coe_mk]
          exact hvp
        have hmul := mul_pow_prime_eq_one_of_class_le_two hp_odd hcl hup' hvp'
        have h2 : (((⟨u, huK⟩ : ↥K) * ⟨v, hvK⟩) ^ p : ↥K) = (1 : ↥K) := hmul
        have h3 : ((((⟨u, huK⟩ : ↥K) * ⟨v, hvK⟩) ^ p : ↥K) : P) = ((1 : ↥K) : P) := by rw [h2]
        rwa [SubmonoidClass.coe_pow, Subgroup.coe_mul, Subgroup.coe_mk, Subgroup.coe_mk,
          OneMemClass.coe_one] at h3
      · -- `cl ≥ 3`: contradiction. First `⟨u, v⟩` noncyclic.
        exfalso
        -- `K` noncyclic (else abelian ⇒ class ≤ 2).
        have hncyc : ¬ IsCyclic ↥K := by
          intro hcyc
          apply hcl
          have := hcyc
          -- cyclic ⇒ abelian ⇒ `center ↥K = ⊤`, so everything is `≤ center`.
          have hcomm_K : ∀ a b : ↥K, a * b = b * a :=
            (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
              (MonoidHom.id ↥K) (by simp)).is_comm.comm
          have hcenter_top : Subgroup.center ↥K = ⊤ := by
            rw [eq_top_iff]
            intro z _
            rw [Subgroup.mem_center_iff]
            intro w; exact hcomm_K w z
          rw [hcenter_top]; exact le_top
        -- `⟨u, vᵘ⟩ ⊊ K` (Lemma 4.12 with `x := v`, `y := u`).
        have hVU_eq : Subgroup.closure ({v, u} : Set P) = K := by
          rw [hK_def, Set.pair_comm v u]
        have hncyc' : ¬ IsCyclic ↥(Subgroup.closure ({v, u} : Set P)) := by
          rw [hVU_eq]; exact hncyc
        have hlt : Subgroup.closure ({u, v * u * v⁻¹} : Set P) < K := by
          have hlt0 := lt_closure_conj_of_noncyclic (x := v) (y := u) hP hncyc'
          rwa [hVU_eq] at hlt0
        -- `v u v⁻¹ ∈ C`, order `p`; IH gives `(⁅v, u⁆)^p = 1`.
        have hconj_C' : v * u * v⁻¹ ∈ C := by
          rw [hC_def, Subgroup.mem_centralizer_iff]
          intro w hw
          have hxw : Commute w v := (Subgroup.mem_centralizer_iff.mp hvC) w hw
          have hyw : Commute w u := (Subgroup.mem_centralizer_iff.mp huC) w hw
          exact ((hxw.mul_right hyw).mul_right hxw.inv_right).eq
        have hvuv_p : (v * u * v⁻¹) ^ p = 1 := by rw [conj_pow, hup, mul_one, mul_inv_cancel]
        have huinv_p : (u⁻¹) ^ p = 1 := by rw [inv_pow, hup, inv_one]
        -- `⟨v u v⁻¹, u⁻¹⟩ ⊆ closure {u, v u v⁻¹} ⊊ K`, so by IH `(⁅v,u⁆)^p = 1`.
        have hsub_le : Subgroup.closure ({v * u * v⁻¹, u⁻¹} : Set P) ≤
            Subgroup.closure ({u, v * u * v⁻¹} : Set P) := by
          rw [Subgroup.closure_le]
          rintro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact Subgroup.subset_closure (by simp)
          · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
        -- `Nat.card ↥S = (↑S).ncard` bridge.
        have hncard : ∀ S : Subgroup P, Nat.card ↥S = (S : Set P).ncard := fun S => by
          rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
        have hcard_sub : Nat.card ↥(Subgroup.closure ({v * u * v⁻¹, u⁻¹} : Set P)) < n := by
          rw [← hcard, hncard, hncard]
          calc ((Subgroup.closure ({v * u * v⁻¹, u⁻¹} : Set P)) : Set P).ncard
              ≤ ((Subgroup.closure ({u, v * u * v⁻¹} : Set P)) : Set P).ncard :=
                Set.ncard_le_ncard hsub_le (Set.toFinite _)
            _ < (K : Set P).ncard := Set.ncard_lt_ncard hlt (Set.toFinite _)
        -- IH: `((v u v⁻¹) * u⁻¹)^p = 1`, i.e. `(⁅v, u⁆)^p = 1`.
        have hvu_comm_p : (v * u * v⁻¹ * u⁻¹) ^ p = 1 := by
          have := ih _ (hcard ▸ hcard_sub) (v * u * v⁻¹) u⁻¹ hconj_C' (C.inv_mem huC)
            hvuv_p huinv_p rfl
          rwa [show v * u * v⁻¹ * u⁻¹ = (v * u * v⁻¹) * u⁻¹ by group]
        -- `u, v` stabilize `A ⊇ Ω₁(A)` (PART 1).
        have hu_cent : ∀ w ∈ H, u * w = w * u := fun w hw =>
          ((Subgroup.mem_centralizer_iff.mp huC) w hw).symm
        have hv_cent : ∀ w ∈ H, v * w = w * v := fun w hw =>
          ((Subgroup.mem_centralizer_iff.mp hvC) w hw).symm
        have hstab_u : ∀ a ∈ A, u⁻¹ * a * u * a⁻¹ ∈ H :=
          stabilizes_of_order_p_centralizing hp_odd hP hA_comm hu_cent hup
        have hstab_v : ∀ a ∈ A, v⁻¹ * a * v * a⁻¹ ∈ H :=
          stabilizes_of_order_p_centralizing hp_odd hP hA_comm hv_cent hvp
        -- `⁅v, u⁆` centralizes `A` (Lemma 4.13), so `⁅v, u⁆ ∈ A`, and order `| p` ⇒ `∈ H`.
        have hcomm_cent_A : ∀ a ∈ A, ⁅v, u⁆ * a = a * ⁅v, u⁆ :=
          commutator_centralizes_of_stabilize hH_le_A hHA_comm hstab_u hstab_v hu_cent hv_cent
        have hcomm_in_A : ⁅v, u⁆ ∈ A := by
          rw [← hCA, Subgroup.mem_centralizer_iff]
          intro a ha; exact (hcomm_cent_A a ha).symm
        have hcomm_p : (⁅v, u⁆) ^ p = 1 := by rw [commutatorElement_def]; exact hvu_comm_p
        have hcomm_in_H : ⁅v, u⁆ ∈ H := (mem_omega1OfAbelian).mpr ⟨hcomm_in_A, hcomm_p⟩
        -- `K ≤ C` (generators `u, v ∈ C`), so every element of `K` centralizes `⁅v, u⁆ ∈ H`.
        have hK_le_C : K ≤ C := by
          rw [hK_def, Subgroup.closure_le]
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact huC
          · exact hvC
        -- `⁅v, u⁆ ∈ K`, central in `↥K`.
        have hvuK : ⁅v, u⁆ ∈ K := by
          rw [commutatorElement_def]
          exact K.mul_mem (K.mul_mem (K.mul_mem hvK huK) (K.inv_mem hvK)) (K.inv_mem huK)
        have hz_center : (⟨⁅v, u⁆, hvuK⟩ : ↥K) ∈ Subgroup.center ↥K := by
          rw [Subgroup.mem_center_iff]
          intro w
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mk]
          -- `(w : P) ∈ K ≤ C` centralizes `⁅v, u⁆ ∈ H`.
          have hwC : (w : P) ∈ C := hK_le_C w.2
          exact ((Subgroup.mem_centralizer_iff.mp hwC) _ hcomm_in_H).symm
        -- `commutator ↥K ≤ center ↥K`: `↥K/Z` is generated by commuting images of `u, v`.
        apply hcl
        rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
        -- Show `↥K ⧸ center ↥K` commutative.
        have huK' : (⟨u, huK⟩ : ↥K) ∈ (⊤ : Subgroup ↥K) := Subgroup.mem_top _
        have hvK' : (⟨v, hvK⟩ : ↥K) ∈ (⊤ : Subgroup ↥K) := Subgroup.mem_top _
        -- `⊤ = closure {⟨u⟩, ⟨v⟩}` in `↥K`: every `w : ↥K` (i.e. `(w : P) ∈ closure {u, v}`)
        -- lies in `closure {⟨u⟩, ⟨v⟩}`.
        have htop_gen : (⊤ : Subgroup ↥K) =
            Subgroup.closure ({⟨u, huK⟩, ⟨v, hvK⟩} : Set ↥K) := by
          refine le_antisymm (fun w _ => ?_) le_top
          have hwK : (w : P) ∈ Subgroup.closure ({u, v} : Set P) := by rw [← hK_def]; exact w.2
          -- Build membership of `w` by induction on `(w : P) ∈ closure {u, v}`.
          have key2 : ∀ z : P, z ∈ Subgroup.closure ({u, v} : Set P) →
              ∀ (hz : z ∈ K), (⟨z, hz⟩ : ↥K) ∈ Subgroup.closure ({⟨u, huK⟩, ⟨v, hvK⟩} : Set ↥K) :=
                  by
            intro z hzc
            induction hzc using Subgroup.closure_induction with
            | mem w hw =>
              intro hzK
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
              rcases hw with rfl | rfl
              · exact Subgroup.subset_closure (by simp)
              · exact Subgroup.subset_closure (by simp)
            | one =>
              intro hz
              exact (show (⟨1, hz⟩ : ↥K) = 1 from Subtype.ext rfl) ▸ one_mem _
            | mul a b ha hb iha ihb =>
              intro hzK
              have haK : a ∈ K := hK_def ▸ ha
              have hbK : b ∈ K := hK_def ▸ hb
              have := Subgroup.mul_mem _ (iha haK) (ihb hbK)
              rwa [show (⟨a * b, hzK⟩ : ↥K) = ⟨a, haK⟩ * ⟨b, hbK⟩ from rfl]
            | inv a ha iha =>
              intro hzK
              have haK : a ∈ K := hK_def ▸ ha
              have := Subgroup.inv_mem _ (iha haK)
              rwa [show (⟨a⁻¹, hzK⟩ : ↥K) = (⟨a, haK⟩ : ↥K)⁻¹ from rfl]
          have := key2 (w : P) hwK w.2
          rwa [Subtype.coe_eta] at this
        refine ⟨⟨fun a b => ?_⟩⟩
        obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) b
        -- It suffices that all generators' images commute.
        have hgen_comm : ∀ s ∈ ({⟨u, huK⟩, ⟨v, hvK⟩} : Set ↥K),
            ∀ t ∈ ({⟨u, huK⟩, ⟨v, hvK⟩} : Set ↥K),
            Commute (QuotientGroup.mk' (Subgroup.center ↥K) s)
              (QuotientGroup.mk' (Subgroup.center ↥K) t) := by
          -- `⁅⟨u⟩, ⟨v⟩⁆ = ⁅u, v⁆ = (⁅v, u⁆)⁻¹ ∈ center`, so images commute.
          have hUV_comm : Commute (QuotientGroup.mk' (Subgroup.center ↥K) ⟨u, huK⟩)
              (QuotientGroup.mk' (Subgroup.center ↥K) ⟨v, hvK⟩) := by
            rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
            -- `⁅⟨u⟩, ⟨v⟩⁆ = ⟨⁅v, u⁆⟩⁻¹ ∈ center`, so its image is `1`.
            have hcomm_eq : (⁅(⟨u, huK⟩ : ↥K), ⟨v, hvK⟩⁆ : ↥K) = (⟨⁅v, u⁆, hvuK⟩ : ↥K)⁻¹ := by
              rw [commutatorElement_def]
              apply Subtype.ext
              simp only [Subgroup.coe_mul, InvMemClass.coe_inv,
                commutatorElement_def]
              group
            rw [hcomm_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
            exact Subgroup.inv_mem _ hz_center
          intro s hs t ht
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
          rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
          · exact Commute.refl _
          · exact hUV_comm
          · exact hUV_comm.symm
          · exact Commute.refl _
        -- All elements commute, by `closure_induction₂`.
        have hmem_a : a' ∈ Subgroup.closure ({⟨u, huK⟩, ⟨v, hvK⟩} : Set ↥K) := by
          rw [← htop_gen]; exact Subgroup.mem_top _
        have hmem_b : b' ∈ Subgroup.closure ({⟨u, huK⟩, ⟨v, hvK⟩} : Set ↥K) := by
          rw [← htop_gen]; exact Subgroup.mem_top _
        change Commute (QuotientGroup.mk' (Subgroup.center ↥K) a')
          (QuotientGroup.mk' (Subgroup.center ↥K) b')
        -- Reduce to generators commuting, via two nested `closure_induction`.
        refine Subgroup.closure_induction₂ (p := fun a b _ _ =>
          Commute (QuotientGroup.mk' (Subgroup.center ↥K) a)
            (QuotientGroup.mk' (Subgroup.center ↥K) b)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hmem_a hmem_b
        · -- mem
          intro s t hs ht; exact hgen_comm s hs t ht
        · -- one_left
          intro s _; exact Commute.one_left _
        · -- one_right
          intro s _; exact Commute.one_right _
        · -- mul_left
          intro s t z _ _ _ h1 h2; rw [map_mul]; exact h1.mul_left h2
        · -- mul_right
          intro s t z _ _ _ h1 h2; rw [map_mul]; exact h1.mul_right h2
        · -- inv_left
          intro s t _ _ h; rw [map_inv]; exact h.inv_left
        · -- inv_right
          intro s t _ _ h; rw [map_inv]; exact h.inv_right
  exact fun u v huC hvC hup hvp => key _ u v huC hvC hup hvp rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Gorenstein "Finite Groups" Lemma 4.14.** Let `P` be a finite `p`-group, `p`
odd, and let `A` be a maximal abelian normal subgroup of `P` of maximal `p`-rank
among normal abelian subgroups (`m(A) = d_n(P)`). Then
`Ω₁(C_P(Ω₁(A))) = Ω₁(A)`. -/
theorem omega1_centralizer_omega1_eq_omega1_of_maximal_rank
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    (hP : IsPGroup p P) {A : Subgroup P} [A.Normal]
    (hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA_maxAb : ∀ N : Subgroup P, N.Normal →
      (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → A ≤ N → N = A)
    (hA_maxRank : ∀ B : Subgroup P, B.Normal → IsMulCommutative B →
      pRank B p ≤ pRank A p) :
    (Omega (↥(Subgroup.centralizer ((omega1OfAbelian P A p hA_comm : Subgroup P) : Set P))) p 1).map
        (Subgroup.centralizer
          ((omega1OfAbelian P A p hA_comm : Subgroup P) : Set P)).subtype
      = omega1OfAbelian P A p hA_comm := by
  classical
  set H := omega1OfAbelian P A p hA_comm with hH_def
  set C := Subgroup.centralizer (↑H : Set P) with hC_def
  have hp : p.Prime := Fact.out
  have hH_le_A : H ≤ A := omega1OfAbelian_le
  -- The goal's LHS is `omega1Map C p = D`.
  change omega1Map C p = H
  -- `D = ⟨{n ∈ C : n^p = 1}⟩`; the set is closed under product (PART 2), so `D` is exp `p`.
  have hmul := omega1_centralizer_mul_pow hp_odd hP hA_comm hA_maxAb
  -- `D = {n ∈ C : n^p = 1}` as a subgroup, with `∀ d ∈ D, d^p = 1`.
  -- `{n ∈ C : n^p = 1}` is a subgroup (closed under `*` by PART 2).
  let Dsub : Subgroup P :=
    { carrier := {n : P | n ∈ C ∧ n ^ p = 1}
      mul_mem' := fun {a b} ha hb => ⟨C.mul_mem ha.1 hb.1, hmul a b ha.1 hb.1 ha.2 hb.2⟩
      one_mem' := ⟨C.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨C.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hDset : ∀ d : P, d ∈ omega1Map C p ↔ d ∈ C ∧ d ^ p = 1 := by
    intro d
    rw [omega1Map_eq_closure]
    constructor
    · intro hd
      have hsub : Subgroup.closure {n : P | n ∈ C ∧ n ^ p = 1} ≤ Dsub := by
        rw [Subgroup.closure_le]; exact fun z hz => hz
      exact hsub hd
    · intro ⟨hdC, hdp⟩
      exact Subgroup.subset_closure ⟨hdC, hdp⟩
  -- `H ≤ C` (H abelian) and `H ≤ D`.
  have hH_le_C : H ≤ C := by
    rw [hC_def]
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hA_comm w (hH_le_A hw) h (hH_le_A hh))
  have hH_le_D : H ≤ omega1Map C p := by
    intro h hh
    rw [hDset]
    exact ⟨hH_le_C hh, ((mem_omega1OfAbelian).mp hh).2⟩
  -- `H ◁ P` and `D ◁ P`.
  have hH_normal : H.Normal := by
    refine { conj_mem := ?_ }
    intro h hh g
    have hh' : h ∈ A ∧ h ^ p = 1 := hh
    refine (mem_omega1OfAbelian).mpr ⟨(inferInstance : A.Normal).conj_mem h hh'.1 g, ?_⟩
    calc (g * h * g⁻¹) ^ p = g * h ^ p * g⁻¹ := conj_pow
      _ = 1 := by rw [hh'.2, mul_one, mul_inv_cancel]
  have := hH_normal
  have hC_normal : C.Normal := by rw [hC_def]; infer_instance
  have hD_normal : (omega1Map C p).Normal :=
    normal_of_characteristic_subgroupOf omega1Map_le
      (by rw [omega1Map]; rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        C.subtype_injective]; exact Omega.characteristic)
  -- The hard inclusion `D ≤ H` (PART 3, rank squeeze).
  refine le_antisymm ?_ hH_le_D
  by_contra hnotle
  -- `H < D`.
  have hHD_lt : H < omega1Map C p := lt_of_le_of_ne hH_le_D (fun heq => hnotle (heq ▸ le_rfl))
  -- Work in `Q = P ⧸ H`.
  set q := QuotientGroup.mk' H with hq_def
  have hPQ : IsPGroup p (P ⧸ H) := hP.to_quotient H
  set Dbar := (omega1Map C p).map q with hDbar_def
  have hDbar_normal : Dbar.Normal :=
    Subgroup.Normal.map hD_normal q (QuotientGroup.mk'_surjective H)
  have hDbar_ne : Dbar ≠ ⊥ := by
    obtain ⟨d, hdD, hdH⟩ := SetLike.exists_of_lt hHD_lt
    intro hbot
    apply hdH
    have : q d ∈ Dbar := Subgroup.mem_map_of_mem q hdD
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff d).mp this
  -- A central order-`p` element `x̄ ∈ Dbar`.
  obtain ⟨xbar, hxbar_D, hxbar_center, hxbar_ne, hxbar_p⟩ :=
    exists_mem_omega1_center_of_normal_ne_bot hPQ hDbar_ne
  -- `E = preimage of ⟨x̄⟩`; normal, `H < E ≤ D`, `|E : H| = p`.
  have hzp_center : Subgroup.zpowers xbar ≤ Subgroup.center (P ⧸ H) :=
    Subgroup.zpowers_le.mpr hxbar_center
  have hzp_normal : (Subgroup.zpowers xbar).Normal :=
    { conj_mem := fun n hn g => by
        rw [Subgroup.mem_center_iff.mp (hzp_center hn) g, mul_assoc, mul_inv_cancel, mul_one]
        exact hn }
  set E := (Subgroup.zpowers xbar).comap q with hE_def
  have hE_normal : E.Normal := inferInstance
  -- `H ≤ E`, `E ≤ D`, `H < E`.
  have hH_le_E : H ≤ E := by
    intro h hh
    rw [hE_def, Subgroup.mem_comap, hq_def, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff h).mpr hh]
    exact one_mem _
  have hE_le_D : E ≤ omega1Map C p := by
    have h1 : E ≤ Dbar.comap q := Subgroup.comap_mono (Subgroup.zpowers_le.mpr hxbar_D)
    have h2 : Dbar.comap q = H ⊔ omega1Map C p := by
      rw [hDbar_def, hq_def, QuotientGroup.comap_map_mk']
    rwa [h2, sup_eq_right.mpr hH_le_D] at h1
  have hHE_lt : H < E := by
    refine lt_of_le_of_ne hH_le_E (fun heq => hxbar_ne ?_)
    -- if `E = H` then `x̄ = 1` (its preimage lies in `H = ker q`).
    obtain ⟨x, hx_eq⟩ := QuotientGroup.mk'_surjective H xbar
    have hxE : x ∈ E := by
      rw [hE_def, Subgroup.mem_comap, hq_def, hx_eq]; exact Subgroup.mem_zpowers xbar
    have hxH : x ∈ H := by rw [heq]; exact hxE
    rw [← hx_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hxH
  -- `E` centralizes `H` (E ≤ D ≤ C), so `H ≤ Z(E)`; and `E/H` cyclic of order `p`.
  have hE_le_C : E ≤ C := le_trans hE_le_D omega1Map_le
  -- `Nat.card ↥E = p * Nat.card ↥H` via `↥E ⧸ H.subgroupOf E ≅ ⟨x̄⟩`.
  have hcard_E : Nat.card ↥E = p * Nat.card ↥H := by
    -- `f : ↥E →* ⟨x̄⟩` surjective with kernel `H.subgroupOf E`.
    have hf_mem : ∀ e : E, q (e : P) ∈ Subgroup.zpowers xbar := fun e => e.2
    set f : E →* Subgroup.zpowers xbar :=
      (q.comp E.subtype).codRestrict (Subgroup.zpowers xbar) hf_mem with hf_def
    have hf_surj : Function.Surjective f := by
      rintro ⟨z, hz⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      obtain ⟨w, hw_eq⟩ := QuotientGroup.mk'_surjective H xbar
      refine ⟨⟨w ^ k, ?_⟩, ?_⟩
      · rw [hE_def, Subgroup.mem_comap, hq_def, map_zpow, hw_eq]
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      · apply Subtype.ext
        rw [hf_def]
        simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
        rw [map_zpow, hw_eq]
    have hf_ker : f.ker = H.subgroupOf E := by
      ext e
      rw [MonoidHom.mem_ker, hf_def, Subgroup.mem_subgroupOf]
      constructor
      · intro he
        have : q (e : P) = 1 := by
          have := congrArg Subtype.val he
          simpa [MonoidHom.codRestrict_apply] using this
        exact (QuotientGroup.eq_one_iff _).mp this
      · intro he
        apply Subtype.ext
        simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
          OneMemClass.coe_one]
        rw [hq_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact he
    -- `↥E ⧸ H.subgroupOf E ≅ ⟨x̄⟩`, of card `p`.
    have hord : orderOf xbar = p := by
      have hdvd : orderOf xbar ∣ p := orderOf_dvd_of_pow_eq_one hxbar_p
      rcases (hp.eq_one_or_self_of_dvd _ hdvd) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hxbar_ne
      · exact h1
    have hquot_card : Nat.card (E ⧸ H.subgroupOf E) = p := by
      rw [← hf_ker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf_surj).toEquiv,
        Nat.card_zpowers, hord]
    -- `Nat.card ↥E = |E/H| * |H|`.
    have hcard_H_sub : Nat.card ↥(H.subgroupOf E) = Nat.card ↥H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH_le_E).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf E), hquot_card,
      hcard_H_sub]
  -- `E` is abelian (Gorenstein Lemma 1.3.4): `E/H` cyclic, `H ≤ Z(E)`.
  -- `H.subgroupOf E ≤ center ↥E`.
  have hHsub_le_center : (H.subgroupOf E) ≤ Subgroup.center ↥E := by
    intro h hh
    rw [Subgroup.mem_subgroupOf] at hh
    rw [Subgroup.mem_center_iff]
    intro e
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    -- `(e : P) ∈ E ≤ C` centralizes `(h : P) ∈ H`.
    have heC : (e : P) ∈ C := hE_le_C e.2
    exact ((Subgroup.mem_centralizer_iff.mp heC) _ hh).symm
  -- `E/H` is cyclic (≅ ⟨x̄⟩).
  have hEH_cyclic : IsCyclic (E ⧸ H.subgroupOf E) := by
    have hf_mem : ∀ e : E, q (e : P) ∈ Subgroup.zpowers xbar := fun e => e.2
    set f : E →* Subgroup.zpowers xbar :=
      (q.comp E.subtype).codRestrict (Subgroup.zpowers xbar) hf_mem with hf_def
    have hf_surj : Function.Surjective f := by
      rintro ⟨z, hz⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      obtain ⟨w, hw_eq⟩ := QuotientGroup.mk'_surjective H xbar
      refine ⟨⟨w ^ k, ?_⟩, ?_⟩
      · rw [hE_def, Subgroup.mem_comap, hq_def, map_zpow, hw_eq]
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
      · apply Subtype.ext
        rw [hf_def]
        simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype]
        rw [map_zpow, hw_eq]
    have hf_ker : f.ker = H.subgroupOf E := by
      ext e
      rw [MonoidHom.mem_ker, hf_def, Subgroup.mem_subgroupOf]
      constructor
      · intro he
        have : q (e : P) = 1 := by
          have := congrArg Subtype.val he
          simpa [MonoidHom.codRestrict_apply] using this
        exact (QuotientGroup.eq_one_iff _).mp this
      · intro he
        apply Subtype.ext
        simp only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
          OneMemClass.coe_one]
        rw [hq_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact he
    -- `↥E ⧸ ker f ≅ ⟨x̄⟩` cyclic; transport along `ker f = H.subgroupOf E`.
    have : IsCyclic (Subgroup.zpowers xbar) := inferInstance
    have hcyc_ker : IsCyclic (E ⧸ f.ker) := isCyclic_of_surjective
      (QuotientGroup.quotientKerEquivOfSurjective f hf_surj).symm.toMonoidHom
      (QuotientGroup.quotientKerEquivOfSurjective f hf_surj).symm.surjective
    exact isCyclic_of_surjective (QuotientGroup.quotientMulEquivOfEq hf_ker).toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hf_ker).surjective
  have hE_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    have := (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (H.subgroupOf E))
      (le_trans (le_of_eq (QuotientGroup.ker_mk' _)) hHsub_le_center)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hE_mulcomm : IsMulCommutative ↥E := ⟨⟨fun a b => Subtype.ext (hE_comm a a.2 b b.2)⟩⟩
  -- `E` is elementary abelian (`E ≤ D` exp `p`).
  have hE_elemAb : E.IsElementaryAbelian p := by
    refine ⟨fun a b => Subtype.ext (hE_comm a a.2 b b.2), fun e => ?_⟩
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact ((hDset (e : P)).mp (hE_le_D e.2)).2
  -- **Rank squeeze**: `pRank ↥E ≥ log_p|E| = log_p|H| + 1 > pRank ↥A ≥ pRank ↥E`.
  -- `Nat.log p |E| ≤ pRank ↥E`.
  have hlogE_le : Nat.log p (Nat.card ↥E) ≤ pRank ↥E p := by
    have htop : (⊤ : Subgroup ↥E).IsElementaryAbelian p :=
      (hE_elemAb : OddOrder.GroupTheory.IsElementaryAbelian p ↥E).to_subgroup ⊤
    have hle := le_pRank (⊤ : Subgroup ↥E) htop
    rwa [Subgroup.card_top] at hle
  -- `Nat.log p |E| = Nat.log p |H| + 1`.
  have hcardH_pos : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
  have hlogE_eq : Nat.log p (Nat.card ↥E) = Nat.log p (Nat.card ↥H) + 1 := by
    rw [hcard_E, mul_comm, Nat.log_mul_base hp.one_lt hcardH_pos]
  -- `pRank ↥A ≤ Nat.log p |H|` (elem-ab subgroups of `A` lie in `H = Ω₁(A)`).
  have hpRankA_le : pRank ↥A p ≤ Nat.log p (Nat.card ↥H) := by
    rw [pRank_le_iff]
    intro B hB
    -- `B.map A.subtype ≤ H`.
    have hBH : B.map A.subtype ≤ H := by
      rintro _ ⟨b, hbB, rfl⟩
      refine (mem_omega1OfAbelian).mpr ⟨b.2, ?_⟩
      -- `b^p = 1` in `↥B`, hence `(b : A)^p = 1` in `↥A`, hence `(b : P)^p = 1`.
      have hbp : (⟨b, hbB⟩ : ↥B) ^ p = 1 := hB.pow_eq_one ⟨b, hbB⟩
      have hbA : (b : A) ^ p = 1 := by
        have h2 : (((⟨b, hbB⟩ : ↥B) ^ p : ↥B) : ↥A) = ((1 : ↥B) : ↥A) := by rw [hbp]
        simpa using h2
      have h3 : (((b : A) ^ p : ↥A) : P) = ((1 : ↥A) : P) := by rw [hbA]
      simpa [Subgroup.coe_subtype] using h3
    calc Nat.log p (Nat.card B) = Nat.log p (Nat.card (B.map A.subtype)) := by
          rw [Subgroup.card_map_of_injective A.subtype_injective]
      _ ≤ Nat.log p (Nat.card ↥H) :=
          Nat.log_mono_right (Nat.card_le_card_of_injective _
            (Subgroup.inclusion_injective hBH))
  -- `hA_maxRank E : pRank ↥E ≤ pRank ↥A`.
  have hmaxRank := hA_maxRank E hE_normal hE_mulcomm
  -- Contradiction: `log|H| + 1 ≤ pRank ↥E ≤ pRank ↥A ≤ log|H|`.
  have : Nat.log p (Nat.card ↥H) + 1 ≤ Nat.log p (Nat.card ↥H) :=
    calc Nat.log p (Nat.card ↥H) + 1 = Nat.log p (Nat.card ↥E) := hlogE_eq.symm
      _ ≤ pRank ↥E p := hlogE_le
      _ ≤ pRank ↥A p := hmaxRank
      _ ≤ Nat.log p (Nat.card ↥H) := hpRankA_le
  exact Nat.not_succ_le_self _ this

/-- **Gorenstein "Finite Groups" Theorem 4.15(i)** (`p` odd): if every normal abelian
subgroup of a finite `p`-group `P` has `p`-rank `≤ 2` (i.e. `d_n(P) ≤ 2`), then `P` itself
has `p`-rank `≤ 2` (`d(P) ≤ 2`).

Pick a maximal abelian normal `A` of maximal rank (`exists_maxRank_maximalAbelianNormal`);
`H = Ω₁(A)` is normal, elementary abelian, `|H| ≤ p²`. For an elementary abelian `E ≤ P`,
the conjugation action `φ : E → Aut(H)` has image a `p`-subgroup of `Aut(H) ≅ GL(≤2,p)`,
hence `|im φ| ≤ p` (`card_pSubgroup_mulAut_le_prime_of_card_le_prime_sq`); its kernel maps
into `Ω₁(C_P(H)) = H` (Lemma 4.14). If `m(E) ≥ 3` then `|ker φ| ≥ p²`, forcing
`ker φ ≅ H ≤ E`; as `E` is abelian it then centralizes `H`, so `E ≤ Ω₁(C_P(H)) = H` and
`m(E) ≤ 2` — contradiction. -/
theorem pRank_le_two_of_normalAbelian_pRank_le_two
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hp_odd : Odd p)
    (hP : IsPGroup p P)
    (hdn : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → pRank B p ≤ 2) :
    pRank P p ≤ 2 := by
  classical
  have hp := (Fact.out : p.Prime)
  rw [pRank_le_iff]
  intro E hE
  by_contra hElog
  rw [not_le] at hElog
  -- (1) maximal abelian normal `A` of maximal rank
  obtain ⟨A, hAmax, hAmaxrank⟩ := exists_maxRank_maximalAbelianNormal (G := P) p
  have hAnorm : A.Normal := hAmax.isNormal
  have hAcomm_inst : IsMulCommutative A := hAmax.isMulCommutative
  have hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) (⟨y, hy⟩ : A))
  have hA_maxAb : ∀ N : Subgroup P, N.Normal →
      (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) → A ≤ N → N = A :=
    fun N hN hNc hAN => hAmax.maximal N hN
      (IsMulCommutative.of_comm fun x y => Subtype.ext (hNc x x.2 y y.2)) hAN
  have h414 := omega1_centralizer_omega1_eq_omega1_of_maximal_rank hp_odd hP hA_comm hA_maxAb
    hAmaxrank
  set H := omega1OfAbelian P A p hA_comm with hHdef
  set C := Subgroup.centralizer (↑H : Set P) with hCdef
  have hH_le_A : H ≤ A := omega1OfAbelian_le
  -- `H ◁ P`
  have hH_normal : H.Normal := by
    refine { conj_mem := fun h hh g => ?_ }
    have hh' : h ∈ A ∧ h ^ p = 1 := hh
    refine (mem_omega1OfAbelian).mpr ⟨hAnorm.conj_mem h hh'.1 g, ?_⟩
    calc (g * h * g⁻¹) ^ p = g * h ^ p * g⁻¹ := conj_pow
      _ = 1 := by rw [hh'.2, mul_one, mul_inv_cancel]
  have : H.Normal := hH_normal
  -- `H` elementary abelian
  have hH_ea : IsElementaryAbelian p ↥H :=
    ⟨fun x y => Subtype.ext (hA_comm x.val (hH_le_A x.2) y.val (hH_le_A y.2)),
     fun x => Subtype.ext (by simpa using pow_eq_one_of_mem_omega1OfAbelian x.2)⟩
  have hHcomm : IsMulCommutative ↥H := IsMulCommutative.of_comm hH_ea.comm
  -- `|H| ≤ p²`
  have hHcard_le : Nat.card ↥H ≤ p ^ 2 := by
    have hlogle : Nat.log p (Nat.card ↥H) ≤ 2 :=
      le_trans hH_ea.log_card_le_pRank (hdn H hH_normal hHcomm)
    calc Nat.card ↥H = p ^ Nat.log p (Nat.card ↥H) := by
            rw [hH_ea.log_card_eq_finrank, hH_ea.card_eq_pow_finrank]
      _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.one_le hlogle
  -- `Ω₁(C_P(H)) ⊆ H` extractor (Lemma 4.14)
  have hΩC_le_H : ∀ x : P, x ∈ C → x ^ p = 1 → x ∈ H := by
    intro x hxC hxp
    have hg1 : (⟨x, hxC⟩ : ↥C) ^ (p ^ 1) = 1 := by
      rw [pow_one]; exact Subtype.ext (by push_cast; exact hxp)
    have hmem : x ∈ (Omega (↥C) p 1).map C.subtype :=
      ⟨⟨x, hxC⟩, Omega.mem_of_pow_eq_one hg1, rfl⟩
    rwa [h414] at hmem
  -- conjugation action `φ : ↥E →* MulAut ↥H`
  let φ : ↥E →* MulAut ↥H := (MulAut.conjNormal (H := H)).comp E.subtype
  -- `|range φ| ≤ p`
  have hrange_pg : IsPGroup p ↥φ.range :=
    hE.isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hrange_le : Nat.card ↥φ.range ≤ p :=
    card_pSubgroup_mulAut_le_prime_of_card_le_prime_sq hH_ea hHcard_le hrange_pg
  -- `|E| = |range φ| · |ker φ|`
  have hLagrange : Nat.card ↥E = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  -- `ker φ ↦ H` (Lemma 4.14)
  have hker_map_le : φ.ker.map E.subtype ≤ H := by
    rintro _ hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨e, he_ker, rfl⟩ := hx
    have he_pow : (E.subtype e) ^ p = 1 := by
      simpa using congrArg (Subgroup.subtype E) (hE.pow_eq_one e)
    have hc1 : MulAut.conjNormal (H := H) (E.subtype e) = 1 := by
      have hk : φ e = 1 := he_ker
      simpa [φ, MonoidHom.comp_apply] using hk
    have he_C : (E.subtype e) ∈ C := by
      rw [hCdef, Subgroup.mem_centralizer_iff]
      intro h hh
      have happ : (MulAut.conjNormal (H := H) (E.subtype e)) ⟨h, hh⟩ = ⟨h, hh⟩ := by
        rw [hc1]; rfl
      have heq := congrArg Subtype.val happ
      rw [MulAut.conjNormal_apply] at heq
      -- heq : E.subtype e * h * (E.subtype e)⁻¹ = h
      exact (mul_inv_eq_iff_eq_mul.mp heq).symm
    exact hΩC_le_H (E.subtype e) he_C he_pow
  -- arithmetic: `nE = p^cE`, `cE ≥ 3`
  obtain ⟨cE, hcE⟩ := IsPGroup.iff_card.mp hE.isPGroup
  have hcE3 : 3 ≤ cE := by
    have : Nat.log p (Nat.card ↥E) = cE := by rw [hcE, Nat.log_pow hp.one_lt]
    omega
  have hpE : p ^ 3 ≤ Nat.card ↥E := by rw [hcE]; exact Nat.pow_le_pow_right hp.one_le hcE3
  have hEpK : Nat.card ↥E ≤ p * Nat.card ↥φ.ker := by
    rw [hLagrange]; exact Nat.mul_le_mul_right _ hrange_le
  have hp2K : p ^ 2 ≤ Nat.card ↥φ.ker := by
    have hp3 : p ^ 3 = p * p ^ 2 := by ring
    have h3 : p * p ^ 2 ≤ p * Nat.card ↥φ.ker := by rw [← hp3]; exact le_trans hpE hEpK
    exact Nat.le_of_mul_le_mul_left h3 hp.pos
  -- `|ker φ| = |H|`, hence `ker φ ↦ H` is onto `H`
  have hkmap_card : Nat.card ↥(φ.ker.map E.subtype) = Nat.card ↥φ.ker :=
    Subgroup.card_map_of_injective E.subtype_injective
  have hK_le_H : Nat.card ↥φ.ker ≤ Nat.card ↥H := by
    rw [← hkmap_card]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hker_map_le)
      (Subgroup.inclusion_injective hker_map_le)
  have hKH : Nat.card ↥φ.ker = Nat.card ↥H := le_antisymm hK_le_H (le_trans hHcard_le hp2K)
  have hkmap_eq : φ.ker.map E.subtype = H :=
    Subgroup.eq_of_le_of_card_ge hker_map_le (le_of_eq (hkmap_card.trans hKH).symm)
  -- `H ≤ E`
  have hH_le_E : H ≤ E := by
    rw [← hkmap_eq]; exact Subgroup.map_subtype_le _
  -- `E ≤ C_P(H)` (abelian `E ⊇ H`)
  have hE_le_C : E ≤ C := by
    intro x hx
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (hE.comm ⟨h, hH_le_E hh⟩ ⟨x, hx⟩)
  -- `E ≤ Ω₁(C_P(H)) = H`
  have hE_le_H : E ≤ H := by
    intro x hx
    refine hΩC_le_H x (hE_le_C hx) ?_
    simpa using congrArg (Subgroup.subtype E) (hE.pow_eq_one ⟨x, hx⟩)
  -- contradiction
  have hcard_le : Nat.card ↥E ≤ Nat.card ↥H :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hE_le_H)
      (Subgroup.inclusion_injective hE_le_H)
  rw [hcE] at hcard_le
  have : p ^ cE ≤ p ^ 2 := le_trans hcard_le hHcard_le
  have : cE ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp this
  omega

/-- **BG Lemma 4.7, hard direction** (= **G** Theorem 5.4.15(i)): a finite `p`-group `R`
(`p` odd) with `SCN₃(R) = ∅` has `p`-rank `≤ 2`. Assembles the translation
(`normalAbelian_pRank_le_two_of_scn3_empty`, giving `d_n(R) ≤ 2`) with Gorenstein 4.15(i)
(`pRank_le_two_of_normalAbelian_pRank_le_two`). Opens §5 and BG Thm 4.16. -/
theorem pRank_le_two_of_scn3_empty {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hpg : IsPGroup p R) (hSCN : ∀ A : Subgroup R, ¬ IsSCN₃ p A) :
    pRank R p ≤ 2 :=
  pRank_le_two_of_normalAbelian_pRank_le_two hp hpg
    fun _ hB hBc => normalAbelian_pRank_le_two_of_scn3_empty hpg hSCN hB hBc

end OddOrder.BG.Ch1.S04


