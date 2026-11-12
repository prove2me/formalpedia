-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_OrbitOnIrr
-- name    : OddOrder_GroupTheory_RepresentationTheory_OrbitOnIrr
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:39:27.091507+00:00
-- url     : https://prove2.me/theorems/9b037a98-91f7-4de5-979f-7827c2499cb5
-- title:
--   Cardinality of an irreducibly-induced family (the $G/H$-orbit count)
-- statement:
--   For a normal subgroup $H\trianglelefteq G$ and a conjugation-invariant finite family $T\subseteq\mathrm{Irr}\,H$, the map $\theta\mapsto\mathrm{Ind}_H^G\theta$ partitions $T$ into fibres, each a whole $G$-conjugation orbit of size $[G:I_G(\theta)]$. When every member induces irreducibly, all fibres have the same size.
--
--   The bundle consists of lemmas only; the main one is `card_image_induce_ge_div`, a lower bound $|T|/[G:H]$ for the size of the irreducibly-induced image.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/OrbitOnIrr.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/OrbitOnIrr.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible

namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]

variable [Fintype G] [Fintype ↥H] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
omit [Fintype ↥H] in
/-- **The irreducibly-induced image has cardinality at least `|T| / [G:H]`** (lower-bound form; no
conjugation-invariance of `T` needed).  For *any* Finset `T ⊆ Irr H` (`H ⊴ G`) whose every member
`θ` has inertia `I_G(θ) = H`, each induction fibre `{θ ∈ T | Ind θ = Ind θ₀}` embeds into the
`G`-conjugation orbit of `θ₀` (`induce_eq_induce_iff_conj`), whose size is `[G:I_G(θ₀)] = [G:H]`; so
`|T| ≤ |image|·[G:H]`, giving `|T| / [G:H] ≤ |image|`.

Unlike `card_image_induce_eq_div`, this drops the `hT` conjugation-closure hypothesis: a lower bound
suffices for the Peterfalvi (9.8.d) family count `|𝒵| ≥ |T|/a`, and dropping `hT` lets the family be
merely inertia-pinned (each member induces irreducibly) rather than a full conjugation-closed set —
sidestepping the `def_Itheta` conjugation-descent entirely. -/
theorem card_image_induce_ge_div
    (T : Finset (IrreducibleCharacter H))
    (hinertia : ∀ θ ∈ T, IrreducibleCharacter.inertia (G := G) (H := H) θ = H) :
    T.card / H.index ≤ (T.image (fun θ => induce H θ.toClassFunction)).card := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  have hidx : 0 < H.index := Nat.pos_of_ne_zero fun h0 => by
    have hmc := H.index_mul_card
    rw [h0, zero_mul] at hmc
    exact (Nat.card_pos (α := G)).ne' hmc.symm
  -- `|T| = ∑_{χ ∈ image} |fibre_χ| ≤ |image|·[G:H]` (each fibre embeds in a `[G:H]`-orbit).
  have hle : T.card
      ≤ (T.image (fun θ => induce H θ.toClassFunction)).card * H.index := by
    rw [Finset.card_eq_sum_card_image (fun θ => induce H θ.toClassFunction) T]
    calc ∑ χ ∈ T.image (fun θ => induce H θ.toClassFunction),
            (T.filter fun θ => induce H θ.toClassFunction = χ).card
        ≤ ∑ _χ ∈ T.image (fun θ => induce H θ.toClassFunction), H.index := by
          refine Finset.sum_le_sum fun χ hχ => ?_
          obtain ⟨θ₀, hθ₀T, hθ₀eq⟩ := Finset.mem_image.mp hχ
          -- the fibre over `χ` embeds into `conjByOrbit θ₀`, of size `[G:I(θ₀)] = [G:H]`.
          have hO : (IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀).Finite := by
            unfold IrreducibleCharacter.conjByOrbit; exact Set.finite_range _
          have hFsub : (T.filter fun θ => induce H θ.toClassFunction = χ) ⊆ hO.toFinset := by
            intro θ hθ
            rw [Finset.mem_filter] at hθ
            rw [Set.Finite.mem_toFinset, IrreducibleCharacter.mem_conjByOrbit]
            have h2 : induce H θ.toClassFunction = induce H θ₀.toClassFunction :=
              hθ.2.trans hθ₀eq.symm
            obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj θ θ₀).mp h2
            exact ⟨g⁻¹, by rw [← hg, ← IrreducibleCharacter.conjBy_mul]; simp⟩
          calc (T.filter fun θ => induce H θ.toClassFunction = χ).card
              ≤ hO.toFinset.card := Finset.card_le_card hFsub
            _ = (IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀).ncard :=
                (Set.ncard_eq_toFinset_card _ hO).symm
            _ = Nat.card (IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀) :=
                (Nat.card_coe_set_eq _).symm
            _ = (IrreducibleCharacter.inertia (G := G) (H := H) θ₀).index :=
                card_conjByOrbit_eq_index_inertia θ₀
            _ = H.index := by rw [hinertia θ₀ hθ₀T]
      _ = (T.image (fun θ => induce H θ.toClassFunction)).card * H.index := by
          rw [Finset.sum_const, smul_eq_mul]
  -- `|T| ≤ |image|·[G:H]` ⟹ `|T|/[G:H] ≤ |image|`.
  calc T.card / H.index
      ≤ ((T.image (fun θ => induce H θ.toClassFunction)).card * H.index) / H.index :=
        Nat.div_le_div_right hle
    _ = (T.image (fun θ => induce H θ.toClassFunction)).card := Nat.mul_div_cancel _ hidx

end OddOrder.RepresentationTheory


