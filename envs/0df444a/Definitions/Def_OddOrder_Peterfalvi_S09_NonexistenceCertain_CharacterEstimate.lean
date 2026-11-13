-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_CharacterEstimate
-- name    : OddOrder_Peterfalvi_S09_NonexistenceCertain_CharacterEstimate
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:51:39.396295+00:00
-- url     : https://prove2.me/theorems/6fb517b2-30df-4fe2-b583-5cd227085156
-- title:
--   Peterfalvi (7.10): the character estimate for a Frobenius family
-- statement:
--   Part of the Peterfalvi §7 Frobenius-family development, setting up the quantities of the (7.10) character estimate.
--
--   Main definitions: `kernelSpread` (the set $(H_i^\#)^G$ of conjugates of nonidentity kernel elements), `G0` (the (7.10)(d) set $G_0=G-\bigcup_i(H_i^\#)^G$), `hypothesis71` and `familyHypothesis71` (the (7.1)/(7.4) Dade setup for family members), `h` and `e` (the kernel order $h_i=|H_i|$ and complement index $e_i=|L_i:H_i|$) and `BsumWeight` (the local contribution $(h_j-1)/e_j$).
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_NonexistenceCertain/CharacterEstimate.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_NonexistenceCertain/CharacterEstimate.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_TwoFamilies

namespace OddOrder.Peterfalvi.S09

open OddOrder.Isaacs.Ch06 (IsFrobeniusGroup)

open OddOrder.GroupTheory (IsTISubset)

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

namespace FrobeniusFamily

variable {k : ℕ}

/-- `(H_i^#)^G`: the set of `G`-conjugates of nonidentity elements of the `i`-th
kernel `H_i`. -/
def kernelSpread (F : FrobeniusFamily G k) (i : Fin k) : Set G :=
  {x : G | ∃ g : G, g * x * g⁻¹ ∈ (F.H i : Set G) \ {1}}

/-- **(7.10)(d).** `G₀ = G - ⋃_i (H_i^#)^G`: the elements not conjugate into any
kernel. -/
def G0 (F : FrobeniusFamily G k) : Set G :=
  {x : G | ∀ i, x ∉ F.kernelSpread i}

/-- The implementation of kernelSpread is the usual conjugacy closure of H_i^#. -/
lemma mem_kernelSpread_iff_conjugatesOfSet (F : FrobeniusFamily G k) (i : Fin k)
    {x : G} :
    x ∈ F.kernelSpread i ↔ x ∈ Group.conjugatesOfSet ((F.H i : Set G) \ {1}) := by
  constructor
  · rintro ⟨g, hg⟩
    rw [Group.mem_conjugatesOfSet_iff]
    refine ⟨g * x * g⁻¹, hg, ?_⟩
    rw [isConj_iff]
    refine ⟨g⁻¹, ?_⟩
    group
  · intro hx
    rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨y, hy, hconj⟩
    rcases isConj_iff.mp hconj with ⟨g, hg⟩
    refine ⟨g⁻¹, ?_⟩
    rw [← hg]
    have hback : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    simpa [hback] using hy

lemma kernelSpread_eq_conjugatesOfSet (F : FrobeniusFamily G k) (i : Fin k) :
    F.kernelSpread i = Group.conjugatesOfSet ((F.H i : Set G) \ {1}) := by
  ext x
  exact F.mem_kernelSpread_iff_conjugatesOfSet i

lemma one_not_mem_kernelSpread (F : FrobeniusFamily G k) (i : Fin k) :
    (1 : G) ∉ F.kernelSpread i := by
  rintro ⟨g, hg⟩
  exact hg.2 (by simp)

/-- Elements of L_i = N_G(H_i) conjugate H_i to itself. -/
lemma mem_kernel_conj_iff_of_mem_L (F : FrobeniusFamily G k) (i : Fin k)
    {g x : G} (hg : g ∈ F.L i) :
    g * x * g⁻¹ ∈ F.H i ↔ x ∈ F.H i := by
  have hnorm : g ∈ Subgroup.normalizer (F.H i : Set G) := by
    rw [← F.normalizer_eq i]
    exact hg
  exact (Subgroup.mem_normalizer_iff.mp hnorm x).symm

/-- Elements of L_i conjugate the sharp kernel H_i^# to itself. -/
lemma mem_kernel_sharp_conj_iff_of_mem_L (F : FrobeniusFamily G k) (i : Fin k)
    {g x : G} (hg : g ∈ F.L i) :
    g * x * g⁻¹ ∈ (F.H i : Set G) \ {1} ↔ x ∈ (F.H i : Set G) \ {1} := by
  constructor
  · intro hx
    exact ⟨(F.mem_kernel_conj_iff_of_mem_L i hg).mp hx.1, by
      intro hx1
      exact hx.2 (by simpa using hx1)⟩
  · intro hx
    exact ⟨(F.mem_kernel_conj_iff_of_mem_L i hg).mpr hx.1, by
      intro hconj
      exact hx.2 (conj_eq_one_iff.mp hconj)⟩

/-- **The Peterfalvi (7.1) Dade ρ-setup for the `i`-th family member.**  The kernel `H_i` of the
`i`-th Frobenius subgroup has `H_i^#` a TI-subset of `G` (`isTI`) with normalizer `L_i`
(`normalizer_eq`, so `L_i` conjugates `H_i^#` to itself, `mem_kernel_sharp_conj_iff_of_mem_L`), so
`Hypothesis71.of_isTISubset` builds the full (7.1) datum `Hypothesis71 G (H_i^#) L_i` (with all
`H(a) = ⊥` and the canonical Dade isometry `τ`).  This is the per-member (7.1) input assembled by
(7.4)/(7.10). -/
noncomputable def hypothesis71 [Fintype G] (F : FrobeniusFamily G k) (i : Fin k) :
    Hypothesis71 G (OddOrder.Peterfalvi.S04.sharp (F.H i : Set G)) (F.L i) :=
  Hypothesis71.of_isTISubset
    (fun x hx => OddOrder.Peterfalvi.S04.mem_sharp.mpr
      ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩)
    (fun _x hx => F.kernel_le i (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1)
    (fun l _a ha => (F.mem_kernel_sharp_conj_iff_of_mem_L i l.2).mpr ha)
    (F.isTI i)

/-- **The Dade support of the `i`-th (7.1) datum is the kernel spread** `(H_i^#)^G`.  For the
TI-subset construction every local subgroup `H(a) = ⊥`, so each coset `aH(a) = {a}`, and the Dade
support `⋃_{a ∈ H_i^#} {a}^G` is exactly the conjugacy spread `(H_i^#)^G = kernelSpread i`.  This
identifies the (7.4) disjointness hypothesis `Disjoint (dadeSupport i) (dadeSupport j)` with the
already-proven `kernelSpread_disjoint`. -/
lemma dadeSupport_hypothesis71_eq_kernelSpread [Fintype G] (F : FrobeniusFamily G k) (i : Fin k) :
    (F.hypothesis71 i).hyp.dadeSupport = F.kernelSpread i := by
  rw [F.kernelSpread_eq_conjugatesOfSet i]
  ext g
  rw [OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff, Group.mem_conjugatesOfSet_iff]
  constructor
  · rintro ⟨a, h, hh, hconj⟩
    have hh1 : h = 1 := Subgroup.mem_bot.mp hh
    subst hh1
    exact ⟨a.1, a.2, by simpa using hconj⟩
  · rintro ⟨y, hy, hconj⟩
    exact ⟨⟨y, hy⟩, 1, Subgroup.one_mem _, by simpa using hconj⟩

lemma ne_one_of_mem_kernelSpread (F : FrobeniusFamily G k) {i : Fin k} {x : G}
    (hx : x ∈ F.kernelSpread i) : x ≠ 1 := by
  rintro rfl
  exact F.one_not_mem_kernelSpread i hx

lemma orderOf_dvd_card_kernel_of_mem_kernelSpread [Finite G]
    (F : FrobeniusFamily G k) {i : Fin k} {x : G}
    (hx : x ∈ F.kernelSpread i) : orderOf x ∣ Nat.card (F.H i) := by
  rcases hx with ⟨g, hg⟩
  have hsub : orderOf (⟨g * x * g⁻¹, hg.1⟩ : F.H i) ∣ Nat.card (F.H i) :=
    orderOf_dvd_natCard _
  have hy_dvd : orderOf (g * x * g⁻¹) ∣ Nat.card (F.H i) := by
    simpa [Subgroup.orderOf_mk] using hsub
  have hsc : SemiconjBy g x (g * x * g⁻¹) := by
    rw [SemiconjBy]
    group
  have horder : orderOf x = orderOf (g * x * g⁻¹) := SemiconjBy.orderOf_eq g hsc
  simpa [horder] using hy_dvd

/-- Distinct kernel spreads in Peterfalvi (7.10) are disjoint.  Any element in
their intersection has order dividing both coprime kernel orders, hence is the
identity, contradicting membership in a sharp conjugate spread. -/
lemma kernelSpread_disjoint [Finite G] (F : FrobeniusFamily G k)
    {i j : Fin k} (hij : i ≠ j) : Disjoint (F.kernelSpread i) (F.kernelSpread j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hcop : Nat.Coprime (orderOf x) (Nat.card (F.H j)) :=
    Nat.Coprime.coprime_dvd_left
      (F.orderOf_dvd_card_kernel_of_mem_kernelSpread hxi) (F.coprime_kernel hij)
  have horder_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl
      (F.orderOf_dvd_card_kernel_of_mem_kernelSpread hxj)
  exact F.ne_one_of_mem_kernelSpread hxi (orderOf_eq_one_iff.mp horder_one)

/-- **The (7.4) `FamilyHypothesis71` of a Frobenius family** (Peterfalvi (7.10)(a)-(c) ⟹ (7.4)).
Each member `i` supplies the (7.1) datum `Hypothesis71 G (H_i^#) L_i` (`hypothesis71`), whose Dade
map
is a genuine isometry (`isDadeIsometry_of_isDadeMap`, from `isDadeMap` + `HConjInvariant`); the
supports `A_i^{τ_i} = dadeSupport_i = (H_i^#)^G` are pairwise disjoint by the coprime-kernel
`kernelSpread_disjoint` (via `dadeSupport_hypothesis71_eq_kernelSpread`).  This assembles the (7.4)
input consumed by the (7.5)/(7.10) `characterEstimateData_of_family71_*` machinery. -/
noncomputable def familyHypothesis71 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) : FamilyHypothesis71 G k where
  L := F.L
  A := fun i => OddOrder.Peterfalvi.S04.sharp (F.H i : Set G)
  fintypeL := fun i => Fintype.ofFinite _
  invertibleL := fun i => invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L i)).ne')
  hyp71 := fun i => F.hypothesis71 i
  isDadeIsometry := fun i => by
    let : Fintype ↥(F.L i) := Fintype.ofFinite _
    let : Invertible (Nat.card ↥(F.L i) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L i)).ne')
    exact OddOrder.Peterfalvi.S04.isDadeIsometry_of_isDadeMap (F.hypothesis71 i).hyp
      (F.hypothesis71 i).τ (F.hypothesis71 i).isDadeMap
  pairwise_disjoint := fun i j hij => by
    rw [F.dadeSupport_hypothesis71_eq_kernelSpread i, F.dadeSupport_hypothesis71_eq_kernelSpread j]
    exact F.kernelSpread_disjoint hij

/-- Kernel order `h_i = |H_i|`. -/
noncomputable def h (F : FrobeniusFamily G k) (i : Fin k) : ℕ := Nat.card (F.H i)

/-- Complement index `e_i = |L_i : H_i|` (exact, since `H_i ≤ L_i`). -/
noncomputable def e (F : FrobeniusFamily G k) (i : Fin k) : ℕ :=
  Nat.card (F.L i) / Nat.card (F.H i)

/-- The unweighted local contribution `(h_j - 1) / e_j` attached to an index in
Peterfalvi's `𝓑`-sum.  Naming it keeps the `ℚ`-to-`ℂ` coercion from being
elaborated as a complex division in orthogonality hypotheses. -/
noncomputable def BsumWeight (F : FrobeniusFamily G k) (j : Fin k) : ℚ :=
  ((F.h j : ℚ) - 1) / (F.e j : ℚ)

end FrobeniusFamily

end OddOrder.Peterfalvi.S09


