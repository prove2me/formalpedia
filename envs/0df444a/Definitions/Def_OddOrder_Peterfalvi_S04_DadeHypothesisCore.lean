-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S04_DadeHypothesisCore
-- name    : OddOrder_Peterfalvi_S04_DadeHypothesisCore
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:39.038952+00:00
-- url     : https://prove2.me/theorems/46d36de2-bb5c-48aa-9de5-8fd138d7ee28
-- title:
--   Peterfalvi (2.2): the Dade hypothesis, core structure
-- statement:
--   Formalizes the `Hypothesis` structure of Peterfalvi (2.2) (the setting of the Dade isometry), the layer of supported class functions, and the basic API up to the TI-subset specialization.
--
--   Main definitions: `sharp` ($A^\#=A\setminus\{1\}$), `centralizerIn` ($C_L(a)$ in the ambient group), `supportInSubgroup`, `SupportedClassFunctions` (Peterfalvi's $\mathrm{CF}(L,A)$: class functions on $L$ supported on $A$), `inclusion` ($\mathrm{CF}(L,A_1)\to\mathrm{CF}(L,A)$ for $A_1\subseteq A$) and `Hypothesis` (Peterfalvi Hypothesis (2.2)).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S04_DadeHypothesisCore.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S04_DadeHypothesisCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_GroupTheory_CoprimeConjugacy
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassFunction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrr
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

namespace OddOrder.Peterfalvi.S04

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The nonidentity part `A# = A \ {1}`. -/
def sharp (A : Set G) : Set G :=
  A \ {1}

@[simp] theorem mem_sharp {A : Set G} {g : G} :
    g ∈ sharp A ↔ g ∈ A ∧ g ≠ 1 := by
  simp [sharp]

/-- `C_L(a)`, viewed as a subgroup of the ambient group `G`. -/
def centralizerIn (L : Subgroup G) (a : G) : Subgroup G :=
  L ⊓ Subgroup.centralizer ({a} : Set G)

@[simp] theorem mem_centralizerIn {L : Subgroup G} {a x : G} :
    x ∈ centralizerIn L a ↔ x ∈ L ∧ x * a = a * x := by
  simp [centralizerIn, Subgroup.mem_centralizer_singleton_iff]

/-- Conjugation by `l ∈ L` is an order-preserving bijection
`C_L(l a l⁻¹) ≃ C_L(a)`, so `|C_L(l a l⁻¹)| = |C_L(a)|`.  Used to see that the
centralizers `C_L(a)` are constant on each `L`-conjugacy class. -/
theorem card_centralizerIn_conj {L : Subgroup G} {l : G} (hl : l ∈ L) (a : G) :
    Nat.card (centralizerIn L (l * a * l⁻¹)) = Nat.card (centralizerIn L a) := by
  apply Nat.card_congr
  refine
    { toFun := fun c => ⟨l⁻¹ * c.1 * l, ?_⟩
      invFun := fun c => ⟨l * c.1 * l⁻¹, ?_⟩
      left_inv := fun c => Subtype.ext (by group)
      right_inv := fun c => Subtype.ext (by group) }
  · obtain ⟨hcL, hcomm⟩ := mem_centralizerIn.mp c.2
    refine mem_centralizerIn.mpr ⟨L.mul_mem (L.mul_mem (L.inv_mem hl) hcL) hl, ?_⟩
    calc (l⁻¹ * c.1 * l) * a
        = l⁻¹ * (c.1 * (l * a * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * a * l⁻¹) * c.1) * l := by rw [hcomm]
      _ = a * (l⁻¹ * c.1 * l) := by group
  · obtain ⟨hcL, hcomm⟩ := mem_centralizerIn.mp c.2
    refine mem_centralizerIn.mpr ⟨L.mul_mem (L.mul_mem hl hcL) (L.inv_mem hl), ?_⟩
    calc (l * c.1 * l⁻¹) * (l * a * l⁻¹)
        = l * (c.1 * a) * l⁻¹ := by group
      _ = l * (a * c.1) * l⁻¹ := by rw [hcomm]
      _ = (l * a * l⁻¹) * (l * c.1 * l⁻¹) := by group

/-- **`L`-conjugator count.**  If `b` lies in the `L`-conjugacy class of `a`, the
set of `l ∈ L` conjugating `a` to `b` is a left coset of `C_L(a)`, hence has
cardinality `|C_L(a)|`. -/
theorem card_conjugatorIn_L {L : Subgroup G} {a b : G}
    (h : ∃ l : L, (l : G) * a * (l : G)⁻¹ = b) :
    Nat.card {l : L // (l : G) * a * (l : G)⁻¹ = b}
      = Nat.card (centralizerIn L a) := by
  obtain ⟨l₀, hl₀⟩ := h
  apply Nat.card_congr
  refine
    { toFun := fun l => ⟨(l₀ : G)⁻¹ * (l.1 : G), ?_⟩
      invFun := fun c => ⟨⟨(l₀ : G) * c.1, L.mul_mem l₀.2 (mem_centralizerIn.mp c.2).1⟩, ?_⟩
      left_inv := fun l => Subtype.ext (Subtype.ext (by group))
      right_inv := fun c => Subtype.ext (by group) }
  · refine mem_centralizerIn.mpr ⟨L.mul_mem (L.inv_mem l₀.2) l.1.2, ?_⟩
    have e1 : (l.1 : G) * a * (l.1 : G)⁻¹ = (l₀ : G) * a * (l₀ : G)⁻¹ := by rw [l.2, hl₀]
    have hsas : ((l₀ : G)⁻¹ * (l.1 : G)) * a * ((l₀ : G)⁻¹ * (l.1 : G))⁻¹ = a := by
      calc ((l₀ : G)⁻¹ * (l.1 : G)) * a * ((l₀ : G)⁻¹ * (l.1 : G))⁻¹
          = (l₀ : G)⁻¹ * ((l.1 : G) * a * (l.1 : G)⁻¹) * (l₀ : G) := by group
        _ = (l₀ : G)⁻¹ * ((l₀ : G) * a * (l₀ : G)⁻¹) * (l₀ : G) := by rw [e1]
        _ = a := by group
    exact mul_inv_eq_iff_eq_mul.mp hsas
  · have hc : c.1 * a = a * c.1 := (mem_centralizerIn.mp c.2).2
    calc ((l₀ : G) * c.1) * a * ((l₀ : G) * c.1)⁻¹
        = (l₀ : G) * (c.1 * a * c.1⁻¹) * (l₀ : G)⁻¹ := by group
      _ = (l₀ : G) * a * (l₀ : G)⁻¹ := by
          rw [show c.1 * a * c.1⁻¹ = a from by rw [hc]; group]
      _ = b := hl₀

/-- The subset of a subgroup `L` obtained by restricting an ambient subset
`A ⊆ G` to elements of `L`. -/
def supportInSubgroup (A : Set G) (L : Subgroup G) : Set L :=
  {x | (x : G) ∈ A}

@[simp] theorem mem_supportInSubgroup {A : Set G} {L : Subgroup G} {x : L} :
    x ∈ supportInSubgroup A L ↔ (x : G) ∈ A := Iff.rfl

theorem supportInSubgroup_mono {A₁ A : Set G} {L : Subgroup G} (hA₁A : A₁ ⊆ A) :
    supportInSubgroup A₁ L ⊆ supportInSubgroup A L := fun _ hx => hA₁A hx

/-- Peterfalvi's `CF(L,A)`: class functions on `L` supported on the ambient
subset `A`. -/
abbrev SupportedClassFunctions (k : Type*) [CommRing k] (A : Set G) (L : Subgroup G) :=
  ↥(ClassFunction.supportedSubmodule (G := L) (k := k) (supportInSubgroup A L))

namespace SupportedClassFunctions

variable {k : Type*} [CommRing k]

variable {A A₁ : Set G} {L : Subgroup G}

/-- The natural inclusion `CF(L,A₁) → CF(L,A)` induced by `A₁ ⊆ A`.

This is the domain map used by the restriction statement in Peterfalvi (2.11). -/
def inclusion (hA₁A : A₁ ⊆ A) :
    (SupportedClassFunctions (G := G) k A₁ L) →ₗ[k]
      (SupportedClassFunctions (G := G) k A L) :=
  Submodule.inclusion (by
    intro φ hφ
    exact fun x hx => hA₁A (hφ hx))

@[simp] theorem coe_inclusion (hA₁A : A₁ ⊆ A)
    (α : SupportedClassFunctions (G := G) k A₁ L) :
    ((inclusion (G := G) (k := k) (L := L) hA₁A α :
        SupportedClassFunctions (G := G) k A L) : ClassFunction L k) =
      (α : ClassFunction L k) :=
  rfl

@[simp] theorem inclusion_apply (hA₁A : A₁ ⊆ A)
    (α : SupportedClassFunctions (G := G) k A₁ L) (x : L) :
    ((inclusion (G := G) (k := k) (L := L) hA₁A α :
        SupportedClassFunctions (G := G) k A L) : ClassFunction L k) x =
      (α : ClassFunction L k) x :=
  rfl

end SupportedClassFunctions

/-- **Peterfalvi Hypothesis (2.2).**

The centralizer decomposition `(2.2.b)` is encoded as a product-like pair of
fields:

* `centralizer_eq_sup`: `C_G(a) = H(a) ⊔ C_L(a)`;
* `centralizer_disjoint`: `H(a) ⊓ C_L(a) = ⊥` in `Disjoint` form.

This keeps the statement usable before a dedicated semidirect-product predicate
for internal subgroup products is introduced. -/
structure Hypothesis (G : Type*) [Group G] [Fintype G] (A : Set G) (L : Subgroup G) where
  subset_sharp : A ⊆ sharp (Set.univ : Set G)
  subset_L : A ⊆ L
  L_normalizes_A : ∀ (l : L) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A
  H : {a : G // a ∈ A} → Subgroup G
  conj_in_L :
    ∀ ⦃a b : G⦄, a ∈ A → b ∈ A → IsConj a b →
      ∃ l : L, (l : G) * a * (l : G)⁻¹ = b
  centralizer_eq_sup :
    ∀ a : {a : G // a ∈ A},
      Subgroup.centralizer ({a.1} : Set G) = H a ⊔ centralizerIn L a.1
  centralizer_disjoint :
    ∀ a : {a : G // a ∈ A}, Disjoint (H a) (centralizerIn L a.1)
  /-- `H(a)` is normal in `C_G(a)`: the normal-complement half of the
  semidirect product `(2.2.b)` `C_G(a) = H(a) ⋊ C_L(a)`.  Without this the join
  `H(a) ⊔ C_L(a)` need not have cardinality `|H(a)|·|C_L(a)|`. -/
  H_normalized :
    ∀ (a : {a : G // a ∈ A}) (c : G),
      c ∈ Subgroup.centralizer ({a.1} : Set G) → ∀ x ∈ H a, c * x * c⁻¹ ∈ H a
  centralizer_coprime :
    ∀ a b : {a : G // a ∈ A},
      Nat.Coprime (Nat.card (H a)) (Nat.card (centralizerIn L b.1))

namespace Hypothesis

variable {A A₁ : Set G} {L : Subgroup G}

variable [Fintype G]

theorem mem_L (hyp : Hypothesis G A L) {a : G} (ha : a ∈ A) : a ∈ L :=
  hyp.subset_L ha

theorem ne_one (hyp : Hypothesis G A L) {a : G} (ha : a ∈ A) : a ≠ 1 :=
  (mem_sharp.mp (hyp.subset_sharp ha)).2

/-- One direction of **Peterfalvi (2.3)**: under Hypothesis (2.2), if all
subgroups `H(a)` are trivial, then `A` is a TI-subset relative to `L`. -/
theorem isTISubset_of_forall_H_eq_bot (hyp : Hypothesis G A L)
    (hH : ∀ a : {a : G // a ∈ A}, hyp.H a = ⊥) :
    OddOrder.GroupTheory.IsTISubset A L := by
  intro g hgap
  rcases hgap with ⟨a, ha, hga⟩
  have hconj : IsConj a (g * a * g⁻¹) := by
    rw [isConj_iff]
    exact ⟨g, rfl⟩
  rcases hyp.conj_in_L ha hga hconj with ⟨l, hl⟩
  let y : G := (l : G)⁻¹ * g
  have hy_comm_left : a * y = y * a := by
    change a * ((l : G)⁻¹ * g) = ((l : G)⁻¹ * g) * a
    calc
      a * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * g := by
        group
      _ = (l : G)⁻¹ * (g * a * g⁻¹) * g := by rw [hl]
      _ = ((l : G)⁻¹ * g) * a := by
        group
  have hy_cent : y ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hy_comm_left.symm
  have hcent_eq := hyp.centralizer_eq_sup ⟨a, ha⟩
  rw [hH ⟨a, ha⟩, bot_sup_eq] at hcent_eq
  have hy_in_centralizerIn : y ∈ centralizerIn L a := by
    rw [← hcent_eq]
    exact hy_cent
  have hy_L : y ∈ L := (mem_centralizerIn.mp hy_in_centralizerIn).1
  have hg : (l : G) * y ∈ L := L.mul_mem l.property hy_L
  have hg_eq : (l : G) * y = g := by
    simp [y]
  exact hg_eq ▸ hg

/-- The other direction of **Peterfalvi (2.3)** in the relative-normalizer API:
from a TI-subset relative to `L`, build Hypothesis (2.2) with all `H(a)=⊥`.

Peterfalvi also states `L = N_G(A)` when `A` is nonempty.  This file keeps
`L` as an explicit normalizer-bound, so the theorem takes the required
`A ⊆ L` and `L`-normalizes-`A` assumptions as fields. -/
def of_isTISubset (hA_sharp : A ⊆ sharp (Set.univ : Set G)) (hA_L : A ⊆ L)
    (hL_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (hTI : OddOrder.GroupTheory.IsTISubset A L) :
    Hypothesis G A L where
  subset_sharp := hA_sharp
  subset_L := hA_L
  L_normalizes_A := hL_norm
  H := fun _ => ⊥
  conj_in_L := by
    intro a b ha hb hconj
    rcases isConj_iff.mp hconj with ⟨g, rfl⟩
    exact ⟨⟨g, hTI g ⟨a, ha, hb⟩⟩, rfl⟩
  centralizer_eq_sup := by
    intro a
    rw [bot_sup_eq]
    ext x
    constructor
    · intro hx
      have hx_comm : x * a.1 = a.1 * x := by
        simpa [Subgroup.mem_centralizer_singleton_iff] using hx
      have hx_conj : x * a.1 * x⁻¹ = a.1 := by
        calc
          x * a.1 * x⁻¹ = a.1 * x * x⁻¹ := by rw [hx_comm]
          _ = a.1 := by group
      have hx_L : x ∈ L := hTI x ⟨a.1, a.2, by simp [hx_conj, a.2]⟩
      rw [mem_centralizerIn]
      exact ⟨hx_L, hx_comm⟩
    · intro hx
      rw [mem_centralizerIn] at hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hx.2
  centralizer_disjoint := fun _ => disjoint_bot_left
  H_normalized := fun _ _ _ x hx => by
    rw [Subgroup.mem_bot.mp hx, mul_one, mul_inv_cancel]; exact (⊥ : Subgroup G).one_mem
  centralizer_coprime := fun _ _ => by
    simp

@[simp] theorem of_isTISubset_H (hA_sharp : A ⊆ sharp (Set.univ : Set G))
    (hA_L : A ⊆ L)
    (hL_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (hTI : OddOrder.GroupTheory.IsTISubset A L) (a : {a : G // a ∈ A}) :
    (of_isTISubset hA_sharp hA_L hL_norm hTI).H a = ⊥ :=
  rfl

/-- If the full centralizer of a point `a ∈ A` lies in `L`, then the local
subgroup `H(a)` of **any** Hypothesis (2.2) datum on `(A, L)` is trivial:
`H(a) ≤ C_G(a)` by `centralizer_eq_sup`, so `C_G(a) ≤ L` places `H(a)` inside
`C_L(a)`, and `centralizer_disjoint` then forces `H(a) = ⊥`.

This is data-independent — it reads only the proof fields of the hypothesis, so
it applies to opaque (2.2) data (e.g. a packaged `dadeData` field) without
knowing how its `H` was constructed. -/
theorem H_eq_bot_of_centralizer_le (hyp : Hypothesis G A L)
    (a : {a : G // a ∈ A})
    (hle : Subgroup.centralizer ({a.1} : Set G) ≤ L) : hyp.H a = ⊥ := by
  have hHle : hyp.H a ≤ Subgroup.centralizer ({a.1} : Set G) :=
    le_sup_left.trans (hyp.centralizer_eq_sup a).ge
  have hHin : hyp.H a ≤ centralizerIn L a.1 := by
    rw [centralizerIn]
    exact le_inf (hHle.trans hle) hHle
  exact (hyp.centralizer_disjoint a).eq_bot_of_le hHin

/-- The reverse direction of **Peterfalvi (2.3)**: over a TI-subset `A`
relative to `L`, **every** Hypothesis (2.2) datum has all local subgroups
trivial, `H(a) = ⊥` — not just the canonical `of_isTISubset` one.  (TI places
the whole centralizer `C_G(a) ≤ L` for `a ∈ A`, cf.
`IsTISubset.centralizer_le`.)  Combined with the uniqueness
`dadeHypothesis_eq_of_forall_H_eq_bot` (`S12_TICyclicSigmaBridge`), the (2.2)
datum on a TI pair `(A, L)` is therefore unique. -/
theorem H_eq_bot_of_isTISubset (hyp : Hypothesis G A L)
    (hTI : OddOrder.GroupTheory.IsTISubset A L) (a : {a : G // a ∈ A}) :
    hyp.H a = ⊥ :=
  hyp.H_eq_bot_of_centralizer_le a (hTI.centralizer_le a.2)

end Hypothesis

end OddOrder.Peterfalvi.S04


