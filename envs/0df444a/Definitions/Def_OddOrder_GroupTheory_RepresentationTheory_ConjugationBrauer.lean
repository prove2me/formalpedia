-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ConjugationBrauer
-- name    : OddOrder_GroupTheory_RepresentationTheory_ConjugationBrauer
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:12:15.637043+00:00
-- url     : https://prove2.me/theorems/ab5b46ec-5fe6-45ae-b64f-5d8aeb600649
-- title:
--   Brauer's permutation lemma for ambient conjugation
-- statement:
--   Starts the conjugation-specific packaging of Brauer's permutation lemma. For a normal subgroup $H\trianglelefteq G$ and $g\in G$, conjugation by $g$ gives compatible permutations of $\mathrm{Irr}\,H$ and of the conjugacy classes of $H$, whose fixed-point counts agree by the general lemma. This is the bridge needed by Peterfalvi (6.8): later files combine the fixed conjugacy-class side with Frobenius fixed-point-freeness to prove $I_G(\theta)=H$ for nontrivial $\theta$.
--
--   Main definitions: two `conjByPerm`, the permutation of $\mathrm{Irr}\,H$ and the permutation of conjugacy classes of $H$ induced by ambient conjugation.
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ConjugationBrauer.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ConjugationBrauer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutation
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Clifford
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] {H : Subgroup G} [H.Normal]

namespace IrreducibleCharacter

/-- The permutation of `Irr H` induced by ambient conjugation by `g : G`. -/
noncomputable def conjByPerm (g : G) : Equiv.Perm (IrreducibleCharacter H) where
  toFun θ := conjBy (G := G) (H := H) g θ
  invFun θ := conjBy (G := G) (H := H) g⁻¹ θ
  left_inv θ := by
    exact conjBy_inv_conjBy (G := G) (H := H) g θ
  right_inv θ := by
    exact conjBy_conjBy_inv (G := G) (H := H) g θ

@[simp] theorem conjByPerm_apply (g : G) (θ : IrreducibleCharacter H) :
    conjByPerm (G := G) (H := H) g θ = conjBy (G := G) (H := H) g θ :=
  rfl

end IrreducibleCharacter

namespace ConjClasses

/-- The permutation of conjugacy classes of `H` induced by ambient conjugation by `g : G`. -/
noncomputable def conjByPerm (g : G) : Equiv.Perm (ConjClasses H) where
  toFun := ConjClasses.map (ClassFunction.conjByMulEquiv (G := G) (H := H) g : H →* H)
  invFun := ConjClasses.map (ClassFunction.conjByMulEquiv (G := G) (H := H) g⁻¹ : H →* H)
  left_inv C := by
    rcases ConjClasses.exists_rep C with ⟨h, rfl⟩
    change ConjClasses.mk
        (ClassFunction.conjByMulEquiv (G := G) (H := H) g⁻¹
          (ClassFunction.conjByMulEquiv (G := G) (H := H) g h)) = ConjClasses.mk h
    have hh :
        ClassFunction.conjByMulEquiv (G := G) (H := H) g⁻¹
            (ClassFunction.conjByMulEquiv (G := G) (H := H) g h) = h := by
      apply Subtype.ext
      simp only [ClassFunction.conjByMulEquiv_apply]
      group
    rw [hh]
  right_inv C := by
    rcases ConjClasses.exists_rep C with ⟨h, rfl⟩
    change ConjClasses.mk
        (ClassFunction.conjByMulEquiv (G := G) (H := H) g
          (ClassFunction.conjByMulEquiv (G := G) (H := H) g⁻¹ h)) = ConjClasses.mk h
    have hh :
        ClassFunction.conjByMulEquiv (G := G) (H := H) g
            (ClassFunction.conjByMulEquiv (G := G) (H := H) g⁻¹ h) = h := by
      apply Subtype.ext
      simp only [ClassFunction.conjByMulEquiv_apply]
      group
    rw [hh]

@[simp] theorem conjByPerm_mk (g : G) (h : H) :
    conjByPerm (G := G) (H := H) g (ConjClasses.mk h) =
      ConjClasses.mk (ClassFunction.conjByMulEquiv (G := G) (H := H) g h) :=
  rfl

@[simp] theorem conjByPerm_one (g : G) :
    conjByPerm (G := G) (H := H) g (1 : ConjClasses H) = 1 := by
  change conjByPerm (G := G) (H := H) g (ConjClasses.mk (1 : H)) =
    ConjClasses.mk (1 : H)
  rw [conjByPerm_mk]
  simp

/-- If the centralizer of every nonidentity element of `H` lies in `H`, then an element
outside `H` can only fix the identity conjugacy class of `H`. -/
theorem fixed_eq_one_of_not_mem_of_centralizer_le (g : G) (hg : g ∉ H)
    (hcent : ∀ h : H, h ≠ 1 → Subgroup.centralizer ({(h : G)} : Set G) ≤ H)
    {C : ConjClasses H} (hfix : conjByPerm (G := G) (H := H) g C = C) :
    C = 1 := by
  rcases ConjClasses.exists_rep C with ⟨h, rfl⟩
  by_cases hh : h = 1
  · rw [hh, ConjClasses.one_eq_mk_one]
  exfalso
  have hmk :
      ConjClasses.mk (ClassFunction.conjByMulEquiv (G := G) (H := H) g h) =
        ConjClasses.mk h := by
    simpa [conjByPerm_mk] using hfix
  have hisConj :
      IsConj (ClassFunction.conjByMulEquiv (G := G) (H := H) g h) h :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hmk
  obtain ⟨c, hc⟩ := isConj_iff.mp hisConj
  have hcG :
      (c : G) * (g * (h : G) * g⁻¹) * (c : G)⁻¹ = (h : G) := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, ClassFunction.conjByMulEquiv_apply]
      using congrArg Subtype.val hc
  have hxconj :
      ((c : G) * g) * (h : G) * (((c : G) * g)⁻¹) = (h : G) := by
    simpa [mul_assoc] using hcG
  have hxcent : (c : G) * g ∈ Subgroup.centralizer ({(h : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmul := congrArg (fun y : G => y * ((c : G) * g)) hxconj
    simpa [mul_assoc] using hmul
  have hxH : (c : G) * g ∈ H := hcent h hh hxcent
  have hgH : g ∈ H := by
    have hcH : (c : G) ∈ H := c.property
    have hprod : (c : G)⁻¹ * ((c : G) * g) ∈ H := H.mul_mem (H.inv_mem hcH) hxH
    simpa [mul_assoc] using hprod
  exact hg hgH

end ConjClasses

/-- **Abelian fixed-class bridge.**  When `H` is abelian (all of its elements commute) and the
ambient centralizer of `g : G` meets `H` only in the identity (`C_G(g) ⊓ H = ⊥`), the conjugation
permutation of the conjugacy classes of `H` by `g` fixes exactly one class — the identity class.

For abelian `H` conjugacy classes are singletons, so a `g`-fixed class `⟦h⟧` forces
`g·h·g⁻¹ = h`, i.e. `h ∈ C_G(g) ⊓ H = ⊥`, hence `h = 1`.  This is the (6.8)(c2) replacement for
`card_fixedPoints_conjClassPerm_eq_one_of_not_mem_of_centralizer_le`, which needs the full
Frobenius centralizer condition `C_G(h) ≤ H` (false in the quotient `H̄`, where `H̄ ≤ C(h̄)`); the
abelian quotient `H̄ = H/⁅H,H⁆` only supplies `C_{H̄}(ḡ) = 1` and abelianness. -/
theorem card_fixedPoints_conjClassPerm_eq_one_of_commute_of_centralizer_inf_eq_bot
    [Finite H] (g : G) (hcomm : ∀ a b : H, Commute a b)
    (hbot : Subgroup.centralizer ({g} : Set G) ⊓ H = ⊥) :
    Nat.card (Function.fixedPoints (ConjClasses.conjByPerm (G := G) (H := H) g)) = 1 := by
  -- Both fixed classes are the identity class: a fixed `⟦h⟧` forces `h ∈ C_G(g) ⊓ H = ⊥`.
  have hfix_one : ∀ E : Function.fixedPoints (ConjClasses.conjByPerm (G := G) (H := H) g),
      (E : ConjClasses H) = 1 := by
    rintro ⟨E, hE⟩
    rcases ConjClasses.exists_rep E with ⟨h, rfl⟩
    have hmk :
        ConjClasses.mk (ClassFunction.conjByMulEquiv (G := G) (H := H) g h) = ConjClasses.mk h := by
      simpa [ConjClasses.conjByPerm_mk] using hE.eq
    have hisConj :
        IsConj (ClassFunction.conjByMulEquiv (G := G) (H := H) g h) h :=
      ConjClasses.mk_eq_mk_iff_isConj.mp hmk
    -- In an abelian `H`, conjugacy is equality.
    have heq : ClassFunction.conjByMulEquiv (G := G) (H := H) g h = h := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hisConj
      have hcomm_ch := (hcomm c (ClassFunction.conjByMulEquiv (G := G) (H := H) g h))
      rw [hcomm_ch.eq, mul_inv_cancel_right] at hc
      exact hc
    -- `h` centralizes `g` and lies in `H`, hence in `⊥`.
    have hcent : (h : G) ∈ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hval : g * (h : G) * g⁻¹ = (h : G) := congrArg Subtype.val heq
      have := congrArg (fun z : G => z * g) hval
      simpa [mul_assoc] using this.symm
    have hh_bot : (h : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]; exact Subgroup.mem_inf.mpr ⟨hcent, h.property⟩
    have hh_one : h = 1 := by
      apply Subtype.ext
      simpa using (Subgroup.mem_bot.mp hh_bot)
    change ConjClasses.mk h = 1
    rw [hh_one]
    exact ConjClasses.one_eq_mk_one.symm
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun C D => Subtype.ext ((hfix_one C).trans (hfix_one D).symm)⟩,
    ⟨⟨1, ConjClasses.conjByPerm_one (G := G) (H := H) g⟩⟩⟩

/-- Compatibility of ambient conjugation on irreducible characters with ambient conjugation on
conjugacy classes, in the exact form consumed by `brauer_permutation_lemma_general'`. -/
theorem characterTableEntry_conjByPerm
    (g : G) (χ : IrreducibleCharacter H) (C : ConjClasses H) :
    characterTableEntry (IrreducibleCharacter.conjByPerm (G := G) (H := H) g χ) C =
      characterTableEntry χ (ConjClasses.conjByPerm (G := G) (H := H) g C) := by
  rcases ConjClasses.exists_rep C with ⟨h, rfl⟩
  rw [ConjClasses.conjByPerm_mk, characterTableEntry_mk, characterTableEntry_mk]
  change (ClassFunction.conjBy (G := G) (H := H) g (χ : ClassFunction H ℂ)) h =
    (χ : ClassFunction H ℂ) (ClassFunction.conjByMulEquiv (G := G) (H := H) g h)
  rfl

/-- Brauer's permutation lemma specialized to ambient conjugation by `g : G`. -/
theorem card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm
    [Finite H] (g : G) :
    Nat.card (Function.fixedPoints (IrreducibleCharacter.conjByPerm (G := G) (H := H) g)) =
      Nat.card (Function.fixedPoints (ConjClasses.conjByPerm (G := G) (H := H) g)) :=
  brauer_permutation_lemma_general'
    (IrreducibleCharacter.conjByPerm (G := G) (H := H) g)
    (ConjClasses.conjByPerm (G := G) (H := H) g)
    (characterTableEntry_conjByPerm (G := G) (H := H) g)

/-- Under the usual fixed-point-free centralizer condition, an element outside `H` fixes exactly
one conjugacy class of `H`: the identity class. -/
theorem card_fixedPoints_conjClassPerm_eq_one_of_not_mem_of_centralizer_le [Finite H]
    (g : G) (hg : g ∉ H)
    (hcent : ∀ h : H, h ≠ 1 → Subgroup.centralizer ({(h : G)} : Set G) ≤ H) :
    Nat.card (Function.fixedPoints (ConjClasses.conjByPerm (G := G) (H := H) g)) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun C D => Subtype.ext ?_⟩,
    ⟨⟨1, ConjClasses.conjByPerm_one (G := G) (H := H) g⟩⟩⟩
  have hC : (C : ConjClasses H) = 1 :=
    ConjClasses.fixed_eq_one_of_not_mem_of_centralizer_le
      (G := G) (H := H) g hg hcent C.2
  have hD : (D : ConjClasses H) = 1 :=
    ConjClasses.fixed_eq_one_of_not_mem_of_centralizer_le
      (G := G) (H := H) g hg hcent D.2
  exact hC.trans hD.symm

@[simp] theorem conjByPerm_trivialIrreducibleCharacter (g : G) :
    IrreducibleCharacter.conjByPerm (G := G) (H := H) g
        (trivialIrreducibleCharacter H) = trivialIrreducibleCharacter H := by
  apply IrreducibleCharacter.ext
  ext h
  simp [IrreducibleCharacter.conjByPerm]

/-- If the conjugation permutation fixes exactly one conjugacy class, any fixed irreducible
character is the trivial character. -/
theorem fixed_irreducible_eq_trivial_of_card_fixedClasses_eq_one [Finite H]
    (g : G)
    (hclass : Nat.card (Function.fixedPoints (ConjClasses.conjByPerm (G := G) (H := H) g)) = 1)
    {θ : IrreducibleCharacter H}
    (hθ : IrreducibleCharacter.conjByPerm (G := G) (H := H) g θ = θ) :
    θ = trivialIrreducibleCharacter H := by
  have hirr_card :
      Nat.card (Function.fixedPoints (IrreducibleCharacter.conjByPerm (G := G) (H := H) g)) = 1 :=
    (card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm
      (G := G) (H := H) g).trans hclass
  have hsub :
      Subsingleton (Function.fixedPoints (IrreducibleCharacter.conjByPerm (G := G) (H := H) g)) :=
    (Nat.card_eq_one_iff_unique.mp hirr_card).1
  let θfix : Function.fixedPoints (IrreducibleCharacter.conjByPerm (G := G) (H := H) g) :=
    ⟨θ, hθ⟩
  let onefix : Function.fixedPoints (IrreducibleCharacter.conjByPerm (G := G) (H := H) g) :=
    ⟨trivialIrreducibleCharacter H,
      conjByPerm_trivialIrreducibleCharacter (G := G) (H := H) g⟩
  exact congrArg Subtype.val (Subsingleton.elim θfix onefix)

/-- Contrapositive form: under the same one-fixed-class hypothesis, a nontrivial irreducible
character is not fixed by the conjugation permutation. -/
theorem conjByPerm_ne_self_of_ne_trivial_of_card_fixedClasses_eq_one [Finite H]
    (g : G)
    (hclass : Nat.card (Function.fixedPoints (ConjClasses.conjByPerm (G := G) (H := H) g)) = 1)
    {θ : IrreducibleCharacter H} (hθ_ne : θ ≠ trivialIrreducibleCharacter H) :
    IrreducibleCharacter.conjByPerm (G := G) (H := H) g θ ≠ θ := by
  intro hfix
  exact hθ_ne (fixed_irreducible_eq_trivial_of_card_fixedClasses_eq_one
    (G := G) (H := H) g hclass hfix)

/-- Inertia form of the one-fixed-class bridge. -/
theorem not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one [Finite H]
    (g : G)
    (hclass : Nat.card (Function.fixedPoints (ConjClasses.conjByPerm (G := G) (H := H) g)) = 1)
    {θ : IrreducibleCharacter H} (hθ_ne : θ ≠ trivialIrreducibleCharacter H) :
    g ∉ IrreducibleCharacter.inertia (G := G) (H := H) θ := by
  intro hg
  rw [IrreducibleCharacter.mem_inertia] at hg
  exact conjByPerm_ne_self_of_ne_trivial_of_card_fixedClasses_eq_one
    (G := G) (H := H) g hclass hθ_ne (by simpa using hg)

/-- Pointwise inertia exclusion from the centralizer form of the free conjugation action. -/
theorem not_mem_inertia_of_ne_trivial_of_not_mem_of_centralizer_le [Finite H]
    (g : G) (hg : g ∉ H)
    (hcent : ∀ h : H, h ≠ 1 → Subgroup.centralizer ({(h : G)} : Set G) ≤ H)
    {θ : IrreducibleCharacter H} (hθ_ne : θ ≠ trivialIrreducibleCharacter H) :
    g ∉ IrreducibleCharacter.inertia (G := G) (H := H) θ := by
  exact not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one
    (G := G) (H := H) g
    (card_fixedPoints_conjClassPerm_eq_one_of_not_mem_of_centralizer_le
      (G := G) (H := H) g hg hcent)
    hθ_ne

/-- Free ambient conjugation on nonidentity classes forces the inertia group of a nontrivial
irreducible character to be exactly `H`. -/
theorem inertia_eq_of_freeAction [Finite H]
    (hcent : ∀ h : H, h ≠ 1 → Subgroup.centralizer ({(h : G)} : Set G) ≤ H)
    {θ : IrreducibleCharacter H} (hθ_ne : θ ≠ trivialIrreducibleCharacter H) :
    ClassFunction.inertia (G := G) (H := H) (θ : ClassFunction H ℂ) = H := by
  apply le_antisymm
  · intro g hg
    by_contra hgH
    exact not_mem_inertia_of_ne_trivial_of_not_mem_of_centralizer_le
      (G := G) (H := H) g hgH hcent hθ_ne hg
  · exact ClassFunction.subgroup_le_inertia (G := G) (H := H) (θ : ClassFunction H ℂ)

section InertiaTransfer

variable {G : Type*} [Group G] {H : Subgroup G} [H.Normal] {M : Subgroup G} [M.Normal]
  {H' : Subgroup (G ⧸ M)} [H'.Normal]

/-- **Inflation–conjugation equivariance.**  For a quotient-corestriction `q : ↥H →* ↥H'`
(`(q x : G/M) = mk' M x`), conjugating the inflated class function `θ̄ ∘ q` by `g : G` equals
inflating the conjugate of `θ̄` by `mk' M g`. -/
theorem conjBy_compHom_eq_compHom_conjBy (q : ↥H →* ↥H')
    (hq : ∀ x : ↥H, ((q x : G ⧸ M)) = QuotientGroup.mk' M (x : G))
    (θbar : ClassFunction ↥H' ℂ) (g : G) :
    ClassFunction.conjBy g (ClassFunction.compHom q θbar) =
      ClassFunction.compHom q
        (ClassFunction.conjBy (QuotientGroup.mk' M g) θbar) := by
  ext h
  -- Both sides evaluate `θ̄` at `H'`-elements with equal `G/M`-values.
  rw [ClassFunction.conjBy_apply, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    ClassFunction.conjBy_apply]
  apply congrArg θbar
  apply Subtype.ext
  -- Reduce to an equality of `G/M`-values: both are `mk'(g)·mk'(h)·mk'(g)⁻¹`.
  change ((q ⟨g * (h : G) * g⁻¹, ‹H.Normal›.conj_mem (h : G) h.property g⟩ : ↥H') : G ⧸ M) =
    QuotientGroup.mk' M g * ((q h : ↥H') : G ⧸ M) * (QuotientGroup.mk' M g)⁻¹
  rw [hq, hq]
  simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

/-- **Inertia transfer.**  Under the quotient corestriction `q`, membership in the inertia group of
the inflated `θ = θ̄ ∘ q` corresponds to membership of `mk' M g` in the inertia group of `θ̄`,
provided `compHom q` is injective (e.g. `q` surjective). -/
theorem mem_inertia_compHom_iff (q : ↥H →* ↥H')
    (hq : ∀ x : ↥H, ((q x : G ⧸ M)) = QuotientGroup.mk' M (x : G))
    (hqinj : Function.Injective
      (ClassFunction.compHom q : ClassFunction ↥H' ℂ → ClassFunction ↥H ℂ))
    (θbar : ClassFunction ↥H' ℂ) (g : G) :
    g ∈ ClassFunction.inertia (ClassFunction.compHom q θbar) ↔
      QuotientGroup.mk' M g ∈ ClassFunction.inertia θbar := by
  rw [ClassFunction.mem_inertia, ClassFunction.mem_inertia,
    conjBy_compHom_eq_compHom_conjBy q hq θbar g]
  exact ⟨fun h => hqinj h, fun h => congrArg (ClassFunction.compHom q) h⟩

end InertiaTransfer

end OddOrder.RepresentationTheory


