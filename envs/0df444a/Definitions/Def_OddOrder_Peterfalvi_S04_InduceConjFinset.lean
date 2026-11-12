-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S04_InduceConjFinset
-- name    : OddOrder_Peterfalvi_S04_InduceConjFinset
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:13:16.955604+00:00
-- url     : https://prove2.me/theorems/dc6d4d66-4949-4364-8810-c312c46cc333
-- title:
--   Peterfalvi (2.10): induction over conjugacy classes of subsets
-- statement:
--   Part of Peterfalvi §4 on the Dade isometry, around formula (2.10): the $L$-action on subsets of $A$, the transversal of $L$-conjugacy classes, and the transversal form of the induced values (2.10.3).
--
--   Main definitions: `conjFinsetAction` (the $L$-conjugation action on subsets of $A$), `conjClassQuotient` (the transversal $\mathcal{B}$ as a quotient), `transversalRep` (a chosen representative subset of a class), `conjFiber` (the conjugating set $\mathcal{A}(g,X)$ of (2.10.3)) and `induce_alphaB_apply_eq_sum_conjFiber` (the first displayed equation of (2.10.3), in transversal form).
--
--   The bundle also proves 22 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S04_InduceConjFinset.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S04_InduceConjFinset.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S04_DadeIsometryBasic

namespace OddOrder.Peterfalvi.S04

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

namespace Hypothesis

variable {A A₁ : Set G} {L : Subgroup G}

variable [Fintype G]

section SemidirectStructure

section ConjugacyInvariance

/-- **Peterfalvi (2.10.1) (Dade-specific).**  The induced class function
`Ind_{M(B^x)}^G α_{B^x}` is `L`-conjugacy invariant: it equals `Ind_{M(B)}^G α_B`.

This is the textbook (2.10.1) used to re-index the inclusion–exclusion sum over `ℬ`
(`L`-conjugacy class representatives of nonempty subsets) into one over all nonempty subsets `𝒫`.
The proof combines the subgroup conjugation `M(B^l) = M(B)^l` (`mBSubgroup_conjFinset_eq_map`),
the class function transport `α_{B^l} = transportConj l α_B` (`alphaB_conjFinset_eq_transportConj`),
and the generic `induce_map_conj`. -/
theorem induce_alphaB_conjFinset (hyp : Hypothesis G A L)
    (l : L) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) (α : ClassFunction L ℂ)
    [Invertible (Nat.card (mBSubgroup hyp (hyp.conjFinset l B)
      (hyp.conjFinset_nonempty hB)) : ℂ)]
    [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] :
    ClassFunction.induce (mBSubgroup hyp (hyp.conjFinset l B) (hyp.conjFinset_nonempty hB))
        (alphaB hyp (hyp.conjFinset_nonempty hB) α)
      = ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hB α) := by
  have : Invertible (Nat.card ((mBSubgroup hyp B hB).map
      (MulAut.conj (l : G) : G →* G)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- Step 1: rewrite the source subgroup to `M(B)^l` and identify the class functions.
  rw [induce_congr_of_subgroup_eq (hyp.mBSubgroup_conjFinset_eq_map l hB)
    (θ₂ := ClassFunction.transportConj (l : G) (alphaB hyp hB α))
    (fun x hx₁ hx₂ => hyp.alphaB_conjFinset_eq_transportConj l hB α x hx₁ hx₂)]
  -- Step 2: generic (2.10.1) `Ind_{H^ℓ}(transportConj ℓ θ) = Ind_H θ`.
  exact ClassFunction.induce_map_conj (l : G) (alphaB hyp hB α)

end ConjugacyInvariance

section Transversal

/-- **Peterfalvi (2.10), the `L`-action on subsets of `A`.**  The `L`-conjugation action
`conjFinset` (`B ↦ B^l = {l·a·l⁻¹ | a ∈ B}`) on `Finset {a : G // a ∈ A}` is a `MulAction`:
the action laws are exactly `conjFinset_one` and `conjFinset_mul`.

This is the action whose orbits index the inclusion–exclusion sum (2.10): the alternating sum
`-∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)} α_B` runs over `L`-conjugacy class representatives `ℬ` of the
nonempty subsets, made well defined by `induce_alphaB_conjFinset` ((2.10.1)) and `conjFinset_card`
(the sign `(-1)^{|B|}` is `L`-invariant since `|B^l| = |B|`).  It is provided as a `def` (not a
global instance) because it depends on the hypothesis `hyp`; downstream lemmas activate it with
`letI := hyp.conjFinsetAction`. -/
@[reducible] noncomputable def conjFinsetAction (hyp : Hypothesis G A L) :
    MulAction L (Finset {a : G // a ∈ A}) where
  smul := hyp.conjFinset
  one_smul := hyp.conjFinset_one
  mul_smul := hyp.conjFinset_mul

@[simp] theorem conjFinsetAction_smul (hyp : Hypothesis G A L) (l : L)
    (B : Finset {a : G // a ∈ A}) :
    (letI := hyp.conjFinsetAction; l • B) = hyp.conjFinset l B := rfl

/-- **Peterfalvi (2.10), the stabilizer is `N_L(B)`.**  Under the `conjFinset` action, the
`MulAction` stabilizer of `B` is exactly the set-stabilizer `setLStabilizer hyp B = N_L(B)`.

`l • B = B` unfolds to `B.image (conjA l) = B`; since `conjA l` is injective this is equivalent to
`conjA l` mapping `B` into `B`, i.e. `∀ a ∈ B, conjA l a ∈ B` — the defining condition of
`setLStabilizer`.  This identifies the orbit-stabilizer weight `|orbit B| = [L : N_L(B)]` used in
(2.10). -/
theorem stabilizer_conjFinsetAction (hyp : Hypothesis G A L)
    (B : Finset {a : G // a ∈ A}) :
    (letI := hyp.conjFinsetAction; MulAction.stabilizer L B) = setLStabilizer hyp B := by
  classical
  let := hyp.conjFinsetAction
  ext l
  rw [MulAction.mem_stabilizer_iff, mem_setLStabilizer]
  change hyp.conjFinset l B = B ↔ ∀ a ∈ B, hyp.conjA l a ∈ B
  constructor
  · intro hl a ha
    rw [← hl]
    exact (hyp.mem_conjFinset).mpr ⟨a, ha, rfl⟩
  · intro hl
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := (hyp.mem_conjFinset).mp ha
      exact hl b hb
    · rw [hyp.conjFinset_card]

/-- **Peterfalvi (2.10), the transversal `ℬ`.**  The quotient of `Finset {a : G // a ∈ A}` by the
`L`-conjugacy relation (`conjFinset` orbits); its elements index the inclusion–exclusion sum once
restricted to nonempty subsets.  Representatives are obtained via `Quotient.out` (`transversalRep`),
realizing Peterfalvi's "`ℬ` = set of representatives of the `L`-conjugacy classes of subsets". -/
noncomputable def conjClassQuotient (hyp : Hypothesis G A L) : Type _ :=
  letI := hyp.conjFinsetAction
  MulAction.orbitRel.Quotient L (Finset {a : G // a ∈ A})

instance (hyp : Hypothesis G A L) : Finite hyp.conjClassQuotient := by
  classical
  unfold Hypothesis.conjClassQuotient
  let := hyp.conjFinsetAction
  let : Finite (Finset {a : G // a ∈ A}) := Finite.of_fintype _
  infer_instance

/-- A chosen representative subset of an `L`-conjugacy class (`Quotient.out`).  This is one element
of Peterfalvi's transversal `ℬ`. -/
noncomputable def transversalRep (hyp : Hypothesis G A L)
    (C : hyp.conjClassQuotient) : Finset {a : G // a ∈ A} :=
  letI := hyp.conjFinsetAction
  Quotient.out (s := MulAction.orbitRel L (Finset {a : G // a ∈ A})) C

/-- **Peterfalvi (2.10), orbit-stabilizer weight.**  For a subset `B`, the size of its
`L`-conjugacy orbit times `|N_L(B)|` equals `|L|`.  Equivalently `|orbit B| = [L : N_L(B)]`, the
fibrewise weight attached to each representative `B ∈ ℬ` in the (2.10) sum normalization.

This is the orbit-stabilizer theorem `card_orbit_mul_card_stabilizer_eq_card_group` specialized to
the `conjFinset` action, with the stabilizer rewritten to `setLStabilizer hyp B`
(`stabilizer_conjFinsetAction`).  Stated with `Nat.card` so no ambient `Fintype L` is needed. -/
theorem card_orbit_mul_card_setLStabilizer (hyp : Hypothesis G A L)
    (B : Finset {a : G // a ∈ A}) :
    letI := hyp.conjFinsetAction
    Nat.card (MulAction.orbit L B) * Nat.card (setLStabilizer hyp B)
      = Nat.card L := by
  classical
  let := hyp.conjFinsetAction
  let : Fintype L := Fintype.ofFinite L
  let : Fintype (MulAction.orbit L B) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer L B) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← hyp.stabilizer_conjFinsetAction B, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group L B

end Transversal

section PointwiseValue

open scoped Classical in
/-- **Peterfalvi (2.10.3), the conjugating set `𝒜(g, X)`.**  For `g : G` and a subset
`X ⊆ G`, `𝒜(g, X) = { x ∈ G | x⁻¹ g x ∈ X }`, as a `Finset G` (using `[Fintype G]`).
This is the index set of the transversal sum in the induced-character value formula. -/
noncomputable def conjFiber (g : G) (X : Set G) : Finset G :=
  Finset.univ.filter (fun x : G => x⁻¹ * g * x ∈ X)

@[simp] theorem mem_conjFiber {g x : G} {X : Set G} :
    x ∈ conjFiber g X ↔ x⁻¹ * g * x ∈ X := by
  classical
  simp [conjFiber]

open scoped Classical in
/-- **Peterfalvi (2.10.3), first displayed equation (transversal form).**  The pointwise
value of the induced class function `Ind_{M(B)}^G α_B` at `g`:

    `(Ind_{M(B)}^G α_B)(g) = ⅟|M(B)| · ∑_{x ∈ 𝒜(g, M(B))} induceTerm M(B) α_B x g`.

This is the literal first line of Peterfalvi's proof of (2.10.3): the induction formula
`induce_apply_eq_sum_filter`, restated with the conjugating set `𝒜(g, M(B)) = conjFiber`.
On the filter the summand `induceTerm M(B) α_B x g` *is* `α_B(x⁻¹ g x)`
(`alphaB_induceTerm_of_mem` below). -/
theorem induce_alphaB_apply_eq_sum_conjFiber (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : ClassFunction L ℂ) [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] (g : G) :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hB α) g
      = ⅟(Nat.card (mBSubgroup hyp B hB) : ℂ) *
          ∑ x ∈ conjFiber g (↑(mBSubgroup hyp B hB) : Set G),
            ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hB α) x g := by
  rw [ClassFunction.induce_apply_eq_sum_filter]
  rfl

/-- On the conjugating set `𝒜(g, M(B))`, the induction summand `induceTerm M(B) α_B x g`
is the explicit value `α_B(x⁻¹ g x)`.  Combined with
`induce_alphaB_apply_eq_sum_conjFiber` this is the `α_B`-explicit first line of (2.10.3). -/
theorem alphaB_induceTerm_of_mem (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) (α : ClassFunction L ℂ)
    {x g : G} (hx : x⁻¹ * g * x ∈ mBSubgroup hyp B hB) :
    ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hB α) x g
      = alphaB hyp hB α ⟨x⁻¹ * g * x, hx⟩ :=
  ClassFunction.induceTerm_of_mem _ hx

/-- **Peterfalvi (2.10.3), the `α_B(x⁻¹gx) = α(b)` collapse.**  For `x ∈ 𝒜(g, M(B))`,
write the conjugate `x⁻¹ g x = h · b` with `h ∈ H(B)` and `b ∈ N_L(B)` (the semidirect
factorization of `M(B)`, `coe_mBSubgroup`).  Then the induction summand collapses, via the
(2.9) defining equation `alphaB_apply_mul`, to `α(b)`.

This isolates the value half of Peterfalvi's "`α_B(x⁻¹ g x) = α(b)`" step (the membership
half — `α(b) ≠ 0 ⟹ b ∈ A` and then `g ∈ (bH(b))^G` — is the coprime-conjugacy argument
driving the `card_conj_fiber` aggregation, tracked separately). -/
theorem exists_nLStabilizerIn_alphaB_induceTerm (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : ClassFunction L ℂ) {x g : G} (hx : x⁻¹ * g * x ∈ mBSubgroup hyp B hB) :
    ∃ (h : G) (_ : h ∈ hIntersection hyp B hB) (b : G) (hb : b ∈ nLStabilizerIn hyp B),
      x⁻¹ * g * x = h * b ∧
        ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hB α) x g
          = α ⟨b, nLStabilizerIn_le_L hyp B hb⟩ := by
  classical
  -- factor `x⁻¹ g x = h * b` with `h ∈ H(B)`, `b ∈ N_L(B)`
  have hmem_prod : x⁻¹ * g * x
      ∈ (↑(hIntersection hyp B hB) * ↑(nLStabilizerIn hyp B) : Set G) := by
    rw [← hyp.coe_mBSubgroup hB]; exact hx
  obtain ⟨h, hh, b, hb, hhb⟩ := hmem_prod
  -- `hhb : h * b = x⁻¹ * g * x`
  refine ⟨h, hh, b, hb, hhb.symm, ?_⟩
  have hhbeq : h * b = x⁻¹ * g * x := hhb
  have hhbM : h * b ∈ mBSubgroup hyp B hB := by rw [hhbeq]; exact hx
  have harg : (⟨x⁻¹ * g * x, hx⟩ : mBSubgroup hyp B hB) = ⟨h * b, hhbM⟩ :=
    Subtype.ext hhb.symm
  calc ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hB α) x g
      = alphaB hyp hB α ⟨x⁻¹ * g * x, hx⟩ :=
        alphaB_induceTerm_of_mem hyp hB α hx
    _ = alphaB hyp hB α ⟨h * b, hhbM⟩ := congrArg (alphaB hyp hB α) harg
    _ = α ⟨b, nLStabilizerIn_le_L hyp B hb⟩ := hyp.alphaB_apply_mul hB α hh hb hhbM

/-- **Coprimality of `orderOf b` with `|H(B)|`** (Peterfalvi (2.2.c), the input to (2.1) in the
proof of (2.10.3)).  For `b ∈ A`, the order of `b` is coprime to `|H(B)|`: `|H(B)| ∣ |H(b₀)|`
for any `b₀ ∈ B` (`H(B) ⊆ H(b₀)`), which is coprime to `|C_L(b)|` by `centralizer_coprime`, and
`orderOf b ∣ |C_L(b)|` since `b ∈ C_L(b)`. -/
theorem coprime_orderOf_card_hIntersection (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) {b : G} (hbA : b ∈ A) :
    Nat.Coprime (orderOf b) (Nat.card (hIntersection hyp B hB)) := by
  obtain ⟨b₀, hb₀⟩ := hB.exists_mem
  have hdvdH : Nat.card (hIntersection hyp B hB) ∣ Nat.card (hyp.H b₀) :=
    Subgroup.card_dvd_of_le (hIntersection_le hyp hB hb₀)
  have hcop : Nat.Coprime (Nat.card (hyp.H b₀)) (Nat.card (centralizerIn L b)) :=
    hyp.centralizer_coprime b₀ ⟨b, hbA⟩
  have hcop' : Nat.Coprime (Nat.card (hIntersection hyp B hB))
      (Nat.card (centralizerIn L b)) :=
    Nat.Coprime.coprime_dvd_left hdvdH hcop
  exact (Nat.Coprime.coprime_dvd_right (hyp.orderOf_dvd_card_centralizerIn hbA) hcop').symm

/-- **Peterfalvi (2.10.3), the vanishing case.**  If `g` lies outside `⋃_{a∈A} (aH(a))^G` (the
Dade support), then `(Ind_{M(B)}^G α_B)(g) = 0`.

Each summand `induceTerm M(B) α_B x g` over `x ∈ 𝒜(g, M(B))`, if nonzero, has
`x⁻¹ g x = h·b` with `h ∈ H(B)`, `b ∈ N_L(B)` and `α(b) ≠ 0`, so `b ∈ A`
(`exists_nLStabilizerIn_alphaB_induceTerm` + support of `α`).  By (2.1)
(`exists_mem_centralizer_conj`, with `b` normalizing the coprime `H(B)`), `h·b` is
`H(B)`-conjugate to `c·b` with `c ∈ C_{H(B)}(b) = H(B∪{b}) ⊆ H(b)`
(`centralizer_inf_hIntersection`);
since `c` commutes with `b`, `c·b = b·c ∈ b·H(b) ⊆ hCoset b`, so `g ∈ (bH(b))^G ⊆ dadeSupport` —
contradicting `g ∉ dadeSupport`.  Hence every summand vanishes. -/
theorem induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] {g : G} (hg : g ∉ hyp.dadeSupport) :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hB (α : ClassFunction L ℂ)) g
      = 0 := by
  classical
  rw [induce_alphaB_apply_eq_sum_conjFiber hyp hB (α : ClassFunction L ℂ) g]
  rw [mul_eq_zero]; right
  apply Finset.sum_eq_zero
  intro x hx
  rw [mem_conjFiber] at hx
  -- factor the conjugate and read off the summand value `α(b)`
  obtain ⟨h, hh, b, hb, hxgx, hterm⟩ :=
    hyp.exists_nLStabilizerIn_alphaB_induceTerm hB (α : ClassFunction L ℂ) hx
  rw [hterm]
  by_contra hαb
  -- `α(b) ≠ 0 ⇒ b ∈ A`
  have hbA : b ∈ A := α.property hαb
  -- `b` normalizes `H(B)` and is coprime to `|H(B)|`; apply (2.1)
  have hnorm : ∀ y ∈ hIntersection hyp B hB, b * y * b⁻¹ ∈ hIntersection hyp B hB := by
    intro y hy
    have := hyp.nLStabilizerIn_le_normalizer hB hb
    rw [Subgroup.mem_normalizer_iff] at this
    exact (this y).mp hy
  have hcop := hyp.coprime_orderOf_card_hIntersection hB hbA
  obtain ⟨c, hcmem, x', hx'H, hx'eq⟩ :=
    OddOrder.GroupTheory.exists_mem_centralizer_conj (g := b) (H := hIntersection hyp B hB)
      hcop hnorm hh
  -- `c ∈ C_{H(B)}(b) = H(B ∪ {b}) ⊆ H(b)`, and `c` commutes with `b`
  obtain ⟨hcH, hccomm⟩ := Subgroup.mem_inf.mp hcmem
  have hccb : Commute c b :=
    Subgroup.mem_centralizer_singleton_iff.mp hccomm
  have hcHb : c ∈ hyp.H ⟨b, hbA⟩ := by
    have hcInsert : c ∈ hIntersection hyp (insert ⟨b, hbA⟩ B)
        (Finset.insert_nonempty _ B) := by
      rw [← hyp.centralizer_inf_hIntersection hB ⟨b, hbA⟩]
      exact Subgroup.mem_inf.mpr ⟨hccomm, hcH⟩
    exact hIntersection_le hyp (Finset.insert_nonempty _ B) (Finset.mem_insert_self _ B) hcInsert
  -- `c·b = b·c ∈ hCoset b`
  have hcb_mem : c * b ∈ hyp.hCoset ⟨b, hbA⟩ := by
    rw [mem_hCoset]
    exact ⟨c, hcHb, hccb.eq⟩
  -- `g` is conjugate to `c·b` (via `x' x⁻¹`), hence in `dadeSupport`
  have hgconj : (x' * x⁻¹) * g * (x' * x⁻¹)⁻¹ = c * b := by
    rw [← hx'eq, ← hxgx]; group
  apply hg
  rw [hyp.mem_dadeSupport_iff]
  refine ⟨⟨b, hbA⟩, c, hcHb, ?_⟩
  rw [show (⟨b, hbA⟩ : {a : G // a ∈ A}).1 * c = c * b from (hccb.eq).symm]
  exact (isConj_iff.mpr ⟨x' * x⁻¹, hgconj⟩).symm

/-- **The `N_L(B)`-component of an element of `M(B)`.**  For `m ∈ M(B)` and `b ∈ N_L(B)`, the
quotient homomorphism `f_B = dadeQuotientHom` sends `m` to `b` (in `L`) exactly when `m` lies in
the coset `H(B)·b`.  This realizes the semidirect decomposition `M(B) = H(B) ⋊ N_L(B)`: `f_B`
projects onto the `N_L(B)`-factor, with fibers the `H(B)`-cosets.

`(⇐)` `m = h·b` with `h ∈ H(B) = ker f_B`, `b ∈ N_L(B)` (retracted by `f_B`); `(⇒)` `m·b⁻¹` maps
to `1` under `f_B`, hence lies in `ker f_B = H(B)`. -/
theorem dadeQuotientHom_eq_iff_mem_hIntersection_mul (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (m : mBSubgroup hyp B hB) {b : G} (hb : b ∈ nLStabilizerIn hyp B) :
    ((hyp.dadeQuotientHom hB m : L) : G) = b ↔
      (m : G) ∈ (↑(hIntersection hyp B hB) : Set G) * ({b} : Set G) := by
  classical
  set bM : mBSubgroup hyp B hB := ⟨b, hyp.nLStabilizerIn_le_mBSubgroup hB hb⟩ with hbM
  have hfbM : ((hyp.dadeQuotientHom hB bM : L) : G) = b :=
    hyp.dadeQuotientHom_coe_of_mem_nLStabilizerIn hB bM hb
  constructor
  · intro hfm
    -- `m * bM⁻¹ ∈ ker = H(B)`
    have hker : (m * bM⁻¹ : mBSubgroup hyp B hB) ∈ (hyp.dadeQuotientHom hB).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hfm, hfbM, mul_inv_cancel]
      rfl
    rw [hyp.ker_dadeQuotientHom hB, Subgroup.mem_subgroupOf] at hker
    -- `(m * bM⁻¹ : G) = (m:G) * b⁻¹ ∈ H(B)`, so `(m:G) = (that) * b ∈ H(B)·b`
    refine ⟨(m : G) * b⁻¹, ?_, b, rfl, ?_⟩
    · have : ((m * bM⁻¹ : mBSubgroup hyp B hB) : G) = (m : G) * b⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rwa [this] at hker
    · group
  · rintro ⟨h, hh, _, rfl, hmeq⟩
    -- `m = h·b` with `h ∈ H(B)`, so `f_B(m) = f_B(h)·f_B(b) = 1·b = b`
    have hhM : h ∈ mBSubgroup hyp B hB := hyp.hIntersection_le_mBSubgroup hB hh
    have hmsplit : m = (⟨h, hhM⟩ : mBSubgroup hyp B hB) * bM := by
      apply Subtype.ext; rw [Subgroup.coe_mul]; exact hmeq.symm
    have hfh : hyp.dadeQuotientHom hB ⟨h, hhM⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hyp.ker_dadeQuotientHom hB, Subgroup.mem_subgroupOf]
      exact hh
    rw [hmsplit, map_mul, hfh, one_mul, hfbM]

/-- The `f_B`-image of any `m ∈ M(B)` lands in the `N_L(B)`-factor: `f_B(m) ∈ N_L(B)`.
This is structural — `f_B = dadeQuotientHom` factors through the inclusion `N_L(B) ≤ L`. -/
theorem dadeQuotientHom_mem_nLStabilizerIn (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (m : mBSubgroup hyp B hB) :
    ((hyp.dadeQuotientHom hB m : L) : G) ∈ nLStabilizerIn hyp B := by
  have : ((hIntersection hyp B hB).subgroupOf (mBSubgroup hyp B hB)).Normal :=
    hyp.hIntersection_subgroupOf_normal hB
  -- `dadeQuotientHom m = inclusion(N_L(B) ≤ L) z` for `z = …`
  set z : nLStabilizerIn hyp B :=
    (Subgroup.subgroupOfEquivOfLe (hyp.nLStabilizerIn_le_mBSubgroup hB))
      ((hyp.isComplement'_subgroupOf hB).QuotientMulEquiv (QuotientGroup.mk' _ m)) with hz
  have hval : hyp.dadeQuotientHom hB m = Subgroup.inclusion (hyp.nLStabilizerIn_le_L B) z :=
    rfl
  rw [hval]
  exact z.2

open Classical in
/-- **Peterfalvi (2.10.3), the `N_L(B)`-aggregated value (value case, before specialization).**
The pointwise value of `Ind_{M(B)}^G α_B` regrouped over the `N_L(B)`-component `b` of the
conjugate `x⁻¹ g x`:

    `(Ind_{M(B)}^G α_B)(g) = ⅟|M(B)| · ∑_{b ∈ N_L(B)} α(b) · |𝒜(g, H(B)·b)|`.

This is the heart of (2.10.3): the conjugating set `𝒜(g, M(B))` partitions over the
`N_L(B)`-factor of `M(B) = H(B) ⋊ N_L(B)`; on the fiber `{x : comp(x⁻¹gx) = b}` the induction
summand is the constant `α(b)` (the (2.9) defining equation, `alphaB_apply_mul`), and that fiber is
exactly `𝒜(g, H(B)·b)` (`dadeQuotientHom_eq_iff_mem_hIntersection_mul`).  The textbook value
formula `(α(a)/|M(B)|)·∑_{b ∈ N_L(B)∩a^L} |𝒜(g, H(B)b)|` follows by discarding the `b ∉ a^L` terms
(where `α(b) = 0` by support of `α`) once `g ∈ (aH(a))^G` is fixed. -/
theorem induce_alphaB_apply_eq_sum_nLStabilizerIn (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : ClassFunction L ℂ) [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] (g : G) :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hB α) g
      = ⅟(Nat.card (mBSubgroup hyp B hB) : ℂ) *
          ∑ b : (nLStabilizerIn hyp B),
            α ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ *
              (conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G))).card := by
  rw [induce_alphaB_apply_eq_sum_conjFiber hyp hB α g]
  congr 1
  -- The component map sends `𝒜(g, M(B))` into `N_L(B)` (the `f_B`-image, with a junk default).
  set φ : G → nLStabilizerIn hyp B := fun x =>
    if hx : x⁻¹ * g * x ∈ mBSubgroup hyp B hB then
      ⟨((hyp.dadeQuotientHom hB ⟨x⁻¹ * g * x, hx⟩ : L) : G),
        hyp.dadeQuotientHom_mem_nLStabilizerIn hB ⟨x⁻¹ * g * x, hx⟩⟩
    else 1 with hφ
  have hmaps : ∀ x ∈ conjFiber g (↑(mBSubgroup hyp B hB) : Set G),
      φ x ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)) := fun x _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (f := fun x => ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hB α) x g)]
  apply Finset.sum_congr rfl
  intro b _
  -- the fiber over `b` is `𝒜(g, H(B)·b)`, and the summand is constant `α(b)` there
  have hfiber_eq : (conjFiber g (↑(mBSubgroup hyp B hB) : Set G)).filter (fun x => φ x = b)
      = conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G)) := by
    ext x
    simp only [Finset.mem_filter, mem_conjFiber]
    -- value of `φ x` when `x⁻¹gx ∈ M(B)`
    have hφval : ∀ hxM : x⁻¹ * g * x ∈ mBSubgroup hyp B hB,
        ((φ x : nLStabilizerIn hyp B) : G)
          = ((hyp.dadeQuotientHom hB ⟨x⁻¹ * g * x, hxM⟩ : L) : G) := by
      intro hxM
      simp only [hφ, dif_pos hxM]
    constructor
    · rintro ⟨hxM, hφx⟩
      have hφx' : ((hyp.dadeQuotientHom hB ⟨x⁻¹ * g * x, hxM⟩ : L) : G) = (b : G) := by
        rw [← hφval hxM, hφx]
      exact (hyp.dadeQuotientHom_eq_iff_mem_hIntersection_mul hB
        ⟨x⁻¹ * g * x, hxM⟩ b.2).mp hφx'
    · intro hxHb
      rw [Set.mem_mul] at hxHb
      obtain ⟨h, hh, b', hb', hmeq⟩ := hxHb
      rw [Set.mem_singleton_iff] at hb'
      subst hb'
      have hxM : x⁻¹ * g * x ∈ mBSubgroup hyp B hB := by
        rw [← hmeq]
        exact (mBSubgroup hyp B hB).mul_mem (hyp.hIntersection_le_mBSubgroup hB hh)
          (hyp.nLStabilizerIn_le_mBSubgroup hB b.2)
      refine ⟨hxM, ?_⟩
      apply Subtype.ext
      rw [hφval hxM]
      exact (hyp.dadeQuotientHom_eq_iff_mem_hIntersection_mul hB
        ⟨x⁻¹ * g * x, hxM⟩ b.2).mpr ⟨h, hh, _, rfl, hmeq⟩
  rw [hfiber_eq]
  -- on `𝒜(g, H(B)·b)` every summand is `α(b)`
  have hconst : ∀ x ∈ conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G)),
      ClassFunction.induceTerm (mBSubgroup hyp B hB) (alphaB hyp hB α) x g
        = α ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ := by
    intro x hx
    rw [mem_conjFiber] at hx
    rw [Set.mem_mul] at hx
    obtain ⟨h, hh, b', hb', hmeq⟩ := hx
    rw [Set.mem_singleton_iff] at hb'
    subst hb'
    have hxM : x⁻¹ * g * x ∈ mBSubgroup hyp B hB := by
      rw [← hmeq]
      exact (mBSubgroup hyp B hB).mul_mem (hyp.hIntersection_le_mBSubgroup hB hh)
        (hyp.nLStabilizerIn_le_mBSubgroup hB b.2)
    rw [alphaB_induceTerm_of_mem hyp hB α hxM]
    have harg : (⟨x⁻¹ * g * x, hxM⟩ : mBSubgroup hyp B hB)
        = ⟨h * (b : G), by rw [hmeq]; exact hxM⟩ := Subtype.ext hmeq.symm
    rw [harg]
    exact hyp.alphaB_apply_mul hB α hh b.2 _
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]

open Classical in
/-- **Peterfalvi (2.10.3), the support-restricted value.**  When `α ∈ CF(L, A)` is supported on
`A`, the `N_L(B)`-aggregated value of `Ind_{M(B)}^G α_B` may be summed over only those
`b ∈ N_L(B)` lying in `A`:

    `(Ind_{M(B)}^G α_B)(g) = ⅟|M(B)| · ∑_{b ∈ N_L(B), b ∈ A} α(b) · |𝒜(g, H(B)·b)|`.

This is the first reduction of (2.10.3)'s value case: the terms with `b ∉ A` carry a vanishing
factor `α(b) = 0` (support of `α`) and so drop out of the `N_L(B)`-sum of
`induce_alphaB_apply_eq_sum_nLStabilizerIn`.  After fixing a Dade-support representative `a` with
`g ∈ (aH(a))^G`, the surviving `b` are moreover `L`-conjugate to `a` (Peterfalvi (2.4.b)), which
collapses `α(b)` to the constant `α(a)` in the textbook value formula. -/
theorem induce_alphaB_apply_eq_sum_nLStabilizerIn_inA (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] (g : G) :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hB (α : ClassFunction L ℂ)) g
      = ⅟(Nat.card (mBSubgroup hyp B hB) : ℂ) *
          ∑ b ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
              (fun b : (nLStabilizerIn hyp B) => ((b : G) ∈ A)),
            (α : ClassFunction L ℂ) ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ *
              (conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G))).card := by
  rw [induce_alphaB_apply_eq_sum_nLStabilizerIn hyp hB (α : ClassFunction L ℂ) g]
  congr 1
  -- terms with `b ∉ A` vanish since `α(b) = 0` there (support of `α`)
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun b _ hb => ?_).symm
  rw [Finset.mem_filter] at hb
  have hbA : (b : G) ∉ A := fun h => hb ⟨Finset.mem_univ _, h⟩
  have hα0 : (α : ClassFunction L ℂ) ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ = 0 := by
    by_contra hαne
    exact hbA (α.property hαne)
  rw [hα0, zero_mul]

end PointwiseValue

section VirtualCharacterRHS

/-- **Peterfalvi (2.6.b), each summand is a virtual character.**  For `α ∈ ℤ[Irr L]` and a
nonempty `B ⊆ A`, the induced class function `Ind_{M(B)}^G α_B` lies in `ℤ[Irr G]`.

This is the building block of the (2.10) inclusion–exclusion's right-hand side
`-∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)}^G α_B`: each term is a virtual character, so any
`ℤ`-linear (in particular alternating) combination is one too.  It chains the (2.9)
pullback `alphaB_mem_ZIrr` (`α_B = α ∘ f_B ∈ ℤ[Irr M(B)]`) with the induction lemma
`ClassFunction.induce_mem_ZIrr` (induction preserves `ℤ[Irr]`). -/
theorem induce_alphaB_mem_ZIrr (hyp : Hypothesis G A L)
    [Invertible (Nat.card G : ℂ)]
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) {α : ClassFunction L ℂ}
    (hα : α ∈ ZIrr L) [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)] :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hB α) ∈ ZIrr G := by
  have : Fintype (mBSubgroup hyp B hB) := Fintype.ofFinite _
  exact ClassFunction.induce_mem_ZIrr (mBSubgroup hyp B hB)
    (hyp.alphaB_mem_ZIrr hB hα)

/-- **Peterfalvi (2.10), an inclusion–exclusion summand `Ind_{M(B)}^G α_B`.**  Packaged as a
`ClassFunction G ℂ` carrying its own `Invertible (|M(B)| : ℂ)` instance (supplied from
`Nat.card_pos`), so the (2.10) right-hand side `-∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)} α_B` can be
formed as an ordinary `Finset` sum without threading invertibility through each binder.  The
subset `B` is carried together with its nonemptiness proof as the subtype `{B // B.Nonempty}`. -/
noncomputable def induceAlphaBTerm (hyp : Hypothesis G A L)
    (α : ClassFunction L ℂ) (p : {B : Finset {a : G // a ∈ A} // B.Nonempty}) :
    ClassFunction G ℂ :=
  letI : Invertible (Nat.card (mBSubgroup hyp p.1 p.2) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  ClassFunction.induce (mBSubgroup hyp p.1 p.2) (alphaB hyp p.2 α)

/-- **Peterfalvi (2.10.1), packaged form.**  The inclusion–exclusion summand `induceAlphaBTerm`
is `L`-conjugacy invariant: replacing the subset `B` by a conjugate `B^l` leaves
`Ind_{M(B)}^G α_B` unchanged.

This lifts the bare-`induce` invariance `induce_alphaB_conjFinset` ((2.10.1) Dade-specific) to the
packaged `ClassFunction G ℂ` summand `induceAlphaBTerm` (which carries its own `Invertible (|M(B)|
: ℂ)` instance).  It is the well-definedness fact making the (2.10) right-hand side
`-∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)} α_B` independent of the chosen transversal representatives:
together with `conjFinset_card` (the sign `(-1)^{|B|}` is `L`-invariant) it lets the sum over the
transversal `ℬ` (`conjClassQuotient`/`transversalRep`) be re-indexed over all nonempty subsets. -/
theorem induceAlphaBTerm_conjFinset (hyp : Hypothesis G A L)
    (α : ClassFunction L ℂ) (l : L) {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    hyp.induceAlphaBTerm α ⟨hyp.conjFinset l B, hyp.conjFinset_nonempty hB⟩
      = hyp.induceAlphaBTerm α ⟨B, hB⟩ := by
  let : Invertible (Nat.card (mBSubgroup hyp (hyp.conjFinset l B)
      (hyp.conjFinset_nonempty hB)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  simp only [induceAlphaBTerm]
  exact hyp.induce_alphaB_conjFinset l hB α

/-- **Peterfalvi (2.6.b), each packaged summand is a virtual character.**  For `α ∈ ℤ[Irr L]`,
the term `induceAlphaBTerm` lies in `ℤ[Irr G]` — the `induce_alphaB_mem_ZIrr` content with the
invertibility instance pinned to the one carried by `induceAlphaBTerm`. -/
theorem induceAlphaBTerm_mem_ZIrr (hyp : Hypothesis G A L)
    [Invertible (Nat.card G : ℂ)] {α : ClassFunction L ℂ} (hα : α ∈ ZIrr L)
    (p : {B : Finset {a : G // a ∈ A} // B.Nonempty}) :
    hyp.induceAlphaBTerm α p ∈ ZIrr G := by
  let : Invertible (Nat.card (mBSubgroup hyp p.1 p.2) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact hyp.induce_alphaB_mem_ZIrr p.2 hα

/-- **Peterfalvi (2.10)/(2.6.b), the right-hand side is a virtual character.**  Any finite
`ℤ`-linear combination `∑_{p ∈ s} c p • Ind_{M(B)}^G α_B` of the inclusion–exclusion summands
(`induceAlphaBTerm`) is a virtual character of `G`.

This is part (d) of the (2.6.b) program: granting the (2.10) identity
`α^τ = -∑_{B ∈ ℬ} (-1)^{|B|} Ind_{M(B)} α_B` (the special case `c B = -(-1)^{|B|}` and
`s = ℬ`), the right-hand side, hence `α^τ`, lies in `ℤ[Irr G]`.  Immediate from
`Submodule.sum_mem` / `Submodule.smul_mem` over `induceAlphaBTerm_mem_ZIrr`. -/
theorem zsmul_induceAlphaBTerm_sum_mem_ZIrr (hyp : Hypothesis G A L)
    [Invertible (Nat.card G : ℂ)]
    {α : ClassFunction L ℂ} (hα : α ∈ ZIrr L)
    (s : Finset {B : Finset {a : G // a ∈ A} // B.Nonempty})
    (c : {B : Finset {a : G // a ∈ A} // B.Nonempty} → ℤ) :
    (∑ p ∈ s, c p • hyp.induceAlphaBTerm α p) ∈ ZIrr G :=
  Submodule.sum_mem _ (fun p _ =>
    Submodule.smul_mem _ _ (hyp.induceAlphaBTerm_mem_ZIrr hα p))

end VirtualCharacterRHS

section MobiusAssembly

/-- **Peterfalvi (2.1)/(2.10.3), the conjugating-set cardinality `|𝒜(g, K·a)| = |C_G(a)|`** when
`a` *centralizes* the subgroup `K` (so `K ⊆ C_G(a)`), `C_G(a)` normalizes `K`, `⟨a⟩` and `K` have
coprime orders, and `g` is `G`-conjugate to an element `a·x₀` (`x₀ ∈ K`).

This is the textbook's "`𝒜(g, H(a)a) = x C_G(a)`" remark.  The conjugating set
`𝒜(g, K·a) = {y | y⁻¹gy ∈ K·a}` is in bijection with the `card_conj_fiber` pair set
`{(p₁, p₂) | p₁ ∈ K ∧ p₂(a·p₁)p₂⁻¹ = g}`: each conjugator `y = p₂` determines a unique `p₁` via
`y⁻¹gy = a·p₁ ∈ a·K = K·a` (the cosets agree as `a` centralizes `K`).  By `card_conj_fiber` the pair
set has cardinality `|C_G(a)|`.  Applied at the Möbius survivor `B = {a}` (where `H({a}) = H(a) ⊆
C_G(a)`, normalized by `C_G(a)` via `H_normalized`) it evaluates the surviving term of (2.10). -/
theorem card_conjFiber_coset_eq_card_centralizer {K : Subgroup G} {a : G}
    (hcomm : ∀ x ∈ K, Commute a x)
    (hnorm : ∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ x ∈ K, c * x * c⁻¹ ∈ K)
    (hcop : Nat.Coprime (orderOf a) (Nat.card K))
    {g x₀ : G} (hx₀K : x₀ ∈ K) (hx₀ : IsConj (a * x₀) g) :
    (conjFiber g ((↑K : Set G) * ({a} : Set G))).card
      = Nat.card (Subgroup.centralizer ({a} : Set G)) := by
  classical
  rw [← OddOrder.GroupTheory.card_conj_fiber hcomm hnorm hcop hx₀K hx₀]
  -- `(conjFiber g (K·a)).card = Nat.card {y // y⁻¹gy ∈ K·a}`.
  have hcard1 : (conjFiber g ((↑K : Set G) * ({a} : Set G))).card
      = Nat.card {y : G // y⁻¹ * g * y ∈ (↑K : Set G) * ({a} : Set G)} := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => mem_conjFiber)
  rw [hcard1]
  -- Bijection `{y // y⁻¹gy ∈ K·a} ≃ {p : G×G // p.1 ∈ K ∧ p.2(a·p.1)p.2⁻¹ = g}`.
  refine Nat.card_congr ?_
  refine
    { toFun := fun y => ⟨(a⁻¹ * (y.1⁻¹ * g * y.1), y.1), ?_, ?_⟩
      invFun := fun p => ⟨p.1.2, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- `a⁻¹·(y⁻¹gy) ∈ K`: from `y⁻¹gy ∈ K·a = a·K`.
    change a⁻¹ * (y.1⁻¹ * g * y.1) ∈ K
    obtain ⟨h, hh, a', ha', hyeq⟩ := y.2
    rw [Set.mem_singleton_iff] at ha'
    simp only at hyeq
    -- `hyeq : h * a' = y.1⁻¹ * g * y.1`, `ha' : a' = a`
    rw [← hyeq, ha']
    have hreduce : a⁻¹ * (h * a) = h := by
      have hcomm_ha : a * h = h * a := (hcomm h hh).eq
      rw [← hcomm_ha]; group
    rw [hreduce]
    exact hh
  · -- `y·(a·(a⁻¹·(y⁻¹gy)))·y⁻¹ = g`
    change y.1 * (a * (a⁻¹ * (y.1⁻¹ * g * y.1))) * y.1⁻¹ = g
    group
  · -- `p.1.2⁻¹·g·p.1.2 ∈ K·a`: from `p.2(a·p.1)p.2⁻¹ = g`, `p.1∈K`.
    obtain ⟨⟨q1, q2⟩, hq1, hq2⟩ := p
    change q2⁻¹ * g * q2 ∈ (↑K : Set G) * ({a} : Set G)
    rw [Set.mem_mul]
    refine ⟨a * q1 * a⁻¹, ?_, a, Set.mem_singleton _, ?_⟩
    · -- `a·q1·a⁻¹ ∈ K` (`K` is normalized by `a`, which lies in `C_G(a)`)
      have hacomm : a * q1 * a⁻¹ = q1 := by rw [(hcomm q1 hq1).eq]; group
      rw [hacomm]; exact hq1
    · -- `q2⁻¹·g·q2 = (a·q1·a⁻¹)·a`
      have hconj : q2⁻¹ * g * q2 = a * q1 := by rw [← hq2]; group
      rw [hconj]; group
  · -- left inverse
    rintro ⟨y, hy⟩
    rfl
  · -- right inverse
    rintro ⟨⟨x, t⟩, hx, ht⟩
    apply Subtype.ext
    apply Prod.ext
    · -- `a⁻¹·(t⁻¹·g·t) = x` from `t(a·x)t⁻¹ = g`
      change a⁻¹ * (t⁻¹ * g * t) = x
      conv_lhs => rw [← ht]
      group
    · rfl

/-- **Peterfalvi (2.10.3), the support test for a single component `b`.**  For `b ∈ N_L(B)` with
`b ∈ A`, if some conjugate `y⁻¹gy` lies in the coset `H(B)·b` (i.e. `𝒜(g, H(B)b) ≠ ∅`), then
`g ∈ (bH(b))^G` lies in the Dade support.

This is the contrapositive content of the vanishing case
`induce_alphaB_apply_eq_zero_of_not_mem_dadeSupport` isolated to one fiber: by (2.1)
(`exists_mem_centralizer_conj`, with `b` normalizing the coprime `H(B)`), `y⁻¹gy = h·b` is
`H(B)`-conjugate to `c·b` with `c ∈ C_{H(B)}(b) = H(B∪{b}) ⊆ H(b)`
(`centralizer_inf_hIntersection`);
since `c` commutes with `b`, `c·b = b·c ∈ b·H(b) ⊆ hCoset b`, so `g ∈ (bH(b))^G`. -/
theorem exists_mem_H_isConj_of_mem_conjFiber_coset (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    {b : G} (hbN : b ∈ nLStabilizerIn hyp B) (hbA : b ∈ A) {g y : G}
    (hy : y⁻¹ * g * y ∈ (↑(hIntersection hyp B hB) : Set G) * ({b} : Set G)) :
    ∃ c ∈ hyp.H ⟨b, hbA⟩, IsConj (b * c) g := by
  classical
  -- factor `y⁻¹gy = h·b` with `h ∈ H(B)`
  rw [Set.mem_mul] at hy
  obtain ⟨h, hh, b', hb', hyeq⟩ := hy
  rw [Set.mem_singleton_iff] at hb'
  rw [hb'] at hyeq
  -- `hyeq : h * b = y⁻¹ * g * y`
  -- `b` normalizes `H(B)` and is coprime to `|H(B)|`; apply (2.1)
  have hnorm : ∀ z ∈ hIntersection hyp B hB, b * z * b⁻¹ ∈ hIntersection hyp B hB := by
    intro z hz
    have := hyp.nLStabilizerIn_le_normalizer hB hbN
    rw [Subgroup.mem_normalizer_iff] at this
    exact (this z).mp hz
  have hcop := hyp.coprime_orderOf_card_hIntersection hB hbA
  obtain ⟨c, hcmem, x', hx'H, hx'eq⟩ :=
    OddOrder.GroupTheory.exists_mem_centralizer_conj (g := b) (H := hIntersection hyp B hB)
      hcop hnorm hh
  obtain ⟨hcH, hccomm⟩ := Subgroup.mem_inf.mp hcmem
  have hccb : Commute c b := Subgroup.mem_centralizer_singleton_iff.mp hccomm
  have hcHb : c ∈ hyp.H ⟨b, hbA⟩ := by
    have hcInsert : c ∈ hIntersection hyp (insert ⟨b, hbA⟩ B) (Finset.insert_nonempty _ B) := by
      rw [← hyp.centralizer_inf_hIntersection hB ⟨b, hbA⟩]
      exact Subgroup.mem_inf.mpr ⟨hccomm, hcH⟩
    exact hIntersection_le hyp (Finset.insert_nonempty _ B) (Finset.mem_insert_self _ B) hcInsert
  -- `g` is conjugate to `c·b = b·c`
  have hgconj : (x' * y⁻¹) * g * (x' * y⁻¹)⁻¹ = c * b := by
    rw [← hx'eq, hyeq]; group
  refine ⟨c, hcHb, ?_⟩
  rw [show b * c = c * b from (hccb.eq).symm]
  exact (isConj_iff.mpr ⟨x' * y⁻¹, hgconj⟩).symm

open Classical in
/-- **Peterfalvi (2.10.3), the value case `a^L`-specialized.**  Fix a Dade-support representative
`a` with `g ∈ (aH(a))^G` (witnessed by `h ∈ H(a)`, `IsConj (a·h) g`).  Then the `N_L(B)`-aggregated
value of `Ind_{M(B)}^G α_B` collapses to the textbook value formula

    `(Ind_{M(B)}^G α_B)(g) = (α(a)/|M(B)|) · ∑_{b ∈ N_L(B) ∩ a^L} |𝒜(g, H(B)·b)|`,

the sum running only over `b` that are `L`-conjugate to `a`.  Starting from
`induce_alphaB_apply_eq_sum_nLStabilizerIn_inA` (sum over `b ∈ N_L(B), b ∈ A`), the terms with
`b ∉ a^L` vanish: if `|𝒜(g, H(B)b)| ≠ 0` then `g ∈ (bH(b))^G` by
`mem_dadeSupport_of_mem_conjFiber_coset`, whence `a·h` and `b·h'` are `G`-conjugate, so by (2.4.b)
(`isConj_in_L_of_mul_H`) `b ∈ a^L` — a contradiction.  On the surviving `b ∈ a^L` the value
`α(b) = α(a)` (an `L`-class function), and `α(a)` factors out. -/
theorem induce_alphaB_apply_eq_alpha_mul_sum_conjL (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty)
    (α : SupportedClassFunctions (G := G) ℂ A L)
    [Invertible (Nat.card (mBSubgroup hyp B hB) : ℂ)]
    {a : {a : G // a ∈ A}} {h g : G} (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    ClassFunction.induce (mBSubgroup hyp B hB) (alphaB hyp hB (α : ClassFunction L ℂ)) g
      = ⅟(Nat.card (mBSubgroup hyp B hB) : ℂ) *
          ((α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ *
            ∑ b ∈ (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
                (fun b : (nLStabilizerIn hyp B) =>
                  ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G)),
              ((conjFiber g ((↑(hIntersection hyp B hB) : Set G)
                * ({(b : G)} : Set G))).card : ℂ)) := by
  classical
  rw [induce_alphaB_apply_eq_sum_nLStabilizerIn_inA hyp hB α g]
  congr 1
  -- restrict `{b ∈ N_L(B), b ∈ A}` to `{b ∈ N_L(B), b ∈ a^L}`, factoring `α(a)`.
  rw [Finset.mul_sum]
  -- abbreviations for the two filtering predicates and the `N`-summand
  set N : (nLStabilizerIn hyp B) → ℂ := fun b =>
    ((conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(b : G)} : Set G))).card : ℂ) with hN
  set sP : Finset (nLStabilizerIn hyp B) :=
    (Finset.univ : Finset (nLStabilizerIn hyp B)).filter (fun b => ((b : G) ∈ A)) with hsP
  set sQ : Finset (nLStabilizerIn hyp B) :=
    (Finset.univ : Finset (nLStabilizerIn hyp B)).filter
      (fun b => ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G)) with hsQ
  -- `sQ ⊆ sP` (a^L ⊆ A) and on `sP \ sQ` the summand `N b` vanishes.
  have hsub : sQ ⊆ sP := by
    intro b hb
    rw [hsQ, Finset.mem_filter] at hb
    obtain ⟨l, hl⟩ := hb.2
    rw [hsP, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hl ▸ hyp.L_normalizes_A l a.2⟩
  -- `∑_{sP} α(b)·N b = ∑_{sQ} α(b)·N b`: terms outside `sQ` have `N b = 0`.
  have hPQ : ∑ b ∈ sP, (α : ClassFunction L ℂ) ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ * N b
      = ∑ b ∈ sQ, (α : ClassFunction L ℂ) ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩ * N b := by
    refine (Finset.sum_subset hsub fun b hbP hbQ => ?_).symm
    rw [hsP, Finset.mem_filter] at hbP
    obtain ⟨_, hbA⟩ := hbP
    -- `b ∉ sQ` ⟹ `b ∉ a^L`; show `N b = 0`, i.e. `𝒜(g, H(B)b) = ∅`.
    have hbnotQ : ¬ ∃ l : L, (l : G) * a.1 * (l : G)⁻¹ = (b : G) := by
      intro hQ; exact hbQ (by rw [hsQ, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hQ⟩)
    have hfiber0 : N b = 0 := by
      change ((conjFiber g ((↑(hIntersection hyp B hB) : Set G)
        * ({(b : G)} : Set G))).card : ℂ) = 0
      norm_cast
      rw [Finset.card_eq_zero]
      by_contra hne
      rw [← Ne, ← Finset.nonempty_iff_ne_empty] at hne
      obtain ⟨y, hy⟩ := hne
      rw [mem_conjFiber] at hy
      obtain ⟨c, hcHb, hgc⟩ :=
        hyp.exists_mem_H_isConj_of_mem_conjFiber_coset hB b.2 hbA hy
      have hconjab : IsConj (a.1 * h) ((b : G) * c) := hga.trans hgc.symm
      obtain ⟨l, hl⟩ := hyp.isConj_in_L_of_mul_H a.2 hbA hh hcHb hconjab
      exact hbnotQ ⟨l, hl⟩
    rw [hfiber0, mul_zero]
  rw [hPQ]
  -- on `sQ`, `α(b) = α(a)`.
  apply Finset.sum_congr rfl
  intro b hb
  rw [hsQ, Finset.mem_filter] at hb
  obtain ⟨l, hl⟩ := hb.2
  have hαeq : (α : ClassFunction L ℂ) ⟨(b : G), nLStabilizerIn_le_L hyp B b.2⟩
      = (α : ClassFunction L ℂ) ⟨a.1, hyp.mem_L a.2⟩ := by
    refine ClassFunction.of_isConj (α : ClassFunction L ℂ) (isConj_iff.mpr ⟨l⁻¹, ?_⟩)
    apply Subtype.ext
    change (l⁻¹ : L) * (b : G) * ((l⁻¹ : L) : G)⁻¹ = a.1
    rw [← hl]; push_cast; group
  simp only [hN]
  rw [hαeq]

open scoped Classical in
/-- **Peterfalvi (2.1), the conjugacy-image fiber count.**  Let `a` normalize a finite subgroup `K`
coprimely and `C = K ⊓ C_G(a)`.  For `w` in the coset `K·a` (`w·a⁻¹ ∈ K`), the fiber of the
parametrization `(c, x) ↦ x⁻¹(c·a)x` of `K·a` over `w` has exactly `|C|` elements:

    `|{(c, x) ∈ C × K | x⁻¹(c·a)x = w}| = |C|`.

This is the disjoint-union count `H(B)a = ⨆ (C·a)^x` (`coset_eq_cosetConjImage`) read fiberwise.
Given a witness `(c₀, x₀)` for `w`, the map `e ↦ (e c₀ e⁻¹, e x₀)` (`e ∈ C`) bijects `C` with the
fiber, with inverse `(c, x) ↦ x x₀⁻¹` landing in `C` by the rigidity
`mem_centralizer_of_coset_conj_eq`. -/
theorem card_cosetConjFiber_eq_card_centralizerInf {K : Subgroup G} {a : G}
    (hcop : Nat.Coprime (orderOf a) (Nat.card K)) {w : G}
    (hwImage : ∃ c ∈ K ⊓ Subgroup.centralizer ({a} : Set G), ∃ x ∈ K,
      x⁻¹ * (c * a) * x = w) :
    ((Finset.univ : Finset (↥(K ⊓ Subgroup.centralizer ({a} : Set G)) × ↥K)).filter
        (fun p => (p.2 : G)⁻¹ * ((p.1 : G) * a) * (p.2 : G) = w)).card
      = Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) := by
  classical
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({a} : Set G) with hC
  obtain ⟨c₀, hc₀C, x₀, hx₀K, hcx₀⟩ := hwImage
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ (α := C)]
  -- membership of `e c₀ e⁻¹` in `C`, packaged for the forward map.
  have hfwd1 : ∀ e : C, (e : G) * (c₀ : G) * (e : G)⁻¹ ∈ C := by
    intro e
    obtain ⟨heK, hecomm⟩ := Subgroup.mem_inf.mp e.2
    obtain ⟨hc₀K, hc₀comm⟩ := Subgroup.mem_inf.mp hc₀C
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem heK hc₀K) (K.inv_mem heK),
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hge : Commute (e : G) a := Subgroup.mem_centralizer_singleton_iff.mp hecomm
    have hgc₀ : Commute (c₀ : G) a := Subgroup.mem_centralizer_singleton_iff.mp hc₀comm
    have hgeinv : (e : G)⁻¹ * a = a * (e : G)⁻¹ := hge.inv_left.eq
    calc (e : G) * (c₀ : G) * (e : G)⁻¹ * a
        = (e : G) * (c₀ : G) * (a * (e : G)⁻¹) := by rw [mul_assoc, hgeinv]
      _ = (e : G) * ((c₀ : G) * a) * (e : G)⁻¹ := by group
      _ = (e : G) * (a * (c₀ : G)) * (e : G)⁻¹ := by rw [hgc₀.eq]
      _ = (e : G) * a * (c₀ : G) * (e : G)⁻¹ := by group
      _ = a * ((e : G) * (c₀ : G) * (e : G)⁻¹) := by rw [hge.eq]; group
  -- `(c, x) ↦ x x₀⁻¹ ∈ C` for fiber elements, packaged for the inverse map.
  have hinv1 : ∀ p : ↥C × ↥K, p ∈ (Finset.univ : Finset (↥C × ↥K)).filter
        (fun p => (p.2 : G)⁻¹ * ((p.1 : G) * a) * (p.2 : G) = w) →
      (p.2 : G) * (x₀ : G)⁻¹ ∈ C := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hxx₀ := OddOrder.GroupTheory.mem_centralizer_of_coset_conj_eq (g := a) (H := K)
      hcop p.2.2 hx₀K p.1.2 hc₀C (by rw [hp.2, ← hcx₀])
    have := C.inv_mem hxx₀
    rwa [mul_inv_rev, inv_inv] at this
  refine Eq.symm ?_
  refine Finset.card_bij'
    (i := fun e _ => ((⟨(e : G) * (c₀ : G) * (e : G)⁻¹, hfwd1 e⟩ : ↥C),
      (⟨(e : G) * x₀, K.mul_mem ((Subgroup.mem_inf.mp e.2).1) hx₀K⟩ : ↥K)))
    (j := fun p hp => (⟨(p.2 : G) * (x₀ : G)⁻¹, hinv1 p hp⟩ : ↥C))
    ?_ ?_ ?_ ?_
  · -- `i e ∈ fiber`
    intro e _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨-, hecomm⟩ := Subgroup.mem_inf.mp e.2
    have hge : Commute (e : G) a := Subgroup.mem_centralizer_singleton_iff.mp hecomm
    have hge' : (e : G)⁻¹ * a = a * (e : G)⁻¹ := hge.inv_left.eq
    change ((e : G) * x₀)⁻¹ * (((e : G) * (c₀ : G) * (e : G)⁻¹) * a) * ((e : G) * x₀) = w
    rw [← hcx₀]
    calc ((e : G) * x₀)⁻¹ * (((e : G) * (c₀ : G) * (e : G)⁻¹) * a) * ((e : G) * x₀)
        = x₀⁻¹ * ((c₀ : G) * ((e : G)⁻¹ * a * (e : G))) * x₀ := by group
      _ = x₀⁻¹ * ((c₀ : G) * a) * x₀ := by rw [hge']; group
  · -- `j p ∈ univ`
    intro p _; exact Finset.mem_univ _
  · -- left inverse: `j (i e) = e`
    intro e _
    apply Subtype.ext
    change (e : G) * x₀ * (x₀ : G)⁻¹ = (e : G)
    group
  · -- right inverse: `i (j p) = p`
    rintro ⟨⟨c, hcC⟩, ⟨x, hxK⟩⟩ hp
    rw [Finset.mem_filter] at hp
    have hpeq : x⁻¹ * (c * a) * x = w := hp.2
    apply Prod.ext
    · -- first coordinate: `(x x₀⁻¹) c₀ (x x₀⁻¹)⁻¹ = c`
      apply Subtype.ext
      change (x * (x₀ : G)⁻¹) * (c₀ : G) * (x * (x₀ : G)⁻¹)⁻¹ = c
      have hxx₀ := OddOrder.GroupTheory.mem_centralizer_of_coset_conj_eq (g := a) (H := K)
        hcop hxK hx₀K hcC hc₀C (by rw [hpeq, ← hcx₀])
      obtain ⟨-, hcomm⟩ := Subgroup.mem_inf.mp hxx₀
      have hxx₀comm : (x₀ : G) * x⁻¹ * a = a * ((x₀ : G) * x⁻¹) :=
        Subgroup.mem_centralizer_singleton_iff.mp hcomm
      have heq : x⁻¹ * (c * a) * x = x₀⁻¹ * ((c₀ : G) * a) * x₀ := by rw [hpeq, hcx₀]
      have e2 : c * a = x * (x₀ : G)⁻¹ * ((c₀ : G) * a) * ((x₀ : G) * x⁻¹) := by
        calc c * a
            = x * (x⁻¹ * (c * a) * x) * x⁻¹ := by group
          _ = x * (x₀⁻¹ * ((c₀ : G) * a) * x₀) * x⁻¹ := by rw [heq]
          _ = x * (x₀ : G)⁻¹ * ((c₀ : G) * a) * ((x₀ : G) * x⁻¹) := by group
      have e3 : c * a = x * (x₀ : G)⁻¹ * (c₀ : G) * (x * (x₀ : G)⁻¹)⁻¹ * a := by
        calc c * a
            = x * (x₀ : G)⁻¹ * ((c₀ : G) * a) * ((x₀ : G) * x⁻¹) := e2
          _ = x * (x₀ : G)⁻¹ * (c₀ : G) * (a * ((x₀ : G) * x⁻¹)) := by group
          _ = x * (x₀ : G)⁻¹ * (c₀ : G) * (((x₀ : G) * x⁻¹) * a) := by rw [hxx₀comm]
          _ = x * (x₀ : G)⁻¹ * (c₀ : G) * (x * (x₀ : G)⁻¹)⁻¹ * a := by group
      exact mul_right_cancel e3.symm
    · -- second coordinate: `(x x₀⁻¹) x₀ = x`
      apply Subtype.ext
      change x * (x₀ : G)⁻¹ * (x₀ : G) = x
      group

open scoped Classical in
/-- **Peterfalvi (2.1), the fiber factorization** (the long pole of (2.10) STEP 2).  Let `a`
normalize a finite subgroup `K` coprimely and `C = K ⊓ C_G(a)`.  Then for any `g`,

    `|𝒜(g, K·a)| · |C| = |𝒜(g, C·a)| · |K|`,

equivalently `|𝒜(g, K·a)| = |𝒜(g, C·a)| · [K : C]`.  This is Peterfalvi's "`H(B)a` is the disjoint
union of `[H(B):C_{H(B)}(a)]` conjugates of `C_{H(B)}(a)a`, so `|𝒜(g, H(B)a)| =
|𝒜(g, C_{H(B)}(a)a)|·[H(B):C_{H(B)}(a)]`".

Both sides are computed as `|S|`, where `S = {(y, c, x) ∈ G × C × K | y⁻¹gy = x⁻¹(c·a)x}`:
* projecting to `y` and using the conjugacy-image fiber count
  `card_cosetConjFiber_eq_card_centralizerInf` (each nonempty fiber has size `|C|`,
  via `coset_eq_cosetConjImage` for the image membership) gives `|S| = |𝒜(g, K·a)|·|C|`;
* the involution-free bijection `(y, c, x) ↦ (yx⁻¹, c, x)` onto
  `{(w, c, x) | w⁻¹gw = c·a}`, in which `x ∈ K` is now free, gives `|S| = |𝒜(g, C·a)|·|K|`. -/
theorem card_conjFiber_coset_mul_card_centralizerInf {K : Subgroup G} {a : G}
    (hnorm : ∀ x ∈ K, a * x * a⁻¹ ∈ K)
    (hcop : Nat.Coprime (orderOf a) (Nat.card K)) (g : G) :
    (conjFiber g ((↑K : Set G) * ({a} : Set G))).card
        * Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set G))
      = (conjFiber g ((↑(K ⊓ Subgroup.centralizer ({a} : Set G)) : Set G) * ({a} : Set G))).card
        * Nat.card ↥K := by
  classical
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({a} : Set G) with hC
  let : Fintype ↥C := Fintype.ofFinite _
  let : Fintype ↥K := Fintype.ofFinite _
  -- The bridge set `S`.
  set S : Finset (G × ↥C × ↥K) := (Finset.univ : Finset (G × ↥C × ↥K)).filter
    (fun p => p.1⁻¹ * g * p.1 = (p.2.2 : G)⁻¹ * ((p.2.1 : G) * a) * (p.2.2 : G)) with hS
  -- helper: `x⁻¹(c·a)x ∈ K·a` for `c ∈ C`, `x ∈ K`.
  have hmemKa : ∀ (c : G) (_ : c ∈ K) (x : G) (_ : x ∈ K),
      x⁻¹ * (c * a) * x ∈ (↑K : Set G) * ({a} : Set G) := by
    intro c hc x hx
    rw [Set.mem_mul]
    refine ⟨x⁻¹ * c * (a * x * a⁻¹), K.mul_mem (K.mul_mem (K.inv_mem hx) hc) (hnorm x hx),
      a, Set.mem_singleton _, by group⟩
  -- ### `|S| = |𝒜(g, K·a)| · |C|`
  have hSleft : S.card = (conjFiber g ((↑K : Set G) * ({a} : Set G))).card * Nat.card ↥C := by
    rw [hS, Nat.card_eq_fintype_card, ← Finset.card_univ (α := ↥C), ← smul_eq_mul,
      ← Finset.sum_const]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p : G × ↥C × ↥K => p.1)
      (t := conjFiber g ((↑K : Set G) * ({a} : Set G))) ?_]
    · -- each fiber over `y ∈ 𝒜(g, K·a)` has card `|univ C|`
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [mem_conjFiber] at hy
      -- `y⁻¹gy = x⁻¹(c·a)x` (image membership) via (2.1)
      have himg : ∃ c ∈ C, ∃ x ∈ K, x⁻¹ * (c * a) * x = y⁻¹ * g * y := by
        obtain ⟨k, hk, a', ha', hkeq⟩ := hy
        rw [Set.mem_singleton_iff] at ha'
        rw [ha'] at hkeq
        -- `hkeq : k * a = y⁻¹ g y`
        obtain ⟨c, hcC, x, hxK, hxeq⟩ :=
          OddOrder.GroupTheory.exists_mem_centralizer_conj (g := a) (H := K) hcop hnorm hk
        -- `hxeq : x (k a) x⁻¹ = c a`, so `y⁻¹gy = k a = x⁻¹ (c a) x`
        refine ⟨c, hcC, x, hxK, ?_⟩
        rw [← hkeq]
        have hxeq' : x * (k * a) * x⁻¹ = c * a := hxeq
        rw [← hxeq']; group
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
        ← card_cosetConjFiber_eq_card_centralizerInf hcop himg]
      -- the `S`-fiber over `y` (drop the fixed first coordinate) bijects with the conjugacy fiber.
      refine Finset.card_bij' (i := fun p _ => p.2) (j := fun q _ => (y, q))
        ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        obtain ⟨hpeq, hpy⟩ := hp
        rw [← hpy]; exact hpeq.symm
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hq.symm, trivial⟩
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨_, hpy⟩ := hp
        exact Prod.ext hpy.symm rfl
      · intro q _; rfl
    · intro p hpS
      simp only [Finset.mem_coe, mem_conjFiber]
      have hp : p.1⁻¹ * g * p.1 = (p.2.2 : G)⁻¹ * ((p.2.1 : G) * a) * (p.2.2 : G) :=
        (Finset.mem_filter.mp hpS).2
      rw [hp]
      exact hmemKa (p.2.1 : G) (Subgroup.mem_inf.mp p.2.1.2).1 (p.2.2 : G) p.2.2.2
  -- helper: membership `w⁻¹gw ∈ C·a ⟹ (w⁻¹gw)·a⁻¹ ∈ C`.
  have hcwC : ∀ w : G, w⁻¹ * g * w ∈ (↑C : Set G) * ({a} : Set G) →
      w⁻¹ * g * w * a⁻¹ ∈ C := by
    intro w hw
    obtain ⟨c, hc, a', ha', hceq⟩ := hw
    rw [Set.mem_singleton_iff] at ha'
    rw [ha'] at hceq
    rw [← hceq, mul_assoc, mul_inv_cancel, mul_one]; exact hc
  -- ### `|S| = |𝒜(g, C·a)| · |K|` via `(y,c,x) ↦ (yx⁻¹, c, x)` and freeing `x`.
  have hSright : S.card
      = (conjFiber g ((↑C : Set G) * ({a} : Set G))).card * Nat.card ↥K := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ (α := ↥K), ← Finset.card_product]
    refine Finset.card_bij'
      (i := fun p _ => (p.1 * (p.2.2 : G)⁻¹, p.2.2))
      (j := fun q hq => (q.1 * (q.2 : G),
        ⟨q.1⁻¹ * g * q.1 * a⁻¹,
          hcwC q.1 (mem_conjFiber.mp (Finset.mem_product.mp hq).1)⟩, q.2))
      ?_ ?_ ?_ ?_
    · -- `i p ∈ conjFiber(C·a) ×ˢ univ`
      intro p hpS
      rw [Finset.mem_product]
      refine ⟨?_, Finset.mem_univ _⟩
      simp only [mem_conjFiber]
      have hp : p.1⁻¹ * g * p.1 = (p.2.2 : G)⁻¹ * ((p.2.1 : G) * a) * (p.2.2 : G) :=
        (Finset.mem_filter.mp hpS).2
      -- `(p.1 p.2.2⁻¹)⁻¹ g (p.1 p.2.2⁻¹) = p.2.2 (p.1⁻¹ g p.1) p.2.2⁻¹ = p.2.1 · a`
      have hval : (p.1 * (p.2.2 : G)⁻¹)⁻¹ * g * (p.1 * (p.2.2 : G)⁻¹)
          = (p.2.1 : G) * a := by
        rw [show (p.1 * (p.2.2 : G)⁻¹)⁻¹ * g * (p.1 * (p.2.2 : G)⁻¹)
            = (p.2.2 : G) * (p.1⁻¹ * g * p.1) * (p.2.2 : G)⁻¹ by group, hp]; group
      rw [hval]
      exact ⟨(p.2.1 : G), p.2.1.2, a, Set.mem_singleton _, rfl⟩
    · -- `j q ∈ S`
      intro q hq
      rw [Finset.mem_product] at hq
      have hwCa : q.1⁻¹ * g * q.1 ∈ (↑C : Set G) * ({a} : Set G) := by
        have := (mem_conjFiber (g := g)).mp (Finset.mem_coe.mpr hq.1); simpa using this
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      -- S-condition: `(q.1 q.2)⁻¹ g (q.1 q.2) = q.2⁻¹ ((q.1⁻¹gq.1·a⁻¹)·a) q.2`
      change (q.1 * (q.2 : G))⁻¹ * g * (q.1 * (q.2 : G))
        = (q.2 : G)⁻¹ * ((q.1⁻¹ * g * q.1 * a⁻¹) * a) * (q.2 : G)
      rw [show (q.1⁻¹ * g * q.1 * a⁻¹) * a = q.1⁻¹ * g * q.1 by group]
      group
    · -- left inverse `j (i p) = p`
      intro p hpS
      have hp : p.1⁻¹ * g * p.1 = (p.2.2 : G)⁻¹ * ((p.2.1 : G) * a) * (p.2.2 : G) :=
        (Finset.mem_filter.mp hpS).2
      -- `(p.1 p.2.2⁻¹)·p.2.2 = p.1`, and the recovered `c = p.2.1`.
      apply Prod.ext
      · change p.1 * (p.2.2 : G)⁻¹ * (p.2.2 : G) = p.1; group
      apply Prod.ext
      · -- recovered centralizer component equals `p.2.1`
        apply Subtype.ext
        change (p.1 * (p.2.2 : G)⁻¹)⁻¹ * g * (p.1 * (p.2.2 : G)⁻¹) * a⁻¹ = (p.2.1 : G)
        rw [show (p.1 * (p.2.2 : G)⁻¹)⁻¹ * g * (p.1 * (p.2.2 : G)⁻¹)
            = (p.2.2 : G) * (p.1⁻¹ * g * p.1) * (p.2.2 : G)⁻¹ by group, hp]
        group
      · rfl
    · -- right inverse `i (j q) = q`
      intro q hq
      apply Prod.ext
      · change q.1 * (q.2 : G) * (q.2 : G)⁻¹ = q.1; group
      · rfl
  rw [hSleft] at hSright
  exact hSright

open scoped Classical in
/-- **Peterfalvi (2.10), the Möbius cancellation identity** (the toggle-`a` pairing of (2.10)).
For `a ∈ A` normalizing `H(B)` (i.e. `a ∈ N_L(B)`) and nonempty `B ⊆ A`,

    `|𝒜(g, H(B)·a)| · |H(B ∪ {a})| = |𝒜(g, H(B ∪ {a})·a)| · |H(B)|`.

This is the (2.10) STEP 2 factorization `card_conjFiber_coset_mul_card_centralizerInf` specialized
to
`K = H(B)`, with `C = H(B) ⊓ C_G(a) = C_{H(B)}(a) = H(B ∪ {a})` by (2.10.2)
(`centralizer_inf_hIntersection`).  In the (2.10) alternating sum it shows the summands
`(-1)^{|B|}/|H(B)| · |𝒜(g, H(B)·a)|` for `B` and `B ∪ {a}` are equal (so cancel by the opposite
signs `(-1)^{|B|}` vs `(-1)^{|B|+1}`), leaving only the survivor `B = {a}`. -/
theorem card_conjFiber_hIntersection_mul_eq (hyp : Hypothesis G A L)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) {a : {a : G // a ∈ A}}
    (haN : (a : G) ∈ nLStabilizerIn hyp B) (g : G) :
    (conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(a : G)} : Set G))).card
        * Nat.card (hIntersection hyp (insert a B) (Finset.insert_nonempty a B))
      = (conjFiber g ((↑(hIntersection hyp (insert a B) (Finset.insert_nonempty a B)) : Set G)
            * ({(a : G)} : Set G))).card
        * Nat.card (hIntersection hyp B hB) := by
  classical
  -- `a` normalizes `H(B)` coprimely; `H(B) ⊓ C_G(a) = H(insert a B)` by (2.10.2).
  have hnorm : ∀ x ∈ hIntersection hyp B hB, (a : G) * x * (a : G)⁻¹ ∈ hIntersection hyp B hB := by
    intro x hx
    have hmem := hyp.nLStabilizerIn_le_normalizer hB haN
    rw [Subgroup.mem_normalizer_iff] at hmem
    exact (hmem x).mp hx
  have hcop := hyp.coprime_orderOf_card_hIntersection hB a.2
  -- `H(B) ⊓ C_G(a) = H(insert a B)`
  have hCeq : hIntersection hyp B hB ⊓ Subgroup.centralizer ({(a : G)} : Set G)
      = hIntersection hyp (insert a B) (Finset.insert_nonempty a B) := by
    rw [inf_comm]; exact hyp.centralizer_inf_hIntersection hB a
  -- apply STEP 2 and rewrite `C` via (2.10.2)
  have hfact := card_conjFiber_coset_mul_card_centralizerInf
    (K := hIntersection hyp B hB) (a := (a : G)) hnorm hcop g
  rw [hCeq] at hfact
  exact hfact

variable (hyp : Hypothesis G A L)

/-- `𝒫(a)` as a `Finset`: the nonempty subsets `B ⊆ A` with `a ∈ N_L(B)`. -/
noncomputable def mobiusIndex (a : {a : G // a ∈ A}) :
    Finset (Finset {a : G // a ∈ A}) := by
  classical
  letI : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  exact (Finset.univ.powerset).filter
    (fun B => B.Nonempty ∧ (a : G) ∈ nLStabilizerIn hyp B)

theorem mem_mobiusIndex {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}} :
    B ∈ hyp.mobiusIndex a ↔ B.Nonempty ∧ (a : G) ∈ nLStabilizerIn hyp B := by
  classical
  let : Fintype {a : G // a ∈ A} := Fintype.ofFinite _
  simp only [mobiusIndex, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]

/-- The Möbius summand `(-1)^{|B|}/|H(B)| · |𝒜(g, H(B)·a)|` (as a complex number). -/
noncomputable def mobiusSummand (a : {a : G // a ∈ A}) (g : G)
    (B : Finset {a : G // a ∈ A}) : ℂ := by
  classical
  exact if hB : B.Nonempty then
      ((-1 : ℂ) ^ B.card / (Nat.card (hIntersection hyp B hB) : ℂ)) *
        ((conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(a : G)} : Set G))).card : ℂ)
    else 0

theorem mobiusSummand_of_nonempty (a : {a : G // a ∈ A}) (g : G)
    {B : Finset {a : G // a ∈ A}} (hB : B.Nonempty) :
    hyp.mobiusSummand a g B
      = ((-1 : ℂ) ^ B.card / (Nat.card (hIntersection hyp B hB) : ℂ)) *
        ((conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(a : G)} : Set G))).card : ℂ) := by
  rw [mobiusSummand, dif_pos hB]

open scoped Classical in
/-- Membership of `a` in `N_L(B)` is insensitive to inserting `a` into `B` (for `a ∉ B`): since
conjugation by `a` fixes `a` (`a·a·a⁻¹ = a`), `a` permutes `B` iff it permutes `insert a B`. -/
theorem mem_nLStabilizerIn_insert_iff (a : {a : G // a ∈ A})
    {B : Finset {a : G // a ∈ A}} (haB : a ∉ B) :
    (a : G) ∈ nLStabilizerIn hyp (insert a B) ↔ (a : G) ∈ nLStabilizerIn hyp B := by
  classical
  have ha : (a : G) ∈ L := hyp.mem_L a.2
  have hfix : ∀ hx : (a : G) ∈ L, hyp.conjA ⟨(a : G), hx⟩ a = a := by
    intro hx
    apply Subtype.ext
    change (a : G) * (a : G) * (a : G)⁻¹ = (a : G)
    group
  have hfixinv : ∀ hx : (a : G) ∈ L, hyp.conjA ⟨(a : G), hx⟩⁻¹ a = a := by
    intro hx
    apply Subtype.ext
    change (a : G)⁻¹ * (a : G) * ((a : G)⁻¹)⁻¹ = (a : G)
    group
  rw [mem_nLStabilizerIn, mem_nLStabilizerIn]
  constructor
  · rintro ⟨hx, hstab⟩
    refine ⟨ha, ?_⟩
    intro c hc
    have hmem := hstab c (Finset.mem_insert_of_mem hc)
    rw [Finset.mem_insert] at hmem
    rcases hmem with hca | hca
    · -- `conjA a c = a` forces `c = a`, contradicting `a ∉ B` (as `c ∈ B`)
      exfalso
      have hceq : c = a := by
        have := congrArg (hyp.conjA ⟨(a : G), hx⟩⁻¹) hca
        rwa [conjA_inv_conjA, hfixinv hx] at this
      exact haB (hceq ▸ hc)
    · exact hca
  · rintro ⟨hx, hstab⟩
    refine ⟨ha, ?_⟩
    intro c hc
    rw [Finset.mem_insert] at hc
    rcases hc with rfl | hc
    · rw [hfix hx]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hstab c hc)

open scoped Classical in
/-- **Peterfalvi (2.10), the toggle-`a` pairwise cancellation.**  For `a ∉ B`, nonempty `B ⊆ A`
with `a ∈ N_L(B)`, the Möbius summands for `B` and `insert a B` are negatives:

    `mobiusSummand a g B + mobiusSummand a g (insert a B) = 0`.

This is the multiplicative identity `card_conjFiber_hIntersection_mul_eq`
(`|𝒜(g,H(B)a)|·|H(B∪{a})| = |𝒜(g,H(B∪{a})a)|·|H(B)|`) cleared of denominators, together with the
sign flip `(-1)^{|B|+1} = -(-1)^{|B|}` from `|insert a B| = |B| + 1`.  It is the cancellation law
fed to `Finset.sum_involution`. -/
theorem mobiusSummand_add_insert_eq_zero (g : G)
    {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}} (haB : a ∉ B) (hB : B.Nonempty)
    (haN : (a : G) ∈ nLStabilizerIn hyp B) :
    hyp.mobiusSummand a g B + hyp.mobiusSummand a g (insert a B) = 0 := by
  classical
  have hiB : (insert a B).Nonempty := Finset.insert_nonempty a B
  -- the multiplicative cancellation identity
  have hmul := hyp.card_conjFiber_hIntersection_mul_eq hB haN g
  -- nonzero cardinalities
  have hHBne : (Nat.card (hIntersection hyp B hB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hHiBne : (Nat.card (hIntersection hyp (insert a B) hiB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hyp.mobiusSummand_of_nonempty a g hB, hyp.mobiusSummand_of_nonempty a g hiB]
  -- card of `insert a B` and sign flip
  rw [Finset.card_insert_of_notMem haB, pow_succ]
  -- abbreviations
  set p : ℂ := (-1 : ℂ) ^ B.card
  set hb : ℂ := (Nat.card (hIntersection hyp B hB) : ℂ)
  set hib : ℂ := (Nat.card (hIntersection hyp (insert a B) hiB) : ℂ)
  set fb : ℂ := ((conjFiber g ((↑(hIntersection hyp B hB) : Set G)
    * ({(a : G)} : Set G))).card : ℂ)
  set fib : ℂ := ((conjFiber g ((↑(hIntersection hyp (insert a B) hiB) : Set G)
    * ({(a : G)} : Set G))).card : ℂ)
  -- cast the multiplicative identity to ℂ: `fb * hib = fib * hb` (`hiB` and `insert_nonempty`
  -- give defeq `H(insert a B)`)
  have hmulC : fb * hib = fib * hb := by
    change ((conjFiber g ((↑(hIntersection hyp B hB) : Set G) * ({(a : G)} : Set G))).card : ℂ)
        * (Nat.card (hIntersection hyp (insert a B) (Finset.insert_nonempty a B)) : ℂ)
      = ((conjFiber g ((↑(hIntersection hyp (insert a B) (Finset.insert_nonempty a B)) : Set G)
            * ({(a : G)} : Set G))).card : ℂ)
        * (Nat.card (hIntersection hyp B hB) : ℂ)
    exact_mod_cast hmul
  -- assemble: `p/hb · fb + (p·(-1))/hib · fib = (p/(hb·hib)) · (fb·hib - fib·hb) = 0`
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  rw [div_add_div (p * fb) (p * -1 * fib) hHBne hHiBne, div_eq_zero_iff]
  left
  -- numerator: `(p·fb)·hib + hb·(p·(-1)·fib) = p·(fb·hib - fib·hb) = 0`
  linear_combination p * hmulC

/-- The singleton `{a}` lies in `𝒫(a)`. -/
theorem singleton_mem_mobiusIndex (a : {a : G // a ∈ A}) :
    ({a} : Finset {a : G // a ∈ A}) ∈ hyp.mobiusIndex a := by
  classical
  rw [hyp.mem_mobiusIndex]
  refine ⟨Finset.singleton_nonempty a, ?_⟩
  rw [mem_nLStabilizerIn]
  refine ⟨hyp.mem_L a.2, ?_⟩
  intro c hc
  rw [Finset.mem_singleton] at hc
  rw [hc, Finset.mem_singleton]
  apply Subtype.ext
  change (a : G) * (a : G) * (a : G)⁻¹ = (a : G)
  group

/-- The toggle-`a` map `B ↦ B △ {a}`: removes `a` from `B` if present, else inserts it. -/
noncomputable def toggleA (a : {a : G // a ∈ A}) (B : Finset {a : G // a ∈ A}) :
    Finset {a : G // a ∈ A} := by
  classical
  exact if a ∈ B then B.erase a else insert a B

omit [Group G] in
omit [Fintype G] in
open scoped Classical in
theorem toggleA_of_mem {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}}
    (haB : a ∈ B) : toggleA a B = B.erase a := by
  classical rw [toggleA]; simp only [if_pos haB]

omit [Group G] in
omit [Fintype G] in
open scoped Classical in
theorem toggleA_of_not_mem {a : {a : G // a ∈ A}} {B : Finset {a : G // a ∈ A}}
    (haB : a ∉ B) : toggleA a B = insert a B := by
  classical rw [toggleA]; simp only [if_neg haB]

open scoped Classical in
/-- **Peterfalvi (2.10), the toggle-`a` involution collapses `𝒫(a)` to its `B = {a}` survivor.**

    `∑_{B ∈ 𝒫(a)} mobiusSummand a g B = mobiusSummand a g {a}`.

The toggle `B ↦ B △ {a}` (`toggleA`) is a fixed-point-free involution on `𝒫(a) \ {{a}}` under which
the summands cancel pairwise (`mobiusSummand_add_insert_eq_zero`), so `∑_{𝒫(a) \ {{a}}} = 0` by
`Finset.sum_involution`; adding back the isolated survivor `{a}` gives the claim. -/
theorem sum_mobiusSummand_eq_singleton (g : G)
    (a : {a : G // a ∈ A}) :
    ∑ B ∈ hyp.mobiusIndex a, hyp.mobiusSummand a g B = hyp.mobiusSummand a g {a} := by
  classical
  -- a helper: `toggleA a B ∈ 𝒫(a) \ {{a}}` and the pairwise data, packaged once.
  have key : ∀ B ∈ (hyp.mobiusIndex a).erase ({a} : Finset {a : G // a ∈ A}),
      hyp.mobiusSummand a g B + hyp.mobiusSummand a g (toggleA a B) = 0
        ∧ toggleA a B ∈ (hyp.mobiusIndex a).erase ({a} : Finset {a : G // a ∈ A})
        ∧ toggleA a (toggleA a B) = B := by
    intro B hB
    rw [Finset.mem_erase, hyp.mem_mobiusIndex] at hB
    obtain ⟨hBne, hBnonempty, hBnorm⟩ := hB
    by_cases haB : a ∈ B
    · -- `toggleA a B = B.erase a`, write `B = insert a (B.erase a)`
      set B' := B.erase a with hB'
      have haB' : a ∉ B' := Finset.notMem_erase a B
      have hBins : B = insert a B' := by rw [hB', Finset.insert_erase haB]
      have hB'ne : B'.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty, hB']
        intro hempty
        rcases (Finset.erase_eq_empty_iff B a).mp hempty with h | h
        · rw [h] at haB; exact absurd haB (Finset.notMem_empty a)
        · exact hBne h
      have hB'norm : (a : G) ∈ nLStabilizerIn hyp B' := by
        rw [← hyp.mem_nLStabilizerIn_insert_iff a haB', ← hBins]; exact hBnorm
      refine ⟨?_, ?_, ?_⟩
      · rw [toggleA_of_mem haB]
        have := hyp.mobiusSummand_add_insert_eq_zero g haB' hB'ne hB'norm
        rw [← hBins] at this
        rw [add_comm]; exact this
      · rw [toggleA_of_mem haB, Finset.mem_erase, hyp.mem_mobiusIndex]
        refine ⟨fun hcontra => haB' ?_, hB'ne, hB'norm⟩
        change a ∈ B.erase a
        rw [hcontra]; exact Finset.mem_singleton_self a
      · rw [toggleA_of_mem haB]
        rw [toggleA_of_not_mem haB', Finset.insert_erase haB]
    · -- `toggleA a B = insert a B`
      have hains : (a : G) ∈ nLStabilizerIn hyp (insert a B) :=
        (hyp.mem_nLStabilizerIn_insert_iff a haB).mpr hBnorm
      refine ⟨?_, ?_, ?_⟩
      · rw [toggleA_of_not_mem haB]
        exact hyp.mobiusSummand_add_insert_eq_zero g haB hBnonempty hBnorm
      · rw [toggleA_of_not_mem haB, Finset.mem_erase, hyp.mem_mobiusIndex]
        refine ⟨?_, Finset.insert_nonempty a B, hains⟩
        intro hcontra
        obtain ⟨c, hc⟩ := hBnonempty
        have hcins : c ∈ insert a B := Finset.mem_insert_of_mem hc
        rw [hcontra, Finset.mem_singleton] at hcins
        exact haB (hcins ▸ hc)
      · rw [toggleA_of_not_mem haB, toggleA_of_mem (Finset.mem_insert_self a B),
          Finset.erase_insert haB]
  -- isolate the survivor `{a}`: `∑_{𝒫(a)} = mobiusSummand {a} + ∑_{𝒫(a) \ {{a}}}`
  rw [← Finset.sum_erase_add _ _ (hyp.singleton_mem_mobiusIndex a)]
  have hzero : ∑ B ∈ (hyp.mobiusIndex a).erase ({a} : Finset {a : G // a ∈ A}),
      hyp.mobiusSummand a g B = 0 := by
    refine Finset.sum_involution (fun B _ => toggleA a B)
      (fun B hB => (key B hB).1)
      (fun B hB _ => ?_)
      (fun B hB => (key B hB).2.1)
      (fun B hB => (key B hB).2.2)
    -- `hg₃`: `toggleA a B ≠ B` (toggle changes membership of `a`)
    show toggleA a B ≠ B
    by_cases haB : a ∈ B
    · rw [toggleA_of_mem haB]
      intro hcontra
      rw [← hcontra] at haB
      exact (Finset.notMem_erase a B) haB
    · rw [toggleA_of_not_mem haB]
      intro hcontra
      have : a ∈ B := by rw [← hcontra]; exact Finset.mem_insert_self a B
      exact haB this
  rw [hzero, zero_add]

/-- `H({a}) = H(a)`: the intersection over the singleton `{a}` is `H(a)`. -/
theorem hIntersection_singleton (a : {a : G // a ∈ A}) :
    hIntersection hyp {a} (Finset.singleton_nonempty a) = hyp.H a := by
  apply le_antisymm
  · exact hyp.hIntersection_le _ (Finset.mem_singleton_self a)
  · intro x hx
    rw [mem_hIntersection]
    intro b hb
    rw [Finset.mem_singleton] at hb
    exact hb ▸ hx

/-- **Peterfalvi (2.10), evaluation of the surviving `B = {a}` term.**  For `g ∈ (aH(a))^G`
(witnessed by `h ∈ H(a)`, `IsConj (a·h) g`),

    `mobiusSummand a g {a} = -(|C_L(a)| : ℂ)`.

Indeed `|{a}| = 1`, `H({a}) = H(a)`, and the surviving conjugating set has
`|𝒜(g, H(a)·a)| = |C_G(a)|` (`card_conjFiber_coset_eq_card_centralizer`), while
`|C_G(a)| = |H(a)|·|C_L(a)|` (`card_centralizer_eq`); the `|H(a)|` cancels the denominator,
leaving `(-1)·|C_L(a)|`. -/
theorem mobiusSummand_singleton_eq (g : G) {a : {a : G // a ∈ A}} {h : G}
    (hh : h ∈ hyp.H a) (hga : IsConj (a.1 * h) g) :
    hyp.mobiusSummand a g {a} = -(Nat.card (centralizerIn L a.1) : ℂ) := by
  classical
  rw [hyp.mobiusSummand_of_nonempty a g (Finset.singleton_nonempty a)]
  -- `H({a}) = H(a)`
  have hHeq : hIntersection hyp {a} (Finset.singleton_nonempty a) = hyp.H a :=
    hyp.hIntersection_singleton a
  rw [hHeq, Finset.card_singleton, pow_one]
  -- `|𝒜(g, H(a)·a)| = |C_G(a)|`
  have hcomm : ∀ x ∈ hyp.H a, Commute a.1 x := fun x hx => hyp.commute_of_mem_H a hx
  have hnorm : ∀ c ∈ Subgroup.centralizer ({a.1} : Set G), ∀ x ∈ hyp.H a, c * x * c⁻¹ ∈ hyp.H a :=
    fun c hc x hx => hyp.H_normalized a c hc x hx
  have hcop : Nat.Coprime (orderOf a.1) (Nat.card (hyp.H a)) := by
    have := hyp.coprime_orderOf_card_hIntersection (Finset.singleton_nonempty a) a.2
    rwa [hHeq] at this
  have hAcard : (conjFiber g ((↑(hyp.H a) : Set G) * ({a.1} : Set G))).card
      = Nat.card (Subgroup.centralizer ({a.1} : Set G)) :=
    card_conjFiber_coset_eq_card_centralizer hcomm hnorm hcop hh hga
  rw [hAcard]
  -- `|C_G(a)| = |H(a)|·|C_L(a)|`
  rw [hyp.card_centralizer_eq a]
  -- `(-1)/|H(a)| · (|H(a)|·|C_L(a)|) = -|C_L(a)|`
  have hHne : (Nat.card (hyp.H a) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  push_cast
  field_simp

end MobiusAssembly

end SemidirectStructure

end Hypothesis

end OddOrder.Peterfalvi.S04


