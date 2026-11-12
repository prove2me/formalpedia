-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
-- name    : OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:36:15.704219+00:00
-- url     : https://prove2.me/theorems/2ef7d0d7-10bd-400e-acca-5336e22c5ade
-- title:
--   Frobenius irreducibility of induced characters (Isaacs Thm 6.34)
-- statement:
--   For a normal subgroup $H\trianglelefteq G$ with quotient $W_1=G/H$, this file builds toward Isaacs, *Character Theory of Finite Groups*, Thm 6.34: when $W_1$ acts freely on $\mathrm{Irr}\,H\setminus\{1\}$ (the Frobenius/Dade situation of Peterfalvi §6), the induced character $\mathrm{Ind}_H^G\theta$ of a nontrivial $\theta$ is irreducible of degree $|W_1|\theta(1)$. This supplies the two facts Peterfalvi (6.8) needs: the constituents lie in $\mathrm{Irr}\,G$ and share the common degree $|W_1|$.
--
--   Declarations include Mackey restriction as an orbit sum (`card_smul_restrict_induce_eq_inertia_smul_orbitSum`), orthogonality of induced characters from non-conjugate irreducibles, the norm of an induced irreducible character, `induce_eq_induce_iff_conj`, injectivity of induction at inertia-stable irreducibles, and orbit size equal to inertia index.
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/InducedIrreducible.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Inertia
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrrFourier
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Clifford
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ConjugationBrauer
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup

namespace OddOrder.RepresentationTheory

open ClassFunction

variable {G : Type*} [Group G] {H : Subgroup G} [hH : H.Normal]

variable {k : Type*} [CommRing k]

/-- Evaluation of a finite sum of class functions is the sum of the evaluations.

A pointwise companion to `ClassFunction.add_apply`/`zero_apply`, needed to unfold the
right-hand side of the Mackey restriction formula. -/
@[simp] theorem ClassFunction.finset_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → ClassFunction G k) (g : G) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]

section FrobeniusInertia

variable [Finite G] [Finite H]

/-- Frobenius-group specialization of the Brauer-conjugation inertia bridge.

If `G = H ⋊ W` is a Frobenius group with kernel `H`, every nontrivial irreducible character of
`H` has inertia subgroup exactly `H`.  This is the form needed in Peterfalvi (6.8), where
`[Is]` Theorem 6.34 is applied to `Ind_H^L θ` in the Frobenius case. -/
theorem inertia_eq_of_frobeniusGroup {W : Subgroup G}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G H W)
    {θ : IrreducibleCharacter H} (hθ_ne : θ ≠ trivialIrreducibleCharacter H) :
    ClassFunction.inertia (G := G) (H := H) (θ : ClassFunction H ℂ) = H := by
  refine inertia_eq_of_freeAction (G := G) (H := H) ?_ hθ_ne
  intro h hh
  have hhG : (h : G) ≠ 1 := by
    intro h1
    exact hh (Subtype.ext h1)
  exact hF.centralizer_kernel_le (h : G) h.property hhG

end FrobeniusInertia

variable [Fintype G] [Invertible (Nat.card H : k)]

/-- **Mackey restriction formula** (normal-subgroup case), in unnormalized form.

For `H ⊴ G` and `θ : ClassFunction ↥H k`,
`|H| • Res_H (Ind_H^G θ) = ∑_{x ∈ G} θ^{x⁻¹}`,
where `θ^{x⁻¹} = ClassFunction.conjBy x⁻¹ θ`.

Summing over the *whole* group `G` (rather than a transversal) keeps the statement free of a
choice of coset representatives: each left coset `xH` contributes `|H|` equal summands
`θ^{x⁻¹}` — equal because `conjBy` is constant along the coset
(`ClassFunction.conjBy_eq_self_of_mem`) — so the global `|H|` factor exactly cancels the
`|H|⁻¹` built into `induce`. The classical transversal form
`Res_H (Ind_H^G θ) = ∑_{w ∈ G/H} θ^{w⁻¹}` is the same identity divided by `|H|`.

The proof is pointwise: for `h ∈ H` every conjugate `x⁻¹ h x` stays in `H` (normality), so
no induction term vanishes (`induceTerm_of_mem_normal`), and `θ(x⁻¹ h x)` is exactly
`(conjBy x⁻¹ θ)(h)`. -/
theorem card_smul_restrict_induce (θ : ClassFunction ↥H k) :
    (Nat.card H : k) • restrict H (induce H θ) = ∑ x : G, conjBy x⁻¹ θ := by
  ext h
  rw [ClassFunction.smul_apply, restrict_apply, induce_apply, ClassFunction.finset_sum_apply,
    ← mul_assoc, mul_invOf_self, one_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [induceTerm_of_mem_normal (le_refl H) θ h.property x, conjBy_apply]
  exact congrArg θ (Subtype.ext (by group))

open scoped Classical in
/-- **Mackey restriction as an orbit sum** (normal-subgroup case): grouping the Mackey sum
`|H| • Res_H (Ind_H^G θ) = ∑_{x∈G} θ^{x⁻¹}` (`card_smul_restrict_induce`) by the value of the
conjugate gives

  `|H| • Res_H (Ind_H^G θ) = |I_G(θ)| • ∑_{ψ ∈ orbit(θ)} ψ`,

where the orbit is the `Finset` image of `x ↦ θ^{x⁻¹}` over `G` and each fibre
`{x | θ^{x⁻¹} = ψ}` is a right coset of the inertia group `I_G(θ)` (hence of constant size
`|I_G(θ)|`).  Combined with `|H|·‖Ind θ‖² = |I_G(θ)|`
(`card_mul_inner_self_induce_eq_card_inertia`) this is the classical
`Res_H (Ind_H^G θ) = ‖Ind θ‖² · (sum of the distinct conjugates)` — the "`(1/‖ζ_i‖²)·Res ζ_i`
is a character" step of Peterfalvi (13.5.a). -/
theorem card_smul_restrict_induce_eq_inertia_smul_orbitSum (θ : ClassFunction ↥H k) :
    (Nat.card H : k) • restrict H (induce H θ)
      = (Nat.card ↥(ClassFunction.inertia (G := G) (H := H) θ)) •
          ∑ ψ ∈ Finset.univ.image (fun x : G => ClassFunction.conjBy x⁻¹ θ), ψ := by
  classical
  rw [card_smul_restrict_induce, Finset.sum_comp (fun ψ : ClassFunction ↥H k => ψ)
    (fun x : G => ClassFunction.conjBy x⁻¹ θ)]
  -- Each fibre is a right coset of the inertia group.
  have hfiber : ∀ ψ ∈ Finset.univ.image (fun x : G => ClassFunction.conjBy x⁻¹ θ),
      (Finset.univ.filter (fun x : G => ClassFunction.conjBy x⁻¹ θ = ψ)).card
        = Nat.card ↥(ClassFunction.inertia (G := G) (H := H) θ) := by
    intro ψ hψ
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp hψ
    have : Fintype ↥(ClassFunction.inertia (G := G) (H := H) θ) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    -- Bijection `x ↦ x₀⁻¹·x` from the fibre (the left coset `x₀·I`) onto the inertia group.
    refine (Finset.card_bij' (fun x hx => (⟨x₀⁻¹ * x, ?_⟩ : ↥(ClassFunction.inertia
        (G := G) (H := H) θ))) (fun j _ => x₀ * (j : G)) ?_ ?_ ?_ ?_)
    · -- the fibre condition puts `x₀⁻¹·x` in the inertia group (`conjBy` composes
      -- contravariantly: `conjBy (a·b) = conjBy b ∘ conjBy a`)
      have hfib : ClassFunction.conjBy x⁻¹ θ = ClassFunction.conjBy x₀⁻¹ θ :=
        (Finset.mem_filter.mp hx).2
      rw [ClassFunction.mem_inertia]
      calc ClassFunction.conjBy (x₀⁻¹ * x) θ
          = ClassFunction.conjBy x (ClassFunction.conjBy x₀⁻¹ θ) := by
            rw [ClassFunction.conjBy_mul]
        _ = ClassFunction.conjBy x (ClassFunction.conjBy x⁻¹ θ) := by rw [hfib]
        _ = ClassFunction.conjBy (x⁻¹ * x) θ := by rw [ClassFunction.conjBy_mul]
        _ = θ := by rw [inv_mul_cancel, ClassFunction.conjBy_one]
    · -- membership of the image point (trivial: full finset)
      intro x hx
      exact Finset.mem_univ _
    · -- the reverse map lands in the fibre
      intro j _
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hjinv : ClassFunction.conjBy ((j : G))⁻¹ θ = θ :=
        ClassFunction.mem_inertia.mp (Subgroup.inv_mem _ j.2)
      calc ClassFunction.conjBy (x₀ * (j : G))⁻¹ θ
          = ClassFunction.conjBy ((j : G)⁻¹ * x₀⁻¹) θ := by rw [mul_inv_rev]
        _ = ClassFunction.conjBy x₀⁻¹ (ClassFunction.conjBy ((j : G))⁻¹ θ) := by
            rw [ClassFunction.conjBy_mul]
        _ = ClassFunction.conjBy x₀⁻¹ θ := by rw [hjinv]
    · -- left inverse
      intro x hx
      group
    · -- right inverse
      intro j _
      exact Subtype.ext (by group)
  rw [Finset.sum_congr rfl (fun ψ hψ => by rw [hfiber ψ hψ]), ← Finset.smul_sum]

section Complex

variable [Fintype H] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]

/-- **Norm of an induced character via the Mackey sum** (any class function).

`|H| · ⟨Ind_H^G θ, Ind_H^G θ⟩ = ∑_{x ∈ G} ⟨θ, θ^{x⁻¹}⟩`.

This is Frobenius reciprocity combined with the Mackey restriction formula
`card_smul_restrict_induce`: pairing `θ` against `|H| • Res_H (Ind θ) = ∑_x θ^{x⁻¹}` and using
that the inner product is conjugate-linear on the right (`inner_smul_right`, with
`star (|H| : ℂ) = |H|`). No irreducibility is needed yet. -/
theorem card_mul_inner_self_induce (θ : ClassFunction ↥H ℂ) :
    (Nat.card H : ℂ) *
        ClassFunction.inner (induce H θ) (induce H θ) =
      ∑ x : G, ClassFunction.inner θ (conjBy x⁻¹ θ) := by
  have key : ClassFunction.inner θ ((Nat.card H : ℂ) • restrict H (induce H θ))
      = (Nat.card H : ℂ) * ClassFunction.inner (induce H θ) (induce H θ) := by
    rw [inner_smul_right, star_natCast, ← inner_induce_eq_inner_restrict]
  rw [← key, card_smul_restrict_induce, inner_sum_right]

/-- **Cross inner product of two induced characters via the Mackey sum** (any class functions).

`|H| · ⟨Ind_H^G θ, Ind_H^G ψ⟩ = ∑_{x ∈ G} ⟨θ, ψ^{x⁻¹}⟩`.  The two-argument generalization of
`card_mul_inner_self_induce`; the proof is identical, using Frobenius reciprocity
(`inner_induce_eq_inner_restrict`, general in the right argument) and the Mackey restriction
formula `card_smul_restrict_induce` applied to `ψ`. -/
theorem card_mul_inner_induce (θ ψ : ClassFunction ↥H ℂ) :
    (Nat.card H : ℂ) *
        ClassFunction.inner (induce H θ) (induce H ψ) =
      ∑ x : G, ClassFunction.inner θ (conjBy x⁻¹ ψ) := by
  have key : ClassFunction.inner θ ((Nat.card H : ℂ) • restrict H (induce H ψ))
      = (Nat.card H : ℂ) * ClassFunction.inner (induce H θ) (induce H ψ) := by
    rw [inner_smul_right, star_natCast, ← inner_induce_eq_inner_restrict]
  rw [← key, card_smul_restrict_induce, inner_sum_right]

omit [Fintype ↥H] in
/-- **Induced characters from non-conjugate irreducibles are orthogonal.**

If no `G`-conjugate of `θ` equals `ψ` (the two irreducibles of `H` lie in distinct `G`-orbits),
then `⟨Ind_H^G θ, Ind_H^G ψ⟩ = 0`.  Each Mackey summand `⟨θ, ψ^{x⁻¹}⟩` is an orthonormality
indicator (`irreducibleCharacter_inner_eq_ite`) that vanishes because `θ = ψ^{x⁻¹}` would give
`θ^x = ψ` (`conjBy_conjBy_inv`), contradicting the non-conjugacy hypothesis.  Used to prove the
`Y = S(H')` family `j ↦ Ind_H^L θ_j` injective. -/
theorem inner_induce_eq_zero_of_not_conj (θ ψ : IrreducibleCharacter H)
    (h : ∀ g : G, IrreducibleCharacter.conjBy g θ ≠ ψ) :
    ClassFunction.inner (induce H (θ : ClassFunction ↥H ℂ))
      (induce H (ψ : ClassFunction ↥H ℂ)) = 0 := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  classical
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  apply mul_left_cancel₀ hcardH
  rw [mul_zero, card_mul_inner_induce]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [← IrreducibleCharacter.coe_conjBy, irreducibleCharacter_inner_eq_ite, if_neg]
  intro hθ
  exact h x (by rw [hθ]; simp)

omit [Fintype ↥H] in
/-- **Norm of an induced irreducible character** ([Is] Thm 6.34, norm part).

For an irreducible character `θ` of `H ⊴ G`, `|H| · ‖Ind_H^G θ‖² = |I_G(θ)|`, equivalently
`‖Ind_H^G θ‖² = [I_G(θ) : H]`: the squared norm counts the cosets of `H` in the inertia group.

Each Mackey summand `⟨θ, θ^{x⁻¹}⟩` is `1` if `x ∈ I_G(θ)` and `0` otherwise, by orthonormality
of irreducible characters (`irreducibleCharacter_inner_eq_ite`) together with
`θ^{x⁻¹} = θ ⇔ x ∈ I_G(θ)`. Summing the indicator over `G` gives `|I_G(θ)|`. -/
theorem card_mul_inner_self_induce_eq_card_inertia (θ : IrreducibleCharacter H) :
    (Nat.card H : ℂ) *
        ClassFunction.inner (induce H (θ : ClassFunction ↥H ℂ))
          (induce H (θ : ClassFunction ↥H ℂ))
      = (Nat.card ↥(ClassFunction.inertia (θ : ClassFunction ↥H ℂ)) : ℂ) := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  classical
  rw [card_mul_inner_self_induce]
  have hterm : ∀ x : G,
      ClassFunction.inner (θ : ClassFunction ↥H ℂ) (conjBy x⁻¹ (θ : ClassFunction ↥H ℂ))
        = if x ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) then (1 : ℂ) else 0 := by
    intro x
    rw [← IrreducibleCharacter.coe_conjBy, irreducibleCharacter_inner_eq_ite]
    have hcond : (θ = IrreducibleCharacter.conjBy x⁻¹ θ)
        ↔ x ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      rw [eq_comm, IrreducibleCharacter.ext_iff, IrreducibleCharacter.coe_conjBy,
        ← ClassFunction.mem_inertia, Subgroup.inv_mem_iff]
    simp only [hcond]
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_boole, ← Fintype.card_subtype,
    Nat.card_eq_fintype_card]

omit [Fintype ↥H] in
/-- **Induced irreducibles coincide iff the sources are `G`-conjugate.**  For `θ, ψ ∈ Irr H`
(`H ⊴ G`), `Ind_H^G θ = Ind_H^G ψ` exactly when some `G`-conjugate of `θ` equals `ψ`.

Forward: if no conjugate of `θ` is `ψ`, then `Ind θ ⊥ Ind ψ` (`inner_induce_eq_zero_of_not_conj`),
so `Ind θ = Ind ψ` would force `‖Ind ψ‖² = 0`, contradicting `|H| · ‖Ind ψ‖² = |I_G(ψ)| > 0`
(`card_mul_inner_self_induce_eq_card_inertia`).  Backward: induction is conjugation-invariant
(`induce_conjBy_eq`).  This is the fibre description underpinning the orbit-counting of `S(A)`
(Peterfalvi (6.2), step 4a): the map `θ ↦ Ind_K^L θ` has fibres exactly the `L`-conjugacy orbits. -/
theorem induce_eq_induce_iff_conj (θ ψ : IrreducibleCharacter H) :
    induce H (θ : ClassFunction ↥H ℂ) = induce H (ψ : ClassFunction ↥H ℂ) ↔
      ∃ g : G, IrreducibleCharacter.conjBy g θ = ψ := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  classical
  constructor
  · intro heq
    by_contra hcon
    push Not at hcon
    have h0 := inner_induce_eq_zero_of_not_conj θ ψ hcon
    rw [heq] at h0
    have hpos : ClassFunction.inner (induce H (ψ : ClassFunction ↥H ℂ))
        (induce H (ψ : ClassFunction ↥H ℂ)) ≠ 0 := by
      have hcard := card_mul_inner_self_induce_eq_card_inertia ψ
      have hI : (Nat.card ↥(ClassFunction.inertia (ψ : ClassFunction ↥H ℂ)) : ℂ) ≠ 0 := by
        rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
      intro hzero
      rw [hzero, mul_zero] at hcard
      exact hI hcard.symm
    exact hpos h0
  · rintro ⟨g, rfl⟩
    have : Fintype G := Fintype.ofFinite G
    rw [IrreducibleCharacter.coe_conjBy, induce_conjBy_eq]

omit [Fintype ↥H] in
/-- **Induction is injective at an inertia-stable irreducible.**  If `θ ∈ Irr H` (`H ⊴ G`) is fixed
by every `G`-conjugation (`I_G(θ) = G`, i.e. its conjugation orbit is the singleton `{θ}`), then
`Ind_H^G θ = Ind_H^G ψ` forces `ψ = θ`: the fibre of `ψ ↦ Ind ψ` over `Ind θ` is that singleton
orbit (`induce_eq_induce_iff_conj`).  This is the injectivity behind the `𝒳 ↔ 𝒮` count when the
relevant sources are `G`-invariant — Peterfalvi (9.5)/(9.9)'s `Smu` uniqueness (the Coq `ResIndXmu`
route: `Res_H (Ind θ) = [G:H] · θ` for `G`-stable `θ`). -/
theorem induce_injective_of_inertia_stable {θ ψ : IrreducibleCharacter H}
    (hθ : ∀ g : G, IrreducibleCharacter.conjBy g θ = θ)
    (h : induce H (θ : ClassFunction ↥H ℂ) = induce H (ψ : ClassFunction ↥H ℂ)) : ψ = θ := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj θ ψ).mp h
  rw [← hg]; exact hθ g

omit [Fintype G] in
omit [Fintype H] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)] in
/-- **Orbit size = inertia index.**  The `G`-conjugation orbit of `θ ∈ Irr H` (`H ⊴ G`) has
cardinality `[G : I_G(θ)]`, via the coset parametrization `conjByOrbitEquivLeftCosets`.  Together
with `induce_eq_induce_iff_conj` (orbit = fibre of `θ ↦ Ind θ`) this gives the multiplicity with
which each `χ ∈ S(A)` is hit, for the Peterfalvi (6.2) step-4a orbit count. -/
theorem card_conjByOrbit_eq_index_inertia (θ : IrreducibleCharacter H) :
    Nat.card (IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ) =
      (IrreducibleCharacter.inertia (G := G) (H := H) θ).index :=
  (Nat.card_congr (IrreducibleCharacter.conjByOrbitEquivLeftCosets (G := G) (H := H) θ)).symm

omit [Fintype G] in
omit [Fintype H] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)] in
/-- **Conjugation preserves degree.**  `(θ^g)(1) = θ(1)`: conjugation evaluates `θ` at
`g · 1 · g⁻¹ = 1`. -/
@[simp] theorem conjBy_apply_one (g : G) (θ : IrreducibleCharacter H) :
    ((IrreducibleCharacter.conjBy (G := G) (H := H) g θ : IrreducibleCharacter H) :
        ClassFunction ↥H ℂ) 1 = (θ : ClassFunction ↥H ℂ) 1 := by
  rw [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
  refine congrArg _ (Subtype.ext ?_)
  simp

open scoped Classical in
omit [Fintype ↥H] in
/-- **Fibre cardinality = inertia index.**  Inside a conjugation-invariant Finset `T` of
irreducibles, the fibre `{θ ∈ T | Ind θ = Ind θ₀}` of the induction map equals the whole
`G`-orbit of `θ₀` (by `induce_eq_induce_iff_conj` and `T`-invariance), so its cardinality is
`[G : I_G(θ₀)]` (`card_conjByOrbit_eq_index_inertia`).  This is the multiplicity input to the
Peterfalvi (6.2) step-4a orbit count. -/
theorem card_filter_induce_eq_index_inertia (T : Finset (IrreducibleCharacter H))
    (hT : ∀ θ ∈ T, ∀ g : G, IrreducibleCharacter.conjBy (G := G) (H := H) g θ ∈ T)
    (θ₀ : IrreducibleCharacter H) (hθ₀ : θ₀ ∈ T) :
    (T.filter fun θ => induce H θ.toClassFunction = induce H θ₀.toClassFunction).card
      = (IrreducibleCharacter.inertia (G := G) (H := H) θ₀).index := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  rw [← card_conjByOrbit_eq_index_inertia (G := G) (H := H) θ₀,
    Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  congr 1
  ext θ
  simp only [Finset.coe_filter, Set.mem_ofPred_eq,
    IrreducibleCharacter.mem_conjByOrbit, induce_eq_induce_iff_conj]
  constructor
  · rintro ⟨_, g, hg⟩
    exact ⟨g⁻¹, by rw [← hg, ← IrreducibleCharacter.conjBy_mul]; simp⟩
  · rintro ⟨g, hg⟩
    exact ⟨hg ▸ hT θ₀ hθ₀ g, g⁻¹, by rw [← hg, ← IrreducibleCharacter.conjBy_mul]; simp⟩

open scoped Classical in
omit [Fintype ↥H] in
/-- **Peterfalvi (6.2), step 4a — the orbit-counted degree-sum identity.**  For a conjugation-
invariant Finset `T ⊆ Irr H` (`H ⊴ G`), summing `χ(1)²/‖χ‖²` over the induced characters
`S = {Ind_H^G θ | θ ∈ T}` equals `[G:H] · ∑_{θ∈T} θ(1)²`.

Each `χ = Ind θ` is hit by the whole `G`-orbit of `θ` (`card_filter_induce_eq_index_inertia`), of
size `[G:I_G(θ)]`, on which the degree is constant (`conjBy_apply_one`).  Combined with the norm
`|H|·‖Ind θ‖² = |I_G(θ)|` (`card_mul_inner_self_induce_eq_card_inertia`) and the degree
`Ind θ(1) = [G:H]·θ(1)` (`induce_apply_one`), the per-`χ` term telescopes via `[G:H]·|H| = |G| =
[G:I]·|I|` to `[G:H]·([G:I]·θ(1)²)`, which is exactly `[G:H]` times the fibre's degree-sum. -/
theorem sum_div_normSq_induce_image_eq (T : Finset (IrreducibleCharacter H))
    (hT : ∀ θ ∈ T, ∀ g : G, IrreducibleCharacter.conjBy (G := G) (H := H) g θ ∈ T) :
    ∑ χ ∈ T.image (fun θ => induce H θ.toClassFunction),
        χ 1 ^ 2 / ClassFunction.inner χ χ
      = (H.index : ℂ) * ∑ θ ∈ T, θ.toClassFunction 1 ^ 2 := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  have hcH : (Nat.card ↥H : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  rw [Finset.mul_sum, ← Finset.sum_fiberwise_of_maps_to
    (fun θ (hθ : θ ∈ T) => Finset.mem_image_of_mem (fun θ => induce H θ.toClassFunction) hθ)]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  obtain ⟨θ₀, hθ₀T, rfl⟩ := Finset.mem_image.mp hχ
  have hcI : (Nat.card ↥(IrreducibleCharacter.inertia (G := G) (H := H) θ₀) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  -- The fibre's `[G:H]·θ(1)²`-sum collapses to `[G:H]·[G:I]·θ₀(1)²` (constant degree + fibre card).
  have hfib : ∑ θ ∈ T.filter (fun θ =>
        induce H θ.toClassFunction = induce H θ₀.toClassFunction),
        (H.index : ℂ) * θ.toClassFunction 1 ^ 2
      = (H.index : ℂ)
          * (IrreducibleCharacter.inertia (G := G) (H := H) θ₀).index * θ₀.toClassFunction 1 ^ 2 :=
              by
    have hconst : ∀ θ ∈ T.filter (fun θ =>
        induce H θ.toClassFunction = induce H θ₀.toClassFunction),
        (H.index : ℂ) * θ.toClassFunction 1 ^ 2 = (H.index : ℂ) * θ₀.toClassFunction 1 ^ 2 := by
      intro θ hθ
      rw [Finset.mem_filter] at hθ
      obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj θ θ₀).mp hθ.2
      rw [← hg, conjBy_apply_one]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const,
      card_filter_induce_eq_index_inertia T hT θ₀ hθ₀T, nsmul_eq_mul]
    ring
  rw [hfib, induce_apply_one]
  have hinner : ClassFunction.inner (induce H θ₀.toClassFunction) (induce H θ₀.toClassFunction)
      = (Nat.card ↥(IrreducibleCharacter.inertia (G := G) (H := H) θ₀) : ℂ) / (Nat.card ↥H : ℂ) :=
          by
    rw [eq_div_iff hcH, mul_comm]
    exact card_mul_inner_self_induce_eq_card_inertia θ₀
  rw [hinner]
  have hHmul : (H.index : ℂ) * (Nat.card ↥H : ℂ) = (Nat.card G : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.index_mul_card]
  have hImul : ((IrreducibleCharacter.inertia (G := G) (H := H) θ₀).index : ℂ)
      * (Nat.card ↥(IrreducibleCharacter.inertia (G := G) (H := H) θ₀) : ℂ) = (Nat.card G : ℂ) := by
    rw [← Nat.cast_mul, Subgroup.index_mul_card]
  have hAB : (H.index : ℂ) * (Nat.card ↥H : ℂ)
      = ((IrreducibleCharacter.inertia (G := G) (H := H) θ₀).index : ℂ)
          * (Nat.card ↥(IrreducibleCharacter.inertia (G := G) (H := H) θ₀) : ℂ) := hHmul.trans
              hImul.symm
  rw [div_div_eq_mul_div, div_eq_iff hcI]
  linear_combination (θ₀.toClassFunction 1 ^ 2 * (H.index : ℂ)) * hAB

/-- Integer-vector combinatorics: if nonzero integer coefficients on a finite set have squares
summing to `1`, the set is a singleton with coefficient `±1`. (The `∑ = 1` analogue of
`exists_pair_of_sum_sq_eq_two`.) -/
theorem exists_single_of_sum_sq_eq_one {ι : Type*} {s : Finset ι} {c : ι → ℤ}
    (hne : ∀ a ∈ s, c a ≠ 0) (hsum : ∑ a ∈ s, c a ^ 2 = 1) :
    ∃ α, s = {α} ∧ (c α = 1 ∨ c α = -1) := by
  classical
  have hge : ∀ a ∈ s, 1 ≤ c a ^ 2 := fun a ha => by
    have h := Int.one_le_abs (hne a ha)
    calc (1 : ℤ) = 1 ^ 2 := by ring
      _ ≤ |c a| ^ 2 := by gcongr
      _ = c a ^ 2 := sq_abs (c a)
  have hcard : s.card = 1 := by
    have hle : (s.card : ℤ) ≤ ∑ a ∈ s, c a ^ 2 := by
      calc (s.card : ℤ) = ∑ _a ∈ s, (1 : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ a ∈ s, c a ^ 2 := Finset.sum_le_sum hge
    rw [hsum] at hle
    have hpos : 0 < s.card := by
      rcases Finset.eq_empty_or_nonempty s with rfl | h
      · simp at hsum
      · exact Finset.card_pos.mpr h
    omega
  obtain ⟨α, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.sum_singleton] at hsum
  refine ⟨α, rfl, ?_⟩
  have hmul : c α * c α = 1 := by rw [← sq]; exact hsum
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmul with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

set_option backward.isDefEq.respectTransparency false in
/-- **A virtual character of squared norm `1` and positive degree is irreducible.**

If `φ ∈ ℤ[Irr G]` has `‖φ‖² = 1` and `φ(1)` is a positive natural number, then `φ` is an
irreducible character. By Parseval its Fourier coefficients are integers with `∑ cᵢ² = 1`, so
exactly one is `±1`; positivity of `φ(1)` rules out the `-1` case, leaving `φ = χ` for an
irreducible `χ`. (The norm-`1` analogue of `exists_irr_sub_irr_of_inner_self_two`.) -/
theorem isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    (hnorm : ClassFunction.inner φ φ = 1)
    (hpos : ∃ d : ℕ, 0 < d ∧ (φ : G → ℂ) 1 = (d : ℂ)) :
    IsIrreducibleCharacter φ := by
  classical
  have : Finite G := Finite.of_fintype G
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have hsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 1 := hsq.symm.trans hnorm
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 1 := by exact_mod_cast hsumC
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  obtain ⟨α₀, hs, hcα⟩ := exists_single_of_sum_sq_eq_one hne hsumZ
  have hα₀ : α₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  rw [hs, Finset.sum_singleton] at hrepr
  obtain ⟨d, hd, hφ1⟩ := hpos
  obtain ⟨e, he, hα1⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨α₀, hα₀⟩ : IrreducibleCharacter G)
  simp only [IrreducibleCharacter.coe_mk] at hα1
  rcases hcα with hcα | hcα
  · -- c α₀ = 1: φ = α₀, which is irreducible
    rw [hrepr, hcα]
    simp only [Int.cast_one, one_smul]
    exact hα₀
  · -- c α₀ = -1: φ(1) = -e < 0, contradicting φ(1) = d > 0
    exfalso
    have hval : (φ : G → ℂ) 1 = -(e : ℂ) := by
      rw [hrepr, hcα]
      simp only [Int.cast_neg, Int.cast_one, ClassFunction.smul_apply, hα1]
      ring
    rw [hval] at hφ1
    have hsum0 : (d : ℂ) + (e : ℂ) = 0 := by linear_combination -hφ1
    rw [← Nat.cast_add] at hsum0
    have : d + e = 0 := by exact_mod_cast hsum0
    omega

/-- **A virtual character of squared norm `1` is `±` an irreducible character.**

The signed refinement of `isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos`: without
the positivity input, Parseval still forces a single Fourier coefficient `±1`, so
`φ = ε • ξ` with `ε ∈ {1, -1}` and `ξ ∈ Irr G`.  This is the normalization step of
Peterfalvi (5.9.a) ("there is an integer `ε = ±1` such that `ε φ^{τ₁} ∈ Irr G`"). -/
theorem exists_zsmul_irreducibleCharacter_of_inner_self_one
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    (hnorm : ClassFunction.inner φ φ = 1) :
    ∃ (ε : ℤ) (ξ : IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧ φ = ε • (ξ : ClassFunction G ℂ) := by
  classical
  have : Finite G := Finite.of_fintype G
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hφ
  have hsumC : ∑ a ∈ c.support, (c a : ℂ) ^ 2 = 1 := hsq.symm.trans hnorm
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 1 := by exact_mod_cast hsumC
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  obtain ⟨α₀, hs, hcα⟩ := exists_single_of_sum_sq_eq_one hne hsumZ
  have hα₀ : α₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  rw [hs, Finset.sum_singleton] at hrepr
  refine ⟨c α₀, ⟨α₀, hα₀⟩, hcα, ?_⟩
  rw [hrepr]
  exact Int.cast_smul_eq_zsmul ℂ (c α₀) α₀

omit [Fintype ↥H] in
/-- **[Is] Theorem 6.34** (Frobenius/Dade induced irreducibility).

For `H ⊴ G` and an irreducible character `θ` of `H` whose inertia group in `G` is just `H`
(the free-action / Frobenius condition — which holds for `θ ≠ 1` when `G/H` acts freely on
`Irr H ∖ {1}`), the induced character `Ind_H^G θ` is irreducible. Its degree is `[G : H] · θ(1)`
(`induce_apply_one`).

Proof: `Ind θ ∈ ℤ[Irr G]` (`induce_mem_ZIrr`); `‖Ind θ‖² = |I_G(θ)|/|H| = 1` from
`card_mul_inner_self_induce_eq_card_inertia` with `I_G(θ) = H`; and `Ind θ (1) = [G:H]·θ(1) > 0`.
Norm `1` with positive degree forces irreducibility. -/
theorem isIrreducibleCharacter_induce_of_inertia_eq (θ : IrreducibleCharacter H)
    (hfree : ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H) :
    IsIrreducibleCharacter (induce H (θ : ClassFunction ↥H ℂ)) := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  have hmem : induce H (θ : ClassFunction ↥H ℂ) ∈ ZIrr G :=
    induce_mem_ZIrr H θ.property.mem_ZIrr
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  have hnorm : ClassFunction.inner (induce H (θ : ClassFunction ↥H ℂ))
      (induce H (θ : ClassFunction ↥H ℂ)) = 1 := by
    have h := card_mul_inner_self_induce_eq_card_inertia θ
    rw [hfree] at h
    exact mul_left_cancel₀ hcardH (by rw [h, mul_one])
  have hpos : ∃ d : ℕ, 0 < d ∧ (induce H (θ : ClassFunction ↥H ℂ) : G → ℂ) 1 = (d : ℂ) := by
    have : Finite G := Finite.of_fintype G
    obtain ⟨e, he, hθ1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hidx : 0 < H.index := Nat.pos_of_ne_zero fun h0 => by
      have hmc := H.index_mul_card
      rw [h0, zero_mul] at hmc
      exact (Nat.card_pos (α := G)).ne' hmc.symm
    refine ⟨H.index * e, Nat.mul_pos hidx he, ?_⟩
    rw [induce_apply_one, hθ1, Nat.cast_mul]
  exact isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos hmem hnorm hpos

omit [Fintype ↥H] in
/-- Frobenius-group form of **[Is] Theorem 6.34**.

In a Frobenius group with kernel `H`, inducing any nontrivial irreducible character of `H`
to the ambient group gives an irreducible character.  The proof combines
`inertia_eq_of_frobeniusGroup` with `isIrreducibleCharacter_induce_of_inertia_eq`; the degree
formula remains `ClassFunction.induce_apply_one`. -/
theorem isIrreducibleCharacter_induce_of_frobeniusGroup {W : Subgroup G}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G H W)
    (θ : IrreducibleCharacter H) (hθ_ne : θ ≠ trivialIrreducibleCharacter H) :
    IsIrreducibleCharacter (induce H (θ : ClassFunction H ℂ)) :=
  isIrreducibleCharacter_induce_of_inertia_eq θ
    (inertia_eq_of_frobeniusGroup hF hθ_ne)

omit [Fintype ↥H] in
/-- **Norm of a Frobenius-induced character is `1`.**  In a Frobenius group with kernel `H`, a
nontrivial irreducible `θ` of `H` induces with `‖Ind_H^G θ‖² = |I_G(θ)|/|H| = 1` — the inertia is
`H` (`inertia_eq_of_frobeniusGroup`), so `card_mul_inner_self_induce_eq_card_inertia` reads
`|H|·‖Ind θ‖² = |H|`.  This is the `‖ζ_0‖² = 1` input that the §7 (7.8) `Hypothesis78` norm
machinery needs for an `Ind`-distinguished family member (e.g. the §12 type-I coherent family). -/
theorem inner_self_induce_eq_one_of_frobeniusGroup {W : Subgroup G}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G H W)
    (θ : IrreducibleCharacter H) (hθ_ne : θ ≠ trivialIrreducibleCharacter H) :
    ClassFunction.inner (induce H (θ : ClassFunction H ℂ))
      (induce H (θ : ClassFunction H ℂ)) = 1 := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by rw [Nat.cast_ne_zero]; exact Nat.card_pos.ne'
  have h := card_mul_inner_self_induce_eq_card_inertia θ
  rw [inertia_eq_of_frobeniusGroup hF hθ_ne] at h
  exact mul_left_cancel₀ hcardH (by rw [h, mul_one])

open scoped Classical in
omit [Fintype ↥H] in
/-- **Odd-order Frobenius: a nontrivial induced irreducible is orthogonal to its complex
conjugate.**  In a Frobenius group `G` of odd order with kernel `H`, for `θ ∈ Irr H`, `θ ≠ 1`,
the induced `Ind_H^G θ` is irreducible (`isIrreducibleCharacter_induce_of_frobeniusGroup`) and
nontrivial (`⟨Ind θ, 1_G⟩ = ⟨θ, 1_H⟩ = 0 ≠ 1`), hence — `G` odd — not real
(`not_isReal_of_ne_trivial_of_odd_card'`): `(Ind θ)‾ = Ind θ̄ ≠ Ind θ`.  Distinct irreducibles are
orthogonal, so `⟨Ind θ, Ind θ̄⟩ = 0`. -/
theorem inner_induce_conj_eq_zero_of_frobenius_of_odd {W : Subgroup G}
    (hodd : Odd (Nat.card G)) (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G H W)
    (θ : IrreducibleCharacter H) (hθ : θ ≠ trivialIrreducibleCharacter H) :
    ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction H ℂ))
      (ClassFunction.induce H ((θ : ClassFunction H ℂ).conj)) = 0 := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  -- `θ̄` is again a nontrivial irreducible character of `H`.
  have hθbar_ne : (⟨(θ : ClassFunction H ℂ).conj, θ.isIrreducible.conj⟩ :
      IrreducibleCharacter H) ≠ trivialIrreducibleCharacter H := by
    intro h
    apply hθ
    have hcoe : (θ : ClassFunction H ℂ).conj = trivialClassFunction H := by
      have h2 := congrArg (fun c : IrreducibleCharacter H => (c : ClassFunction H ℂ)) h
      simpa using h2
    apply Subtype.ext
    change (θ : ClassFunction H ℂ) = trivialClassFunction H
    rw [← ClassFunction.conj_conj (θ : ClassFunction H ℂ), hcoe]
    exact trivialClassFunction_isReal
  have hirr := isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ
  have hirr' := isIrreducibleCharacter_induce_of_frobeniusGroup hF
    (⟨(θ : ClassFunction H ℂ).conj, θ.isIrreducible.conj⟩ : IrreducibleCharacter H) hθbar_ne
  -- `Ind θ` is nontrivial: `⟨Ind θ, 1_G⟩ = ⟨θ, 1_H⟩ = 0`, but `⟨1_G, 1_G⟩ = 1`.
  have hne_triv : (⟨ClassFunction.induce H (θ : ClassFunction H ℂ), hirr⟩ :
      IrreducibleCharacter G) ≠ trivialIrreducibleCharacter G := by
    intro h
    have hrestrict : ClassFunction.restrict H
          (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        = (trivialIrreducibleCharacter H : ClassFunction H ℂ) := by
      ext x
      simp [ClassFunction.restrict_apply, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        trivialClassFunction_apply]
    have hzero : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction H ℂ))
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 := by
      rw [ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
        irreducibleCharacter_inner_eq_ite, if_neg hθ]
    have hcf : ClassFunction.induce H (θ : ClassFunction H ℂ)
        = (trivialIrreducibleCharacter G : ClassFunction G ℂ) :=
      congrArg (fun c : IrreducibleCharacter G => (c : ClassFunction G ℂ)) h
    rw [hcf, irreducibleCharacter_inner_eq_ite, if_pos rfl] at hzero
    exact one_ne_zero hzero
  -- Odd order gives `(Ind θ)‾ ≠ Ind θ`.
  have hnotreal := not_isReal_of_ne_trivial_of_odd_card' hodd hne_triv
  have hconj_eq : (ClassFunction.induce H (θ : ClassFunction H ℂ)).conj
      = ClassFunction.induce H ((θ : ClassFunction H ℂ).conj) :=
    ClassFunction.induce_conj H (θ : ClassFunction H ℂ)
  have hne : ClassFunction.induce H (θ : ClassFunction H ℂ)
      ≠ ClassFunction.induce H ((θ : ClassFunction H ℂ).conj) :=
    fun heq => hnotreal (hconj_eq.trans heq.symm)
  -- Distinct irreducibles are orthogonal.
  have hii := irreducibleCharacter_inner_eq_ite
    (⟨ClassFunction.induce H (θ : ClassFunction H ℂ), hirr⟩ : IrreducibleCharacter G)
    ⟨ClassFunction.induce H ((θ : ClassFunction H ℂ).conj), hirr'⟩
  rwa [if_neg (fun h => hne (congrArg (fun c : IrreducibleCharacter G =>
    (c : ClassFunction G ℂ)) h))] at hii

omit hH [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **Degree from restriction multiplicities** (the degree side of Clifford's theorem).  For
`H ⊴ G` and any class function `χ` of `G`, the degree `χ(1)` equals `∑_θ ⟨Res χ, θ⟩ · θ(1)` over
the irreducible characters `θ` of `H` — the Fourier expansion
(`sum_inner_irreducibleCharacter_smul`)
of `Res^G_H χ` evaluated at `1`.

Combined with single-orbit + common multiplicity
(`hasCommonRestrictionMultiplicity_of_singleOrbit`) and the orbit size
(`card_conjByOrbit_eq_index_inertia`), this is the degree statement of Clifford's theorem
`χ(1) = e · [G : I_G(θ)] · θ(1)`. -/
theorem apply_one_eq_sum_restrictionMultiplicity_mul [Fintype (IrreducibleCharacter ↥H)]
    (χ : ClassFunction G ℂ) :
    χ (1 : G) = ∑ θ : IrreducibleCharacter ↥H,
      ClassFunction.restrictionMultiplicity H χ (θ : ClassFunction ↥H ℂ)
        * (θ : ClassFunction ↥H ℂ) (1 : ↥H) := by
  classical
  have hsum : ∀ (s : Finset (IrreducibleCharacter ↥H))
      (F : IrreducibleCharacter ↥H → ClassFunction ↥H ℂ),
      (∑ θ ∈ s, F θ) (1 : ↥H) = ∑ θ ∈ s, (F θ) (1 : ↥H) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  have hexp := sum_inner_irreducibleCharacter_smul (G := ↥H) (ClassFunction.restrict H χ)
  have key := congrArg (fun f : ClassFunction ↥H ℂ => f (1 : ↥H)) hexp
  simp only [hsum, ClassFunction.smul_apply, ClassFunction.restrict_apply,
    OneMemClass.coe_one] at key
  simp only [ClassFunction.restrictionMultiplicity_def]
  exact key.symm

end Complex

section SignedIrreducible

variable {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]

/-- A norm-`1` virtual character has nonzero degree: if `φ = ε • ξ` with `ε = ±1` and `ξ`
irreducible, then `φ(1) = ε · ξ(1) ≠ 0` (irreducible degrees are positive). -/
theorem apply_one_ne_zero_of_mem_ZIrr_of_inner_self_one
    {φ : ClassFunction Γ ℂ} (hφ : φ ∈ ZIrr Γ)
    (hφn : ClassFunction.inner φ φ = 1) : φ (1 : Γ) ≠ 0 := by
  obtain ⟨ε, ξ, hε, rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hφ hφn
  obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ξ
  rw [← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction Γ ℂ), ClassFunction.smul_apply, hd1]
  refine mul_ne_zero ?_ ?_
  · rcases hε with h | h <;> subst h <;> norm_num
  · exact_mod_cast hd.ne'

/-- A norm-`1` virtual character has degree of absolute value at least `1`: `φ = ε • ξ` with
`ε = ±1` and `ξ` irreducible, so `‖φ(1)‖ = ξ(1) ≥ 1`.  The quantitative form of
`apply_one_ne_zero_of_mem_ZIrr_of_inner_self_one`, feeding the `‖φ(1)‖²/|G| ≥ 1/|G|` term of the
Peterfalvi (13.10.1)/(13.10.2) Parseval estimates. -/
theorem one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one
    {φ : ClassFunction Γ ℂ} (hφ : φ ∈ ZIrr Γ)
    (hφn : ClassFunction.inner φ φ = 1) : 1 ≤ ‖φ (1 : Γ)‖ ^ 2 := by
  obtain ⟨ε, ξ, hε, rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hφ hφn
  obtain ⟨d, hd, hd1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ξ
  rw [← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction Γ ℂ), ClassFunction.smul_apply, hd1,
    norm_mul]
  have hε1 : ‖(ε : ℂ)‖ = 1 := by rcases hε with h | h <;> subst h <;> norm_num
  rw [hε1, one_mul, Complex.norm_natCast]
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith

/-- Two signed irreducibles with nonzero inner product are equal up to that inner product:
`ψ = ⟨φ, ψ⟩ • φ`.  (Writing `φ = ε•a`, `ψ = ε'•b`, the inner product `εε'·(a = b)` is nonzero only
if `a = b`, in which case `⟨φ,ψ⟩ = εε'` and `εε'·ε = ε'` since `ε² = 1`.) -/
theorem eq_inner_smul_of_inner_ne_zero
    {φ ψ : ClassFunction Γ ℂ} (hφ : φ ∈ ZIrr Γ) (hψ : ψ ∈ ZIrr Γ)
    (hφn : ClassFunction.inner φ φ = 1) (hψn : ClassFunction.inner ψ ψ = 1)
    (hne : ClassFunction.inner φ ψ ≠ 0) :
    ψ = ClassFunction.inner φ ψ • φ := by
  classical
  obtain ⟨ε, a, hε, rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hφ hφn
  obtain ⟨ε', b, hε', rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hψ hψn
  have key : ClassFunction.inner (ε • (a : ClassFunction Γ ℂ)) (ε' • (b : ClassFunction Γ ℂ)) =
      (ε : ℂ) * (ε' : ℂ) *
        ClassFunction.inner (a : ClassFunction Γ ℂ) (b : ClassFunction Γ ℂ) := by
    rw [← Int.cast_smul_eq_zsmul ℂ ε (a : ClassFunction Γ ℂ),
      ← Int.cast_smul_eq_zsmul ℂ ε' (b : ClassFunction Γ ℂ),
      ClassFunction.inner_smul_left, inner_smul_right, star_intCast]
    ring
  have hab : a = b := by
    by_contra hab
    exact hne (by rw [key, irreducibleCharacter_inner, if_neg hab, mul_zero])
  subst hab
  rw [key, irreducibleCharacter_inner, if_pos rfl, mul_one,
    ← Int.cast_smul_eq_zsmul ℂ ε' (a : ClassFunction Γ ℂ),
    ← Int.cast_smul_eq_zsmul ℂ ε (a : ClassFunction Γ ℂ), smul_smul]
  congr 1
  rcases hε with h | h <;> subst h <;> push_cast <;> ring

/-- **Peterfalvi (4.1)** (mmd 04.6 L5), cross-orthogonality core.

For signed irreducibles `α, β, γ, δ ∈ ±Irr Γ` (norm-`1` elements of `ZIrr Γ`) and nonzero reals
`u, v`, if `(α,β) = (γ,δ) = 0`, the signed difference `(α − β, u•γ − v•δ) = 0`, and both signed
differences vanish at `1`, then `(α, γ) = 0`.

Proof (mmd): if `(α,γ) ≠ 0`, then `γ = εα` (`ε = ±1`); orthogonality of `γ,δ` forces `(α,δ) = 0`,
and `(α,β) = 0` forces `(β,γ) = 0`.  Expanding `(α−β, u•γ−v•δ) = 0` gives `uε + v(β,δ) = 0`, so
`(β,δ) ≠ 0` and `v•δ = −uε•β`.  Then `u•γ − v•δ = uε•(α+β)`, and evaluating at `1` (using
`(α−β)(1) = 0`, i.e. `α(1) = β(1)`) gives `0 = 2uεα(1)`, contradicting `u ≠ 0`, `ε ≠ 0`,
`α(1) ≠ 0`. -/
theorem inner_eq_zero_of_orthogonal_signedDifference
    {α β γ δ : ClassFunction Γ ℂ} {u v : ℝ} (hu : u ≠ 0) (_hv : v ≠ 0)
    (hα : α ∈ ZIrr Γ) (hαn : ClassFunction.inner α α = 1)
    (hβ : β ∈ ZIrr Γ) (hβn : ClassFunction.inner β β = 1)
    (hγ : γ ∈ ZIrr Γ) (hγn : ClassFunction.inner γ γ = 1)
    (hδ : δ ∈ ZIrr Γ) (hδn : ClassFunction.inner δ δ = 1)
    (hαβ : ClassFunction.inner α β = 0) (hγδ : ClassFunction.inner γ δ = 0)
    (hdiff : ClassFunction.inner (α - β) ((u : ℂ) • γ - (v : ℂ) • δ) = 0)
    (hα1 : (α - β) (1 : Γ) = 0)
    (hγδ1 : ((u : ℂ) • γ - (v : ℂ) • δ) (1 : Γ) = 0) :
    ClassFunction.inner α γ = 0 := by
  by_contra hαγ
  -- (1) `γ = ⟨α,γ⟩ • α`.
  have hγeq : γ = ClassFunction.inner α γ • α :=
    eq_inner_smul_of_inner_ne_zero hα hγ hαn hγn hαγ
  -- (2) `⟨α,δ⟩ = 0` (else `δ = ±α = ±γ`, contradicting `γ ⊥ δ`).
  have hαδ : ClassFunction.inner α δ = 0 := by
    by_contra hαδ
    have hδeq : δ = ClassFunction.inner α δ • α :=
      eq_inner_smul_of_inner_ne_zero hα hδ hαn hδn hαδ
    have hcontra : ClassFunction.inner γ δ =
        ClassFunction.inner α γ * star (ClassFunction.inner α δ) := by
      conv_lhs => rw [hγeq, hδeq]
      rw [ClassFunction.inner_smul_left, inner_smul_right, hαn, mul_one]
    exact (mul_ne_zero hαγ (star_ne_zero.mpr hαδ)) (hγδ ▸ hcontra).symm
  -- (3) `⟨β,γ⟩ = 0`.
  have hβγ : ClassFunction.inner β γ = 0 := by
    rw [hγeq, inner_smul_right, inner_conj_symm α β, hαβ, star_zero, mul_zero]
  -- (4) Expand the signed-difference orthogonality to `u⟨α,γ⟩ + v⟨β,δ⟩ = 0`.
  have hexpand : (u : ℂ) * ClassFunction.inner α γ + (v : ℂ) * ClassFunction.inner β δ = 0 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
      inner_smul_right, inner_smul_right, inner_smul_right, inner_smul_right] at hdiff
    simp only [show star ((u : ℝ) : ℂ) = ((u : ℝ) : ℂ) from by simp,
      show star ((v : ℝ) : ℂ) = ((v : ℝ) : ℂ) from by simp, hαδ, hβγ, mul_zero] at hdiff
    linear_combination hdiff
  -- (5) `⟨β,δ⟩ ≠ 0`, so `δ = ⟨β,δ⟩ • β`.
  have hβδ : ClassFunction.inner β δ ≠ 0 := by
    intro h0
    rw [h0, mul_zero, add_zero] at hexpand
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hu) hαγ) hexpand
  have hδeq : δ = ClassFunction.inner β δ • β :=
    eq_inner_smul_of_inner_ne_zero hβ hδ hβn hδn hβδ
  -- (6) Evaluate at `1`.  `α(1) = β(1)` from `(α−β)(1) = 0`.
  have hαβ1 : α (1 : Γ) = β (1 : Γ) := by
    have h := hα1; rw [ClassFunction.sub_apply, sub_eq_zero] at h; exact h
  have hγ1 : γ (1 : Γ) = ClassFunction.inner α γ * α (1 : Γ) := by
    conv_lhs => rw [hγeq]
    rw [ClassFunction.smul_apply]
  have hδ1 : δ (1 : Γ) = ClassFunction.inner β δ * β (1 : Γ) := by
    conv_lhs => rw [hδeq]
    rw [ClassFunction.smul_apply]
  rw [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.smul_apply, hγ1, hδ1,
    ← hαβ1] at hγδ1
  -- `hγδ1 : u·(⟨α,γ⟩·α(1)) − v·(⟨β,δ⟩·α(1)) = 0`.
  have hfinal : 2 * (u : ℂ) * ClassFunction.inner α γ * α (1 : Γ) = 0 := by
    linear_combination hγδ1 + α (1 : Γ) * hexpand
  -- (7) Contradiction: every factor is nonzero.
  refine (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) hαγ)
    (apply_one_ne_zero_of_mem_ZIrr_of_inner_self_one hα hαn)) hfinal
  · norm_num
  · exact Complex.ofReal_ne_zero.mpr hu

/-- **Peterfalvi (4.1)** (mmd 04.6 L5).  Signed irreducibles `α, β, γ, δ ∈ ±Irr Γ` with
`(α,β) = (γ,δ) = 0`, orthogonal signed difference `(α − β, u•γ − v•δ) = 0` (`u, v` nonzero reals)
and both signed differences vanishing at `1` are **pairwise orthogonal**: all four cross inner
products `(α,γ), (α,δ), (β,γ), (β,δ)` vanish.

Each follows from the cross-orthogonality core
`inner_eq_zero_of_orthogonal_signedDifference` applied to a sign-flipped / swapped instance
(`α ↔ β`, `γ ↔ δ` with `u ↔ v`); the permuted hypotheses are produced by conjugate symmetry
(`inner_conj_symm`) and `neg_sub`. -/
theorem pairwise_inner_eq_zero_of_orthogonal_signedDifference
    {α β γ δ : ClassFunction Γ ℂ} {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hα : α ∈ ZIrr Γ) (hαn : ClassFunction.inner α α = 1)
    (hβ : β ∈ ZIrr Γ) (hβn : ClassFunction.inner β β = 1)
    (hγ : γ ∈ ZIrr Γ) (hγn : ClassFunction.inner γ γ = 1)
    (hδ : δ ∈ ZIrr Γ) (hδn : ClassFunction.inner δ δ = 1)
    (hαβ : ClassFunction.inner α β = 0) (hγδ : ClassFunction.inner γ δ = 0)
    (hdiff : ClassFunction.inner (α - β) ((u : ℂ) • γ - (v : ℂ) • δ) = 0)
    (hα1 : (α - β) (1 : Γ) = 0)
    (hγδ1 : ((u : ℂ) • γ - (v : ℂ) • δ) (1 : Γ) = 0) :
    ClassFunction.inner α γ = 0 ∧ ClassFunction.inner α δ = 0 ∧
      ClassFunction.inner β γ = 0 ∧ ClassFunction.inner β δ = 0 := by
  -- Conjugate-symmetric companions of the orthogonality hypotheses.
  have hδγ : ClassFunction.inner δ γ = 0 := by rw [inner_conj_symm γ δ, hγδ, star_zero]
  have hβα : ClassFunction.inner β α = 0 := by rw [inner_conj_symm α β, hαβ, star_zero]
  -- The `β ↔ α` and `γ,u ↔ δ,v` sign-flipped signed differences (orthogonal + vanishing at `1`).
  have hdiffYX : ClassFunction.inner (α - β) ((v : ℂ) • δ - (u : ℂ) • γ) = 0 := by
    rw [← neg_sub ((u : ℂ) • γ) ((v : ℂ) • δ), ClassFunction.inner_neg_right, hdiff, neg_zero]
  have hdiffBA : ClassFunction.inner (β - α) ((u : ℂ) • γ - (v : ℂ) • δ) = 0 := by
    rw [← neg_sub α β, ClassFunction.inner_neg_left, hdiff, neg_zero]
  have hdiffBAYX : ClassFunction.inner (β - α) ((v : ℂ) • δ - (u : ℂ) • γ) = 0 := by
    rw [← neg_sub α β, ← neg_sub ((u : ℂ) • γ) ((v : ℂ) • δ),
      ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg, hdiff]
  have h1BA : (β - α) (1 : Γ) = 0 := by
    rw [← neg_sub α β, ClassFunction.neg_apply, hα1, neg_zero]
  have h1YX : ((v : ℂ) • δ - (u : ℂ) • γ) (1 : Γ) = 0 := by
    rw [← neg_sub ((u : ℂ) • γ) ((v : ℂ) • δ), ClassFunction.neg_apply, hγδ1, neg_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact inner_eq_zero_of_orthogonal_signedDifference hu hv hα hαn hβ hβn hγ hγn hδ hδn
      hαβ hγδ hdiff hα1 hγδ1
  · exact inner_eq_zero_of_orthogonal_signedDifference hv hu hα hαn hβ hβn hδ hδn hγ hγn
      hαβ hδγ hdiffYX hα1 h1YX
  · exact inner_eq_zero_of_orthogonal_signedDifference hu hv hβ hβn hα hαn hγ hγn hδ hδn
      hβα hγδ hdiffBA h1BA hγδ1
  · exact inner_eq_zero_of_orthogonal_signedDifference hv hu hβ hβn hα hαn hδ hδn hγ hγn
      hβα hδγ hdiffBAYX h1BA h1YX

end SignedIrreducible

end OddOrder.RepresentationTheory


