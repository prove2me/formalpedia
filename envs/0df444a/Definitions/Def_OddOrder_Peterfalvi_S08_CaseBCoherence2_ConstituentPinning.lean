-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBCoherence2_ConstituentPinning
-- name    : OddOrder_Peterfalvi_S08_CaseBCoherence2_ConstituentPinning
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:06:16.65128+00:00
-- url     : https://prove2.me/theorems/aa44c2e3-317f-48e2-a6cc-f3a68e7b70b6
-- title:
--   Peterfalvi §8 case (B): constituent pinning and orthogonality
-- statement:
--   The induction aggregates, integral coefficient bounds and orthogonality lemmas used to pin each case-(B) constituent in Peterfalvi (6.8.2.3).
--
--   Main definition: `constituentWeight` (the (6.8.2.3) weight $a_\theta=\langle\varphi,\mathrm{Res}^M_N\theta\rangle$, the Clifford multiplicity). Results include `tau_sum_smul_image` (aggregate $\tau$-image of integer-weighted constituents) and `aggregate_eq_sum_of_constituent` (the (6.8.2.2) to (6.8.2.3) aggregate builder).
--
--   The bundle also proves 26 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBCoherence2/ConstituentPinning.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBCoherence2/ConstituentPinning.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBTransport

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **Induction commutes with a `ℂ`-linear combination over a `Finset`** (the binary `induce_add` /
`induce_smul` extended to `Ind_H (∑ cᵢ • fᵢ) = ∑ cᵢ • Ind_H fᵢ`). -/
theorem induce_finset_sum_smul {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    [Invertible (Nat.card H : ℂ)] {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → ClassFunction ↥H ℂ) :
    ClassFunction.induce H (∑ i ∈ s, c i • f i)
      = ∑ i ∈ s, c i • ClassFunction.induce H (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [ClassFunction.induce]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.induce_add,
      ClassFunction.induce_smul, ih]

/-- **(6.8.2.3) aggregate, the `∑ aᵢχᵢ = Ind^L_{W₂} φ` half.**  Summing the constituent characters
`χθ = Ind^M_H θ` weighted by the multiplicities `aθ = ⟨φ∘e, Res_{K.subgroupOf H} θ⟩` of the
decomposition `Ind^H_{K.subgroupOf H}(φ∘e) = ∑ aθ·θ` recovers `Ind^M_K φ` in one step:
`∑_θ aθ • Ind^M_H θ = Ind^M_K φ`.  Combine the constituent decomposition
(`induce_eq_sum_inner_restrict_smul`), `ℂ`-linearity of `Ind_H` (`induce_finset_sum_smul`), and
induction in stages (`induce_induce_subgroupOf`). -/
theorem sum_inner_restrict_smul_induce_eq_induce {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {K H : Subgroup M} (hKH : K ≤ H)
    [Finite ↥H] [Finite ↥K] [Fintype ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (φ : ClassFunction ↥K ℂ) :
    ∑ θ : IrreducibleCharacter ↥H,
        ClassFunction.inner
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ)
            (ClassFunction.restrict (K.subgroupOf H) (θ : ClassFunction ↥H ℂ))
          • ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      = ClassFunction.induce K φ := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  rw [← induce_finset_sum_smul, ← induce_eq_sum_inner_restrict_smul]
  exact induce_induce_subgroupOf hKH φ

/-- **Parseval for an induced character** (the `∑ aᵢ² = ‖Ind φ‖²` step of the (6.8.2.3) aggregate).
`‖Ind^M_N φ‖² = ∑_{θ ∈ Irr M} aθ·\overline{aθ}` where `aθ = ⟨φ, Res_N θ⟩` are the constituent
multiplicities: expand `Ind^M_N φ = ∑ aθ·θ` (`induce_eq_sum_inner_restrict_smul`) and use
orthonormality of `Irr M` (`inner_sum_smul_sum` + `irreducibleCharacter_inner_eq_ite`). -/
theorem inner_self_induce_eq_sum_mul_star {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {N : Subgroup M} [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (φ : ClassFunction ↥N ℂ) :
    ClassFunction.inner (ClassFunction.induce N φ) (ClassFunction.induce N φ)
      = ∑ θ : IrreducibleCharacter M,
          ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
          * star (ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))) := by
  rw [induce_eq_sum_inner_restrict_smul φ, OddOrder.Peterfalvi.S05.inner_sum_smul_sum]
  refine Finset.sum_congr rfl (fun θ _ => ?_)
  rw [Finset.sum_eq_single θ]
  · rw [irreducibleCharacter_inner_eq_ite, if_pos rfl, mul_one]
  · intro θ' _ hne
    rw [irreducibleCharacter_inner_eq_ite, if_neg (Ne.symm hne), mul_zero]
  · intro h; exact absurd (Finset.mem_univ θ) h

/-- **(6.8.2.3) aggregate: `∑ aᵢ² = |M : N|`** for a central `N ≤ Z(M)` and an irreducible (linear)
`φ ∈ Irr N`.  The squared constituent multiplicities `aθ = ⟨φ, Res_N θ⟩` sum to the index:
`∑_θ aθ² = ∑_θ aθ·\overline{aθ}` (the `aθ` are integer multiplicities, `inner_mem_ZIrr_int`, hence
real) `= ‖Ind^M_N φ‖²` (`inner_self_induce_eq_sum_mul_star`) `= |M : N|`
(`inner_induce_self_eq_index_of_le_center`).  This is the `∑ aᵢ² = |H : Z|` term of the
Peterfalvi (6.8.2.3) `αᵢ = χᵢ − aᵢη₁` aggregate. -/
theorem sum_inner_restrict_sq_eq_index {M : Type*} [Group M] [Finite M]
    [Invertible (Nat.card M : ℂ)] {N : Subgroup M} [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    (hN : N ≤ Subgroup.center M) {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) :
    ∑ θ : IrreducibleCharacter M,
        ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
          * ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
      = (N.index : ℂ) := by
  have : Fintype M := Fintype.ofFinite M
  have hreal : ∀ θ : IrreducibleCharacter M,
      ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
        = star (ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))) := by
    intro θ
    obtain ⟨m, hm⟩ :=
      ClassFunction.inner_mem_ZIrr_int hφ.mem_ZIrr (ClassFunction.restrict_mem_ZIrr N θ.2.mem_ZIrr)
    rw [hm, star_intCast]
  rw [show (∑ θ : IrreducibleCharacter M,
        ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
          * ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ)))
        = ∑ θ : IrreducibleCharacter M,
          ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
            * star (ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ)))
      from Finset.sum_congr rfl (fun θ _ => by rw [← hreal θ]),
    ← inner_self_induce_eq_sum_mul_star]
  exact inner_induce_self_eq_index_of_le_center hN hφ

/-- **(6.8.2.3) `αᵢ` aggregate** (Peterfalvi (6.8.2.3): `∑ aᵢαᵢ = Ind^L_{W₂} φ − |H:Z|·η₁`).
Summing
the differences `αθ = χθ − aθ·η₁` (`χθ = Ind^M_H θ`, `aθ = ⟨φ∘e, Res_{K.subgroupOf H} θ⟩`) weighted
by
`aθ` recovers `Ind^M_K φ − |H:K|·η₁`.  Mechanical combination of the two aggregate halves:
`∑ aθ·χθ = Ind^M_K φ` (`sum_inner_restrict_smul_induce_eq_induce`) and `∑ aθ² = |H:K|`
(`sum_inner_restrict_sq_eq_index`, the index `|↥H : K.subgroupOf H| = |H:K|`). -/
theorem sum_smul_constituent_diff_eq {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {K H : Subgroup M} (hKH : K ≤ H)
    [Finite ↥H] [Finite ↥K] [Fintype ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (hcen : K.subgroupOf H ≤ Subgroup.center ↥H)
    (φ : ClassFunction ↥K ℂ)
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ))
    (η₁ : ClassFunction M ℂ) :
    ∑ θ : IrreducibleCharacter ↥H,
        ClassFunction.inner
            (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ)
            (ClassFunction.restrict (K.subgroupOf H) (θ : ClassFunction ↥H ℂ))
          • (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
              - ClassFunction.inner
                  (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ)
                  (ClassFunction.restrict (K.subgroupOf H) (θ : ClassFunction ↥H ℂ)) • η₁)
      = ClassFunction.induce K φ - ((K.subgroupOf H).index : ℂ) • η₁ := by
  simp_rw [smul_sub, smul_smul]
  rw [Finset.sum_sub_distrib, sum_inner_restrict_smul_induce_eq_induce, ← Finset.sum_smul,
    sum_inner_restrict_sq_eq_index hcen hφ']

/-- **(6.8.2.3) pinning** (Peterfalvi (6.8.2.3): `bᵢ = aᵢ` for all `i`).  Given nonnegative integer
weights `aᵢ ≥ 0` with `bᵢ ≤ aᵢ` and `∑ aᵢbᵢ = ∑ aᵢ²`, every *positive* weight forces `bᵢ = aᵢ`.

This is the final pinning step of (6.8.2.3): from `∑ aᵢbᵢ = |H:Z| = ∑ aᵢ²` (the index, via
`sum_inner_restrict_sq_eq_index` combined with `(6.8.2.2)` `∑ aᵢαᵢ^τ = X − |H:Z|Y`) and the
per-constituent bound `bᵢ ≤ aᵢ` ((5.4.a) `‖Xᵢ‖² ≥ ‖χᵢ‖²`), the slackness
`∑ aᵢ(aᵢ − bᵢ) = ∑ aᵢ² − ∑ aᵢbᵢ = 0` of nonnegative terms forces each `aᵢ(aᵢ − bᵢ) = 0`, hence
`bᵢ = aᵢ` whenever `aᵢ > 0` (the constituent multiplicities `aᵢ = θᵢ(1) > 0`; the `aᵢ = 0`
non-constituents drop out of the `αᵢ` aggregate). -/
theorem eq_of_sum_mul_eq_sum_sq {ι : Type*} (s : Finset ι) (a b : ι → ℤ)
    (hnonneg : ∀ i ∈ s, 0 ≤ a i) (hab : ∀ i ∈ s, b i ≤ a i)
    (hsum : ∑ i ∈ s, a i * b i = ∑ i ∈ s, a i * a i) :
    ∀ i ∈ s, 0 < a i → b i = a i := by
  have hsum0 : ∑ i ∈ s, a i * (a i - b i) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hnn : ∀ i ∈ s, 0 ≤ a i * (a i - b i) := fun i hi =>
    mul_nonneg (hnonneg i hi) (sub_nonneg.mpr (hab i hi))
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
  intro i hi hpos
  rcases mul_eq_zero.mp (hzero i hi) with h | h
  · exact absurd h (ne_of_gt hpos)
  · linarith [sub_eq_zero.mp h]

/-- **Cauchy–Schwarz against a norm-`1` vector** (integer-coefficient form).  If `⟨u, w⟩ = b ∈ ℤ`
and `‖w‖² = 1`, then `b² ≤ ‖u‖²`.  Pythagoras against the orthogonal split `u = b·w + (u − b·w)`
(the complement `W` is orthogonal to `w`, since `b` is real:
`⟨w, W⟩ = \overline{⟨u, w⟩} − \overline{b}
= 0`), with `‖W‖² ≥ 0` (`inner_self_re_nonneg`).

Specializes (with `u = D.Y`, `w = Y`) to the (6.8.2.3) per-step bound `bᵢ² ≤ ‖D.Y‖²`
(`inner_Y_coeff_le_of_psi_nsmul`), and (with `‖u‖² = 1`) gives the integrality bound `|b| ≤ 1` used
in the orthogonality extraction for the disjointness `R(μ_j) ⊥ Y`. -/
theorem inner_intCast_sq_le {u w : ClassFunction G ℂ}
    (hw : ClassFunction.inner w w = 1)
    {b : ℤ} (hb : ClassFunction.inner u w = (b : ℂ)) :
    (b : ℝ) ^ 2 ≤ (ClassFunction.inner u u).re := by
  set W := u - (b : ℂ) • w with hWdef
  have hwW : ClassFunction.inner w W = 0 := by
    rw [hWdef, ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
      hw, mul_one, OddOrder.RepresentationTheory.inner_conj_symm u w, hb, star_intCast,
      sub_self]
  have hWw : ClassFunction.inner W w = 0 := by
    rw [hWdef, ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hb, hw, mul_one,
      sub_self]
  have hexpand : ClassFunction.inner u u = (b : ℂ) * (b : ℂ) + ClassFunction.inner W W := by
    conv_lhs => rw [show u = (b : ℂ) • w + W by rw [hWdef]; abel]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, hw, hwW,
      hWw, mul_one, mul_zero, star_intCast, add_zero, zero_add]
  rw [hexpand, Complex.add_re,
    show ((b : ℂ) * (b : ℂ)).re = (b : ℝ) ^ 2 by
      rw [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]; ring]
  have := inner_self_re_nonneg W
  linarith

/-- **Per-step coefficient bound `bᵢ ≤ aᵢ`** (Peterfalvi (6.8.2.3), the integer tail of the
Cauchy–Schwarz step).  For a (5.4) decomposition `Da : CharacterPsiDecomposition τ χ (a·η)` with
`η` a norm-`1` vector and `Y` a norm-`1` vector, the integer coefficient `b = ⟨Da.Y, Y⟩` is bounded
by the multiplicity `a`.

Chaining `inner_intCast_sq_le` (`b² ≤ ‖Da.Y‖²`) with the (5.6.2) opening bound
`inner_self_Y_re_le_inner_self_psi` (`‖Da.Y‖² ≤ ‖a·η‖² = a²`) gives `b² ≤ a²` over `ℤ`; with
`a ≥ 0` the integer tail `b² ≤ a² ∧ 0 ≤ a ⟹ b ≤ a` finishes.  This is the per-constituent input to
the (6.8.2.3) pinning `eq_of_sum_mul_eq_sum_sq`. -/
theorem inner_Y_coeff_le_of_psi_nsmul {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {χ η : ClassFunction ↥L ℂ} {a : ℕ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ (a • η))
    (hηnorm : ClassFunction.inner η η = 1)
    {Y : ClassFunction G ℂ} (hYnorm : ClassFunction.inner Y Y = 1)
    {b : ℤ} (hb : ClassFunction.inner D.Y Y = (b : ℂ)) :
    b ≤ (a : ℤ) := by
  -- `‖ψ‖² = ‖a·η‖² = a²` (`η` norm `1`).
  have hψnorm : (ClassFunction.inner (a • η : ClassFunction ↥L ℂ) (a • η)).re = (a : ℝ) ^ 2 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a η, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hηnorm, mul_one, star_natCast,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  -- `b² ≤ ‖Da.Y‖² ≤ ‖ψ‖² = a²`, over `ℝ` then `ℤ`.
  have hsq := inner_intCast_sq_le hYnorm hb
  have hYle := D.inner_self_Y_re_le_inner_self_psi
  rw [hψnorm] at hYle
  have hb2z : b ^ 2 ≤ (a : ℤ) ^ 2 := by exact_mod_cast le_trans hsq hYle
  -- Integer tail: `b² ≤ a² ∧ 0 ≤ a ⟹ b ≤ a`.
  by_contra hcon
  push Not at hcon
  have ha : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg a
  nlinarith [mul_nonneg ha (le_of_lt (sub_pos.mpr hcon)),
    mul_pos (lt_of_le_of_lt ha hcon) (sub_pos.mpr hcon), hb2z]

/-- **(6.8.2.3) pinning input `∑ aᵢbᵢ = n`.**  Taking the inner product against the `Y`-anchor of
the (6.8.2.2) aggregate identity `Xagg − n·Y = ∑ᵢ aᵢ·(Xᵢ − Yᵢ)` (each `αᵢ^τ = Xᵢ − Yᵢ` a
per-constituent (5.4) image, `bᵢ = ⟨Yᵢ, Y⟩`): the `X`-sides are orthogonal to `Y`
(`⟨Xagg,Y⟩ = 0`, `⟨Xᵢ,Y⟩ = 0`), so `⟨LHS,Y⟩ = −n` and `⟨RHS,Y⟩ = −∑ aᵢbᵢ`, forcing `∑ aᵢbᵢ = n`.
With `∑ aᵢ² = |H:Z| = n` (`sum_inner_restrict_sq_eq_index`) and the per-step bound `bᵢ ≤ aᵢ`
(`inner_Y_coeff_le_of_psi_nsmul`), this is the `hsum` input to the pinning
`eq_of_sum_mul_eq_sum_sq`. -/
theorem sum_coeff_eq_of_aggregate {ι : Type*} (s : Finset ι) (a b : ι → ℤ)
    (X Yv : ι → ClassFunction G ℂ) (Xagg Y : ClassFunction G ℂ) (n : ℤ)
    (hagg : Xagg - (n : ℂ) • Y = ∑ i ∈ s, (a i : ℂ) • (X i - Yv i))
    (hXorth : ∀ i ∈ s, ClassFunction.inner (X i) Y = 0)
    (hb : ∀ i ∈ s, ClassFunction.inner (Yv i) Y = (b i : ℂ))
    (hXaggorth : ClassFunction.inner Xagg Y = 0)
    (hYY : ClassFunction.inner Y Y = 1) :
    ∑ i ∈ s, a i * b i = n := by
  have key : ClassFunction.inner (Xagg - (n : ℂ) • Y) Y
      = ClassFunction.inner (∑ i ∈ s, (a i : ℂ) • (X i - Yv i)) Y := by rw [hagg]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, hXaggorth, hYY, mul_one,
    zero_sub, inner_sum_left] at key
  -- `⟨LHS,Y⟩ = −n`; each `RHS` term `⟨aᵢ•(Xᵢ−Yᵢ), Y⟩ = −aᵢbᵢ`.
  have hterm : ∑ i ∈ s, ClassFunction.inner ((a i : ℂ) • (X i - Yv i)) Y
      = ∑ i ∈ s, -((a i : ℂ) * (b i : ℂ)) :=
    Finset.sum_congr rfl fun i hi => by
      rw [ClassFunction.inner_smul_left, ClassFunction.inner_sub_left, hXorth i hi, hb i hi]; ring
  rw [hterm, Finset.sum_neg_distrib] at key
  -- `key : −n = −∑ aᵢbᵢ` over `ℂ`; cancel the sign and descend to `ℤ`.
  have hcast : (n : ℂ) = ∑ i ∈ s, (a i : ℂ) * (b i : ℂ) := neg_injective key
  exact_mod_cast hcast.symm

/-- **Cauchy–Schwarz equality ⟹ parallel** (the (6.8.2.3) `Yᵢ = aᵢ·Y` bridge).  For a norm-`1`
vector `w`, an integer `a`, and a vector `v` with `⟨v, w⟩ = a` and `‖v‖² = a²`, the equality case of
Cauchy–Schwarz forces `v = a·w`: indeed `‖v − a·w‖² = ‖v‖² − a⟨v,w⟩ − a⟨w,v⟩ + a²‖w‖² = 0`, so the
positive-definiteness `eq_zero_of_inner_self_re_eq_zero` gives `v − a·w = 0`.

This is the bridge from the (6.8.2.3) pinning `bᵢ = ⟨Yᵢ,Y⟩ = aᵢ` together with
`‖Yᵢ‖² = ‖aᵢ·η₁‖² = aᵢ²`
((5.4.b)) to the per-step image `Yᵢ = aᵢ·Y`, which then assembles the per-`χ` identity
`(χ − a·η₁)^τ = X₁ − a·Y`. -/
theorem eq_smul_of_inner_self_eq {v w : ClassFunction G ℂ} {a : ℤ}
    (hvw : ClassFunction.inner v w = (a : ℂ))
    (hvv : ClassFunction.inner v v = (a : ℂ) ^ 2)
    (hww : ClassFunction.inner w w = 1) :
    v = (a : ℂ) • w := by
  have hnorm : ClassFunction.inner (v - (a : ℂ) • w) (v - (a : ℂ) • w) = 0 := by
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_conj_symm v w, hvw, hvv, hww, star_intCast]
    ring
  have hre : (ClassFunction.inner (v - (a : ℂ) • w) (v - (a : ℂ) • w)).re = 0 := by
    rw [hnorm]; simp
  exact sub_eq_zero.mp (eq_zero_of_inner_self_re_eq_zero hre)

omit [Fintype G] in
omit [Invertible (Nat.card G : ℂ)] in
/-- **Aggregate τ-image of integer-weighted constituents** (the (6.8.2.2)→(6.8.2.3) bridge).  For a
`ℤ`-linear character map `τ` and per-constituent images `τ(αᵢ) = Xᵢ − Yᵢ`, the integer-weighted
aggregate maps termwise: `τ(∑ᵢ aᵢ·αᵢ) = ∑ᵢ aᵢ·(Xᵢ − Yᵢ)`.  Pure `ℤ`-linearity (`map_sum` +
`map_zsmul`, with the `(aᵢ : ℂ)`-scalar smul reduced to the `ℤ`-action via
`Int.cast_smul_eq_zsmul`).

Combined with `sum_smul_constituent_diff_eq` (`∑ aᵢ·αᵢ = Ind^L_{W₂}φ − |H:Z|·η₁`) and the (6.8.2.2)
decomposition `exists_decomposition_caseB` (`τ(Ind φ − |H:Z|·η₁) = Xagg − |H:Z|·Y`), this supplies
the
`hagg` input `Xagg − n·Y = ∑ᵢ aᵢ·(Xᵢ − Yᵢ)` of the pinning lemma `sum_coeff_eq_of_aggregate`. -/
theorem tau_sum_smul_image {L : Subgroup G} [Finite ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {ι : Type*} (s : Finset ι) (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G)
    (α : ι → ClassFunction ↥L ℂ) (Xv Yv : ι → ClassFunction G ℂ) (a : ι → ℤ)
    (himg : ∀ i ∈ s, τ (α i) = Xv i - Yv i) :
    τ (∑ i ∈ s, (a i : ℂ) • α i) = ∑ i ∈ s, (a i : ℂ) • (Xv i - Yv i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Int.cast_smul_eq_zsmul ℂ (a i) (α i), map_zsmul, himg i hi,
    ← Int.cast_smul_eq_zsmul ℂ (a i) (Xv i - Yv i)]

omit [Fintype G] in
omit [Invertible (Nat.card G : ℂ)] in
/-- **(6.8.2.2)→(6.8.2.3) aggregate `hagg` builder.**  Assembles the `hagg` input of
`per_constituent_Y_eq_smul` from the three (6.8.2.2) pieces: the image decomposition
`τ β = Xagg − n·Y` (`exists_decomposition_caseB`, `β = Ind^L_{W₂}φ − |H:Z|·η₁`, `n = |H:Z|`), the
constituent sum `β = ∑ aᵢ·αᵢ` (`sum_smul_constituent_diff_eq`), and the per-constituent images
`τ(αᵢ) = Xᵢ − Yᵢ` (each `CharacterPsiDecomposition.tau1_image`, with `τ₁ = τ` for the certain-type
`certainTypeDecompositionDa`).  Rewriting `Xagg − n·Y = τ β = τ(∑ aᵢαᵢ) = ∑ aᵢ(Xᵢ − Yᵢ)` via
`tau_sum_smul_image` gives the aggregate `Xagg − n·Y = ∑ aᵢ·(Xᵢ − Yᵢ)`. -/
theorem aggregate_eq_sum_of_constituent {L : Subgroup G} [Finite ↥L]
    [Invertible (Nat.card ↥L : ℂ)]
    {ι : Type*} (s : Finset ι) (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G)
    (α : ι → ClassFunction ↥L ℂ) (Xv Yv : ι → ClassFunction G ℂ) (a : ι → ℤ)
    {β : ClassFunction ↥L ℂ} {Xagg Y : ClassFunction G ℂ} {n : ℤ}
    (hmemimg : ∀ i ∈ s, τ (α i) = Xv i - Yv i)
    (hconstit : β = ∑ i ∈ s, (a i : ℂ) • α i)
    (hdecomp : τ β = Xagg - (n : ℂ) • Y) :
    Xagg - (n : ℂ) • Y = ∑ i ∈ s, (a i : ℂ) • (Xv i - Yv i) := by
  rw [← hdecomp, hconstit]
  exact tau_sum_smul_image s τ α Xv Yv a hmemimg

/-- **Reindex a finite sum to the positive-weight subtype.**  Terms with zero weight (`a i = 0`)
drop out, so a sum over all of `ι` equals the sum over the subtype `{i // 0 < a i}`.

This restricts the (6.8.2.3) constituent aggregate — indexed by *all* of `Irr H`, with the
zero-multiplicity constituents `Ind^L_H θ` (`aθ = ⟨φ, Res_{W₂}θ⟩ = 0`) contributing nothing — to the
positive-multiplicity constituents `{θ // 0 < aθ}`.  The restriction is forced: `Ind^L_H θ` has
degree `≠ 0`, so it is *not* `H^#`-supported and admits **no** `CharacterPsiDecomposition` with the
zero anchor `0 • η₁`; the per-`φ` decomposition family can only be defined on the positive-weight
subtype. -/
theorem sum_eq_sum_pos_weight_subtype {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (a : ι → ℕ) (f : ι → M) (hf : ∀ i, a i = 0 → f i = 0) :
    ∑ i : ι, f i = ∑ i : {i : ι // 0 < a i}, f i.val := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i => 0 < a i)) (fun x => by simp) f]
  exact (Finset.sum_filter_of_ne
    (fun i _ hne => Nat.pos_of_ne_zero (fun h0 => hne (hf i h0)))).symm

/-- **(6.8.2.3) constituent weight as a natural number.**  For an irreducible `φ` of a subgroup
`N ≤ M` and an irreducible character `θ` of `M`, the multiplicity `⟨φ, Res^M_N θ⟩` is a natural
number (Clifford [Is] Thm 6.5, `restrictionMultiplicity_natCast`): a nonnegative integer, repackaged
for the `φ`-first inner-product slot used by the (6.8.2.3) constituent aggregate
`sum_smul_constituent_diff_eq` (which weights `αθ = Ind^M_H θ − aθ·η₁` by `aθ = ⟨φ, Res θ⟩`). This
is
the source of the natural-number weight `a : ι → ℕ` consumed by the pinning
`per_constituent_Y_eq_smul`. -/
theorem exists_inner_restrict_natCast {M : Type*} [Group M] [Finite M] {N : Subgroup M}
    [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) (θ : IrreducibleCharacter M) :
    ∃ k : ℕ, ClassFunction.inner φ
      (ClassFunction.restrict N (θ : ClassFunction M ℂ)) = (k : ℂ) := by
  obtain ⟨k, hk⟩ := ClassFunction.restrictionMultiplicity_natCast N θ.2 hφ
  exact ⟨k, by rw [OddOrder.RepresentationTheory.inner_conj_symm,
    ← ClassFunction.restrictionMultiplicity_def, hk, star_natCast]⟩

/-- **(6.8.2.3) constituent weight** `aθ = ⟨φ, Res^M_N θ⟩ : ℕ` (the Clifford multiplicity of `φ`
in `Res^M_N θ`).  The natural-number weight indexing the (6.8.2.3) `αθ`-aggregate and consumed by
the pinning `per_constituent_Y_eq_smul`.  The defining `ℂ`-equation is `constituentWeight_spec`. -/
noncomputable def constituentWeight {M : Type*} [Group M] [Finite M] {N : Subgroup M}
    [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) (θ : IrreducibleCharacter M) : ℕ :=
  (exists_inner_restrict_natCast hφ θ).choose

/-- The defining equation of `constituentWeight`: `⟨φ, Res^M_N θ⟩ = (aθ : ℂ)`. -/
theorem constituentWeight_spec {M : Type*} [Group M] [Finite M] {N : Subgroup M}
    [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) (θ : IrreducibleCharacter M) :
    ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ))
      = (constituentWeight hφ θ : ℂ) :=
  (exists_inner_restrict_natCast hφ θ).choose_spec

/-- A constituent has positive weight iff `φ` actually occurs in `Res^M_N θ` (i.e. `θ` "lies over"
`φ`).  This is the membership test for the positive-weight subtype `{θ // 0 < aθ}` (the per-`φ`
decomposition family index, `sum_eq_sum_pos_weight_subtype`). -/
theorem constituentWeight_pos_iff {M : Type*} [Group M] [Finite M] {N : Subgroup M}
    [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    {φ : ClassFunction ↥N ℂ} (hφ : IsIrreducibleCharacter φ) (θ : IrreducibleCharacter M) :
    0 < constituentWeight hφ θ ↔
      ClassFunction.inner φ (ClassFunction.restrict N (θ : ClassFunction M ℂ)) ≠ 0 := by
  rw [constituentWeight_spec hφ θ, ne_eq, Nat.cast_eq_zero, ← ne_eq, ← Nat.pos_iff_ne_zero]

/-- **(6.8.2.3) constituent aggregate over the positive-weight subtype.**  The `αθ`-aggregate
`sum_smul_constituent_diff_eq` (indexed by all of `Irr H`, with weight `aθ = ⟨φ, Res θ⟩` written as
the `ℂ`-valued multiplicity) reindexed to the positive-weight subtype `{θ // 0 < aθ}` with the
weight
in natural-number form `constituentWeight`:
`Ind^M_K φ − |H:K|·η₁ = ∑_{θ : 0 < aθ} aθ·(Ind^M_H θ − aθ·η₁)`.

This is the `hconstit` source aggregate for the per-`φ` pinning: the index matches the per-`φ`
decomposition family `{θ // 0 < aθ}`, and the weight is the `ℕ` consumed by
`per_constituent_Y_eq_smul` (the `ℂ`-coefficient `⟨φ, Res θ⟩` is `(constituentWeight … : ℂ)` by
`constituentWeight_spec`; the `aθ = 0` constituents drop out by `sum_eq_sum_pos_weight_subtype`). -/
theorem sum_smul_constituent_diff_pos_weight_subtype {M : Type*} [Group M] [Fintype M]
    [Invertible (Nat.card M : ℂ)] {K H : Subgroup M} (hKH : K ≤ H)
    [Finite ↥H] [Finite ↥K] [Fintype ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (hcen : K.subgroupOf H ≤ Subgroup.center ↥H)
    (φ : ClassFunction ↥K ℂ)
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ))
    (η₁ : ClassFunction M ℂ) :
    ClassFunction.induce K φ - ((K.subgroupOf H).index : ℂ) • η₁
      = ∑ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
          (constituentWeight hφ' i.val : ℂ) •
            (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
              - (constituentWeight hφ' i.val : ℂ) • η₁) := by
  rw [← sum_smul_constituent_diff_eq hKH hcen φ hφ' η₁]
  simp only [constituentWeight_spec hφ']
  exact sum_eq_sum_pos_weight_subtype (constituentWeight hφ')
    (fun θ => (constituentWeight hφ' θ : ℂ) • (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      - (constituentWeight hφ' θ : ℂ) • η₁)) (fun θ hθ => by
        simp only [hθ, Nat.cast_zero, zero_smul])

/-- **(6.8.2.3) per-constituent pinned image `Yᵢ = aᵢ·Y`.**  The capstone of the (6.8.2.3) per-step
bound + pinning + Cauchy–Schwarz-equality bridge, packaging the whole `pinning → image` algebra so
the
case-(B) instantiation need only discharge the named structural hypotheses.

For per-constituent (5.4) decompositions `Dᵢ : CharacterPsiDecomposition τ χᵢ (aᵢ·η)` (the `χᵢ` the
constituents of `Ind^L_{W₂}φ`, `η` the norm-`1` `Y`-anchor at source), given:
* the (6.8.2.2) aggregate `Xagg − n·Y = ∑ᵢ aᵢ·(Dᵢ.X − Dᵢ.Y)` (`tau_sum_smul_image` +
  `sum_smul_constituent_diff_eq` + `exists_decomposition_caseB`), `∑ aᵢ² = n` (`= |H:Z|`,
  `sum_inner_restrict_sq_eq_index`), and `‖Y‖² = 1`;
* the orthogonalities `⟨Dᵢ.X, Y⟩ = 0` (`inner_decomposition_X_extension_member_eq_zero`),
  `⟨Xagg, Y⟩ = 0`, and the integrality `⟨Dᵢ.Y, Y⟩ = bᵢ ∈ ℤ`;
the pinning `∑ aᵢbᵢ = n = ∑ aᵢ²` (`sum_coeff_eq_of_aggregate`) with the per-step bound `bᵢ ≤ aᵢ`
(`inner_Y_coeff_le_of_psi_nsmul`) forces `bᵢ = aᵢ` (`eq_of_sum_mul_eq_sum_sq`), whence
`aᵢ² = bᵢ² ≤ ‖Dᵢ.Y‖² ≤ ‖aᵢ·η‖² = aᵢ²` gives `‖Dᵢ.Y‖² = aᵢ²` and the Cauchy–Schwarz equality
`eq_smul_of_inner_self_eq` yields `Dᵢ.Y = aᵢ·Y`. -/
theorem per_constituent_Y_eq_smul {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {ι : Type*} (s : Finset ι) {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    {χ : ι → ClassFunction ↥L ℂ} {η : ClassFunction ↥L ℂ} {a : ι → ℕ}
    (D : (i : ι) → OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ (χ i) (a i • η))
    {Y Xagg : ClassFunction G ℂ} {b : ι → ℤ} {n : ℤ}
    (hηnorm : ClassFunction.inner η η = 1)
    (hYY : ClassFunction.inner Y Y = 1)
    (hXaggorth : ClassFunction.inner Xagg Y = 0)
    (hagg : Xagg - (n : ℂ) • Y = ∑ i ∈ s, ((a i : ℤ) : ℂ) • ((D i).X - (D i).Y))
    (hsq : ∑ i ∈ s, ((a i : ℤ)) ^ 2 = n)
    (hXorth : ∀ i ∈ s, ClassFunction.inner (D i).X Y = 0)
    (hbi : ∀ i ∈ s, ClassFunction.inner (D i).Y Y = (b i : ℂ))
    (i : ι) (hi : i ∈ s) (hpos : 0 < a i) :
    (D i).Y = (a i : ℂ) • Y := by
  -- Pinning: `∑ aᵢbᵢ = n = ∑ aᵢ²`, with `bᵢ ≤ aᵢ` and `aᵢ ≥ 0`, forces `bᵢ = aᵢ`.
  have hsumab : ∑ j ∈ s, (a j : ℤ) * b j = n :=
    sum_coeff_eq_of_aggregate s (fun j => (a j : ℤ)) b (fun j => (D j).X) (fun j => (D j).Y)
      Xagg Y n hagg hXorth hbi hXaggorth hYY
  have hbound : ∀ j ∈ s, b j ≤ (a j : ℤ) := fun j hj =>
    inner_Y_coeff_le_of_psi_nsmul (D j) hηnorm hYY (hbi j hj)
  have hsumeq : ∑ j ∈ s, (a j : ℤ) * b j = ∑ j ∈ s, (a j : ℤ) * (a j : ℤ) := by
    rw [hsumab, ← hsq]; exact Finset.sum_congr rfl fun j _ => pow_two (a j : ℤ)
  have hbeq : b i = (a i : ℤ) :=
    eq_of_sum_mul_eq_sum_sq s (fun j => (a j : ℤ)) b (fun j _ => Int.natCast_nonneg (a j))
      hbound hsumeq i hi (show (0 : ℤ) < ((a i : ℕ) : ℤ) by exact_mod_cast hpos)
  -- `‖Dᵢ.Y‖² = aᵢ²`:  `aᵢ² = bᵢ² ≤ ‖Dᵢ.Y‖² ≤ ‖aᵢ·η‖² = aᵢ²`.
  have hCS := inner_intCast_sq_le hYY (hbi i hi)
  have h562 := (D i).inner_self_Y_re_le_inner_self_psi
  have hψnorm : (ClassFunction.inner (a i • η : ClassFunction ↥L ℂ) (a i • η)).re
      = (a i : ℝ) ^ 2 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ (a i) η, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hηnorm, mul_one, star_natCast,
      Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    ring
  rw [hψnorm] at h562
  have hYinorm_re : (ClassFunction.inner (D i).Y (D i).Y).re = (a i : ℝ) ^ 2 := by
    have hba : (b i : ℝ) = (a i : ℝ) := by exact_mod_cast hbeq
    rw [hba] at hCS; linarith
  -- Realness `⟨Dᵢ.Y, Dᵢ.Y⟩ = ((⟨Dᵢ.Y,Dᵢ.Y⟩).re : ℂ)` upgrades the `.re` to a `ℂ`-equation.
  have hreal : ClassFunction.inner (D i).Y (D i).Y
      = ((ClassFunction.inner (D i).Y (D i).Y).re : ℂ) := by
    rw [inner_self_eq_realCast, Complex.ofReal_re]
  -- Cauchy–Schwarz equality `Dᵢ.Y = aᵢ·Y` (via the `ℤ`-cast scalar, then `Int.cast_natCast`).
  have key := eq_smul_of_inner_self_eq (v := (D i).Y) (w := Y) (a := (a i : ℤ))
    (by rw [hbi i hi]; exact_mod_cast hbeq)
    (by rw [hreal, hYinorm_re]; push_cast; ring) hYY
  rwa [Int.cast_natCast] at key

/-- **Seam-1 orthogonality `⟨Dᵢ.X, Y⟩ = 0`** (Peterfalvi (6.8.2.3): "`R(χᵢ)` is orthogonal to
`Y^{τ₁}` by (5.3) and (5.5)").  Since `Dᵢ.X ∈ ℤ[R(χᵢ)]`, orthogonality of `Y` to the image family
`R(χᵢ)` (the `(5.3)/(5.5)` disjointness, supplied at the case-(B) instantiation — e.g. `Y = ε·ξ` for
an irreducible `ξ ∉ R(χᵢ)` via `coherentYset_extension_eq_zsmul_irreducible`) propagates to `Dᵢ.X`
(`inner_X_eq_zero_of_orthogonal_imageSet`), and conjugate symmetry flips the slot.

This is the `hXorth` input of `per_constituent_Y_eq_smul`. -/
theorem inner_X_Y_eq_zero_of_orthogonal {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {χ ψ : ClassFunction ↥L ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ) {Y : ClassFunction G ℂ}
    (hY : ∀ α ∈ D.imageFamily.imageSet, ClassFunction.inner Y α = 0) :
    ClassFunction.inner D.X Y = 0 := by
  rw [OddOrder.RepresentationTheory.inner_conj_symm Y D.X,
    D.inner_X_eq_zero_of_orthogonal_imageSet hY, star_zero]

/-- **Orthogonality extraction from a two-irreducible difference** (the (6.8.2.3) disjointness
core).  If `ξ`, `ξ'` are orthonormal (`‖ξ‖² = 1`, `⟨ξ, ξ'⟩ = 0`), `θ` is a norm-`1` vector with
`⟨ξ, θ⟩ ∈ ℤ`, and `c·ξ − c'·ξ' ⊥ θ` for `c ≠ 0`, then `⟨ξ, θ⟩ = 0`.

This is the extraction step of the disjointness `R(μ_j) ⊥ Y`: writing `Y = ε·ξ` (`ξ` the `Y`-anchor
irreducible image, `coherentYset_extension_eq_zsmul_irreducible`) so that
`(η₁ − η̄₁)^τ = ε·ξ − ε'·ξ'` is orthogonal to every `σ`-image `θ = ω^σ` (by (3.8) /
`grid_eq_zero_of_ncard_support_lt`, since `NC ≤ 2 < min(w₁, w₂)`), the integrality bound
`|⟨ξ, θ⟩| ≤ 1` (`inner_intCast_sq_le`) forces `⟨ξ, θ⟩ = 0`: otherwise `⟨ξ, θ⟩ = ±1` makes
`ξ = ±θ` (Cauchy–Schwarz equality `eq_smul_of_inner_self_eq`), so `⟨ξ', θ⟩ = 0` (from `⟨ξ, ξ'⟩ = 0`)
and the orthogonality collapses to `c·⟨ξ, θ⟩ = 0`, contradicting `c ≠ 0`. -/
theorem inner_eq_zero_of_smul_sub_smul_orthogonal {ξ ξ' θ : ClassFunction G ℂ}
    (hξ : ClassFunction.inner ξ ξ = 1) (hθ : ClassFunction.inner θ θ = 1)
    (hξξ' : ClassFunction.inner ξ ξ' = 0)
    {m : ℤ} (hm : ClassFunction.inner ξ θ = (m : ℂ))
    {c c' : ℂ} (hc : c ≠ 0)
    (horth : ClassFunction.inner (c • ξ - c' • ξ') θ = 0) :
    ClassFunction.inner ξ θ = 0 := by
  rw [hm]
  by_contra hne
  have hmne : m ≠ 0 := fun h => hne (by rw [h]; simp)
  -- `|m| ≤ 1` from the norm-`1` Cauchy–Schwarz bound, hence `m = ±1`.
  have hmsqz : m ^ 2 ≤ 1 := by
    have h := inner_intCast_sq_le hθ hm
    rw [hξ, Complex.one_re] at h
    exact_mod_cast h
  have hlo : -1 ≤ m := by nlinarith [sq_nonneg (m + 1)]
  have hhi : m ≤ 1 := by nlinarith [sq_nonneg (m - 1)]
  have hmsq1 : (m : ℂ) ^ 2 = 1 := by interval_cases m <;> simp_all
  -- `‖ξ‖² = (m:ℂ)²`, so `ξ = (m:ℂ)·θ` by the equality case of Cauchy–Schwarz.
  have hξeq : ξ = (m : ℂ) • θ := eq_smul_of_inner_self_eq hm (by rw [hξ, hmsq1]) hθ
  -- `⟨ξ, ξ'⟩ = (m:ℂ)·⟨θ, ξ'⟩ = 0` with `(m:ℂ) ≠ 0` ⟹ `⟨ξ', θ⟩ = 0`.
  rw [hξeq, ClassFunction.inner_smul_left] at hξξ'
  have hξ'θ : ClassFunction.inner ξ' θ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm θ ξ',
      (mul_eq_zero.mp hξξ').resolve_left hne, star_zero]
  -- `horth` collapses to `c·(m:ℂ) = 0`, contradicting `c ≠ 0`, `(m:ℂ) ≠ 0`.
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    hξ'θ, mul_zero, sub_zero, hm] at horth
  exact (mul_ne_zero hc hne) horth

/-- **`σ`-coefficient vanishing from a small support** (the (3.2.d)/(3.8) "all coefficients zero"
case, via `grid_eq_zero_of_ncard_support_lt`).  For `ψ` vanishing on `V` with `NC(ψ) < min(w₁, w₂)`,
every `σ`-image coefficient `sigmaCoeff ψ = ⟨ψ, ω^σ⟩` vanishes: the (3.7) additive identity
`sigmaCoeff_add_eq` (from `ψ` vanishing on `V`) makes the coefficient grid additively separable, so
a
support smaller than `min(w₁, w₂)` forces it identically zero.

This is the (6.8.2.3) disjointness driver: applied to `ψ = (η₁ − η̄₁)^τ` (vanishing on `V` since
`η₁ − η̄₁` is `A`-supported, with `NC ≤ 2 < min(w₁, w₂)` as a difference of two irreducibles), it
gives `(η₁ − η̄₁)^τ ⊥ Im σ`, feeding the extraction `inner_eq_zero_of_smul_sub_smul_orthogonal`.
The simpler `grid_eq_zero_of_ncard_support_lt` (no `w₁ + 2 ≤ w₂` gap) suffices here, unlike the full
trichotomy `sigmaCoeff_trichotomy`. -/
theorem sigmaCoeff_eq_zero_of_vanishOnV_of_ncard_lt
    (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff)
    (app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication hyp)
    {ψ : ClassFunction G ℂ} (hψ : ∀ v ∈ hyp.V, ψ v = 0)
    (hNC : hyp.sigmaNC hVeq app ψ < min (Nat.card hyp.W1) (Nat.card hyp.W2))
    (pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    hyp.sigmaCoeff hVeq app ψ pq = 0 := by
  refine OddOrder.Peterfalvi.S05.grid_eq_zero_of_ncard_support_lt
    (fun pq => hyp.sigmaCoeff hVeq app ψ pq)
    (fun p p' q q' => hyp.sigmaCoeff_add_eq hVeq app hψ p p' q q') ?_ pq
  rw [hyp.card_charGroup_subgroupOf hyp.W1_le_W, hyp.card_charGroup_subgroupOf hyp.W2_le_W]
  exact hNC

/-- **`NC ≤ 2` for a two-irreducible difference** (the (6.8.2.3) `NC((η₁ − η̄₁)^τ) ≤ 2` bound).  If
every nonzero `σ`-coefficient of `ψ` forces a nonzero inner product with one of two norm-`1` virtual
characters `ξ`, `ξ' ∈ ±Irr(G)` (the case `ψ = c·ξ − c'·ξ'`), then `NC(ψ) ≤ 2`: by (3.9)(a)
(`ncard_inner_chiFam_ne_zero_le_one`) each of `ξ`, `ξ'` has at most one nonzero `σ`-coefficient, and
the support of `ψ` lies in their union.  With `min(w₁, w₂) ≥ 3` (odd-order Hall), this feeds the
`grid_eq_zero` driver `sigmaCoeff_eq_zero_of_vanishOnV_of_ncard_lt`. -/
theorem sigmaNC_le_two_of_inner_chiFam
    (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff)
    (app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication hyp)
    {ξ ξ' : ClassFunction G ℂ} (hξZ : ξ ∈ ZIrr G) (hξ1 : ClassFunction.inner ξ ξ = 1)
    (hξ'Z : ξ' ∈ ZIrr G) (hξ'1 : ClassFunction.inner ξ' ξ' = 1)
    {ψ : ClassFunction G ℂ}
    (hψsupp : ∀ pq, hyp.sigmaCoeff hVeq app ψ pq ≠ 0 →
      ClassFunction.inner ξ (hyp.chiFam hVeq app pq) ≠ 0 ∨
        ClassFunction.inner ξ' (hyp.chiFam hVeq app pq) ≠ 0) :
    hyp.sigmaNC hVeq app ψ ≤ 2 := by
  classical
  have : Finite G := Finite.of_fintype G
  have hsub : {pq | hyp.sigmaCoeff hVeq app ψ pq ≠ 0} ⊆
      {pq | ClassFunction.inner ξ (hyp.chiFam hVeq app pq) ≠ 0} ∪
        {pq | ClassFunction.inner ξ' (hyp.chiFam hVeq app pq) ≠ 0} :=
    fun pq hpq => hψsupp pq hpq
  calc hyp.sigmaNC hVeq app ψ
      = {pq | hyp.sigmaCoeff hVeq app ψ pq ≠ 0}.ncard := rfl
    _ ≤ ({pq | ClassFunction.inner ξ (hyp.chiFam hVeq app pq) ≠ 0} ∪
          {pq | ClassFunction.inner ξ' (hyp.chiFam hVeq app pq) ≠ 0}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ {pq | ClassFunction.inner ξ (hyp.chiFam hVeq app pq) ≠ 0}.ncard +
          {pq | ClassFunction.inner ξ' (hyp.chiFam hVeq app pq) ≠ 0}.ncard := Set.ncard_union_le _ _
    _ ≤ 1 + 1 := by
        gcongr
        · exact OddOrder.Peterfalvi.S05.TICyclicHypothesis.ncard_inner_chiFam_ne_zero_le_one
            hyp hVeq app hξZ hξ1
        · exact OddOrder.Peterfalvi.S05.TICyclicHypothesis.ncard_inner_chiFam_ne_zero_le_one
            hyp hVeq app hξ'Z hξ'1
    _ = 2 := rfl

/-- **(6.8.2.3) anchor, group-theoretic core: `V` avoids the `G`-conjugates of `K`-elements.**
A point `v` of the `(ticVdiff h)`-exceptional set `V = W − (W₁ ∪ W₂)` is never `G`-conjugate to an
element of the kernel `K = h.K` (viewed in `G` via `L ↪ G`).

Indeed, write `v = ↑w` with `w = x·y ∈ W₁ × W₂` (`exists_mul_of_mem_sup`); since `v ∉ W₂` the
`W₁`-component `x ≠ 1`, and `x = w ^ n` (`exists_zpow_proj`) gives
`orderOf x ∣ orderOf w = orderOf v`.
If `v` were `G`-conjugate to `↑k` (`k ∈ K`) then `orderOf v = orderOf k ∣ |K|` (conjugation
preserves
order), so `orderOf x ∣ gcd(|K|, |W₁|) = 1` (`card_coprime`), forcing `x = 1` — a contradiction.

This is the structural disjointness `V ∩ (K^#)^G = ∅` powering the anchor: since
`Supp(η₁ − η̄₁) ⊆ H^# ⊆ K^#` and `(η₁ − η̄₁)^τ` is a Dade image (vanishing off
`conjugatesOfSet H^#`),
it vanishes on `V`. -/
theorem ticVdiffV_not_mem_conjugatesOfSet_K {A : Set G}
    (h : OddOrder.Peterfalvi.S06.Hypothesis46 A L) {v : G}
    (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h).V) :
    v ∉ Group.conjugatesOfSet ((h.K.map L.subtype : Subgroup G) : Set G) := by
  intro hconj
  -- `v` is `G`-conjugate to `a = ↑k` with `k ∈ K`
  obtain ⟨a, haK, hav⟩ := Group.mem_conjugatesOfSet_iff.mp hconj
  obtain ⟨k, hkK, hka⟩ := Subgroup.mem_map.mp haK
  -- `orderOf a = orderOf v` (conjugation preserves order)
  obtain ⟨c, hc⟩ := isConj_iff.mp hav
  have hsemi : SemiconjBy c a v := by
    change c * a = v * c
    rw [← hc]; group
  have hav_ord : orderOf a = orderOf v := SemiconjBy.orderOf_eq c hsemi
  -- `orderOf a = orderOf k ∣ |K|`
  have hak : a = ((k : ↥L) : G) := hka.symm
  have hoak : orderOf a = orderOf k := by rw [hak]; exact Subgroup.orderOf_coe k
  have hok_dvd : orderOf k ∣ Nat.card ↥h.K := by
    rw [← Subgroup.orderOf_mk (H := h.K) k hkK]; exact orderOf_dvd_natCard _
  -- `v ∈ tic.W`, `v ∉ tic.W2`
  have hvmem : v ∈ (↑h.tic.W : Set G) \ ((↑h.tic.W1 : Set G) ∪ ↑h.tic.W2) := hv
  have hvW : v ∈ h.tic.W := hvmem.1
  rw [OddOrder.Peterfalvi.S06.tic_W_eq_map h] at hvW
  obtain ⟨w, hwW12, hwv⟩ := Subgroup.mem_map.mp hvW
  -- `v ∉ tic.W2 ⟹ w ∉ W₂`
  have hvnW2 : v ∉ h.tic.W2 := fun hc => hvmem.2 (Or.inr hc)
  have hwnW2 : w ∉ h.W2 := by
    intro hwW2
    exact hvnW2 (h.tic_W2 ▸ Subgroup.mem_map.mpr ⟨w, hwW2, hwv⟩)
  -- decompose `w = x·y` with `x ∈ W₁`, `y ∈ W₂`; `w ∉ W₂` forces `x ≠ 1`
  obtain ⟨x, hxW1, y, hyW2, hxy⟩ := h.exists_mul_of_mem_sup hwW12
  have hx1 : x ≠ 1 := by
    intro hx
    exact hwnW2 (by rw [← hxy, hx, one_mul]; exact hyW2)
  -- `x = w ^ n`, so `orderOf x ∣ orderOf w = orderOf v`
  obtain ⟨n, hn⟩ := h.exists_zpow_proj
  have hxwn : w ^ n = x := by rw [← hxy]; exact hn x hxW1 y hyW2
  have hox_dvd_ow : orderOf x ∣ orderOf w :=
    orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨n, hxwn⟩)
  have how_ov : orderOf w = orderOf v := by rw [← hwv]; exact (Subgroup.orderOf_coe w).symm
  -- `orderOf x ∣ |K|` and `orderOf x ∣ |W₁|`, coprime ⟹ `x = 1`, contradiction
  have how_K : orderOf w ∣ Nat.card ↥h.K := by
    rw [how_ov, ← hav_ord, hoak]; exact hok_dvd
  have hox_K : orderOf x ∣ Nat.card ↥h.K := hox_dvd_ow.trans how_K
  have hox_W1 : orderOf x ∣ Nat.card ↥h.W1 := by
    rw [← Subgroup.orderOf_mk (H := h.W1) x hxW1]; exact orderOf_dvd_natCard _
  exact hx1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h.card_coprime hox_K hox_W1))

/-- **(6.8.2.3) anchor: the Dade image of an `H^#`-supported function vanishes on `V`.**
For `α` supported on `H^# = sharpImage H`, the Sibley Dade image `α^τ = hyp.tau α` vanishes on the
`(ticVdiff h46)`-exceptional set `V`.  Since `α^τ = dadeIntegralCharacterMap hyp.dade …` is a
genuine
Dade image, it vanishes off `conjugatesOfSet H^#`
(`map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot`
via `dade_H_eq_bot`); and `V` is disjoint from `conjugatesOfSet H^# ⊆ conjugatesOfSet (K^G)` by
`ticVdiffV_not_mem_conjugatesOfSet_K` (using `h46.K = H`, so `H^# ⊆ K^G`).  This is the **anchor**
`hvanish` input of `inner_smul_chiFam_eq_zero_of_diff_vanishOnV`: with `α = η₁ − η̄₁`
(`Supp ⊆ H^#`, Peterfalvi (4.7)) it gives that `(η₁ − η̄₁)^τ` vanishes on `V`.

⚠ **This one is genuinely not an instance of the (4.6)-level anchor**
`S06.dadeICM_apply_eq_zero_of_mem_ticVdiffV` (issue 0160), unlike its type-P and type-II
counterparts, which were rewritten as one-line specializations of it.  The general lemma evaluates
the Dade map at `v` as a **base point** — which needs `V ⊆ A₀`, true for `h46.dade0` (whose set is
`A ∪ V^L`).  Here the datum is `hyp.dade : S04.Hypothesis G (sharpImage H) L`, supported on `H^#`
only: `V` is *outside* it, so there is no base point and the image vanishes for the opposite
reason.  The two routes are complementary, not redundant — keep both. -/
theorem tau_apply_eq_zero_of_mem_ticVdiffV
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    {α : ClassFunction ↥L ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    {v : G} (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V) :
    (hyp.tau α) v = 0 := by
  rw [SibleyDadeHypothesis.tau, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
    hyp.dade _ hαsupp]
  refine OddOrder.Peterfalvi.S04.map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
    hyp.dade.isDadeMap_dadeMap hyp.dade_H_eq_bot _ ?_
  intro hvconj
  have hbridge : sharpImage H ⊆ ((h46.K.map L.subtype : Subgroup G) : Set G) := by
    rw [hHK]; exact Set.sdiff_subset
  exact ticVdiffV_not_mem_conjugatesOfSet_K h46 hv (Group.conjugatesOfSet_mono hbridge hvconj)

/-- **(6.8.2.3) anchor, generic coherent-extension form: a difference of coherent images of two
`H^#`-supported-difference members vanishes on `V`.** For *any* coherence
`cS : IsCoherent hyp.tau S₁ H^#`
and members `η, η' ∈ S₁` whose difference `η − η'` is `H^#`-supported, the image difference
`cS.extension η − cS.extension η'` vanishes on the `(ticVdiff h46)`-exceptional set `V`: the
coherent
extension agrees with the Dade map on the supported lattice (`extends_on_supported`,
`cS.extension η − cS.extension η' = (η − η')^τ`), and `(η − η')^τ` vanishes on `V` by the anchor
`tau_apply_eq_zero_of_mem_ticVdiffV`.

This is the uniform `hvanish` input of `inner_smul_chiFam_eq_zero_of_diff_vanishOnV` for *every*
certain-type cross-orthogonality: with `η' = η̄` (the conjugate, equal degree so `η − η̄` is
`H^#`-supported) and `η^{τ₁} = ε·ξ`, it gives `ε·ξ − ε'·ξ'` vanishes on `V` — for `η ∈ Y` (seam-1)
*and* for an irreducible `η ∈ X` (the column–irreducible cross-orthogonality of the case-(B)
`X`-coherence glue). -/
theorem coherent_extension_diff_apply_eq_zero_of_mem_ticVdiffV
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (cS : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ S₁) (hη' : η' ∈ S₁)
    (hsupp : (η - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    {v : G} (hv : v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V) :
    (cS.extension η - cS.extension η') v = 0 := by
  have htaud : cS.extension η - cS.extension η' = hyp.tau (η - η') := by
    rw [← map_sub]
    exact cS.extends_on_supported (η - η')
      ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη'), hsupp⟩
  rw [htaud]
  exact tau_apply_eq_zero_of_mem_ticVdiffV hyp h46 hHK hsupp hv

/-- **The (6.8.2.3) disjointness machine** (modulo the anchor).  For orthonormal `ξ`, `ξ' ∈ ±Irr(G)`
and `c ≠ 0`, if the two-irreducible difference `c·ξ − c'·ξ'` vanishes on `V` (the **anchor**), then
`⟨c·ξ, ω^σ⟩ = 0` for every `σ`-image `ω^σ = chiFam pq`.  Chains the four disjointness bricks:
`sigmaNC_le_two_of_inner_chiFam` (`NC ≤ 2`) → `sigmaCoeff_eq_zero_of_vanishOnV_of_ncard_lt`
(`grid_eq_zero`, all `σ`-coefficients vanish since `2 < min(w₁, w₂)`) →
`inner_eq_zero_of_smul_sub_smul_orthogonal` (extract `⟨ξ, ω^σ⟩ = 0` from `⟨c·ξ − c'·ξ', ω^σ⟩ = 0`,
integrality `⟨ξ, ω^σ⟩ ∈ ℤ`).

This is Peterfalvi (5.3.b) for the certain-type column families: with `c·ξ = Y = cY.extension η₁`
and `c·ξ − c'·ξ' = (η₁ − η̄₁)^τ`, it gives `⟨Y, certainTypeOmegaSigma⟩ = 0`, the seam-1 `hXorth`
input of the capstone `per_constituent_Y_eq_smul`.  Only the anchor `(η₁ − η̄₁)^τ` vanishes on `V`
(the structural `V ∩ dadeSupport = ∅`) remains to be supplied. -/
theorem inner_smul_chiFam_eq_zero_of_diff_vanishOnV
    (hyp : OddOrder.Peterfalvi.S05.TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    (hVeq : hyp.V = hyp.Vdiff)
    (app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication hyp)
    {ξ ξ' : ClassFunction G ℂ} (hξZ : ξ ∈ ZIrr G) (hξ1 : ClassFunction.inner ξ ξ = 1)
    (hξ'Z : ξ' ∈ ZIrr G) (hξ'1 : ClassFunction.inner ξ' ξ' = 1)
    (hξξ' : ClassFunction.inner ξ ξ' = 0)
    {c c' : ℂ} (hc : c ≠ 0)
    (hvanish : ∀ v ∈ hyp.V, (c • ξ - c' • ξ') v = 0)
    (hmin : 2 < min (Nat.card hyp.W1) (Nat.card hyp.W2))
    (pq : ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) × ((hyp.W2.subgroupOf hyp.W) →* ℂˣ)) :
    ClassFunction.inner (c • ξ) (hyp.chiFam hVeq app pq) = 0 := by
  -- `NC(ψ) ≤ 2` where `ψ = c•ξ − c'•ξ'`.
  have hNC : hyp.sigmaNC hVeq app (c • ξ - c' • ξ') ≤ 2 := by
    refine sigmaNC_le_two_of_inner_chiFam hyp hVeq app hξZ hξ1 hξ'Z hξ'1 (fun pq' hpq' => ?_)
    by_contra hcon
    push Not at hcon
    refine hpq' ?_
    change ClassFunction.inner (c • ξ - c' • ξ') (hyp.chiFam hVeq app pq') = 0
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
      hcon.1, hcon.2, mul_zero, mul_zero, sub_zero]
  -- All `σ`-coefficients vanish (`grid_eq_zero`, `NC < min`).
  have hpsi : ClassFunction.inner (c • ξ - c' • ξ') (hyp.chiFam hVeq app pq) = 0 :=
    sigmaCoeff_eq_zero_of_vanishOnV_of_ncard_lt hyp hVeq app hvanish (lt_of_le_of_lt hNC hmin) pq
  -- Extract `⟨ξ, chiFam pq⟩ = 0`, then `⟨c•ξ, chiFam pq⟩ = 0`.
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hξZ ((hyp.chiFam_spec hVeq app).2.1 pq)
  have hθ : ClassFunction.inner (hyp.chiFam hVeq app pq) (hyp.chiFam hVeq app pq) = 1 := by
    rw [(hyp.chiFam_spec hVeq app).2.2.1, if_pos rfl]
  rw [ClassFunction.inner_smul_left,
    inner_eq_zero_of_smul_sub_smul_orthogonal hξ1 hθ hξξ' hm hc hpsi, mul_zero]

/-- **Coherent image of an irreducible member is `±` an irreducible (generic form).**  Generalizes
`coherentYset_extension_eq_zsmul_irreducible` to any coherence `cS : IsCoherent τ S₁ A`: an
irreducible member `η ∈ S₁` has `cS.extension η = ε·ξ` for `ε = ±1`, `ξ ∈ Irr G` (the image is
norm-`1` in `ZIrr G`, `exists_zsmul_irreducibleCharacter_of_inner_self_one`, Peterfalvi (5.9.a)). -/
theorem coherent_extension_eq_zsmul_irreducible
    {S₁ : Set (ClassFunction ↥L ℂ)} {A : Set ↥L}
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G}
    (cS : OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A)
    {η : ClassFunction ↥L ℂ} (hirr : IsIrreducibleCharacter η) (hη : η ∈ S₁) :
    ∃ (ε : ℤ) (ξ : IrreducibleCharacter G),
      (ε = 1 ∨ ε = -1) ∧ cS.extension η = ε • (ξ : ClassFunction G ℂ) := by
  have hηnorm : ClassFunction.inner η η = 1 := by
    have h := irreducibleCharacter_inner (⟨η, hirr⟩ : IrreducibleCharacter ↥L)
      (⟨η, hirr⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hηspan : η ∈ OddOrder.Peterfalvi.S07.zSpan S₁ := Submodule.subset_span hη
  have hextnorm : ClassFunction.inner (cS.extension η) (cS.extension η) = 1 := by
    rw [cS.extension_inner_eq η η hηspan hηspan, hηnorm]
  exact exists_zsmul_irreducibleCharacter_of_inner_self_one (cS.extension_mem_ZIrr η hηspan)
      hextnorm

/-- **(6.8.2.3) seam-1 orthogonality, generic coherent form `⟨η^{τ₁}, ω_{ij}^σ⟩ = 0`.**  For *any*
coherence `cS : IsCoherent hyp.tau S₁ H^#` and two irreducible members `η, η' ∈ S₁` with
`⟨η, η'⟩ = 0`
and `η − η'` `H^#`-supported, the image `cS.extension η` is orthogonal to every certain-type
`σ`-image
`ω_{ij}^σ = certainTypeOmegaSigma h46 χ₂ i`.

Writing `η^{τ₁} = ε·ξ`, `η'^{τ₁} = ε'·ξ'` (`coherent_extension_eq_zsmul_irreducible`), the images
are
orthonormal (`⟨ξ, ξ'⟩ = 0` from `extension_inner_eq` + `⟨η, η'⟩ = 0`), and the difference
`ε·ξ − ε'·ξ' = η^{τ₁} − η'^{τ₁}` vanishes on `V`
(`coherent_extension_diff_apply_eq_zero_of_mem_ticVdiffV`, the anchor); the disjointness machine
`inner_smul_chiFam_eq_zero_of_diff_vanishOnV` then gives `⟨ε·ξ, ω_{ij}^σ⟩ = 0`
(`ω_{ij}^σ = chiFam P_{ij}`). Instantiating `η' = η̄` (`⟨η, η̄⟩ = 0`, `η − η̄` `H^#`-supported by
equal
degree) covers both the `Y`-anchor (seam-1) and an irreducible `X`-member (the column–irreducible
cross-orthogonality of the case-(B) `X`-coherence glue). -/
theorem inner_coherent_extension_certainTypeOmegaSigma_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (cS : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η η' : ClassFunction ↥L ℂ} (hη : η ∈ S₁) (hη' : η' ∈ S₁)
    (hηirr : IsIrreducibleCharacter η) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η η' = 0)
    (hsupp : (η - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (i : Fin (Nat.card h46.W1)) :
    ClassFunction.inner (cS.extension η)
      (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i) = 0 := by
  obtain ⟨ε, ξ, hε, hηext⟩ := coherent_extension_eq_zsmul_irreducible cS hηirr hη
  obtain ⟨ε', ξ', hε', hη'ext⟩ := coherent_extension_eq_zsmul_irreducible cS hη'irr hη'
  have hεC : (ε : ℂ) ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hε'C : (ε' : ℂ) ≠ 0 := by rcases hε' with h | h <;> simp [h]
  have hηextC : cS.extension η = (ε : ℂ) • (ξ : ClassFunction G ℂ) := by
    rw [hηext, Int.cast_smul_eq_zsmul]
  have hη'extC : cS.extension η' = (ε' : ℂ) • (ξ' : ClassFunction G ℂ) := by
    rw [hη'ext, Int.cast_smul_eq_zsmul]
  have hee0 : ClassFunction.inner (cS.extension η) (cS.extension η') = 0 := by
    rw [cS.extension_inner_eq η η' (Submodule.subset_span hη) (Submodule.subset_span hη'), hee]
  have hξξ' : ClassFunction.inner (ξ : ClassFunction G ℂ) (ξ' : ClassFunction G ℂ) = 0 := by
    rw [hηextC, hη'extC, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, star_intCast] at hee0
    rcases mul_eq_zero.mp hee0 with h | h
    · exact absurd h hεC
    · exact (mul_eq_zero.mp h).resolve_left hε'C
  have hξZ : (ξ : ClassFunction G ℂ) ∈ ZIrr G := ξ.2.mem_ZIrr
  have hξ'Z : (ξ' : ClassFunction G ℂ) ∈ ZIrr G := ξ'.2.mem_ZIrr
  have hξ1 : ClassFunction.inner (ξ : ClassFunction G ℂ) (ξ : ClassFunction G ℂ) = 1 := by
    have h := irreducibleCharacter_inner_eq_ite ξ ξ; rwa [if_pos rfl] at h
  have hξ'1 : ClassFunction.inner (ξ' : ClassFunction G ℂ) (ξ' : ClassFunction G ℂ) = 1 := by
    have h := irreducibleCharacter_inner_eq_ite ξ' ξ'; rwa [if_pos rfl] at h
  have hvanish : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V,
      ((ε : ℂ) • (ξ : ClassFunction G ℂ) - (ε' : ℂ) • (ξ' : ClassFunction G ℂ)) v = 0 := by
    intro v hv
    have h := coherent_extension_diff_apply_eq_zero_of_mem_ticVdiffV hyp h46 hHK cS hη hη' hsupp hv
    rwa [hηextC, hη'extC] at h
  have hmin : 2 < min (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W1)
      (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W2) := by
    have h1 := (OddOrder.Peterfalvi.S06.ticVdiff h46).three_le_card_W1
    have h2 := (OddOrder.Peterfalvi.S06.ticVdiff h46).three_le_card_W2
    omega
  rw [OddOrder.Peterfalvi.S06.certainTypeOmegaSigma_eq_chiFam, hηextC]
  exact inner_smul_chiFam_eq_zero_of_diff_vanishOnV (OddOrder.Peterfalvi.S06.ticVdiff h46) rfl
    (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication h46) hξZ hξ1 hξ'Z hξ'1 hξξ' hεC hvanish
    hmin _

end OddOrder.Peterfalvi.S08


