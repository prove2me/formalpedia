-- Prove2me | Definitions.Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt
-- name    : Mathlib_Topology_Algebra_Valued_WithZeroMulInt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/2ccd068e-7c1d-5e68-8ea0-4a4d520c8bdf
-- title:
--   Compactness of the valuation ring of a discretely valued field
-- statement:
--   Throughout, $K$ is a field equipped with a valuation $v$ taking values in $\mathbb{Z}^{m0} = \mathrm{WithZero}(\mathrm{Multiplicative}\,\mathbb{Z})$ and with the associated topology; $\mathcal{O}[K]$ denotes the ring of elements of valuation $\le 1$, $\mathfrak{m}[K]$ its maximal ideal and $\mathfrak{k}[K]$ the residue field. Two elementary facts come first: if $\varpi \in \mathcal{O}[K]$ is irreducible then $v(\varpi) < 1$ (`irreducible_valuation_lt_one`, from the fact that a unit of the valuation ring is exactly an element of valuation $1$), and consequently $v(\varpi) \le \mathrm{ofAdd}(-1)$, the value of $\mathbb{Z}^{m0}$ attached to the integer $-1$ (`irreducible_valuation_le_ofAdd_neg_one`). Next, for $\mathcal{O}[K]$ a discrete valuation ring, $x \in \mathfrak{m}[K]^n$ and $\varpi$ irreducible, one has $v(x) \le v(\varpi)^n$ (`mem_maximalIdeal_pow_valuation`).
--
--   The finiteness lemma `finite_quotient_maximalIdeal_pow_of_finite_residueField` is stated for a valuation with values in an arbitrary linearly ordered commutative group with zero: if $\mathcal{O}[K]$ is a discrete valuation ring with finite residue field, then $\mathcal{O}[K]/\mathfrak{m}[K]^n$ is finite for every $n$, proved by induction on $n$ using the isomorphism between successive quotients $\mathfrak{m}^n/\mathfrak{m}^{n+1}$ and the residue field. From it, `finite_cover_of_uniformity_basis` produces, for each unit $\gamma$ of $\mathbb{Z}^{m0}$, a finite subset $t \subseteq K$ (a set of representatives of $\mathcal{O}[K]/\mathfrak{m}[K]^m$ for suitable $m$) such that every $x \in \mathcal{O}[K]$ satisfies $v(y - x) < \gamma$ for some $y \in t$.
--
--   The concluding result `integer_compactSpace` asserts: if $K$ is complete, $\mathcal{O}[K]$ is a discrete valuation ring whose residue field is finite, $v$ is of rank one discrete and $v$ is surjective onto $\mathbb{Z}^{m0}$, then $\mathcal{O}[K]$ is a compact space — obtained by combining total boundedness, via the finite covers above, with closedness of $\mathcal{O}[K]$ in the complete field $K$.
--
--   **Relation to Mathlib.** Everything here is phrased with Mathlib's `Valued`, `IsDiscreteValuationRing` and `Valuation.IsRankOneDiscrete`, in Mathlib's `Valued.WithZeroMulInt` namespace; the only ingredient from outside Mathlib is [`Ideal.Quotient.out_sub`](../def/Mathlib_RingTheory_Ideal_Quotient_Basic.html#L7), that $\mathrm{mk}_I(x).\mathrm{out} - x \in I$.
--
--   **Where it is used.** These results supply the topology of local fields used in the proof: the ring of integers of a complete discretely valued field with finite residue field is compact, which underlies the local analytic input to the automorphic and Galois-theoretic parts of the argument.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Topology/Algebra/Valued/WithZeroMulInt.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Ideal_Quotient_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

open Multiplicative WithZero

open scoped Topology

namespace Valued.WithZeroMulInt

variable {K : Type*} [Field K] [hv : Valued K ℤᵐ⁰]

theorem irreducible_valuation_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : v ϖ.1 < 1 := by
  have := mt (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 h.not_isUnit
  exact lt_of_le_of_ne (Valuation.mem_integer_iff _ _ |>.1 ϖ.2) this

theorem irreducible_valuation_le_ofAdd_neg_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v ϖ.1 ≤ ofAdd (-1 : ℤ) := by
  letI := (lt_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])).1 (irreducible_valuation_lt_one h)
  rw [le_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])]
  omega

theorem mem_maximalIdeal_pow_valuation [IsDiscreteValuationRing 𝒪[K]]
    {x : 𝒪[K]} {n : ℕ} (hx : x ∈ 𝓂[K] ^ n) {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v x.val ≤ v ϖ.1 ^ n := by
  by_cases hx₀ : x = 0
  · simp [hx₀]
  · simp_rw [h.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    let ⟨y, hy⟩ := hx
    simp only [hy, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ge_iff_le]
    exact le_trans (mul_le_of_le_one_right' <| (Valuation.mem_integer_iff _ _).1 y.2) le_rfl

lemma finite_quotient_maximalIdeal_pow_of_finite_residueField {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsDiscreteValuationRing 𝒪[K]]
    (h : Finite 𝓀[K]) (n : ℕ) :
    Finite (𝒪[K] ⧸ 𝓂[K] ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    exact Finite.of_fintype (↥𝒪[K] ⧸ ⊤)
  | succ n ih =>
    have : 𝓂[K] ^ (n + 1) ≤ 𝓂[K] ^ n := Ideal.pow_le_pow_right (by simp)
    replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE this).symm.toEquiv
    suffices Finite (Ideal.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))) (𝓂[K] ^ n)) from
      Finite.of_ideal_quotient
        (I := Ideal.map (Ideal.Quotient.mk _) (𝓂[K] ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

theorem finite_cover_of_uniformity_basis [IsDiscreteValuationRing 𝒪[K]] (γ : ℤᵐ⁰ˣ)
    (h : Finite 𝓀[K]) :
    ∃ t : Set K, Set.Finite t ∧
      (𝒪[K]).carrier ⊆ ⋃ y ∈ t, { x | (x, y) ∈ { p | v (p.2 - p.1) < γ.val } } := by
  classical
  let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let ⟨m, hm⟩ := exists_pow_lt_of_le_exp_neg_one (irreducible_valuation_le_ofAdd_neg_one hϖ) γ
  letI := finite_quotient_maximalIdeal_pow_of_finite_residueField h m
  have h := Fintype.ofFinite (𝒪[K] ⧸ 𝓂[K] ^ m)
  let T := Subtype.val '' (h.elems.image Quotient.out : Set 𝒪[K])
  refine ⟨T, (Set.Finite.image _ (Finset.finite_toSet _)), fun x hx => ?_⟩
  simp only [Set.mem_iUnion]
  let y := (Ideal.Quotient.mk (𝓂[K] ^ m) ⟨x, hx⟩).out
  refine ⟨y, Set.mem_image_of_mem _ <| Finset.mem_image_of_mem Quotient.out (h.complete _),
    lt_of_le_of_lt (mem_maximalIdeal_pow_valuation (Ideal.Quotient.out_sub _ _) hϖ) hm⟩

variable (K)

open Valuation.IsRankOneDiscrete in

theorem integer_compactSpace [CompleteSpace K] [IsDiscreteValuationRing 𝒪[K]]
    [hv.v.IsRankOneDiscrete] (h : Finite 𝓀[K]) (hsurj : Function.Surjective hv.v) :
    CompactSpace 𝒪[K] where
  isCompact_univ := by
    refine isCompact_iff_isCompact_univ.1 <| isCompact_iff_totallyBounded_isComplete.2
      ⟨(hasBasis_uniformity _ _).totallyBounded_iff.2 fun γ _ ↦ ?_, (isClosed_integer K).isComplete⟩
    obtain ⟨t, htf, ht⟩ := finite_cover_of_uniformity_basis
      (Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt v).toMulEquiv γ) h
    refine ⟨t, htf, ht.trans fun x hx ↦ ?_⟩
    simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hit, hi⟩ := hx
    use i, hit
    rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
      valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hsurj]
    simpa using hi

end Valued.WithZeroMulInt

end


