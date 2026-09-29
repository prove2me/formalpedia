-- Prove2me | Definitions.Def_WeierstrassCurve_ZeroComponentReduction
-- name    : WeierstrassCurve_ZeroComponentReduction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:30.087021+00:00
-- url     : https://prove2.me/theorems/ba75576d-25c5-51a6-9cee-917f2a97e3db
-- title:
--   Formal coordinates, kernel of reduction, zero component of Weierstrass models
-- statement:
--   Throughout, $A$ is a valuation subring of a field $L$, with maximal ideal the set `A.nonunits` of elements of valuation $<1$ and residue field $k$, and $W$ is a Weierstrass model over $A$; points are taken on the base change $W$ to $L$ and, after reduction, on the base change of $W$ along $A \to k$. [`FormalCoordinates A G d`](../def/WeierstrassCurve_ZeroComponentReduction.html#L28) is a structure packaging axiomatic formal-group data on an additive group $G$: a subgroup `disc`, a coordinate map $G \to (\mathrm{Fin}\,d \to L)$, and as fields the assertions that all coordinates of members of `disc` lie in `A.nonunits`, that a member of `disc` with vanishing coordinates is $0$, that $0$ has vanishing coordinates, and the estimate that for $P \in$ `disc`, $n \in \mathbb{N}$ and each index $i$ one has $\mathrm{coord}(nP)_i - n\,\mathrm{coord}(P)_i = \sum_j c_j \mathrm{coord}(P)_j$ for some $c_j$ of valuation $<1$. From these, [`FormalCoordinates.eq_zero_of_nsmul_eq_zero`](../def/WeierstrassCurve_ZeroComponentReduction.html#L59) shows that if $n$ is a unit of $A$ then no nonzero element of `disc` is killed by $n$; [`FormalCoordinates.additive`](../def/WeierstrassCurve_ZeroComponentReduction.html#L100) instantiates the structure on $(\mathfrak m_A)^d$ with the identity coordinates.
--
--   [`WeierstrassCurve.formalParam`](../def/WeierstrassCurve_ZeroComponentReduction.html#L145) sends $O \mapsto 0$ and $(x,y) \mapsto -x/y$; `IsNonIntegral W P` asserts that whenever $P$ is the affine point $(x,y)$ one has $x \notin A$ (so $O$ qualifies vacuously), and `nonIntegralLocus` is the resulting subgroup, closure under addition being proved through a common-depth choice of parameter and the formal-parameter estimate for addition. `formalCoordinates` exhibits this subgroup as formal-coordinate data of length $1$ with coordinate $-x/y$, whence `X_mem_of_nsmul_eq_zero_of_formalCoordinates`: if $n \neq 0$ in $k$ and $n \cdot (x,y) = O$, then $x \in A$.
--
--   `HasNonsingularReduction W P` asserts that whenever $P = (x,y)$ with $x, y \in A$, the reduced pair $(\bar x, \bar y)$ is a nonsingular point of $W$ over $k$; it holds vacuously at $O$ and at non-integral points, and holds for all points when the reduced discriminant is nonzero. `reducePointSmooth` sends $O$ to $O$, an affine point with $x \in A$ and nonsingular reduction to its reduction, and all other points to $O$; it commutes with negation and agrees with the reduction map `reducePoint` when the reduced discriminant is nonzero. `zeroComponentSubgroup` is the subgroup of points with nonsingular reduction; the case analysis behind its closure under addition — with valuation estimates on slopes and on `addX` — also yields that `reducePointSmooth` is additive on it. `SmoothLocusReductionData` is a structure carrying a subgroup, the assertion that its members are exactly the points with nonsingular reduction, and the additivity of `reducePointSmooth` on it; any such datum has underlying subgroup `zeroComponentSubgroup`, gives a homomorphism `reduceHom₀` to the points of the reduced curve whose kernel is exactly `nonIntegralLocus`, and the canonical datum is `smoothLocusReductionData`. Auxiliary lemmas record that integers are units of $A$ when not in `A.nonunits`, that `nonIntegralLocus` is contained in `zeroComponentSubgroup`, that the latter is everything under good reduction, and decidability of the Weierstrass equation and nonsingularity conditions over a ring with decidable equality.
--
--   **Relation to Mathlib.** Mathlib supplies `WeierstrassCurve`, affine point groups and `ValuationSubring` with its residue field, but has no formal-group coordinate data, no kernel of reduction and no zero component for a Weierstrass model over a valuation ring; these, together with the smooth-locus reduction map `reducePointSmooth`, are the project's own notions, and `reducePointSmooth` is compared with the project's good-reduction map `reducePoint`.
--
--   **Where it is used.** These local notions support the study of torsion on the Frey curve: the formal-coordinate argument gives integrality of the coordinates of a point whose order is invertible in the residue field, and the zero component with its reduction homomorphism is the setting in which a rational point of prime order is located relative to the components of the special fibre at a prime of multiplicative reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_ZeroComponentReduction.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ReduceHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Finset

namespace ValuationSubring

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem valuation_eq_one_of_notMem_nonunits {a : L} (haA : a ∈ A) (ha : a ∉ A.nonunits) :
    A.valuation a = 1 :=
  le_antisymm ((A.valuation_le_one_iff a).mpr haA)
    (not_lt.mp fun h => ha (A.mem_nonunits_iff.mpr h))

theorem natCast_mem (n : ℕ) : (n : L) ∈ A := by
  simp

theorem valuation_natCast_eq_one {n : ℕ} (hn : (n : L) ∉ A.nonunits) :
    A.valuation (n : L) = 1 :=
  A.valuation_eq_one_of_notMem_nonunits (A.natCast_mem n) hn

end ValuationSubring

variable {L : Type*} [Field L]

structure FormalCoordinates (A : ValuationSubring L) (G : Type*) [AddCommGroup G]
    (d : ℕ) where

  disc : AddSubgroup G

  coord : G → Fin d → L

  coord_mem_nonunits : ∀ P ∈ disc, ∀ i, coord P i ∈ A.nonunits

  eq_zero_of_coord_eq_zero : ∀ P ∈ disc, (∀ i, coord P i = 0) → P = 0

  coord_zero : ∀ i, coord 0 i = 0

  coord_nsmul_sub : ∀ P ∈ disc, ∀ (n : ℕ) (i : Fin d), ∃ c : Fin d → L,
    (∀ j, c j ∈ A.nonunits) ∧
    coord (n • P) i - n * coord P i = ∑ j, c j * coord P j

namespace FormalCoordinates

variable {A : ValuationSubring L} {G : Type*} [AddCommGroup G] {d : ℕ}

theorem exists_dominant_coord (F : FormalCoordinates A G d) {P : G}
    {i₁ : Fin d} (hi₁ : F.coord P i₁ ≠ 0) :
    ∃ i₀, F.coord P i₀ ≠ 0 ∧ ∀ j, A.valuation (F.coord P j) ≤ A.valuation (F.coord P i₀) := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ
    (fun i => A.valuation (F.coord P i)) ⟨i₁, Finset.mem_univ _⟩
  refine ⟨i₀, fun h0 => hi₁ ?_, fun j => hi₀ j (Finset.mem_univ _)⟩
  have h := hi₀ i₁ (Finset.mem_univ _)
  rw [h0, map_zero, le_zero_iff] at h
  exact (Valuation.zero_iff _).mp h

theorem eq_zero_of_nsmul_eq_zero (F : FormalCoordinates A G d) {n : ℕ}
    (hn : (n : L) ∉ A.nonunits) {P : G} (hP : P ∈ F.disc) (h : n • P = 0) : P = 0 := by
  by_contra hP0

  obtain ⟨i₁, hi₁⟩ : ∃ i, F.coord P i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hP0 (F.eq_zero_of_coord_eq_zero P hP hall)

  obtain ⟨i₀, hi₀ne, hi₀⟩ := F.exists_dominant_coord hi₁
  have hv₀ : A.valuation (F.coord P i₀) ≠ 0 := (Valuation.ne_zero_iff _).mpr hi₀ne

  obtain ⟨c, hc, hest⟩ := F.coord_nsmul_sub P hP n i₀

  have hcorr : A.valuation (∑ j, c j * F.coord P j) < A.valuation (F.coord P i₀) := by
    refine Valuation.map_sum_lt _ hv₀ fun j _ => ?_
    rw [map_mul]
    calc
      A.valuation (c j) * A.valuation (F.coord P j)
          ≤ A.valuation (c j) * A.valuation (F.coord P i₀) := by
            gcongr
            exact hi₀ j
      _ = A.valuation (F.coord P i₀) * A.valuation (c j) := mul_comm _ _
      _ < A.valuation (F.coord P i₀) * 1 := by
            have hk : A.valuation (c j) < 1 := A.mem_nonunits_iff.mp (hc j)
            exact lt_of_le_of_ne (mul_le_mul_right hk.le _) fun heq =>
              (ne_of_lt hk) (mul_left_cancel₀ hv₀ heq)
      _ = A.valuation (F.coord P i₀) := mul_one _

  have hlead : A.valuation ((n : L) * F.coord P i₀) = A.valuation (F.coord P i₀) := by
    rw [map_mul, A.valuation_natCast_eq_one hn, one_mul]

  have hkey : A.valuation (F.coord (n • P) i₀) = A.valuation (F.coord P i₀) := by
    have hsum : F.coord (n • P) i₀ =
        (n : L) * F.coord P i₀ + ∑ j, c j * F.coord P j := by
      rw [← hest]; ring
    rw [hsum, Valuation.map_add_eq_of_lt_left _ (hlead.symm ▸ hcorr), hlead]

  rw [h, F.coord_zero i₀, map_zero] at hkey
  exact hv₀ hkey.symm

def additive (A : ValuationSubring L) (d : ℕ) :
    FormalCoordinates A (Fin d → L) d where
  disc := AddSubgroup.pi Set.univ fun _ => A.nonunits.toAddSubgroup
  coord f := f
  coord_mem_nonunits f hf i := hf i (Set.mem_univ i)
  eq_zero_of_coord_eq_zero f _ hf := funext hf
  coord_zero _ := rfl
  coord_nsmul_sub f _ n i := by
    refine ⟨fun _ => 0, fun _ => A.nonunits.zero_mem, ?_⟩
    simp [Pi.smul_apply, nsmul_eq_mul]

end FormalCoordinates

set_option autoImplicit false

namespace ModularCurve

namespace ElevenA1

open WeierstrassCurve Affine

section Count

variable {K : Type*} [CommRing K] (W : WeierstrassCurve.Affine K)

instance instDecidableEquation [DecidableEq K] (x y : K) : Decidable (W.Equation x y) :=
  decidable_of_iff _ (W.equation_iff x y).symm

instance instDecidableNonsingular [DecidableEq K] (x y : K) : Decidable (W.Nonsingular x y) :=
  decidable_of_iff _ (W.nonsingular_iff x y).symm

end Count

end ElevenA1

end ModularCurve

set_option autoImplicit false

open IsLocalRing ValuationSubring WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

def formalParam : (W.map A.subtype).toAffine.Point → L
  | .zero => 0
  | .some x y _ => -(x / y)

@[simp] theorem formalParam_zero : W.formalParam 0 = 0 := rfl

@[simp] theorem formalParam_some {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y) :
    W.formalParam (some x y h) = -(x / y) := rfl

def IsNonIntegral (P : (W.map A.subtype).toAffine.Point) : Prop :=
  ∀ x y (h : (W.map A.subtype).toAffine.Nonsingular x y), P = some x y h → x ∉ A

theorem isNonIntegral_zero : W.IsNonIntegral 0 := fun _ _ h heq =>
  absurd heq (Ne.symm (some_ne_zero h))

theorem isNonIntegral_some_iff {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y) :
    W.IsNonIntegral (some x y h) ↔ x ∉ A := by
  refine ⟨fun hP => hP x y h rfl, fun hx x' y' h' heq => ?_⟩
  obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by rwa [Affine.Point.some.injEq] at heq
  exact hx

theorem exists_common_depth {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂)
    (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A) :
    ∃ τ : L, τ ∈ A.nonunits ∧ τ ≠ 0 ∧ (x₁ / y₁) / τ ∈ A ∧ (x₂ / y₂) / τ ∈ A := by
  have hy₁0 : y₁ ≠ 0 := Y_ne_zero_of_X_notMem W h₁ hx₁
  have hy₂0 : y₂ ≠ 0 := Y_ne_zero_of_X_notMem W h₂ hx₂
  have hx₁0 : x₁ ≠ 0 := fun h0 => hx₁ (h0 ▸ A.zero_mem)
  have hx₂0 : x₂ ≠ 0 := fun h0 => hx₂ (h0 ▸ A.zero_mem)
  have ht₁0 : x₁ / y₁ ≠ 0 := div_ne_zero hx₁0 hy₁0
  have ht₂0 : x₂ / y₂ ≠ 0 := div_ne_zero hx₂0 hy₂0
  rcases A.mem_or_inv_mem ((x₁ / y₁) / (x₂ / y₂)) with hd | hd
  · exact ⟨x₂ / y₂, X_div_Y_mem_nonunits W h₂ hx₂, ht₂0, hd, by
      rw [div_self ht₂0]; exact A.one_mem⟩
  · rw [show ((x₁ / y₁) / (x₂ / y₂))⁻¹ = (x₂ / y₂) / (x₁ / y₁) by rw [inv_div]] at hd
    exact ⟨x₁ / y₁, X_div_Y_mem_nonunits W h₁ hx₁, ht₁0, by
      rw [div_self ht₁0]; exact A.one_mem, hd⟩

variable [DecidableEq L]

def nonIntegralLocus : AddSubgroup (W.map A.subtype).toAffine.Point where
  carrier := {P | W.IsNonIntegral P}
  zero_mem' := W.isNonIntegral_zero
  neg_mem' := by
    rintro (_ | @⟨a, b, hab⟩) hP
    · exact W.isNonIntegral_zero
    · rw [neg_some]
      exact (W.isNonIntegral_some_iff _).mpr ((W.isNonIntegral_some_iff hab).mp hP)
  add_mem' := by
    rintro (_ | @⟨x₁, y₁, h₁⟩) (_ | @⟨x₂, y₂, h₂⟩) hP hQ
    · simpa [← Affine.Point.zero_def] using W.isNonIntegral_zero
    · simpa [← Affine.Point.zero_def] using hQ
    · simpa [← Affine.Point.zero_def] using hP
    · have hx₁ : x₁ ∉ A := (W.isNonIntegral_some_iff h₁).mp hP
      have hx₂ : x₂ ∉ A := (W.isNonIntegral_some_iff h₂).mp hQ
      by_cases hxy : x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂
      · rw [add_of_Y_eq hxy.1 hxy.2]
        exact W.isNonIntegral_zero
      · rw [add_some hxy]
        obtain ⟨τ, hτ, hτ0, ht₁, ht₂⟩ := W.exists_common_depth h₁.1 h₂.1 hx₁ hx₂
        exact (W.isNonIntegral_some_iff _).mpr
          (add_formal_param_estimate (W := W) h₁.1 h₂.1 hx₁ hx₂ hxy hτ hτ0 ht₁ ht₂).1

theorem mem_nonIntegralLocus_some_iff {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) :
    some x y h ∈ W.nonIntegralLocus ↔ x ∉ A :=
  W.isNonIntegral_some_iff h

def formalCoordinates : FormalCoordinates A (W.map A.subtype).toAffine.Point 1 where
  disc := W.nonIntegralLocus
  coord P _ := W.formalParam P
  coord_mem_nonunits := by
    rintro (_ | @⟨x, y, h⟩) hP i
    · exact A.nonunits.zero_mem
    · exact A.nonunits.neg_mem
        (X_div_Y_mem_nonunits W h.1 ((W.mem_nonIntegralLocus_some_iff h).mp hP))
  eq_zero_of_coord_eq_zero := by
    rintro (_ | @⟨x, y, h⟩) hP hcoord
    · rfl
    · exfalso
      have hx : x ∉ A := (W.mem_nonIntegralLocus_some_iff h).mp hP
      have hy0 : y ≠ 0 := Y_ne_zero_of_X_notMem W h.1 hx
      have h0 := hcoord 0
      rw [formalParam_some, neg_eq_zero, div_eq_zero_iff] at h0
      exact hx ((h0.resolve_right hy0) ▸ A.zero_mem)
  coord_zero _ := rfl
  coord_nsmul_sub := by
    rintro (_ | @⟨x, y, h⟩) hP n i
    · exact ⟨fun _ => 0, fun _ => A.nonunits.zero_mem, by
        simp [← Affine.Point.zero_def]⟩
    · have hx : x ∉ A := (W.mem_nonIntegralLocus_some_iff h).mp hP
      have hy0 : y ≠ 0 := Y_ne_zero_of_X_notMem W h.1 hx
      have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
      have hτ0 : -(x / y) ≠ 0 := neg_ne_zero.mpr (div_ne_zero hx0 hy0)
      obtain ⟨hzero, haffine⟩ := formal_param_nsmul (W := W) h hx n
      rcases hnP : (n • (some x y h : (W.map A.subtype).toAffine.Point))
        with _ | @⟨x', y', h'⟩
      ·
        refine ⟨fun _ => -(n : L), fun _ => A.nonunits.neg_mem (hzero hnP), ?_⟩
        simp only [Fin.sum_univ_one, ← Affine.Point.zero_def, formalParam_zero,
          formalParam_some]
        ring
      ·
        obtain ⟨-, hcong⟩ := haffine x' y' h' hnP
        refine ⟨fun _ => -(x' / y') / -(x / y) - (n : L), fun _ => hcong, ?_⟩
        simp only [Fin.sum_univ_one, formalParam_some]
        rw [sub_mul, div_mul_cancel₀ _ hτ0]

theorem X_mem_of_nsmul_eq_zero_of_formalCoordinates {n : ℕ}
    (hn : (n : ResidueField A) ≠ 0) {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hP : n • (some x y h : (W.map A.subtype).toAffine.Point) = 0) : x ∈ A := by
  by_contra hx
  refine some_ne_zero h (W.formalCoordinates.eq_zero_of_nsmul_eq_zero ?_
    ((W.mem_nonIntegralLocus_some_iff h).mpr hx) hP)
  rw [A.natCast_mem_nonunits_iff_residue_eq_zero]
  exact hn

end WeierstrassCurve

set_option autoImplicit false

open IsLocalRing

namespace WeierstrassCurve

section General

variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

def HasNonsingularReduction (P : (W.map A.subtype).toAffine.Point) : Prop :=
  ∀ x y (h : (W.map A.subtype).toAffine.Nonsingular x y), P = .some x y h →
    ∀ (hx : x ∈ A) (hy : y ∈ A),
      (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)

theorem hasNonsingularReduction_zero : W.HasNonsingularReduction 0 :=
  fun _ _ h heq => absurd heq (Ne.symm (Affine.Point.some_ne_zero h))

theorem hasNonsingularReduction_some_iff {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) :
    W.HasNonsingularReduction (.some x y h) ↔
      ∀ (hx : x ∈ A) (hy : y ∈ A),
        (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
  refine ⟨fun hP hx hy => hP x y h rfl hx hy, fun hns x' y' h' heq hx' hy' => ?_⟩
  obtain ⟨rfl, rfl⟩ : x = x' ∧ y = y' := by rwa [Affine.Point.some.injEq] at heq
  exact hns hx' hy'

theorem hasNonsingularReduction_some_of_notMem {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∉ A) :
    W.HasNonsingularReduction (.some x y h) :=
  (W.hasNonsingularReduction_some_iff h).mpr fun hx' _ => absurd hx' hx

theorem hasNonsingularReduction_of_good (hΔ : (W.map (residue A)).Δ ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) : W.HasNonsingularReduction P :=
  fun _ _ h _ _ _ => Affine.nonsingular_residue W hΔ h.1

theorem hasNonsingularReduction_of_isNonIntegral {P : (W.map A.subtype).toAffine.Point}
    (hP : W.IsNonIntegral P) : W.HasNonsingularReduction P :=
  fun x y h heq hx _ => absurd hx (hP x y h heq)

theorem hasNonsingularReduction_neg {P : (W.map A.subtype).toAffine.Point}
    (hP : W.HasNonsingularReduction P) : W.HasNonsingularReduction (-P) := by
  cases P with
  | zero =>
    show W.HasNonsingularReduction (-(0 : (W.map A.subtype).toAffine.Point))
    rw [Affine.Point.neg_zero]
    exact W.hasNonsingularReduction_zero
  | some x y h =>
    rw [Affine.Point.neg_some]
    rw [W.hasNonsingularReduction_some_iff] at hP
    rw [W.hasNonsingularReduction_some_iff]
    intro hx hy'
    have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
    have hns := hP hx hy
    have hkey : residue A (⟨(W.map A.subtype).toAffine.negY x y, hy'⟩ : A) =
        (W.map (residue A)).toAffine.negY (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
      rw [A.residue_eq_of_coe_eq hy' (v := W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩)
        (coe_negY hx hy).symm]
      exact residue_negY hx hy
    rw [hkey]
    exact (Affine.nonsingular_neg ..).mpr hns

section NonIntegralLocus

variable [DecidableEq L]

theorem isNonIntegral_of_mem_nonIntegralLocus {P : (W.map A.subtype).toAffine.Point}
    (hP : P ∈ W.nonIntegralLocus) : W.IsNonIntegral P :=
  fun _ _ h heq => (W.mem_nonIntegralLocus_some_iff h).mp (heq ▸ hP)

theorem hasNonsingularReduction_of_mem_nonIntegralLocus {P : (W.map A.subtype).toAffine.Point}
    (hP : P ∈ W.nonIntegralLocus) : W.HasNonsingularReduction P :=
  W.hasNonsingularReduction_of_isNonIntegral (W.isNonIntegral_of_mem_nonIntegralLocus hP)

end NonIntegralLocus

private lemma some_smoothLocus_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

open Classical in

noncomputable def reducePointSmooth :
    (W.map A.subtype).toAffine.Point → (W.map (residue A)).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x ∈ A then
      if hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
          (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩) then
        .some _ _ hns
      else .zero
    else .zero

@[simp]
theorem reducePointSmooth_zero : W.reducePointSmooth 0 = 0 := rfl

theorem reducePointSmooth_some_of_mem {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A) {hy : y ∈ A}
    (hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩)) :
    W.reducePointSmooth (.some x y h) = .some (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) hns := by
  simp only [reducePointSmooth]
  rw [dif_pos hx]
  exact dif_pos hns

theorem reducePointSmooth_some_of_notMem {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∉ A) :
    W.reducePointSmooth (.some x y h) = 0 := by
  simp only [reducePointSmooth]
  exact dif_neg hx

theorem reducePointSmooth_some_of_singular {x y : L}
    (h : (W.map A.subtype).toAffine.Nonsingular x y) (hx : x ∈ A) {hy : y ∈ A}
    (hsing : ¬ (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
      (residue A ⟨y, hy⟩)) :
    W.reducePointSmooth (.some x y h) = 0 := by
  simp only [reducePointSmooth]
  rw [dif_pos hx]
  exact dif_neg fun hcon => hsing hcon

theorem reducePointSmooth_eq_reducePoint (hΔ : (W.map (residue A)).Δ ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) :
    W.reducePointSmooth P = reducePoint hΔ P := by
  cases P with
  | zero => rfl
  | some x y h =>
    by_cases hx : x ∈ A
    · rw [W.reducePointSmooth_some_of_mem h hx
        (Affine.nonsingular_residue W hΔ (x := ⟨x, hx⟩)
          (y := ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩) h.1),
        reducePoint_some_of_mem _ _ hx]
    · rw [W.reducePointSmooth_some_of_notMem h hx, reducePoint_some_of_notMem _ _ hx]

theorem reducePointSmooth_neg (P : (W.map A.subtype).toAffine.Point) :
    W.reducePointSmooth (-P) = -W.reducePointSmooth P := by
  cases P with
  | zero =>
    show W.reducePointSmooth (-(0 : (W.map A.subtype).toAffine.Point)) =
      -W.reducePointSmooth (0 : (W.map A.subtype).toAffine.Point)
    rw [Affine.Point.neg_zero, reducePointSmooth_zero, Affine.Point.neg_zero]
  | some x y h =>
    rw [Affine.Point.neg_some]
    by_cases hx : x ∈ A
    · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
      have hy' : (W.map A.subtype).toAffine.negY x y ∈ A := negY_mem hx hy
      have hkey : residue A (⟨(W.map A.subtype).toAffine.negY x y, hy'⟩ : A) =
          (W.map (residue A)).toAffine.negY (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) := by
        rw [A.residue_eq_of_coe_eq hy' (v := W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩)
          (coe_negY hx hy).symm]
        exact residue_negY hx hy
      by_cases hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
          (residue A ⟨y, hy⟩)
      · have hns' : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
            (residue A ⟨(W.map A.subtype).toAffine.negY x y, hy'⟩) := by
          rw [hkey]
          exact (Affine.nonsingular_neg ..).mpr hns
        rw [W.reducePointSmooth_some_of_mem _ hx hns', W.reducePointSmooth_some_of_mem h hx hns,
          Affine.Point.neg_some]
        exact some_smoothLocus_congr rfl hkey _ _
      · have hns' : ¬ (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩)
            (residue A ⟨(W.map A.subtype).toAffine.negY x y, hy'⟩) := by
          rw [hkey]
          intro hcon
          exact hns ((Affine.nonsingular_neg ..).mp hcon)
        rw [W.reducePointSmooth_some_of_singular _ hx hns',
          W.reducePointSmooth_some_of_singular h hx hns]
        exact (Affine.Point.neg_zero).symm
    · rw [W.reducePointSmooth_some_of_notMem _ hx, W.reducePointSmooth_some_of_notMem h hx]
      exact (Affine.Point.neg_zero).symm

section Kernel

variable [DecidableEq L]

theorem reducePointSmooth_eq_zero_of_mem_nonIntegralLocus
    {P : (W.map A.subtype).toAffine.Point} (hP : P ∈ W.nonIntegralLocus) :
    W.reducePointSmooth P = 0 := by
  cases P with
  | zero => exact W.reducePointSmooth_zero
  | some x y h =>
    exact W.reducePointSmooth_some_of_notMem h ((W.mem_nonIntegralLocus_some_iff h).mp hP)

theorem mem_nonIntegralLocus_of_reducePointSmooth_eq_zero
    {P : (W.map A.subtype).toAffine.Point} (hP : W.HasNonsingularReduction P)
    (h0 : W.reducePointSmooth P = 0) : P ∈ W.nonIntegralLocus := by
  cases P with
  | zero => exact zero_mem _
  | some x y h =>
    by_cases hx : x ∈ A
    · exfalso
      have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
      have hns := (W.hasNonsingularReduction_some_iff h).mp hP hx hy
      rw [W.reducePointSmooth_some_of_mem h hx hns] at h0
      exact Affine.Point.some_ne_zero hns h0
    · exact (W.mem_nonIntegralLocus_some_iff h).mpr hx

end Kernel

theorem Affine.notMem_nonunits_of_sub_negY_mem_nonunits_of_nonsingular_residue
    {x y : L} (hx : x ∈ A) (hy : y ∈ A)
    (hns : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩))
    (hY : y - (W.map A.subtype).toAffine.negY x y ∈ A.nonunits) :
    3 * x ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x + (W.map A.subtype).toAffine.a₄ -
      (W.map A.subtype).toAffine.a₁ * y ∉ A.nonunits := by

  set eX : A := 3 * ⟨x, hx⟩ ^ 2 + 2 * W.a₂ * ⟨x, hx⟩ + W.a₄ - W.a₁ * ⟨y, hy⟩ with heX
  set eY : A := ⟨y, hy⟩ - W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩ with heY

  have hcoeX : (eX : L) = 3 * x ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x +
      (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y := by
    push_cast [heX]
    rfl
  have hcoeY : (eY : L) = y - (W.map A.subtype).toAffine.negY x y := by
    have h1 : ((W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩ : A) : L) = (W.map A.subtype).toAffine.negY x y :=
      (Affine.map_negY A.subtype (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm
    rw [heY]
    push_cast
    rw [h1]

  rw [Affine.nonsingular_iff] at hns

  have hY0 : residue A eY = 0 := by
    rw [← A.coe_mem_nonunits_iff_residue_eq_zero, hcoeY]
    exact hY

  have hX0 : residue A eX ≠ 0 := by
    rcases hns.2 with hX | hY'
    · intro h0
      apply hX
      rw [heX] at h0
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at h0
      show residue A W.a₁ * residue A ⟨y, hy⟩ = 3 * residue A ⟨x, hx⟩ ^ 2 +
        2 * residue A W.a₂ * residue A ⟨x, hx⟩ + residue A W.a₄
      linear_combination -h0
    · exact absurd (by
        show residue A ⟨y, hy⟩ = -residue A ⟨y, hy⟩ - residue A W.a₁ * residue A ⟨x, hx⟩ -
          residue A W.a₃
        rw [heY] at hY0
        simp only [Affine.negY, map_sub, map_neg, map_mul] at hY0
        linear_combination hY0) hY'

  rw [← hcoeX, A.coe_mem_nonunits_iff_residue_eq_zero]
  exact hX0

section Slope

variable [DecidableEq L]

theorem Affine.slope_notMem_of_sub_mem_nonunits_of_nonsingular_residue
    {x₁ x₂ y₁ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₁ : y₁ ∈ A)
    (hns₁ : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x₁, hx₁⟩)
      (residue A ⟨y₁, hy₁⟩))
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∉ A := by
  have hy₂ : y₂ ∈ A := Affine.Y_mem_of_X_mem W h₂ hx₂

  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha₃ : (W.map A.subtype).toAffine.a₃ ∈ A := SetLike.coe_mem W.a₃
  have ha₄ : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄

  have hnegY : (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A := by
    rw [Affine.negY]
    exact A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem hy₂)
      (A.toSubring.mul_mem ha₁ hx₂)) ha₃
  by_cases hx : x₁ = x₂
  ·

    have hy : y₁ ≠ (W.map A.subtype).toAffine.negY x₂ y₂ := fun h => hPQ ⟨hx, h⟩
    have hy12 : y₁ = y₂ := (Affine.Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    rw [Affine.slope_of_Y_ne hx hy]

    have hden : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ∈ A.nonunits := by
      rwa [← hx, ← hy12] at hyy
    have hden0 : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ≠ 0 := by
      rw [sub_ne_zero]
      intro hcon
      exact hy (by rw [← hx, ← hy12]; exact hcon)

    have hnum := Affine.notMem_nonunits_of_sub_negY_mem_nonunits_of_nonsingular_residue W
      hx₁ hy₁ hns₁ hden
    exact A.div_notMem hnum hden hden0
  ·
    by_cases hyy' : y₁ - y₂ ∈ A.nonunits
    ·

      rw [Affine.slope_of_X_ne hx]

      have hden : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ∈ A.nonunits := by
        have key : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ =
            (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) + (y₁ - y₂) +
              (W.map A.subtype).toAffine.a₁ * (x₁ - x₂) := by
          simp only [Affine.negY]
          ring
        rw [key]
        exact add_mem (add_mem hyy hyy') (A.mul_mem_nonunits ha₁ hxx)

      have hnum := Affine.notMem_nonunits_of_sub_negY_mem_nonunits_of_nonsingular_residue W
        hx₁ hy₁ hns₁ hden

      set N : L := x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (W.map A.subtype).toAffine.a₂ * (x₁ + x₂) +
        (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ with hN
      have hNunit : N ∉ A.nonunits := by
        intro hmem
        apply hnum
        have key : 3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
            (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ =
            N - (x₁ + x₁ + x₂ + (W.map A.subtype).toAffine.a₂) * -(x₁ - x₂) := by
          rw [hN]; ring
        rw [key]
        exact sub_mem hmem (A.mul_mem_nonunits
          (add_mem (add_mem (add_mem hx₁ hx₁) hx₂) ha₂) (neg_mem hxx))

      have hd0 : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ≠ 0 := by
        intro hd
        apply hNunit
        rw [hN]
        have hid := Affine.sub_mul_sub_negY h₁ h₂
        rw [hd, mul_zero] at hid
        rcases mul_eq_zero.mp hid.symm with h | h
        · exact absurd (sub_eq_zero.mp h) hx
        · rw [h]
          exact zero_mem _

      have hslope : (y₁ - y₂) / (x₁ - x₂) = N / (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) := by
        rw [div_eq_div_iff (sub_ne_zero.mpr hx) hd0, hN]
        linear_combination Affine.sub_mul_sub_negY h₁ h₂
      rw [hslope]
      exact A.div_notMem hNunit hyy hd0
    ·

      rw [Affine.slope_of_X_ne hx]
      exact A.div_notMem hyy' hxx (sub_ne_zero.mpr hx)

theorem Affine.addX_notMem_of_sub_mem_nonunits_of_nonsingular_residue
    {x₁ x₂ y₁ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₁ : y₁ ∈ A)
    (hns₁ : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨x₁, hx₁⟩)
      (residue A ⟨y₁, hy₁⟩))
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∉ A := by
  have hℓ := Affine.slope_notMem_of_sub_mem_nonunits_of_nonsingular_residue W h₁ h₂ hx₁ hx₂
    hy₁ hns₁ hPQ hxx hyy
  set ℓ : L := (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂

  rw [show (W.map A.subtype).toAffine.addX x₁ x₂ ℓ =
    ℓ * (ℓ + (W.map A.subtype).toAffine.a₁) +
      (-(W.map A.subtype).toAffine.a₂ - x₁ - x₂) from by rw [Affine.addX]; ring]
  exact A.add_notMem (A.mul_notMem hℓ (by simpa [add_comm] using A.add_notMem hℓ ha₁))
    (A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem ha₂) hx₁) hx₂)

end Slope

section Carrier

variable [DecidableEq L] [DecidableEq (ResidueField A)]

structure SmoothLocusReductionData : Type _ where

  zeroComponent : AddSubgroup (W.map A.subtype).toAffine.Point

  mem_iff : ∀ P : (W.map A.subtype).toAffine.Point,
    P ∈ zeroComponent ↔ W.HasNonsingularReduction P

  reducePointSmooth_add : ∀ P Q : (W.map A.subtype).toAffine.Point,
    P ∈ zeroComponent → Q ∈ zeroComponent →
      W.reducePointSmooth (P + Q) = W.reducePointSmooth P + W.reducePointSmooth Q

namespace SmoothLocusReductionData

variable {W}

theorem nonIntegralLocus_le (D : W.SmoothLocusReductionData) :
    W.nonIntegralLocus ≤ D.zeroComponent := fun P hP =>
  (D.mem_iff P).mpr (W.hasNonsingularReduction_of_mem_nonIntegralLocus hP)

theorem zero_mem (D : W.SmoothLocusReductionData) : (0 : (W.map A.subtype).toAffine.Point) ∈
    D.zeroComponent := (D.mem_iff 0).mpr (W.hasNonsingularReduction_zero)

noncomputable def reduceHom₀ (D : W.SmoothLocusReductionData) :
    D.zeroComponent →+ (W.map (residue A)).toAffine.Point where
  toFun P := W.reducePointSmooth (P : (W.map A.subtype).toAffine.Point)
  map_zero' := by simp
  map_add' P Q := by
    simpa using D.reducePointSmooth_add (P : (W.map A.subtype).toAffine.Point)
      (Q : (W.map A.subtype).toAffine.Point) P.2 Q.2

@[simp]
theorem reduceHom₀_apply (D : W.SmoothLocusReductionData) (P : D.zeroComponent) :
    D.reduceHom₀ P = W.reducePointSmooth (P : (W.map A.subtype).toAffine.Point) := rfl

theorem reduceHom₀_eq_zero_iff (D : W.SmoothLocusReductionData) (P : D.zeroComponent) :
    D.reduceHom₀ P = 0 ↔ (P : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus := by
  constructor
  · intro h0
    exact W.mem_nonIntegralLocus_of_reducePointSmooth_eq_zero ((D.mem_iff _).mp P.2) h0
  · intro hmem
    exact W.reducePointSmooth_eq_zero_of_mem_nonIntegralLocus hmem

end SmoothLocusReductionData

end Carrier

end General

section ConsumerEngine

variable {L : Type} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve A}
  [DecidableEq L] [DecidableEq (ResidueField A)]

end ConsumerEngine

end WeierstrassCurve

set_option autoImplicit false

open IsLocalRing

namespace WeierstrassCurve

variable {L : Type*} [Field L] {A : ValuationSubring L} {W : WeierstrassCurve A}

private lemma some_smoothClosure_congr {R : Type*} [CommRing R] {V : Affine R}
    {x₁ x₂ y₁ y₂ : R} (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁)
    (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

section CoordinatewiseEngine

variable [DecidableEq L] [DecidableEq (ResidueField A)]

theorem addX_mem_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits)) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
  obtain ⟨hsmem, -⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hX_coe : (W.map A.subtype).toAffine.addX x₁ x₂
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addX (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  rw [hX_coe]
  exact SetLike.coe_mem _

theorem addY_mem_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits)) :
    (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
  obtain ⟨hsmem, -⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hy₁ : y₁ ∈ A := Affine.Y_mem_of_X_mem W h₁ hx₁
  have hY_coe : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addY (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  rw [hY_coe]
  exact SetLike.coe_mem _

set_option maxHeartbeats 800000 in

theorem residue_addX_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits))
    (hmem : (W.map A.subtype).toAffine.addX x₁ x₂
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A) :
    residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩ =
      (W.map (residue A)).toAffine.addX (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        ((W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩)) := by
  obtain ⟨hsmem, hsres⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hsres' : residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ =
      (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩) := hsres
  have hX_coe : (W.map A.subtype).toAffine.addX x₁ x₂
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addX (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  calc residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩
      = residue A (W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        A.residue_eq_of_coe_eq hmem hX_coe
    _ = (W.map (residue A)).toAffine.addX (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        (Affine.map_addX (W' := W) (residue A) (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩).symm
    _ = _ := by rw [hsres']

set_option maxHeartbeats 800000 in

theorem residue_addY_of_not_inverse {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₁ : y₁ ∈ A) (hy₂ : y₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits))
    (hmem : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A) :
    residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩ =
      (W.map (residue A)).toAffine.addY (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        (residue A ⟨y₁, hy₁⟩)
        ((W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩)) := by
  obtain ⟨hsmem, hsres⟩ := slope_mem_residue_of_not_inverse h₁ h₂ hx₁ hx₂ hred
  have hsres' : residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ =
      (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
        (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩) := hsres
  have hY_coe : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
      ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
      ((W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
    Affine.map_addY (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A) (⟨x₂, hx₂⟩ : A)
      ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
  calc residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hmem⟩
      = residue A (W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        A.residue_eq_of_coe_eq hmem hY_coe
    _ = (W.map (residue A)).toAffine.addY (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, hy₁⟩)
          (residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
        (Affine.map_addY (W' := W) (residue A) (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A)
          (⟨x₂, hx₂⟩ : A)
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩).symm
    _ = _ := by rw [hsres']

end CoordinatewiseEngine

section CaseAnalysis

variable [DecidableEq L] [DecidableEq (ResidueField A)]

set_option maxHeartbeats 1600000 in

private lemma addAux_of_mem_of_mem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hP : W.HasNonsingularReduction (.some x₁ y₁ h₁))
    (hQ : W.HasNonsingularReduction (.some x₂ y₂ h₂)) :
    W.HasNonsingularReduction (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) ∧
      W.reducePointSmooth (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
        W.reducePointSmooth (.some x₁ y₁ h₁) + W.reducePointSmooth (.some x₂ y₂ h₂) := by
  have hy₁ : y₁ ∈ A := Affine.Y_mem_of_X_mem W h₁.1 hx₁
  have hy₂ : y₂ ∈ A := Affine.Y_mem_of_X_mem W h₂.1 hx₂
  have hns₁ := (W.hasNonsingularReduction_some_iff h₁).mp hP hx₁ hy₁
  have hns₂ := (W.hasNonsingularReduction_some_iff h₂).mp hQ hx₂ hy₂
  by_cases hred : x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits
  ·

    obtain ⟨hredx, hredy⟩ := (residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mpr hred
    by_cases hPQ : x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂
    · constructor
      · rw [Affine.Point.add_of_Y_eq hPQ.1 hPQ.2]
        exact W.hasNonsingularReduction_zero
      · rw [Affine.Point.add_of_Y_eq hPQ.1 hPQ.2, W.reducePointSmooth_zero,
          W.reducePointSmooth_some_of_mem h₁ hx₁ hns₁, W.reducePointSmooth_some_of_mem h₂ hx₂ hns₂,
          Affine.Point.add_of_Y_eq hredx hredy]
    · have haddX := Affine.addX_notMem_of_sub_mem_nonunits_of_nonsingular_residue W h₁.1 h₂.1
        hx₁ hx₂ hy₁ hns₁ hPQ hred.1 hred.2
      constructor
      · rw [Affine.Point.add_some hPQ]
        exact W.hasNonsingularReduction_some_of_notMem _ haddX
      · rw [Affine.Point.add_some hPQ, W.reducePointSmooth_some_of_notMem _ haddX,
          W.reducePointSmooth_some_of_mem h₁ hx₁ hns₁, W.reducePointSmooth_some_of_mem h₂ hx₂ hns₂,
          Affine.Point.add_of_Y_eq hredx hredy]
  ·

    have hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂) := by
      rintro ⟨hxe, hye⟩
      exact hred ⟨by rw [hxe, sub_self]; exact A.nonunits.zero_mem,
        by rw [hye, sub_self]; exact A.nonunits.zero_mem⟩
    have hredk : ¬(residue A ⟨x₁, hx₁⟩ = residue A ⟨x₂, hx₂⟩ ∧
        residue A ⟨y₁, hy₁⟩ =
          (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩)) :=
      fun h => hred ((residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mp h)
    have hXmem : (W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A :=
      addX_mem_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hred
    have hYmem : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A :=
      addY_mem_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hred
    have hXres := residue_addX_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hy₁ hy₂ hred hXmem
    have hYres := residue_addY_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hy₁ hy₂ hred hYmem
    have hns₃ : (W.map (residue A)).toAffine.Nonsingular
        (residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hXmem⟩)
        (residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
          ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hYmem⟩) := by
      rw [hXres, hYres]
      exact Affine.nonsingular_add hns₁ hns₂ hredk
    constructor
    · rw [Affine.Point.add_some hPQ, W.hasNonsingularReduction_some_iff]
      intro hx hy
      exact hns₃
    · rw [Affine.Point.add_some hPQ, W.reducePointSmooth_some_of_mem _ hXmem hns₃,
        W.reducePointSmooth_some_of_mem h₁ hx₁ hns₁, W.reducePointSmooth_some_of_mem h₂ hx₂ hns₂,
        Affine.Point.add_some hredk]
      exact some_smoothClosure_congr hXres hYres _ _

private lemma addAux_of_notMem_of_notMem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A) :
    W.HasNonsingularReduction (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) ∧
      W.reducePointSmooth (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
        W.reducePointSmooth (.some x₁ y₁ h₁) + W.reducePointSmooth (.some x₂ y₂ h₂) := by
  have hPmem : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus :=
    (W.mem_nonIntegralLocus_some_iff h₁).mpr hx₁
  have hQmem : (.some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus :=
    (W.mem_nonIntegralLocus_some_iff h₂).mpr hx₂
  have hSmem : (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) ∈
      W.nonIntegralLocus := add_mem hPmem hQmem
  refine ⟨W.hasNonsingularReduction_of_mem_nonIntegralLocus hSmem, ?_⟩
  rw [W.reducePointSmooth_eq_zero_of_mem_nonIntegralLocus hSmem,
    W.reducePointSmooth_some_of_notMem h₁ hx₁, W.reducePointSmooth_some_of_notMem h₂ hx₂,
    add_zero]

set_option maxHeartbeats 800000 in

private lemma addAux_of_mem_of_notMem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂)
    (hP : W.HasNonsingularReduction (.some x₁ y₁ h₁)) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∉ A) :
    W.HasNonsingularReduction (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) ∧
      W.reducePointSmooth (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
        W.reducePointSmooth (.some x₁ y₁ h₁) + W.reducePointSmooth (.some x₂ y₂ h₂) := by
  have hy₁ : y₁ ∈ A := Affine.Y_mem_of_X_mem W h₁.1 hx₁
  have hns₁ := (W.hasNonsingularReduction_some_iff h₁).mp hP hx₁ hy₁

  have hPn : (W.map A.subtype).toAffine.Nonsingular x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) :=
    (Affine.nonsingular_neg _ _).mpr h₁
  have hPneg : (.some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn :
      (W.map A.subtype).toAffine.Point) = -(.some x₁ y₁ h₁) := (Affine.Point.neg_some h₁).symm
  cases hadd : (.some x₁ y₁ h₁ + .some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) with
  | zero =>

    exfalso
    have hPQ : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) = -(.some x₂ y₂ h₂) :=
      eq_neg_of_add_eq_zero_left hadd
    rw [Affine.Point.neg_some] at hPQ
    simp only [Affine.Point.some.injEq] at hPQ
    exact hx₂ (hPQ.1 ▸ hx₁)
  | some X₃ Y₃ h₃ =>
    by_cases hX₃ : X₃ ∈ A
    ·

      have hY₃ : Y₃ ∈ A := Affine.Y_mem_of_X_mem W h₃.1 hX₃
      have hkey : X₃ - x₁ ∈ A.nonunits ∧
          Y₃ - (W.map A.subtype).toAffine.negY x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) ∈
            A.nonunits := by
        by_contra hcon

        have hSnegP : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) +
            .some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn = .some x₂ y₂ h₂ := by
          rw [hPneg, ← hadd]; abel

        have hSP : ¬(X₃ = x₁ ∧
            Y₃ = (W.map A.subtype).toAffine.negY x₁ ((W.map A.subtype).toAffine.negY x₁ y₁)) := by
          rintro ⟨hX, hY⟩
          have h0 : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) +
              .some x₁ ((W.map A.subtype).toAffine.negY x₁ y₁) hPn = 0 :=
            Affine.Point.add_of_Y_eq hX hY
          rw [hSnegP] at h0
          exact Affine.Point.some_ne_zero h₂ h0

        have haddX : (W.map A.subtype).toAffine.addX X₃ x₁
            ((W.map A.subtype).toAffine.slope X₃ x₁ Y₃
              ((W.map A.subtype).toAffine.negY x₁ y₁)) ∈ A :=
          addX_mem_of_not_inverse h₃.1 hPn.1 hX₃ hx₁ hcon
        rw [Affine.Point.add_some hSP] at hSnegP
        simp only [Affine.Point.some.injEq] at hSnegP
        exact hx₂ (hSnegP.1 ▸ haddX)
      rw [Affine.negY_negY] at hkey
      have hXres : residue A ⟨X₃, hX₃⟩ = residue A ⟨x₁, hx₁⟩ :=
        (A.residue_eq_residue_iff_sub_mem_nonunits hX₃ hx₁).mpr hkey.1
      have hYres : residue A ⟨Y₃, hY₃⟩ = residue A ⟨y₁, hy₁⟩ :=
        (A.residue_eq_residue_iff_sub_mem_nonunits hY₃ hy₁).mpr hkey.2
      have hnsS : (W.map (residue A)).toAffine.Nonsingular (residue A ⟨X₃, hX₃⟩)
          (residue A ⟨Y₃, hY₃⟩) := by
        rw [hXres, hYres]
        exact hns₁
      constructor
      · rw [W.hasNonsingularReduction_some_iff]
        intro hx hy
        exact hnsS
      · rw [W.reducePointSmooth_some_of_mem h₃ hX₃ hnsS,
          W.reducePointSmooth_some_of_notMem h₂ hx₂,
          W.reducePointSmooth_some_of_mem h₁ hx₁ hns₁, add_zero]
        exact some_smoothClosure_congr hXres hYres _ _
    ·
      exfalso
      have hS : (.some X₃ Y₃ h₃ : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus :=
        (W.mem_nonIntegralLocus_some_iff h₃).mpr hX₃
      have hQmem : (.some x₂ y₂ h₂ : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus :=
        (W.mem_nonIntegralLocus_some_iff h₂).mpr hx₂
      have hPmem : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) ∈ W.nonIntegralLocus := by
        have hPeq : (.some x₁ y₁ h₁ : (W.map A.subtype).toAffine.Point) =
            .some X₃ Y₃ h₃ - .some x₂ y₂ h₂ := by
          rw [← hadd]; abel
        rw [hPeq]
        exact sub_mem hS hQmem
      exact ((W.mem_nonIntegralLocus_some_iff h₁).mp hPmem) hx₁

end CaseAnalysis

section Closure

variable [DecidableEq L] [DecidableEq (ResidueField A)]

theorem hasNonsingularReduction_add {P Q : (W.map A.subtype).toAffine.Point}
    (hP : W.HasNonsingularReduction P) (hQ : W.HasNonsingularReduction Q) :
    W.HasNonsingularReduction (P + Q) := by
  cases P with
  | zero =>
    show W.HasNonsingularReduction ((0 : (W.map A.subtype).toAffine.Point) + Q)
    rw [zero_add]
    exact hQ
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show W.HasNonsingularReduction (.some x₁ y₁ h₁ + (0 : (W.map A.subtype).toAffine.Point))
      rw [add_zero]
      exact hP
    | some x₂ y₂ h₂ =>
      by_cases hx₁ : x₁ ∈ A <;> by_cases hx₂ : x₂ ∈ A
      · exact (addAux_of_mem_of_mem h₁ h₂ hx₁ hx₂ hP hQ).1
      · exact (addAux_of_mem_of_notMem h₁ h₂ hP hx₁ hx₂).1
      · rw [add_comm (Affine.Point.some x₁ y₁ h₁) (Affine.Point.some x₂ y₂ h₂)]
        exact (addAux_of_mem_of_notMem h₂ h₁ hQ hx₂ hx₁).1
      · exact (addAux_of_notMem_of_notMem h₁ h₂ hx₁ hx₂).1

theorem reducePointSmooth_add_of_hasNonsingularReduction
    {P Q : (W.map A.subtype).toAffine.Point}
    (hP : W.HasNonsingularReduction P) (hQ : W.HasNonsingularReduction Q) :
    W.reducePointSmooth (P + Q) = W.reducePointSmooth P + W.reducePointSmooth Q := by
  cases P with
  | zero =>
    show W.reducePointSmooth ((0 : (W.map A.subtype).toAffine.Point) + Q) =
      W.reducePointSmooth (0 : (W.map A.subtype).toAffine.Point) + W.reducePointSmooth Q
    rw [zero_add, W.reducePointSmooth_zero, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show W.reducePointSmooth (.some x₁ y₁ h₁ + (0 : (W.map A.subtype).toAffine.Point)) =
        W.reducePointSmooth (.some x₁ y₁ h₁) +
          W.reducePointSmooth (0 : (W.map A.subtype).toAffine.Point)
      rw [add_zero, W.reducePointSmooth_zero, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hx₁ : x₁ ∈ A <;> by_cases hx₂ : x₂ ∈ A
      · exact (addAux_of_mem_of_mem h₁ h₂ hx₁ hx₂ hP hQ).2
      · exact (addAux_of_mem_of_notMem h₁ h₂ hP hx₁ hx₂).2
      · rw [add_comm (Affine.Point.some x₁ y₁ h₁) (Affine.Point.some x₂ y₂ h₂),
          (addAux_of_mem_of_notMem h₂ h₁ hQ hx₂ hx₁).2]
        exact add_comm _ _
      · exact (addAux_of_notMem_of_notMem h₁ h₂ hx₁ hx₂).2

end Closure

section Carrier

variable [DecidableEq L] [DecidableEq (ResidueField A)]

variable (W) in

def zeroComponentSubgroup : AddSubgroup (W.map A.subtype).toAffine.Point where
  carrier := {P | W.HasNonsingularReduction P}
  zero_mem' := W.hasNonsingularReduction_zero
  neg_mem' := fun {_P} hP => W.hasNonsingularReduction_neg hP
  add_mem' := fun {_P _Q} hP hQ => W.hasNonsingularReduction_add hP hQ

variable (W) in
@[simp]
theorem mem_zeroComponentSubgroup_iff {P : (W.map A.subtype).toAffine.Point} :
    P ∈ W.zeroComponentSubgroup ↔ W.HasNonsingularReduction P := Iff.rfl

variable (W) in

noncomputable def smoothLocusReductionData : W.SmoothLocusReductionData where
  zeroComponent := W.zeroComponentSubgroup
  mem_iff := fun _ => Iff.rfl
  reducePointSmooth_add := fun _ _ hP hQ =>
    W.reducePointSmooth_add_of_hasNonsingularReduction hP hQ

variable (W) in

theorem smoothLocusReductionData_zeroComponent :
    (W.smoothLocusReductionData).zeroComponent = W.zeroComponentSubgroup := rfl

variable (W) in

theorem nonempty_smoothLocusReductionData : Nonempty (W.SmoothLocusReductionData) :=
  ⟨W.smoothLocusReductionData⟩

theorem SmoothLocusReductionData.zeroComponent_eq (D : W.SmoothLocusReductionData) :
    D.zeroComponent = W.zeroComponentSubgroup :=
  AddSubgroup.ext fun P => D.mem_iff P

variable (W) in

theorem zeroComponentSubgroup_eq_top_of_good (hΔ : (W.map (residue A)).Δ ≠ 0) :
    W.zeroComponentSubgroup = ⊤ := by
  refine AddSubgroup.ext fun P => ?_
  simp only [AddSubgroup.mem_top, iff_true]
  exact W.hasNonsingularReduction_of_good hΔ P

variable (W) in

theorem nonIntegralLocus_le_zeroComponentSubgroup :
    W.nonIntegralLocus ≤ W.zeroComponentSubgroup := fun _ hP =>
  W.hasNonsingularReduction_of_mem_nonIntegralLocus hP

end Carrier

end WeierstrassCurve


