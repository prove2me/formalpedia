-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclicPermEigenCount
-- name    : OddOrder_GroupTheory_RepresentationTheory_CyclicPermEigenCount
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:21.356198+00:00
-- url     : https://prove2.me/theorems/ceb8e254-cbb3-48e0-97ae-cd1a33827b57
-- title:
--   Eigenspace count for a monomial permutation operator (orbit assembly of BG (2.11))
-- statement:
--   The orbit assembly for the keystone $\dim E_0=\dim E_m+1$ of (2.11) in Bender–Glauberman, *Local Analysis for the Odd Order Theorem*. It treats an operator $T$ acting monomially with respect to a basis and a permutation $\sigma$ with $\sigma^h=1$, $T^h=1$, over a field with a primitive $h$-th root of unity, and counts eigenspace dimensions orbit by orbit, with a distinguished $\sigma$-fixed point.
--
--   The main declaration: `orbitSetoid`.
--
--   The bundle also proves 13 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CyclicPermEigenCount.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CyclicPermEigenCount.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclicShiftEigenspace

namespace OddOrder.RepresentationTheory

open Finset EigenspaceUnderCyclicAction Module

namespace CyclicPermEigen

variable {κ : Type*}

variable (σ : Equiv.Perm κ) {h : ℕ} [NeZero h]

/-- Composing two `ZMod h`-indexed powers of `σ` adds the indices (mod `h`), since `σ^h = 1`. -/
theorem perm_pow_val_add (hσ : σ ^ h = 1) (a b : ZMod h) (c : κ) :
    (σ ^ a.val) ((σ ^ b.val) c) = (σ ^ (a + b).val) c := by
  rw [← Equiv.Perm.mul_apply, ← pow_add]
  have hmod : a.val + b.val ≡ (a + b).val [MOD h] := by
    rw [ZMod.val_add]; exact (Nat.mod_modEq _ _).symm
  rw [pow_eq_pow_of_modEq hσ hmod]

/-- Two indices are in the same `σ`-orbit (parametrised by `ZMod h`): `c ~ c'` iff
`σ^{k} c = c'` for some `k : ZMod h`.  An equivalence relation once `σ^h = 1`. -/
def orbitSetoid (hσ : σ ^ h = 1) : Setoid κ where
  r c c' := ∃ k : ZMod h, (σ ^ k.val) c = c'
  iseqv := by
    refine ⟨fun c => ⟨0, by simp⟩, ?_, ?_⟩
    · rintro c c' ⟨k, hk⟩
      exact ⟨-k, by rw [← hk, perm_pow_val_add σ hσ (-k) k c]; simp⟩
    · rintro c c' c'' ⟨k, hk⟩ ⟨l, hl⟩
      exact ⟨l + k, by rw [← perm_pow_val_add σ hσ l k c, hk, hl]⟩

variable {F : Type*} [Field F]

/-- `∑_{k : ZMod h} ζ^{k} = 0` for a root of unity `ζ ≠ 1` (`ζ^h = 1`): multiplying the sum
by `ζ` permutes the summands (`Equiv.addRight 1`), so `(ζ − 1)·sum = 0`. -/
theorem sum_pow_val_eq_zero {ζ : F} (hζh : ζ ^ h = 1) (hζ : ζ ≠ 1) :
    ∑ k : ZMod h, ζ ^ k.val = 0 := by
  have hstep : ∀ k : ZMod h, ζ ^ (k.val + 1) = ζ ^ (k + 1).val := by
    intro k
    refine pow_eq_pow_of_modEq hζh ((ZMod.natCast_eq_natCast_iff _ _ _).1 ?_)
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_rightInverse k, ZMod.natCast_rightInverse (k + 1)]
  have key : ζ * ∑ k : ZMod h, ζ ^ k.val = ∑ k : ZMod h, ζ ^ k.val := by
    rw [Finset.mul_sum]
    calc ∑ k : ZMod h, ζ * ζ ^ k.val
        = ∑ k : ZMod h, ζ ^ (k.val + 1) := by simp_rw [pow_succ']
      _ = ∑ k : ZMod h, ζ ^ (k + 1).val := Finset.sum_congr rfl fun k _ => hstep k
      _ = ∑ k : ZMod h, ζ ^ k.val :=
        Equiv.sum_comp (Equiv.addRight (1 : ZMod h)) fun k => ζ ^ k.val
  have hsub : (ζ - 1) * ∑ k : ZMod h, ζ ^ k.val = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 hsub).resolve_left (sub_ne_zero.2 hζ)

/-- `∑_{k : ZMod h} 1 = h`. -/
theorem sum_one_eq_card : ∑ _k : ZMod h, (1 : F) = (h : F) := by
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

variable {W : Type*} [AddCommGroup W] [Module F W]

/-- A power of an operator fixes any vector it fixes. -/
theorem pow_apply_fixed (T : Module.End F W) {v : W} (hv : T v = v) (n : ℕ) : (T ^ n) v = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, hv, ih]

/-- If `T^h = 1` (`h ≠ 0`) then every power `T^k` is injective: `T^{k(h-1)}` is a left inverse. -/
theorem pow_injective (T : Module.End F W) (hTh : T ^ h = 1) (k : ℕ) :
    Function.Injective (T ^ k) := by
  have hinv : (T ^ (k * (h - 1))) * (T ^ k) = 1 := by
    rw [← pow_add,
      show k * (h - 1) + k = h * k by
        conv_rhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne h))]
        ring,
      pow_mul, hTh, one_pow]
  intro x y hxy
  have h2 := congrArg (T ^ (k * (h - 1))) hxy
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, hinv, Module.End.one_apply,
    Module.End.one_apply] at h2

variable {κ : Type*} (b : Basis κ F W) (T : Module.End F W) (σ : Equiv.Perm κ)

/-- **Off-orbit coordinates vanish.** If `c'` is not in the `σ`-orbit of `c`, the Fourier
projection of `b c` has zero `c'`-coordinate (each summand `T^{k}(b c)` is supported on
`b (σ^k c)`). -/
theorem repr_sum_fourier_orbit_zero
    (hmon : ∀ (k : ℕ) (c : κ), ∃ a : F, (T ^ k) (b c) = a • b ((σ ^ k) c))
    {ε : F} {m : ℕ} {c c' : κ} (hcc' : ∀ k : ZMod h, (σ ^ k.val) c ≠ c') :
    b.repr (∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val) • (T ^ k.val) (b c)) c' = 0 := by
  classical
  rw [map_sum]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  obtain ⟨a, ha⟩ := hmon k.val c
  rw [ha]
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]
  rw [if_neg (hcc' k), mul_zero, mul_zero]

/-- **Diagonal coordinate is `1` on a free orbit.** If the `σ`-orbit of `c` is free
(`σ^{k} c = c ⟹ k = 0`), the Fourier projection of `b c` has `c`-coordinate `1` (only the `k = 0`
summand `b c` contributes). -/
theorem repr_sum_fourier_self_free
    (hmon : ∀ (k : ℕ) (c : κ), ∃ a : F, (T ^ k) (b c) = a • b ((σ ^ k) c))
    {ε : F} {m : ℕ} {c : κ} (hfree : ∀ k : ZMod h, (σ ^ k.val) c = c → k = 0) :
    b.repr (∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val) • (T ^ k.val) (b c)) c = 1 := by
  classical
  rw [map_sum]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single (0 : ZMod h)]
  · simp only [ZMod.val_zero, pow_zero, one_smul, Module.End.one_apply,
      Basis.repr_self, Finsupp.single_eq_same]
  · intro k _ hk
    obtain ⟨a, ha⟩ := hmon k.val c
    rw [ha]
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, Basis.repr_self, Finsupp.single_apply,
      smul_eq_mul]
    rw [if_neg (fun heq => hk (hfree k heq)), mul_zero, mul_zero]
  · intro hc0; exact absurd (Finset.mem_univ _) hc0

/-- **The Fourier projection of a fixed point is a scalar multiple of it.** If `T (b c₀) = b c₀`
(eigenvalue `1`), then `∑_k (ε^m)⁻¹^{k} • T^{k}(b c₀) = (∑_k (ε^m)⁻¹^{k}) • b c₀`.
-/
theorem sum_fourier_fixed_eq (T : Module.End F W)
    {c₀ : κ} (hc₀ : T (b c₀) = b c₀) {ε : F} (m : ℕ) :
    (∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val) • (T ^ k.val) (b c₀))
      = (∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val)) • b c₀ := by
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_apply_fixed T hc₀]

/-- **`E_m` is spanned by the Fourier projections of the basis** (`range_sum_pow_eq_eigenspace`
applied to a basis): `T.eigenspace (ε^m) = span {∑_k (ε^m)⁻¹^{k} • T^{k}(b c) : c}`. -/
theorem eigenspace_eq_span_fourier (b : Basis κ F W) (T : Module.End F W)
    {ε : F} (hε : ε ≠ 0) (hεh : ε ^ h = 1) (hTh : T ^ h = 1) (hh : (h : F) ≠ 0) (m : ℕ) :
    Module.End.eigenspace T (ε ^ m)
      = Submodule.span F (Set.range fun c : κ =>
          ∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val) • (T ^ k.val) (b c)) := by
  have hop : (fun c : κ => ∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val) • (T ^ k.val) (b c))
      = fun c => (∑ k : ZMod h, ((ε ^ m)⁻¹ ^ k.val) • T ^ k.val) (b c) := by
    funext c; simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [hop, ← range_sum_pow_eq_eigenspace T hε hεh hTh hh m, LinearMap.range_eq_map,
    ← b.span_eq, Submodule.map_span, ← Set.range_comp]
  rfl

/-- **Orbit proportionality.** If `c` lies in the `σ`-orbit of `c'`, the Fourier projection of
`b c` is a scalar multiple of that of `b c'` (`sum_pow_smul_pow_comm` + `T^k` invertible).  Hence
the span over all of `κ` collapses onto orbit representatives. -/
theorem fourier_mem_span_rep (b : Basis κ F W) (T : Module.End F W) (σ : Equiv.Perm κ)
    (hmon : ∀ (k : ℕ) (c : κ), ∃ a : F, (T ^ k) (b c) = a • b ((σ ^ k) c))
    (hTh : T ^ h = 1)
    {ε : F} (hε : ε ≠ 0) (hεh : ε ^ h = 1) (m : ℕ) {c c' : κ}
    (hcc' : ∃ k : ZMod h, (σ ^ k.val) c' = c) :
    (∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b c))
      ∈ Submodule.span F {∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b c')} := by
  obtain ⟨k, hk⟩ := hcc'
  obtain ⟨a, ha⟩ := hmon k.val c'
  rw [hk] at ha
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ha
    exact b.ne_zero c' (pow_injective T hTh k.val (by rw [ha, map_zero]))
  have hbc : b c = a⁻¹ • (T ^ k.val) (b c') := by
    rw [ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  have heq : (∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b c))
      = a⁻¹ • ∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) ((T ^ k.val) (b c')) := by
    rw [hbc]
    simp only [map_smul]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  rw [heq, sum_pow_smul_pow_comm T hε hεh hTh (b c') m k.val]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

/-- **The Fourier-projected representatives form a basis of `E_m`.** Given an index `I` and
`rep : I → κ` such that the projections span `E_m` (`hspan`), have nonzero diagonal coordinate
(`hdiag`), and vanish off-diagonal (`hoff`), then `finrank E_m = card I`. -/
theorem finrank_eigenspace_eq_card (b : Basis κ F W) (T : Module.End F W) {ε : F} {m : ℕ}
    {I : Type*} [Fintype I] (rep : I → κ)
    (hspan : Module.End.eigenspace T (ε ^ m) = Submodule.span F (Set.range fun i =>
      ∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b (rep i))))
    (hdiag : ∀ i, b.repr (∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b (rep i))) (rep i) ≠ 0)
    (hoff : ∀ i i', i ≠ i' →
      b.repr (∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b (rep i))) (rep i') = 0) :
    Module.finrank F (Module.End.eigenspace T (ε ^ m)) = Fintype.card I := by
  have hli : LinearIndependent F
      (fun i => ∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b (rep i))) :=
    linearIndependent_of_triangular b _ rep hdiag hoff
  rw [hspan, finrank_span_eq_card hli]

/-- **General orbit count** (issue 0106, publicized from the `count` block of
`finrank_eigenspace_fixed_succ`): `dim E_{ε^m} = #(contributing orbits)`.  Given a `Finset S`
of orbit representatives such that

* every index is either in the orbit of some `s ∈ S` or has vanishing Fourier projection
  (`hcover`) — so `S` carries every contributing orbit,
* distinct elements of `S` lie in distinct orbits (`hdisj`), and
* each `s ∈ S` has nonzero diagonal Fourier coordinate (`hdiag` — supplied by
  `repr_sum_fourier_self_free` for free orbits, `repr_sum_fourier_self_partial_of_pow_eq_one`
  for partial-period orbits of a plain permutation),

the `ε^m`-eigenspace of `T` has dimension exactly `S.card`. -/
theorem finrank_eigenspace_eq_card_contributing [Finite κ]
    (b : Basis κ F W) (T : Module.End F W) (σ : Equiv.Perm κ)
    (hmon : ∀ (k : ℕ) (c : κ), ∃ a : F, (T ^ k) (b c) = a • b ((σ ^ k) c))
    (hTh : T ^ h = 1)
    {ε : F} (hε : ε ≠ 0) (hεh : ε ^ h = 1) (hh : (h : F) ≠ 0) (m : ℕ)
    (S : Finset κ)
    (hcover : ∀ c : κ, (∃ s ∈ S, ∃ k : ZMod h, (σ ^ k.val) s = c) ∨
      (∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b c)) = 0)
    (hdisj : ∀ s ∈ S, ∀ s' ∈ S, (∃ k : ZMod h, (σ ^ k.val) s = s') → s = s')
    (hdiag : ∀ s ∈ S,
      b.repr (∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b s)) s ≠ 0) :
    Module.finrank F (Module.End.eigenspace T (ε ^ m)) = S.card := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  have hspan : Module.End.eigenspace T (ε ^ m) = Submodule.span F (Set.range fun i : ↥S =>
      ∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b (i : κ))) := by
    rw [eigenspace_eq_span_fourier b T hε hεh hTh hh m]
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨c, rfl⟩
      rcases hcover c with ⟨s, hsS, hk⟩ | hzero
      · refine Submodule.span_mono ?_ (fourier_mem_span_rep b T σ hmon hTh hε hεh m hk)
        rw [Set.singleton_subset_iff]
        exact ⟨⟨s, hsS⟩, rfl⟩
      · change (∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b c)) ∈ _
        rw [hzero]
        exact Submodule.zero_mem _
    · rintro _ ⟨i, rfl⟩; exact ⟨(i : κ), rfl⟩
  have hoff : ∀ i i' : ↥S, i ≠ i' →
      b.repr (∑ l : ZMod h, ((ε ^ m)⁻¹ ^ l.val) • (T ^ l.val) (b (i : κ))) (i' : κ) = 0 := by
    rintro ⟨s, hsS⟩ ⟨s', hs'S⟩ hne
    refine repr_sum_fourier_orbit_zero b T σ hmon (fun k hk => ?_)
    exact (fun h => hne (Subtype.ext h)) (hdisj s hsS s' hs'S ⟨k, hk⟩)
  have hcard := finrank_eigenspace_eq_card b T (Subtype.val : ↥S → κ) hspan
    (fun i => hdiag (i : κ) i.2) hoff
  rw [hcard, Fintype.card_coe]

/-- **Keystone (BG (2.11)).** For a monomial permutation operator `T` on `b : Basis κ F W`
(`T^k (b c) = a • b (σ^k c)`) with `σ^h = 1`, `T^h = 1`, `ε` a primitive `h`-th root, `char ∤ h`,
a `σ`-fixed `c₀` with `T (b c₀) = b c₀` whose orbit is the *only* non-free one
(every `c ≠ c₀` lies in a free orbit), the `ε`-eigenspaces of the conjugation `T` satisfy
`dim (E_{ε^0}) = dim (E_{ε^m}) + 1` for every `m` with `ε^m ≠ 1`.

`E_{ε^m}` is spanned by the Fourier projections of the orbit representatives
(`eigenspace_eq_span_fourier` + `fourier_mem_span_rep`); these are independent (disjoint orbit
support); so `dim E_{ε^m}` equals the number of *contributing* orbits — every orbit for `ε^0 = 1`,
all but the `c₀`-orbit for `ε^m ≠ 1` (where the fixed point projects to `0`). The orbit count
cancels, leaving the difference `1`. -/
theorem finrank_eigenspace_fixed_succ [Finite κ]
    (b : Basis κ F W) (T : Module.End F W) (σ : Equiv.Perm κ)
    (hmon : ∀ (k : ℕ) (c : κ), ∃ a : F, (T ^ k) (b c) = a • b ((σ ^ k) c))
    (hσ : σ ^ h = 1) (hTh : T ^ h = 1)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    {c₀ : κ} (hc₀ : T (b c₀) = b c₀) (hfixσ : σ c₀ = c₀)
    (hfree : ∀ c : κ, c ≠ c₀ → ∀ k : ZMod h, (σ ^ k.val) c = c → k = 0)
    {m : ℕ} (hm : ε ^ m ≠ 1) :
    Module.finrank F (Module.End.eigenspace T (ε ^ 0))
      = Module.finrank F (Module.End.eigenspace T (ε ^ m)) + 1 := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  let inst : Setoid κ := orbitSetoid σ hσ
  have hε0 : ε ≠ 0 := hprim.ne_zero (NeZero.ne h)
  have hεh : ε ^ h = 1 := hprim.pow_eq_one
  set rep : κ → κ := fun c => (Quotient.mk inst c).out with hrepdef
  have hmk_rep : ∀ c, Quotient.mk inst (rep c) = Quotient.mk inst c := fun c => Quotient.out_eq _
  have hrep_equiv : ∀ c, ∃ k : ZMod h, (σ ^ k.val) (rep c) = c :=
    fun c => Quotient.exact (hmk_rep c)
  have hrep_idem : ∀ c, rep (rep c) = rep c := fun c => by
    change (Quotient.mk inst (rep c)).out = (Quotient.mk inst c).out
    rw [hmk_rep]
  -- `c₀` is fixed by every power of `σ`.
  have hc₀pow : ∀ n : ℕ, (σ ^ n) c₀ = c₀ := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, Equiv.Perm.mul_apply, hfixσ, ih]
  -- `c₀` is its own representative, and the only element mapping to it.
  have hrep_c₀ : rep c₀ = c₀ := by
    obtain ⟨k, hk⟩ := hrep_equiv c₀
    exact (σ ^ k.val).injective (by rw [hk, hc₀pow k.val])
  have honly_c₀ : ∀ c, rep c = c₀ → c = c₀ := by
    intro c hc
    obtain ⟨k, hk⟩ := hrep_equiv c
    rw [hc] at hk
    rw [← hk, hc₀pow k.val]
  -- distinct representatives lie in distinct orbits
  have hdistinct : ∀ c c' : κ, rep c = c → rep c' = c' →
      (∃ k : ZMod h, (σ ^ k.val) c = c') → c = c' := by
    intro c c' hc hc' hcc'
    have : Quotient.mk inst c = Quotient.mk inst c' := Quotient.sound hcc'
    calc c = rep c := hc.symm
      _ = (Quotient.mk inst c).out := rfl
      _ = (Quotient.mk inst c').out := by rw [this]
      _ = rep c' := rfl
      _ = c' := hc'
  -- the fixed point projects to `0` for a nontrivial character
  have hg_c₀_zero : ∀ m', ε ^ m' ≠ 1 →
      (∑ l : ZMod h, ((ε ^ m')⁻¹ ^ l.val) • (T ^ l.val) (b c₀)) = 0 := by
    intro m' hm'
    have hroot : ((ε ^ m')⁻¹) ^ h = 1 := by
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hεh, one_pow, inv_one]
    have hne1 : (ε ^ m')⁻¹ ≠ 1 := by rw [ne_eq, inv_eq_one]; exact hm'
    rw [sum_fourier_fixed_eq b T hc₀ m', sum_pow_val_eq_zero hroot hne1, zero_smul]
  -- per-character count: `dim E_{ε^m'} = #{contributing orbit reps}`
  -- (delegated to `finrank_eigenspace_eq_card_contributing`, issue 0106)
  have count : ∀ m' : ℕ, Module.finrank F (Module.End.eigenspace T (ε ^ m'))
      = (Finset.univ.filter (fun c => rep c = c ∧ (ε ^ m' = 1 ∨ c ≠ c₀))).card := by
    intro m'
    set S : Finset κ := Finset.univ.filter (fun c => rep c = c ∧ (ε ^ m' = 1 ∨ c ≠ c₀)) with hSdef
    have hSmem : ∀ c, c ∈ S ↔ rep c = c ∧ (ε ^ m' = 1 ∨ c ≠ c₀) := by
      intro c; rw [hSdef, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ c)
    refine finrank_eigenspace_eq_card_contributing b T σ hmon hTh hε0 hεh hh m' S ?_ ?_ ?_
    · intro c
      by_cases hm1 : ε ^ m' = 1
      · exact Or.inl ⟨rep c, (hSmem _).2 ⟨hrep_idem c, Or.inl hm1⟩, hrep_equiv c⟩
      · by_cases hc0 : rep c = c₀
        · exact Or.inr (by rw [honly_c₀ c hc0]; exact hg_c₀_zero m' hm1)
        · exact Or.inl ⟨rep c, (hSmem _).2 ⟨hrep_idem c, Or.inr hc0⟩, hrep_equiv c⟩
    · intro s hsS s' hs'S hss'
      exact hdistinct s s' ((hSmem s).mp hsS).1 ((hSmem s').mp hs'S).1 hss'
    · intro s hsS
      rw [hSmem] at hsS
      by_cases hc0 : s = c₀
      · subst hc0
        have hm1 : ε ^ m' = 1 := hsS.2.resolve_right (by simp)
        rw [sum_fourier_fixed_eq b T hc₀ m', hm1, inv_one]
        simp only [one_pow]
        rw [sum_one_eq_card]
        simp only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
          smul_eq_mul, mul_one]
        exact hh
      · rw [repr_sum_fourier_self_free b T σ hmon (hfree s hc0)]; exact one_ne_zero
  -- combine the two counts; the total orbit count cancels.
  rw [count 0, count m]
  have hPeq : (Finset.univ.filter (fun c => rep c = c ∧ (ε ^ 0 = 1 ∨ c ≠ c₀)))
      = Finset.univ.filter (fun c => rep c = c) :=
    Finset.filter_congr fun c _ => by simp [pow_zero]
  have hQeq : (Finset.univ.filter (fun c => rep c = c ∧ (ε ^ m = 1 ∨ c ≠ c₀)))
      = Finset.univ.filter (fun c => rep c = c ∧ c ≠ c₀) :=
    Finset.filter_congr fun c _ => by simp only [hm, false_or]
  rw [hPeq, hQeq]
  have hins : Finset.univ.filter (fun c => rep c = c)
      = insert c₀ (Finset.univ.filter (fun c => rep c = c ∧ c ≠ c₀)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hc
      by_cases h : c = c₀
      · exact Or.inl h
      · exact Or.inr ⟨hc, h⟩
    · rintro (rfl | ⟨hc, _⟩)
      · exact hrep_c₀
      · exact hc
  have hnotmem : c₀ ∉ Finset.univ.filter (fun c => rep c = c ∧ c ≠ c₀) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    exact fun _ h => absurd rfl h
  rw [hins, Finset.card_insert_of_notMem hnotmem]

end CyclicPermEigen

end OddOrder.RepresentationTheory


