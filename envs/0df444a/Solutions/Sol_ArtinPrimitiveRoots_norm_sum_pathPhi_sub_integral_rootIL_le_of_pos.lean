-- Prove2me | solution 1 for ArtinPrimitiveRoots.norm_sum_pathPhi_sub_integral_rootIL_le_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:45:55.079434+00:00
-- url     : https://prove2.me/submissions/c9e48b2d-cd0b-4699-bc62-e31b181ea36a

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_abs_card_specialLinearGroup_box_sub_le
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare

section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

end ArtinPrimitiveRoots
end

section
/-! # L102D_MemDefs — alias of the bundle `Def_ArtinMemoryModel` (round 5)

The memory model (root coordinates, `pathPhi`, `rootIL`, the memory space, `ghostOp`, `edgeOp`,
`memMomentD`, `dyadParams`, and `MemParams.RootIn`) now lives in
`Definitions/Def_ArtinMemoryModel.lean` (same declarations, same names). -/
end

section
/-! # L102K: the Kloosterman fourth moment ([21] Lemma 3.3, (3.24))

`K_m(h, k) = ∑_{y ∈ (ℤ/m)ˣ} e((h y + k y⁻¹)/m)`. Orthogonality gives
`∑_{h,k} |K_m(h,k)|⁴ = m² T_m`, where `T_m` counts unit quadruples with equal sums and equal
inverse sums, and `T_m ≤ 2 τ₃(m) m²`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset

noncomputable section

/-! ### The pointwise bound -/

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: the Euler-factor average and the constant `1/ζ(2)`

`P(S) = ∑_{(l,S)=1} μ(l)/l²` and `J(S) = ∑_{d ∣ S} μ(d)/d²` satisfy `J(S) P(S) = 6/π²`, and
`∑_{A ≤ u < B, u ≡ u₀ (S)} ∑_{l ∣ u, (l,S)=1} μ(l)/l = (B − A)/S · P(S) + O(1 + log B)`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: `|SL₂(ℤ/S)| = S³ ∑_{d ∣ S} μ(d)/d²` ([21] (3.29))

Unimodular columns are counted by Möbius inversion (`#{d ∣ u, d ∣ v} = (S/d)²`), and each
unimodular column has exactly `S` completions. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/-- A column `(u, v)` is unimodular iff `(u, v, S) = 1`. -/
lemma exists_completion_iff (S : ℕ) [NeZero S] (u v : ZMod S) :
    (∃ c d : ZMod S, u * d - c * v = 1) ↔ Nat.gcd (Nat.gcd u.val v.val) S = 1 := by
  set g := Nat.gcd (Nat.gcd u.val v.val) S with hg
  constructor
  · rintro ⟨c, d, h⟩
    have hgS : g ∣ S := Nat.gcd_dvd_right _ _
    let π := ZMod.castHom hgS (ZMod g)
    have hu : π u = 0 := by
      have : π u = ((u.val : ℕ) : ZMod g) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val u]
        rw [map_natCast]
      rw [this, ZMod.natCast_eq_zero_iff]
      exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hv : π v = 0 := by
      have : π v = ((v.val : ℕ) : ZMod g) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val v]
        rw [map_natCast]
      rw [this, ZMod.natCast_eq_zero_iff]
      exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have h1 := congrArg π h
    rw [map_sub, map_mul, map_mul, hu, hv, map_one] at h1
    simp only [zero_mul, mul_zero, sub_zero] at h1
    have h01 : (0 : ZMod g) = 1 := h1
    have := ZMod.natCast_self g
    by_contra hne
    have hg1 : 1 < g ∨ g = 0 := by omega
    rcases hg1 with hg1 | hg0
    · have : Fact (1 < g) := ⟨hg1⟩
      exact zero_ne_one h01
    · have h0 : Nat.gcd (Nat.gcd u.val v.val) S = 0 := hg0
      exact NeZero.ne S (Nat.gcd_eq_zero_iff.mp h0).2
  · intro h1
    -- Bezout in `ℤ`
    have hcop : IsCoprime ((Nat.gcd u.val v.val : ℕ) : ℤ) (S : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]; exact h1
    obtain ⟨a, b, hab⟩ := hcop
    obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, ((Nat.gcd u.val v.val : ℕ) : ℤ) = x * u.val + y * v.val := by
      refine ⟨Nat.gcdA u.val v.val, Nat.gcdB u.val v.val, ?_⟩
      rw [Nat.gcd_eq_gcd_ab]; ring
    refine ⟨-((a * y : ℤ) : ZMod S), ((a * x : ℤ) : ZMod S), ?_⟩
    have h2 : (((a * (x * u.val + y * v.val) + b * S : ℤ)) : ZMod S) = 1 := by
      rw [← hxy, hab]; simp
    push_cast at h2
    rw [ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2
    rw [← h2]; push_cast; ring

/-- A unimodular column has exactly `S` completions. -/
lemma card_completions (S : ℕ) [NeZero S] (u v : ZMod S) (c₀ d₀ : ZMod S)
    (h₀ : u * d₀ - c₀ * v = 1) :
    #((univ : Finset (ZMod S × ZMod S)).filter (fun q => u * q.2 - q.1 * v = 1)) = S := by
  classical
  suffices h : #(univ : Finset (ZMod S)) =
      #((univ : Finset (ZMod S × ZMod S)).filter (fun q => u * q.2 - q.1 * v = 1)) by
    rw [← h, Finset.card_univ, ZMod.card]
  refine Finset.card_bij (fun t _ => (c₀ + t * u, d₀ + t * v)) ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linear_combination h₀
  · intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    have e1 : (t - t') * u = 0 := by linear_combination h.1
    have e2 : (t - t') * v = 0 := by linear_combination h.2
    have : t - t' = 0 := by
      have : (t - t') * (u * d₀ - c₀ * v) = 0 := by linear_combination d₀ * e1 - c₀ * e2
      rwa [h₀, mul_one] at this
    exact sub_eq_zero.mp this
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨d₀ * (q.1 - c₀) - c₀ * (q.2 - d₀), Finset.mem_univ _, ?_⟩
    ext
    · simp only
      linear_combination q.1 * h₀ - c₀ * hq
    · simp only
      linear_combination q.2 * h₀ - d₀ * hq

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102E: the root basis and residue counting in `SL₂(ℤ/S)`

* `rootC u v` (`= c`, `c ≡ −v⁻¹ (mod u)`, `0 ≤ c < u`) and `rootD u v = (1 + v c)/u` complete a
  primitive `(u, v)` to `g = (u c; v d) ∈ SL₂(ℤ)`, and `rootRatio u v = c/u`.
* `crt_column`: for coprime `A₁, A₂` and a primitive `(z₁, N₀)` there are integers `α, β, x, y`
  with `A₁A₂ ∣ uα + cβ ⟺ (A₁ ∣ u ∧ A₂ ∣ u z₁ + c N₀)` and `A₁A₂ ∣ αx + βy − 1`.
* `card_filter_mul_zero_le`: `#{g₀ ∈ SL₂(ℤ/S) : (g₀N)₀₀ = 0} ≤ S²` for every `N`.
* `card_SL2_ge`: `|SL₂(ℤ/S)| ≥ (36/π⁴) S³` (from K's `card_SL2`, `JS_mul_PS`). -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset
open ArtinPrimitiveRoots

/-! ## The root basis -/

/-- `c ≡ −v⁻¹ (mod u)`, `0 ≤ c < u`. -/
noncomputable def rootC (u v : ℕ) : ℕ := (-(v : ZMod u)⁻¹ : ZMod u).val

/-- `d = (1 + v c)/u`. -/
noncomputable def rootD (u v : ℕ) : ℕ := (1 + v * rootC u v) / u

lemma rootRatio_eq (u v : ℕ) : rootRatio u v = (rootC u v : ℝ) / u := rfl

lemma rootC_lt {u : ℕ} (hu : 0 < u) (v : ℕ) : rootC u v < u := by
  have : NeZero u := ⟨hu.ne'⟩
  exact ZMod.val_lt _

lemma dvd_one_add_rootC {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    u ∣ 1 + v * rootC u v := by
  have : NeZero u := ⟨hu.ne'⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [rootC, ZMod.natCast_zmod_val, mul_neg, ZMod.coe_mul_inv_eq_one v hcop.symm]
  ring

lemma rootDet {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    (u : ℤ) * rootD u v - rootC u v * v = 1 := by
  have h := Nat.div_mul_cancel (dvd_one_add_rootC hu hcop)
  have : (u : ℤ) * (rootD u v : ℤ) = 1 + v * rootC u v := by
    unfold rootD; rw [mul_comm]; exact_mod_cast h
  rw [this]; ring

/-- The matrix `(u c; v d)`. -/
noncomputable def rootMat (u v : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(u : ℤ), (rootC u v : ℤ); (v : ℤ), (rootD u v : ℤ)]

lemma rootMat_det {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) : (rootMat u v).det = 1 := by
  rw [Matrix.det_fin_two]; simp only [rootMat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  exact rootDet hu hcop

/-- The root element `g ∈ SL₂(ℤ)` (the identity if `(u, v)` is not primitive). -/
noncomputable def rootG (u v : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  if h : (rootMat u v).det = 1 then (⟨rootMat u v, h⟩ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
  else 1

lemma rootG_coe {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    (rootG u v : Matrix (Fin 2) (Fin 2) ℤ) = rootMat u v := by
  simp [rootG, rootMat_det hu hcop]

lemma rootG_apply {u v : ℕ} (hu : 0 < u) (hcop : Nat.Coprime u v) :
    rootG u v 0 0 = u ∧ rootG u v 0 1 = rootC u v ∧ rootG u v 1 0 = v ∧
      rootG u v 1 1 = rootD u v := by
  have h := rootG_coe hu hcop
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h] <;> simp [rootMat]

/-! ## The CRT column -/

/-! ## Counting in `SL₂(ℤ/S)` -/

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): residue lines at a root

* `kerCode p u c` codes the line `{z : u z₁ + c z₂ = 0}` of `𝔽_p²` exactly as `lineOf` codes
  `[z]_p` (`p` for the line `z₁ = 0`, else `z₂/z₁`), so for primitive `z`
  `lineOf p z = kerCode p u c ↔ u z₁ + c z₂ = 0` (`lineOf_eq_kerCode_iff`).
* The physical oracle is a line condition: `physDelta P₀ p z ↔ lineOf p z = κ_p(P₀)` with
  `κ_p(P₀) = kerCode p u c`, `(u c; v d)` the completion of `P₀` (`physDelta_iff_lineOf`).
* **Equidistribution** (`sum_SL2_prod_rowCode`): for `S = ∏_{p ∈ Q} p` (distinct primes),
  `∑_{g ∈ SL₂(ℤ/S)} ∏_{p ∈ Q} f_p(κ_p(g)) = S ∏_{p ∈ Q} (p − 1) ∑_{λ ≤ p} f_p(λ)`
  (first rows with `S` completions each; CRT; `p − 1` rows per line). -/

namespace ArtinPrimitiveRoots.L102E

open Finset

/-- The code of the line `{u z₁ + c z₂ = 0}` of `𝔽_p²` in the coding of `lineOf`. -/
def kerCode (p : ℕ) (u c : ZMod p) : ℕ := if c = 0 then p else (-u * c⁻¹).val

lemma kerCode_le (p : ℕ) [NeZero p] (u c : ZMod p) : kerCode p u c ≤ p := by
  unfold kerCode; split_ifs
  · exact le_rfl
  · exact (ZMod.val_lt _).le

lemma lineOf_le (p : ℕ) [NeZero p] (z : ℤ × ℤ) : lineOf p z ≤ p := by
  unfold lineOf; split_ifs
  · exact le_rfl
  · exact (ZMod.val_lt _).le

lemma intCast_zmod_ne_zero_of_coprime {p : ℕ} (hp : p.Prime) {z : ℤ × ℤ}
    (hz : Int.gcd z.1 z.2 = 1) (h1 : (z.1 : ZMod p) = 0) : (z.2 : ZMod p) ≠ 0 := by
  intro h2
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
  have : (p : ℤ) ∣ (Int.gcd z.1 z.2 : ℤ) := Int.dvd_coe_gcd h1 h2
  rw [hz] at this
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact hp.one_lt.ne' (by exact_mod_cast this)

/-- For primitive `z` and `(u, c) ≠ 0`: `[z]_p` is the kernel line of `(u, c)` iff
`u z₁ + c z₂ = 0` in `𝔽_p`. -/
lemma lineOf_eq_kerCode_iff {p : ℕ} (hp : p.Prime) {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1)
    {u c : ZMod p} (huc : u ≠ 0 ∨ c ≠ 0) :
    lineOf p z = kerCode p u c ↔ u * (z.1 : ZMod p) + c * (z.2 : ZMod p) = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  unfold lineOf kerCode
  by_cases h1 : (p : ℤ) ∣ z.1
  · have hz1 : (z.1 : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h1
    have hz2 := intCast_zmod_ne_zero_of_coprime hp hz hz1
    rw [if_pos h1, hz1, mul_zero, zero_add]
    by_cases hc : c = 0
    · rw [if_pos hc, hc, zero_mul]; simp
    · rw [if_neg hc]
      constructor
      · intro h; exact absurd h.symm (ZMod.val_lt _).ne
      · intro h; exact absurd (mul_eq_zero.1 h) (by tauto)
  · have hz1 : (z.1 : ZMod p) ≠ 0 := fun h => h1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h)
    rw [if_neg h1]
    by_cases hc : c = 0
    · rw [if_pos hc, hc, zero_mul, add_zero]
      have hu : u ≠ 0 := by tauto
      constructor
      · intro h; exact absurd h (ZMod.val_lt _).ne
      · intro h; exact absurd (mul_eq_zero.1 h) (by tauto)
    · rw [if_neg hc]
      constructor
      · intro h
        have h' := ZMod.val_injective p h
        field_simp at h'
        linear_combination h'
      · intro h
        congr 1
        field_simp
        linear_combination h

/-- The line `κ_p` of a first row `(u, c)` over `ℤ/S`, reduced mod `p`. -/
def rowCode (S p : ℕ) (u c : ZMod S) : ℕ := kerCode p (u.val : ZMod p) (c.val : ZMod p)

/-- The line `κ_p(P₀)` of a primitive position. -/
noncomputable def rootCode (p : ℕ) (P₀ : ℕ × ℕ) : ℕ :=
  kerCode p (P₀.1 : ZMod p) ((rootC P₀.1 P₀.2 : ℕ) : ZMod p)

lemma physDelta_iff_lineOf {p : ℕ} (hp : p.Prime) {P₀ : ℕ × ℕ} (hu : 0 < P₀.1)
    (hcop : Nat.Coprime P₀.1 P₀.2) {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) :
    physDelta P₀ p z ↔ lineOf p z = rootCode p P₀ := by
  have hdet := rootDet hu hcop
  have huc : (P₀.1 : ZMod p) ≠ 0 ∨ ((rootC P₀.1 P₀.2 : ℕ) : ZMod p) ≠ 0 := by
    by_contra h
    push Not at h
    have e : ((((P₀.1 : ℤ) * rootD P₀.1 P₀.2 - rootC P₀.1 P₀.2 * P₀.2 : ℤ)) : ZMod p) = 0 := by
      push_cast; rw [h.1, h.2]; ring
    rw [hdet] at e
    have : Fact p.Prime := ⟨hp⟩
    simp at e
  unfold rootCode physDelta
  rw [lineOf_eq_kerCode_iff hp hz huc, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have : ((-(P₀.2 : ZMod P₀.1)⁻¹ : ZMod P₀.1).val : ℤ) = (rootC P₀.1 P₀.2 : ℤ) := rfl
  rw [this]
  push_cast
  rfl

/-! ## One prime: each line is the kernel of `p − 1` nonzero rows -/

lemma card_kerCode_fiber {p : ℕ} [NeZero p] (hp : p.Prime) (t : ℕ) (ht : t ≤ p) :
    ((univ : Finset (ZMod p × ZMod p)).filter fun y => y ≠ 0 ∧ kerCode p y.1 y.2 = t).card =
      p - 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  rcases ht.lt_or_eq with hlt | heq
  · -- `c ≠ 0`, `u = −λ c`
    have hset : (univ : Finset (ZMod p × ZMod p)).filter (fun y => y ≠ 0 ∧ kerCode p y.1 y.2 = t) =
        ((univ : Finset (ZMod p)).filter (· ≠ 0)).image fun c => (-(t : ZMod p) * c, c) := by
      ext ⟨u, c⟩
      simp only [mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
      unfold kerCode
      constructor
      · rintro ⟨hne, hk⟩
        by_cases hc : c = 0
        · rw [if_pos hc] at hk; omega
        · rw [if_neg hc] at hk
          refine ⟨c, hc, ?_, rfl⟩
          have h1 : ((t : ℕ) : ZMod p) = -u * c⁻¹ := by
            rw [← hk, ZMod.natCast_zmod_val]
          rw [h1]; field_simp
      · rintro ⟨c', hc', h1, rfl⟩
        refine ⟨fun h => hc' (Prod.mk.inj h).2, ?_⟩
        rw [if_neg hc', ← h1]
        have : -(-(t : ZMod p) * c') * c'⁻¹ = (t : ZMod p) := by field_simp
        rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    rw [hset, card_image_of_injective _ (fun c c' h => (Prod.mk.inj h).2)]
    rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  · -- `c = 0`, `u ≠ 0`
    subst heq
    have hset : (univ : Finset (ZMod t × ZMod t)).filter
        (fun y => y ≠ 0 ∧ kerCode t y.1 y.2 = t) =
        ((univ : Finset (ZMod t)).filter (· ≠ 0)).image fun u => (u, (0 : ZMod t)) := by
      ext ⟨u, c⟩
      simp only [mem_filter, mem_univ, true_and, mem_image, Prod.mk.injEq]
      unfold kerCode
      constructor
      · rintro ⟨hne, hk⟩
        by_cases hc : c = 0
        · refine ⟨u, fun hu => hne (by rw [hu, hc]; rfl), rfl, hc.symm⟩
        · rw [if_neg hc] at hk; exact absurd hk (ZMod.val_lt _).ne
      · rintro ⟨u', hu', rfl, rfl⟩
        exact ⟨fun h => hu' (Prod.mk.inj h).1, by simp⟩
    rw [hset, card_image_of_injective _ (fun u u' h => (Prod.mk.inj h).1)]
    rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]

lemma sum_rows_kerCode {p : ℕ} [NeZero p] (hp : p.Prime) (f : ℕ → ℝ) :
    ∑ y : ZMod p × ZMod p, (if y ≠ 0 then f (kerCode p y.1 y.2) else 0) =
      ((p : ℝ) - 1) * ∑ t ∈ range (p + 1), f t := by
  classical
  rw [← sum_filter]
  rw [← sum_fiberwise_of_maps_to (g := fun y : ZMod p × ZMod p => kerCode p y.1 y.2)
    (t := range (p + 1)) (fun y _ => mem_range.2 (Nat.lt_succ_of_le (kerCode_le p _ _)))]
  rw [mul_sum]
  refine sum_congr rfl fun t ht => ?_
  rw [filter_filter]
  have hc := card_kerCode_fiber hp t (Nat.lt_succ_iff.1 (mem_range.1 ht))
  rw [sum_congr rfl (g := fun _ => f t) fun y hy => by rw [(mem_filter.1 hy).2.2]]
  rw [sum_const, nsmul_eq_mul, hc]
  rw [Nat.cast_sub hp.one_le]; push_cast; ring

/-! ## `SL₂(ℤ/S)` through its first rows -/

/-- The matrix with rows `(x₁₁, x₁₂)`, `(x₂₁, x₂₂)`. -/
def rowMat {R : Type*} (x : (R × R) × (R × R)) : Matrix (Fin 2) (Fin 2) R :=
  !![x.1.1, x.1.2; x.2.1, x.2.2]

lemma rowMat_bijective (R : Type*) : Function.Bijective (rowMat (R := R)) := by
  constructor
  · intro x y h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp only [rowMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h01 h10 h11
    ext <;> assumption
  · intro M
    refine ⟨((M 0 0, M 0 1), (M 1 0, M 1 1)), ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> rfl

lemma sum_SL2_row (S : ℕ) [NeZero S] (G : ZMod S × ZMod S → ℝ) :
    ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), G (g 0 0, g 0 1) =
      ∑ y : ZMod S × ZMod S, (if ∃ v d : ZMod S, y.1 * d - v * y.2 = 1 then (S : ℝ) else 0) *
        G y := by
  classical
  have e1 : ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), G (g 0 0, g 0 1) =
      ∑ M : Matrix (Fin 2) (Fin 2) (ZMod S), if M.det = 1 then G (M 0 0, M 0 1) else 0 := by
    rw [← sum_filter]
    rw [Finset.sum_subtype (univ.filter fun M : Matrix (Fin 2) (Fin 2) (ZMod S) => M.det = 1)
      (p := fun M => M.det = 1) (fun M => by simp) (fun M => G (M 0 0, M 0 1))]
    exact Fintype.sum_equiv (Equiv.refl _) _ _ fun g => rfl
  rw [e1, ← Fintype.sum_bijective _ (rowMat_bijective (ZMod S)) _ _ fun _ => rfl]
  simp only [rowMat, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun y _ => ?_
  dsimp only
  rw [← sum_filter, sum_const, nsmul_eq_mul, Prod.mk.eta]
  congr 1
  split_ifs with h
  · obtain ⟨v, d, hvd⟩ := h
    have := L102K.card_completions S y.1 y.2 v d hvd
    have e : (univ.filter fun x : ZMod S × ZMod S => y.1 * x.2 - y.2 * x.1 = 1) =
        (univ.filter fun q : ZMod S × ZMod S => y.1 * q.2 - q.1 * y.2 = 1) := by
      congr 1; ext q; constructor <;> intro h <;> linear_combination h
    rw [e, this]
  · have e : (univ.filter fun x : ZMod S × ZMod S => y.1 * x.2 - y.2 * x.1 = 1) = ∅ := by
      refine filter_false_of_mem fun x _ hx => h ⟨x.1, x.2, by linear_combination hx⟩
    rw [e]; simp

/-! ## The Chinese remainder step -/

lemma pairwise_coprime_of_primes {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) :
    Pairwise (Function.onFun Nat.Coprime fun i : Q => (i : ℕ)) := by
  intro i j hij
  exact (Nat.coprime_primes (hQ _ i.2) (hQ _ j.2)).2 fun h => hij (Subtype.ext h)

lemma prod_primes_pos {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) : 0 < ∏ i : Q, (i : ℕ) :=
  prod_pos fun i _ => (hQ _ i.2).pos

/-- A first row over `ℤ/S` (`S` a product of distinct primes) has a completion iff it is nonzero
modulo every prime. -/
lemma unimod_iff {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) [NeZero (∏ i : Q, (i : ℕ))]
    (y : ZMod (∏ i : Q, (i : ℕ)) × ZMod (∏ i : Q, (i : ℕ))) :
    (∃ v d : ZMod (∏ i : Q, (i : ℕ)), y.1 * d - v * y.2 = 1) ↔
      ∀ i : Q, ((y.1.val : ZMod i), (y.2.val : ZMod i)) ≠ 0 := by
  rw [L102K.exists_completion_iff (∏ i : Q, (i : ℕ)) y.1 y.2]
  constructor
  · intro h i hi
    have h1 : (y.1.val : ZMod i) = 0 := congrArg Prod.fst hi
    have h2 : (y.2.val : ZMod i) = 0 := congrArg Prod.snd hi
    rw [ZMod.natCast_eq_zero_iff] at h1 h2
    have hiS : (i : ℕ) ∣ ∏ i : Q, (i : ℕ) := dvd_prod_of_mem (fun i : Q => (i : ℕ)) (mem_univ i)
    have : (i : ℕ) ∣ Nat.gcd (Nat.gcd y.1.val y.2.val) (∏ i : Q, (i : ℕ)) :=
      Nat.dvd_gcd (Nat.dvd_gcd h1 h2) hiS
    rw [h] at this
    exact (hQ _ i.2).one_lt.ne' (Nat.dvd_one.1 this)
  · intro h
    refine Nat.coprime_of_dvd fun k hk hk1 hkS => ?_
    obtain ⟨i, -, hki⟩ := (Nat.prime_iff.1 hk).dvd_finsetProd_iff (fun i : Q => (i : ℕ)) |>.1 hkS
    have hki' : k = i := (Nat.prime_dvd_prime_iff_eq hk (hQ _ i.2)).1 hki
    apply h i
    have h1 : k ∣ y.1.val := hk1.trans (Nat.gcd_dvd_left _ _)
    have h2 : k ∣ y.2.val := hk1.trans (Nat.gcd_dvd_right _ _)
    rw [hki'] at h1 h2
    ext
    · exact (ZMod.natCast_eq_zero_iff _ _).2 h1
    · exact (ZMod.natCast_eq_zero_iff _ _).2 h2

/-- **CRT**: a sum over `(ℤ/S)²` of a product of functions of the reductions mod `p ∈ Q`. -/
lemma sum_pairs_prod_crt {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) [NeZero (∏ i : Q, (i : ℕ))]
    [∀ i : Q, NeZero (i : ℕ)] (φ : (i : Q) → ZMod i × ZMod i → ℝ) :
    ∑ y : ZMod (∏ i : Q, (i : ℕ)) × ZMod (∏ i : Q, (i : ℕ)),
        ∏ i : Q, φ i ((y.1.val : ZMod i), (y.2.val : ZMod i)) =
      ∏ i : Q, ∑ w : ZMod i × ZMod i, φ i w := by
  classical
  set e := ZMod.prodEquivPi (fun i : Q => (i : ℕ)) (pairwise_coprime_of_primes hQ)
  have he : ∀ (u : ZMod (∏ i : Q, (i : ℕ))) (i : Q), e u i = (u.val : ZMod i) := by
    intro u i
    rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Fintype.sum_equiv ((Equiv.prodCongr e.toEquiv e.toEquiv).trans
    (Equiv.arrowProdEquivProdArrow _ _ _).symm) _ _ fun y => ?_
  refine prod_congr rfl fun i _ => ?_
  show φ i _ = φ i (e y.1 i, e y.2 i)
  rw [he, he]

/-- **Equidistribution of the lines in `SL₂(ℤ/S)`.** -/
theorem sum_SL2_prod_rowCode {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) [NeZero (∏ i : Q, (i : ℕ))]
    [∀ i : Q, NeZero (i : ℕ)] (f : ℕ → ℕ → ℝ) :
    ∑ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod (∏ i : Q, (i : ℕ))),
        ∏ i : Q, f i (rowCode (∏ i : Q, (i : ℕ)) i (g 0 0) (g 0 1)) =
      ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) *
        ∏ i : Q, ((((i : ℕ) : ℝ) - 1) * ∑ t ∈ range ((i : ℕ) + 1), f i t) := by
  classical
  set S := ∏ i : Q, (i : ℕ)
  rw [sum_SL2_row S (fun y => ∏ i : Q, f i (rowCode S i y.1 y.2))]
  have key : ∀ y : ZMod S × ZMod S,
      (if ∃ v d : ZMod S, y.1 * d - v * y.2 = 1 then (S : ℝ) else 0) *
          ∏ i : Q, f i (rowCode S i y.1 y.2) =
        (S : ℝ) * ∏ i : Q, (if ((y.1.val : ZMod i), (y.2.val : ZMod i)) ≠ 0 then
          f i (kerCode i (y.1.val : ZMod i) (y.2.val : ZMod i)) else 0) := by
    intro y
    by_cases h : ∃ v d : ZMod S, y.1 * d - v * y.2 = 1
    · rw [if_pos h, Finset.prod_ite_zero, if_pos (fun i _ => (unimod_iff hQ y).1 h i)]
      rfl
    · have h' : ¬ ∀ i ∈ (univ : Finset Q), ((y.1.val : ZMod i), (y.2.val : ZMod i)) ≠ 0 :=
        fun h'' => h ((unimod_iff hQ y).2 fun i => h'' i (mem_univ i))
      rw [if_neg h, zero_mul, Finset.prod_ite_zero, if_neg h', mul_zero]
  rw [sum_congr rfl fun y _ => key y, ← mul_sum]
  congr 1
  rw [sum_pairs_prod_crt hQ (fun i w => if w ≠ 0 then f i (kerCode i w.1 w.2) else 0)]
  exact prod_congr rfl fun i _ => sum_rows_kerCode (hQ _ i.2) (f i)

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): the path expansion of `pathPhi`

`physTail ω δ k f s = ∑_{cs : Fin k → steps} wNon · 1[archP ω] · visP δ · f(endSt)`, a step being
`(pr, z', nw)` (slot permutation of the source list, target position, new last labels), with

* `wNon` the root- and oracle-independent weight (`S`-average, `∏Vᵢ⁻¹`, `edgeMult`, the
  non-archimedean edge restrictions: injective source, ban, pad dyad, `D ∣ det`);
* `archP ω` the archimedean restrictions (box and goodness at both ends of every edge);
* `visP δ = ∏_{p ∈ 𝒢} hpP δ p` the visit factors, a product over the group primes.

(`symP_physTail`, `physTail_perm` are copied from prover D's `L102D_PathExp` to keep the import
chain light.) -/

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

namespace ArtinPrimitiveRoots.L102E

open Finset

namespace PE

variable (P : MemParams)

/-- Path states. -/
abbrev St := (ℤ × ℤ) × P.Lst

/-- A step: a slot permutation of the source list, the target position, the new labels. -/
abbrev Stp := (Fin P.K → Equiv.Perm (Fin (P.J + 1))) × (ℤ × ℤ) × (Fin P.K → ℕ)

/-- The admissible steps. -/
noncomputable def stepSet : Finset (Stp P) := univ ×ˢ (P.zSet ×ˢ Fintype.piFinset P.grp)

/-- The step type. -/
abbrev StepT := {c // c ∈ stepSet P}

/-- `ℓ ∘ pr` slotwise. -/
def permL (ℓ : P.Lst) (pr : Fin P.K → Equiv.Perm (Fin (P.J + 1))) : P.Lst := fun i => ℓ i ∘ pr i

/-- The next state. -/
def nxt (s : St P) (c : Stp P) : St P := (c.2.1, P.newList (permL P s.2 c.1) c.2.2)

/-- The non-archimedean edge restrictions. -/
def NonArch (s : St P) (c : Stp P) : Prop :=
  (∀ i, Function.Injective (permL P s.2 c.1 i)) ∧ (∀ i, c.2.2 i ∉ Set.range (permL P s.2 c.1 i)) ∧
    P.d₀ ≤ padProd (permL P s.2 c.1) ∧ padProd (permL P s.2 c.1) < 2 * P.d₀ ∧
    (padProd (permL P s.2 c.1) : ℤ) ∣ detZ s.1 c.2.1

/-- The archimedean edge restrictions. -/
def ArchStep (ω : ℝ × ℝ × ℝ) (s : St P) (c : Stp P) : Prop :=
  P.InBox ω s.1 ∧ P.InBox ω c.2.1 ∧ P.GoodAt ω s.1 (permL P s.2 c.1) ∧
    P.GoodAt ω c.2.1 (P.newList (permL P s.2 c.1) c.2.2)

lemma edgeOK_iff (ω : ℝ × ℝ × ℝ) (s : St P) (c : Stp P) :
    P.EdgeOK ω s.1 c.2.1 (permL P s.2 c.1) c.2.2 ↔ NonArch P s c ∧ ArchStep P ω s c := by
  unfold MemParams.EdgeOK NonArch ArchStep
  tauto

/-- The factorial normalization `((J+1)!^K)⁻¹`. -/
noncomputable def facInv : ℂ := ((((P.J + 1).factorial ^ P.K : ℕ) : ℂ))⁻¹

open Classical in
/-- The root-independent step weight. -/
noncomputable def stepNon (j : ℕ) (s : St P) (c : Stp P) : ℂ :=
  facInv P * (if NonArch P s c then ((∏ i, (P.Vg i)⁻¹ : ℝ) : ℂ) *
    P.edgeMult j (detZ s.1 c.2.1 / padProd (permL P s.2 c.1)) (∏ i, c.2.2 i)
      (lastProd (permL P s.2 c.1)) (padProd (permL P s.2 c.1)) else 0)

/-! ## Copies of D's permutation lemmas -/

lemma visitFac_perm (δ : ℕ → ℤ × ℤ → Prop) (j : ℕ) (z : ℤ × ℤ) (ℓ : P.Lst)
    (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))) :
    P.visitFac δ j (z, fun i => ℓ i ∘ σ i) = P.visitFac δ j (z, ℓ) := by
  classical
  unfold MemParams.visitFac MemParams.primeFac
  refine prod_congr rfl fun p _ => ?_
  have hiff : (∃ i k, (fun i => ℓ i ∘ σ i) i k = p) ↔ ∃ i k, ℓ i k = p := by
    constructor
    · rintro ⟨i, k, h⟩; exact ⟨i, σ i k, h⟩
    · rintro ⟨i, k, h⟩; exact ⟨i, (σ i).symm k, by simp [h]⟩
  simp only [hiff]

lemma listSym_perm (g : P.Lst → ℂ) (ℓ : P.Lst) (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))) :
    P.listSym g (fun i => ℓ i ∘ σ i) = P.listSym g ℓ := by
  unfold MemParams.listSym
  congr 1
  let e : (Fin P.K → Equiv.Perm (Fin (P.J + 1))) ≃ (Fin P.K → Equiv.Perm (Fin (P.J + 1))) :=
    Equiv.piCongrRight fun i => Equiv.mulLeft (σ i)
  refine Fintype.sum_equiv e _ _ fun pr => ?_
  congr 1

lemma physTail_perm (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) (k : ℕ)
    (f : (ℤ × ℤ) × P.Lst → ℂ)
    (hf : ∀ z ℓ (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))), f (z, fun i => ℓ i ∘ σ i) = f (z, ℓ))
    (z : ℤ × ℤ) (ℓ : P.Lst) (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))) :
    P.physTail ω δ k f (z, fun i => ℓ i ∘ σ i) = P.physTail ω δ k f (z, ℓ) := by
  cases k with
  | zero => simp only [MemParams.physTail, visitFac_perm, hf]
  | succ k =>
    simp only [MemParams.physTail, visitFac_perm]
    rw [show ∀ g : (ℤ × ℤ) × P.Lst → ℂ, P.symP g (z, fun i => ℓ i ∘ σ i) = P.symP g (z, ℓ) from
      fun g => listSym_perm P _ ℓ σ]

lemma symP_physTail (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) (k : ℕ)
    (f : (ℤ × ℤ) × P.Lst → ℂ)
    (hf : ∀ z ℓ (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))), f (z, fun i => ℓ i ∘ σ i) = f (z, ℓ)) :
    P.symP (P.physTail ω δ k f) = P.physTail ω δ k f := by
  funext s
  unfold MemParams.symP MemParams.listSym
  simp only [physTail_perm P ω δ k f hf]
  rw [sum_const, card_univ, Fintype.card_pi, prod_const, card_univ, Fintype.card_fin,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have : (((P.J + 1).factorial ^ P.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  field_simp

/-! ## One step -/

open Classical in
lemma physTail_succ_eq (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) (k : ℕ)
    (f : (ℤ × ℤ) × P.Lst → ℂ)
    (hf : ∀ z ℓ (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))), f (z, fun i => ℓ i ∘ σ i) = f (z, ℓ))
    (s : St P) :
    P.physTail ω δ (k + 1) f s = (P.visitFac δ (P.N - (k + 1)) s : ℂ) *
      ∑ c : StepT P, stepNon P (P.N - (k + 1)) s c.1 *
        (if ArchStep P ω s c.1 then 1 else 0) * P.physTail ω δ k f (nxt P s c.1) := by
  rw [MemParams.physTail, symP_physTail P ω δ k f hf]
  dsimp only
  congr 1
  unfold MemParams.symP MemParams.listSym MemParams.physEdge
  dsimp only
  rw [Finset.sum_coe_sort (stepSet P)
    (fun c : Stp P => stepNon P (P.N - (k + 1)) s c * (if ArchStep P ω s c then (1 : ℂ) else 0) *
      P.physTail ω δ k f (nxt P s c))]
  unfold stepSet
  rw [sum_product, mul_sum]
  refine sum_congr rfl fun pr _ => ?_
  rw [sum_product, mul_sum]
  refine sum_congr rfl fun z' _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun nw _ => ?_
  have hE : P.EdgeOK ω s.1 z' (fun i => s.2 i ∘ pr i) nw ↔
      NonArch P s (pr, z', nw) ∧ ArchStep P ω s (pr, z', nw) := edgeOK_iff P ω s (pr, z', nw)
  unfold stepNon facInv nxt permL
  simp only
  by_cases hN : NonArch P s (pr, z', nw) <;> by_cases hA : ArchStep P ω s (pr, z', nw)
  · rw [if_pos (hE.2 ⟨hN, hA⟩), if_pos hN, if_pos hA]; ring
  · rw [if_neg (fun h => hA (hE.1 h).2), if_pos hN, if_neg hA]; ring
  · rw [if_neg (fun h => hN (hE.1 h).1), if_neg hN]; ring
  · rw [if_neg (fun h => hN (hE.1 h).1), if_neg hN]; ring

/-! ## Paths -/

/-- The root-independent path weight. -/
noncomputable def wNon : (k : ℕ) → St P → (Fin k → StepT P) → ℂ
  | 0, _, _ => 1
  | k + 1, s, cs => stepNon P (P.N - (k + 1)) s (cs 0).1 * wNon k (nxt P s (cs 0).1) (Fin.tail cs)

/-- The archimedean path restrictions. -/
def archP (ω : ℝ × ℝ × ℝ) : (k : ℕ) → St P → (Fin k → StepT P) → Prop
  | 0, _, _ => True
  | k + 1, s, cs => ArchStep P ω s (cs 0).1 ∧ archP ω k (nxt P s (cs 0).1) (Fin.tail cs)

/-- The visit factors along a path. -/
noncomputable def visP (δ : ℕ → ℤ × ℤ → Prop) : (k : ℕ) → St P → (Fin k → StepT P) → ℝ
  | 0, s, _ => P.visitFac δ P.N s
  | k + 1, s, cs => P.visitFac δ (P.N - (k + 1)) s * visP δ k (nxt P s (cs 0).1) (Fin.tail cs)

/-- The end state of a path. -/
def endSt : (k : ℕ) → St P → (Fin k → StepT P) → St P
  | 0, s, _ => s
  | k + 1, s, cs => endSt k (nxt P s (cs 0).1) (Fin.tail cs)

lemma sum_fin_succ_paths {M : Type*} [AddCommMonoid M] (k : ℕ) (F : (Fin (k + 1) → StepT P) → M) :
    ∑ cs : Fin (k + 1) → StepT P, F cs =
      ∑ c : StepT P, ∑ cs : Fin k → StepT P, F (Fin.cons c cs) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => StepT P) _ _ fun _ => rfl).symm

open Classical in
/-- **The path expansion.** -/
theorem physTail_expand (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) (f : (ℤ × ℤ) × P.Lst → ℂ)
    (hf : ∀ z ℓ (σ : Fin P.K → Equiv.Perm (Fin (P.J + 1))), f (z, fun i => ℓ i ∘ σ i) = f (z, ℓ))
    (k : ℕ) (s : St P) :
    P.physTail ω δ k f s = ∑ cs : Fin k → StepT P, wNon P k s cs *
      (if archP P ω k s cs then 1 else 0) * (visP P δ k s cs : ℂ) * f (endSt P k s cs) := by
  induction k generalizing s with
  | zero =>
    rw [Fintype.sum_unique]
    simp [MemParams.physTail, wNon, archP, visP, endSt]
  | succ k ih =>
    rw [physTail_succ_eq P ω δ k f hf s, sum_fin_succ_paths, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [ih, mul_sum, mul_sum]
    refine sum_congr rfl fun cs _ => ?_
    simp only [wNon, archP, visP, endSt, Fin.cons_zero, Fin.tail_cons]
    by_cases h1 : ArchStep P ω s c.1 <;> by_cases h2 : archP P ω k (nxt P s c.1) cs <;>
      simp [h1, h2]; ring

/-! ## The visit factors prime by prime -/

/-- The factor of one prime along a path. -/
noncomputable def hpP (δ : ℕ → ℤ × ℤ → Prop) (p : ℕ) :
    (k : ℕ) → St P → (Fin k → StepT P) → ℝ
  | 0, s, _ => P.primeFac δ P.N p s
  | k + 1, s, cs => P.primeFac δ (P.N - (k + 1)) p s * hpP δ p k (nxt P s (cs 0).1) (Fin.tail cs)

lemma visP_eq_prod (δ : ℕ → ℤ × ℤ → Prop) (k : ℕ) (s : St P) (cs : Fin k → StepT P) :
    visP P δ k s cs = ∏ p ∈ P.gPrimes, hpP P δ p k s cs := by
  induction k generalizing s with
  | zero => simp [visP, hpP, MemParams.visitFac]
  | succ k ih =>
    simp only [visP, hpP, ih, MemParams.visitFac]
    rw [prod_mul_distrib]

lemma primeFac_congr {δ δ' : ℕ → ℤ × ℤ → Prop} {j p : ℕ} {s : St P}
    (h : δ p s.1 ↔ δ' p s.1) : P.primeFac δ j p s = P.primeFac δ' j p s := by
  classical
  unfold MemParams.primeFac
  simp only [h]

lemma nxt_fst (s : St P) (c : Stp P) : (nxt P s c).1 = c.2.1 := rfl

lemma gcd_of_mem_zSet {z : ℤ × ℤ} (h : z ∈ P.zSet) : Int.gcd z.1 z.2 = 1 := by
  unfold MemParams.zSet at h
  rw [mem_filter] at h
  exact h.2

lemma step_z_mem (c : StepT P) : c.1.2.1 ∈ P.zSet := by
  have hc := c.2
  unfold stepSet at hc
  exact (mem_product.1 (mem_product.1 hc).2).1

lemma step_nw_mem (c : StepT P) : c.1.2.2 ∈ Fintype.piFinset P.grp := by
  have hc := c.2
  unfold stepSet at hc
  exact (mem_product.1 (mem_product.1 hc).2).2

lemma hpP_congr {δ δ' : ℕ → ℤ × ℤ → Prop} {p : ℕ}
    (h : ∀ z : ℤ × ℤ, Int.gcd z.1 z.2 = 1 → (δ p z ↔ δ' p z)) (k : ℕ) (s : St P)
    (hs : Int.gcd s.1.1 s.1.2 = 1) (cs : Fin k → StepT P) :
    hpP P δ p k s cs = hpP P δ' p k s cs := by
  induction k generalizing s with
  | zero => exact primeFac_congr P (h _ hs)
  | succ k ih =>
    simp only [hpP]
    rw [primeFac_congr P (h _ hs)]
    congr 1
    have hz := gcd_of_mem_zSet P (step_z_mem P (cs 0))
    rw [← nxt_fst P s (cs 0).1] at hz
    exact ih _ hz _

/-- The line version: the factor of `p` when its line is `t`. -/
noncomputable def hpL (p t k : ℕ) (s : St P) (cs : Fin k → StepT P) : ℝ :=
  hpP P (fun _ z => lineOf p z = t) p k s cs

lemma primeFac_mem (δ : ℕ → ℤ × ℤ → Prop) (j p : ℕ) (s : St P) :
    0 ≤ P.primeFac δ j p s ∧ P.primeFac δ j p s ≤ 1 := by
  classical
  unfold MemParams.primeFac MemParams.qv
  split_ifs <;> norm_num

lemma hpP_mem (δ : ℕ → ℤ × ℤ → Prop) (p k : ℕ) (s : St P) (cs : Fin k → StepT P) :
    0 ≤ hpP P δ p k s cs ∧ hpP P δ p k s cs ≤ 1 := by
  induction k generalizing s with
  | zero => exact primeFac_mem P δ _ p s
  | succ k ih =>
    simp only [hpP]
    obtain ⟨h1, h2⟩ := primeFac_mem P δ (P.N - (k + 1)) p s
    obtain ⟨h3, h4⟩ := ih (nxt P s (cs 0).1) (Fin.tail cs)
    exact ⟨mul_nonneg h1 h3, mul_le_one₀ h2 h3 h4⟩

end PE

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102D: good positions and their measure ([21] §3.2, Lemma 3.2)

For lists `ℓ` of `M` primes in each group, the omission products `D` (omit one label per group),
the two good-state tests on a ratio `r ∈ ℝ/ℤ` (realized on `(0, 1]`), and Lemma 3.2: the set of
`r` failing goodness has measure at most `exp(-c L^{0.1})`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Distance to the nearest integer and its level sets -/

lemma circNorm_eq_norm (t : ℝ) : circNorm t = ‖(t : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]; rfl

lemma continuous_circNorm : Continuous circNorm := by
  have : circNorm = fun t : ℝ => ‖(t : UnitAddCircle)‖ := funext circNorm_eq_norm
  rw [this]
  exact continuous_norm.comp (AddCircle.continuous_mk' 1)

/-! ## Test (i): the union bound -/

/-! ## Markov's inequality for a finite weighted family of bad sets -/

/-! ## Test (ii): one fresh draw, then Markov over the fresh draws -/

lemma pos_of_mem_primeGroup {x b : ℝ} {p : ℕ} (h : p ∈ primeGroup x b) : 0 < p := by
  unfold primeGroup at h
  exact (Finset.mem_filter.1 h).2.1.pos

/-! ## Counting and asymptotics -/

lemma card_primeGroup_le (x b : ℝ) : ((primeGroup x b).card : ℝ) ≤ exp (2 * log x ^ b) + 1 := by
  unfold primeGroup
  have h1 := card_filter_le (range (⌊exp (2 * log x ^ b)⌋₊ + 1))
    (fun p : ℕ => p.Prime ∧ exp (log x ^ b) ≤ (p : ℝ))
  rw [card_range] at h1
  have h2 : ((⌊exp (2 * log x ^ b)⌋₊ : ℕ) : ℝ) ≤ exp (2 * log x ^ b) := Nat.floor_le (exp_pos _).le
  have h3 : (((range (⌊exp (2 * log x ^ b)⌋₊ + 1)).filter
      (fun p : ℕ => p.Prime ∧ exp (log x ^ b) ≤ (p : ℝ))).card : ℝ) ≤
      ((⌊exp (2 * log x ^ b)⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

/-! ## Lemma 3.2 -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102E (D7r): slab geometry

In normalized root coordinates `p = (u/U, v/V, r)` the box condition of a position `z` reads
`1 ≤ u τ ≤ 16`, `1 ≤ v τ + z₂/(UVu) ≤ 2` with `τ = z₁ + r z₂` (`inBox_norm`). On a slab
`r ∈ [r₀, r₀ + 1/n]`, `|τ(r) − τ(r₀)| ≤ Δ = Z/n` when `|z₂| ≤ Z`, so the region of a list of
positions is sandwiched between two rectangles in `(u, v)` whose side lengths differ by
`O(Δ + Z/(UV))` (`inner_sub`, `outer_sup`, `len_diff_*`). -/

namespace ArtinPrimitiveRoots.L102E

open Real

/-! ## Max and min over a list -/

/-- `max(b, max_{q ∈ L} f q)`. -/
def lmax {α : Type*} (L : List α) (f : α → ℝ) (b : ℝ) : ℝ := L.foldr (fun q acc => max (f q) acc) b

/-- `min(b, min_{q ∈ L} f q)`. -/
def lmin {α : Type*} (L : List α) (f : α → ℝ) (b : ℝ) : ℝ := L.foldr (fun q acc => min (f q) acc) b

section ListMax

variable {α : Type*}

lemma lmax_le_iff (L : List α) (f : α → ℝ) (b c : ℝ) :
    lmax L f b ≤ c ↔ b ≤ c ∧ ∀ q ∈ L, f q ≤ c := by
  induction L with
  | nil => simp [lmax]
  | cons q L ih =>
    simp only [lmax, List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [ih]; tauto

lemma le_lmin_iff (L : List α) (f : α → ℝ) (b c : ℝ) :
    c ≤ lmin L f b ↔ c ≤ b ∧ ∀ q ∈ L, c ≤ f q := by
  induction L with
  | nil => simp [lmin]
  | cons q L ih =>
    simp only [lmin, List.foldr_cons, le_min_iff, List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [ih]; tauto

lemma base_le_lmax (L : List α) (f : α → ℝ) (b : ℝ) : b ≤ lmax L f b :=
  ((lmax_le_iff L f b _).1 le_rfl).1

lemma le_lmax (L : List α) (f : α → ℝ) (b : ℝ) {q : α} (hq : q ∈ L) : f q ≤ lmax L f b :=
  ((lmax_le_iff L f b _).1 le_rfl).2 q hq

lemma lmin_le_base (L : List α) (f : α → ℝ) (b : ℝ) : lmin L f b ≤ b :=
  ((le_lmin_iff L f b _).1 le_rfl).1

lemma lmin_le (L : List α) (f : α → ℝ) (b : ℝ) {q : α} (hq : q ∈ L) : lmin L f b ≤ f q :=
  ((le_lmin_iff L f b _).1 le_rfl).2 q hq

lemma lmax_le_lmax_add (L : List α) (f g : α → ℝ) (b d : ℝ) (hd : 0 ≤ d)
    (h : ∀ q ∈ L, g q ≤ f q + d) : lmax L g b ≤ lmax L f b + d := by
  rw [lmax_le_iff]
  refine ⟨by linarith [base_le_lmax L f b], fun q hq => ?_⟩
  linarith [h q hq, le_lmax L f b hq]

lemma lmin_le_lmin_add (L : List α) (f g : α → ℝ) (b d : ℝ) (hd : 0 ≤ d)
    (h : ∀ q ∈ L, g q ≤ f q + d) : lmin L g b ≤ lmin L f b + d := by
  have : lmin L g b - d ≤ lmin L f b := by
    rw [le_lmin_iff]
    refine ⟨by linarith [lmin_le_base L g b], fun q hq => ?_⟩
    linarith [h q hq, lmin_le L g b hq]
  linarith

end ListMax

/-- The length `max(b − a, 0)` of `[a, b]`. -/
def len (a b : ℝ) : ℝ := max (b - a) 0

lemma len_nonneg (a b : ℝ) : 0 ≤ len a b := le_max_right _ _

lemma len_sub_le {a b a' b' d : ℝ} (hd : 0 ≤ d) (ha : a' ≤ a + d) (hb : b ≤ b' + d) :
    len a b - len a' b' ≤ 2 * d := by
  unfold len
  rcases le_total (b - a) 0 with h | h
  · rw [max_eq_right h]
    have : 0 ≤ max (b' - a') 0 := le_max_right _ _
    linarith
  · rw [max_eq_left h]
    linarith [le_max_left (b' - a') 0]

lemma len_le {a b c d : ℝ} (ha : c ≤ a) (hb : b ≤ d) (hcd : c ≤ d) : len a b ≤ d - c := by
  unfold len
  exact max_le (by linarith) (by linarith)

/-! ## Normalized coordinates -/

/-- `τ(z) = z₁ + r z₂`. -/
def tauAt (z : ℤ × ℤ) (r : ℝ) : ℝ := z.1 + r * z.2

lemma tauR_eq (ω : ℝ × ℝ × ℝ) (z : ℤ × ℤ) : tauR ω z = tauAt z ω.2.2 := rfl

lemma abs_tauAt_sub (z : ℤ × ℤ) (r r₀ : ℝ) :
    |tauAt z r - tauAt z r₀| = |(z.2 : ℝ)| * |r - r₀| := by
  unfold tauAt
  rw [show (z.1 : ℝ) + r * z.2 - (z.1 + r₀ * z.2) = z.2 * (r - r₀) by ring, abs_mul]

lemma inBox_norm (P : MemParams) (hU : 0 < P.U) (hV : 0 < P.V) {u v r : ℝ} (hu : 0 < u)
    (z : ℤ × ℤ) :
    P.InBox (P.U * u, P.V * v, r) z ↔ 1 ≤ u * tauAt z r ∧ u * tauAt z r ≤ 16 ∧
      1 ≤ v * tauAt z r + z.2 / (P.U * P.V * u) ∧
      v * tauAt z r + z.2 / (P.U * P.V * u) ≤ 2 := by
  unfold MemParams.InBox
  simp only [tauR_eq]
  have e1 : P.U * u * tauAt z r = P.U * (u * tauAt z r) := by ring
  have e2 : P.V * v * tauAt z r + (z.2 : ℝ) / (P.U * u) =
      P.V * (v * tauAt z r + z.2 / (P.U * P.V * u)) := by
    field_simp
  rw [e1, e2]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-! ## The rectangles of a slab -/

section Rect

variable {β : Type*} (L : List ((ℤ × ℤ) × β)) (r₀ Δ ε : ℝ)

/-- `τ` of a list entry at the slab base. -/
def tau0 (q : (ℤ × ℤ) × β) : ℝ := tauAt q.1 r₀

noncomputable def A1p : ℝ := lmax L (fun q => (1 - 16 * Δ) / tau0 r₀ q) 1
noncomputable def B1p : ℝ := lmin L (fun q => (16 + 16 * Δ) / tau0 r₀ q) 16
noncomputable def A1m : ℝ := lmax L (fun q => (1 + 16 * Δ) / tau0 r₀ q) 1
noncomputable def B1m : ℝ := lmin L (fun q => (16 - 16 * Δ) / tau0 r₀ q) 16
noncomputable def A2p : ℝ := lmax L (fun q => (1 - ε - 2 * Δ) / tau0 r₀ q) 1
noncomputable def B2p : ℝ := lmin L (fun q => (2 + ε + 2 * Δ) / tau0 r₀ q) 2
noncomputable def A2m : ℝ := lmax L (fun q => (1 + ε + 2 * Δ) / tau0 r₀ q) 1
noncomputable def B2m : ℝ := lmin L (fun q => (2 - ε - 2 * Δ) / tau0 r₀ q) 2

end Rect

section Contain

variable (P : MemParams) (L : List ((ℤ × ℤ) × P.Lst)) {Zb : ℝ} {n : ℕ} {r₀ r u v : ℝ}

/-- The common hypotheses: `U, V > 0`, `|z₂| ≤ Z` on the list, `τ(r₀) > 1/32`, `r` within `1/n`
of `r₀`. -/
structure SlabHyp (Zb : ℝ) (n : ℕ) (r₀ r : ℝ) : Prop where
  hU : 0 < P.U
  hV : 0 < P.V
  hn : 0 < n
  hZ : 0 ≤ Zb
  hz : ∀ q ∈ L, |((q.1.2 : ℤ) : ℝ)| ≤ Zb
  htau : ∀ q ∈ L, 1 / 32 < tau0 r₀ q
  hr : |r - r₀| ≤ 1 / n

variable {P L}

lemma SlabHyp.tau_close (H : SlabHyp P L Zb n r₀ r) {q : (ℤ × ℤ) × P.Lst} (hq : q ∈ L) :
    |tauAt q.1 r - tau0 r₀ q| ≤ Zb / n := by
  unfold tau0
  rw [abs_tauAt_sub]
  have hn : (0 : ℝ) < n := by exact_mod_cast H.hn
  calc |((q.1.2 : ℤ) : ℝ)| * |r - r₀| ≤ Zb * (1 / n) :=
        mul_le_mul (H.hz q hq) H.hr (abs_nonneg _) H.hZ
    _ = Zb / n := by ring

lemma SlabHyp.e_le (H : SlabHyp P L Zb n r₀ r) {q : (ℤ × ℤ) × P.Lst} (hq : q ∈ L) (hu : 1 ≤ u) :
    |((q.1.2 : ℤ) : ℝ) / (P.U * P.V * u)| ≤ Zb / (P.U * P.V) := by
  have hUV : 0 < P.U * P.V := mul_pos H.hU H.hV
  rw [abs_div, abs_of_pos (by positivity : 0 < P.U * P.V * u)]
  calc |((q.1.2 : ℤ) : ℝ)| / (P.U * P.V * u) ≤ Zb / (P.U * P.V * u) := by
        gcongr; exact H.hz q hq
    _ ≤ Zb / (P.U * P.V) := by
        apply div_le_div_of_nonneg_left H.hZ hUV
        nlinarith

/-- **Outer rectangle.** -/
lemma outer_sup (H : SlabHyp P L Zb n r₀ r) (hu1 : 1 ≤ u) (hu2 : u ≤ 16) (hv1 : 1 ≤ v)
    (hv2 : v ≤ 2) (hbox : ∀ q ∈ L, P.InBox (P.U * u, P.V * v, r) q.1) :
    A1p L r₀ (Zb / n) ≤ u ∧ u ≤ B1p L r₀ (Zb / n) ∧
      A2p L r₀ (Zb / n) (Zb / (P.U * P.V)) ≤ v ∧ v ≤ B2p L r₀ (Zb / n) (Zb / (P.U * P.V)) := by
  have hu0 : 0 < u := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [A1p, lmax_le_iff]
    refine ⟨hu1, fun q hq => ?_⟩
    have ht := H.htau q hq
    have hc := abs_le.1 (H.tau_close hq)
    have hb := ((inBox_norm P H.hU H.hV hu0 q.1).1 (hbox q hq)).1
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · rw [B1p, le_lmin_iff]
    refine ⟨hu2, fun q hq => ?_⟩
    have ht := H.htau q hq
    have hc := abs_le.1 (H.tau_close hq)
    have hb := ((inBox_norm P H.hU H.hV hu0 q.1).1 (hbox q hq)).2.1
    rw [le_div_iff₀ (by linarith)]
    have hZn : 0 ≤ Zb / n := by have := H.hZ; positivity
    nlinarith
  · rw [A2p, lmax_le_iff]
    refine ⟨hv1, fun q hq => ?_⟩
    have ht := H.htau q hq
    have hc := abs_le.1 (H.tau_close hq)
    have he := abs_le.1 (H.e_le hq hu1)
    have hb := ((inBox_norm P H.hU H.hV hu0 q.1).1 (hbox q hq)).2.2.1
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · rw [B2p, le_lmin_iff]
    refine ⟨hv2, fun q hq => ?_⟩
    have ht := H.htau q hq
    have hc := abs_le.1 (H.tau_close hq)
    have he := abs_le.1 (H.e_le hq hu1)
    have hb := ((inBox_norm P H.hU H.hV hu0 q.1).1 (hbox q hq)).2.2.2
    rw [le_div_iff₀ (by linarith)]
    have hZn : 0 ≤ Zb / n := by have := H.hZ; positivity
    nlinarith

/-- **Inner rectangle.** -/
lemma inner_sub (H : SlabHyp P L Zb n r₀ r)
    (h1 : A1m L r₀ (Zb / n) ≤ u) (h2 : u ≤ B1m L r₀ (Zb / n))
    (h3 : A2m L r₀ (Zb / n) (Zb / (P.U * P.V)) ≤ v)
    (h4 : v ≤ B2m L r₀ (Zb / n) (Zb / (P.U * P.V))) :
    1 ≤ u ∧ u ≤ 16 ∧ 1 ≤ v ∧ v ≤ 2 ∧ ∀ q ∈ L, P.InBox (P.U * u, P.V * v, r) q.1 := by
  have hu1 : 1 ≤ u := (base_le_lmax _ _ _).trans h1
  have hu2 : u ≤ 16 := h2.trans (lmin_le_base _ _ _)
  have hv1 : 1 ≤ v := (base_le_lmax _ _ _).trans h3
  have hv2 : v ≤ 2 := h4.trans (lmin_le_base _ _ _)
  refine ⟨hu1, hu2, hv1, hv2, fun q hq => ?_⟩
  have hu0 : 0 < u := by linarith
  have ht := H.htau q hq
  have hc := abs_le.1 (H.tau_close hq)
  have he := abs_le.1 (H.e_le hq hu1)
  have hZn : 0 ≤ Zb / n := by have := H.hZ; positivity
  have g1 := (le_lmax L _ _ hq).trans h1
  have g2 := h2.trans (lmin_le L _ _ hq)
  have g3 := (le_lmax L _ _ hq).trans h3
  have g4 := h4.trans (lmin_le L _ _ hq)
  rw [div_le_iff₀ (by linarith)] at g1 g3
  rw [le_div_iff₀ (by linarith)] at g2 g4
  rw [inBox_norm P H.hU H.hV hu0 q.1]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end Contain

section Width

variable {β : Type*} (L : List ((ℤ × ℤ) × β)) {r₀ Δ ε : ℝ}

lemma len1_diff (hΔ : 0 ≤ Δ) (htau : ∀ q ∈ L, 1 / 32 < tau0 r₀ q) :
    len (A1p L r₀ Δ) (B1p L r₀ Δ) - len (A1m L r₀ Δ) (B1m L r₀ Δ) ≤ 2048 * Δ := by
  have h1 : A1m L r₀ Δ ≤ A1p L r₀ Δ + 1024 * Δ := by
    refine lmax_le_lmax_add L _ _ 1 _ (by positivity) fun q hq => ?_
    have ht := htau q hq
    rw [show (1 + 16 * Δ) / tau0 r₀ q = (1 - 16 * Δ) / tau0 r₀ q + 32 * Δ / tau0 r₀ q by ring]
    gcongr
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2 : B1p L r₀ Δ ≤ B1m L r₀ Δ + 1024 * Δ := by
    refine lmin_le_lmin_add L _ _ 16 _ (by positivity) fun q hq => ?_
    have ht := htau q hq
    rw [show (16 + 16 * Δ) / tau0 r₀ q = (16 - 16 * Δ) / tau0 r₀ q + 32 * Δ / tau0 r₀ q by ring]
    gcongr
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have := len_sub_le (by positivity) h1 h2
  linarith

lemma len2_diff (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) (htau : ∀ q ∈ L, 1 / 32 < tau0 r₀ q) :
    len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) - len (A2m L r₀ Δ ε) (B2m L r₀ Δ ε) ≤
      64 * (2 * ε + 4 * Δ) := by
  have hd : 0 ≤ 32 * (2 * ε + 4 * Δ) := by positivity
  have h1 : A2m L r₀ Δ ε ≤ A2p L r₀ Δ ε + 32 * (2 * ε + 4 * Δ) := by
    refine lmax_le_lmax_add L _ _ 1 _ hd fun q hq => ?_
    have ht := htau q hq
    rw [show (1 + ε + 2 * Δ) / tau0 r₀ q =
      (1 - ε - 2 * Δ) / tau0 r₀ q + (2 * ε + 4 * Δ) / tau0 r₀ q by ring]
    gcongr
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2 : B2p L r₀ Δ ε ≤ B2m L r₀ Δ ε + 32 * (2 * ε + 4 * Δ) := by
    refine lmin_le_lmin_add L _ _ 2 _ hd fun q hq => ?_
    have ht := htau q hq
    rw [show (2 + ε + 2 * Δ) / tau0 r₀ q =
      (2 - ε - 2 * Δ) / tau0 r₀ q + (2 * ε + 4 * Δ) / tau0 r₀ q by ring]
    gcongr
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have := len_sub_le hd h1 h2
  linarith

/-- The two rectangles differ in area by `≤ 6000 (Δ + ε)`. -/
lemma area_diff (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) (htau : ∀ q ∈ L, 1 / 32 < tau0 r₀ q) :
    len (A1p L r₀ Δ) (B1p L r₀ Δ) * len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) -
      len (A1m L r₀ Δ) (B1m L r₀ Δ) * len (A2m L r₀ Δ ε) (B2m L r₀ Δ ε) ≤ 6000 * (Δ + ε) := by
  have d1 := len1_diff L hΔ htau
  have d2 := len2_diff L hΔ hε htau
  have l2p : len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) ≤ 1 :=
    (len_le (base_le_lmax _ _ _) (lmin_le_base _ _ _) (by norm_num)).trans (by norm_num)
  have l1m : len (A1m L r₀ Δ) (B1m L r₀ Δ) ≤ 15 :=
    (len_le (base_le_lmax _ _ _) (lmin_le_base _ _ _) (by norm_num)).trans (by norm_num)
  have n2p := len_nonneg (A2p L r₀ Δ ε) (B2p L r₀ Δ ε)
  have n1m := len_nonneg (A1m L r₀ Δ) (B1m L r₀ Δ)
  have e : len (A1p L r₀ Δ) (B1p L r₀ Δ) * len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) -
      len (A1m L r₀ Δ) (B1m L r₀ Δ) * len (A2m L r₀ Δ ε) (B2m L r₀ Δ ε) =
      (len (A1p L r₀ Δ) (B1p L r₀ Δ) - len (A1m L r₀ Δ) (B1m L r₀ Δ)) *
          len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) +
        len (A1m L r₀ Δ) (B1m L r₀ Δ) *
          (len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) - len (A2m L r₀ Δ ε) (B2m L r₀ Δ ε)) := by ring
  rw [e]
  have t1 : (len (A1p L r₀ Δ) (B1p L r₀ Δ) - len (A1m L r₀ Δ) (B1m L r₀ Δ)) *
      len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) ≤ 2048 * Δ * 1 := by
    rcases le_total 0 (len (A1p L r₀ Δ) (B1p L r₀ Δ) - len (A1m L r₀ Δ) (B1m L r₀ Δ)) with h | h
    · exact mul_le_mul d1 l2p n2p (by positivity)
    · have : (len (A1p L r₀ Δ) (B1p L r₀ Δ) - len (A1m L r₀ Δ) (B1m L r₀ Δ)) *
          len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h n2p
      linarith [show (0 : ℝ) ≤ 2048 * Δ * 1 by positivity]
  have t2 : len (A1m L r₀ Δ) (B1m L r₀ Δ) *
      (len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) - len (A2m L r₀ Δ ε) (B2m L r₀ Δ ε)) ≤
        15 * (64 * (2 * ε + 4 * Δ)) := by
    rcases le_total 0 (len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) - len (A2m L r₀ Δ ε) (B2m L r₀ Δ ε))
      with h | h
    · exact mul_le_mul l1m d2 h (by norm_num)
    · have : len (A1m L r₀ Δ) (B1m L r₀ Δ) *
          (len (A2p L r₀ Δ ε) (B2p L r₀ Δ ε) - len (A2m L r₀ Δ ε) (B2m L r₀ Δ ε)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos n1m h
      linarith [show (0 : ℝ) ≤ 15 * (64 * (2 * ε + 4 * Δ)) by positivity]
  nlinarith

end Width

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E: the core count of the single-edge root replacement

For coprime `A₁, A₂` with `S = A₁A₂` squarefree, `N₀ ∈ ℤ`, a set `B` of ratios and its
`ε`-fattening `B⁺`,

`ε · #{(P, Q) ∈ Ω² : A₁ ∣ P₁, A₂ ∣ Q₁, det(P, Q) = N₀, r_P ∈ B} ≤ 19 Λ vol(B⁺ ∩ (0,1])`,

`Λ = S²(30 ε U V/(ζ(2)|SL₂(ℤ/S)|) + U V x^{-c})`, when `|N₀| ε ≤ 1`. The ingredients: the root
basis `Q = z₁ P + N₀ (c, d)` with `z₁` in a window of `≤ 19` integers; the CRT column, which turns
`A₁ ∣ u, A₂ ∣ u z₁ + c N₀` into `(g₀ N̄)₀₀ = 0` for `g₀ = g mod S`; `#{g₀ : (g₀N̄)₀₀ = 0} ≤ S²`;
[21] Lemma 3.3 (K's `rootResidues`) for each `g₀`; and averaging the indicator of `B` over windows
inside `B⁺`. -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory
open ArtinPrimitiveRoots

/-! ## Lemma 3.3 at one `x` -/

/-! ## Finiteness of the counted sets -/

/-! ## Positions -/

lemma posBox_bounds {U V : ℝ} (hU : 0 < U) (hV : 0 < V) {P : ℕ × ℕ} (hP : P ∈ posBox U V) :
    U ≤ P.1 ∧ (P.1 : ℝ) ≤ 16 * U ∧ V ≤ P.2 ∧ (P.2 : ℝ) ≤ 2 * V ∧ Nat.Coprime P.1 P.2 := by
  simp only [posBox, mem_filter, mem_product, mem_Icc] at hP
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hP
  exact ⟨(Nat.le_ceil U).trans (by exact_mod_cast h1),
    (Nat.cast_le.2 h2).trans (Nat.floor_le (by linarith)),
    (Nat.le_ceil V).trans (by exact_mod_cast h3),
    (Nat.cast_le.2 h4).trans (Nat.floor_le (by linarith)), h5⟩

lemma rootRatio_mem {u : ℕ} (hu : 0 < u) (v : ℕ) : 0 ≤ rootRatio u v ∧ rootRatio u v < 1 := by
  rw [rootRatio_eq]
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  refine ⟨by positivity, (div_lt_one hu').2 (by exact_mod_cast rootC_lt hu v)⟩

/-! ## One residue condition: Lemma 3.3 summed over the admissible classes -/

/-! ## The root basis of an edge -/

lemma zeta_two_re : (riemannZeta 2).re = π ^ 2 / 6 := by
  rw [riemannZeta_two]
  rw [show (π : ℂ) ^ 2 / 6 = ((π ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/-! ## Averaging the bad indicator over windows -/

/-! ## The core count -/

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): the region comparison over slabs

For a list `L` of `(position, list)` pairs, the region
`R = {p = (u/U, v/V, r) : p ∈ [1,16] × [1,2] × [0,1), ∀ q ∈ L, box ∧ goodness of q at p}`
and a physical weight `Φ ∈ [0, 1]` with box sums `≈ (6/π²) UV vol(box) m` (an *oracle*), the sum
of `Φ` over the box points with normalized root in `R` is `(6/π²) UV m vol(R)` up to
`n (ε_Φ + 2 ε_c) + 12000 c (Z/n + Z/(UV)) + #bad slabs · (30 c/n + ε_c)` (`region_compare`). -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory

variable (P : MemParams)

/-- The normalized root `(u/U, v/V, r)` of a position. -/
noncomputable def normRoot (P₀ : ℕ × ℕ) : ℝ × ℝ × ℝ :=
  ((P₀.1 : ℝ) / P.U, (P₀.2 : ℝ) / P.V, rootRatio P₀.1 P₀.2)

/-- Goodness of a list entry at the ratio coordinate `r`. -/
def goodR (q : (ℤ × ℤ) × P.Lst) (r : ℝ) : Prop := P.GoodAt (0, 0, r) q.1 q.2

/-- The region in normalized coordinates. -/
def RegionN (L : List ((ℤ × ℤ) × P.Lst)) (p : ℝ × ℝ × ℝ) : Prop :=
  1 ≤ p.1 ∧ p.1 ≤ 16 ∧ 1 ≤ p.2.1 ∧ p.2.1 ≤ 2 ∧ 0 ≤ p.2.2 ∧ p.2.2 < 1 ∧
    ∀ q ∈ L, P.InBox (P.U * p.1, P.V * p.2.1, p.2.2) q.1 ∧ goodR P q p.2.2

/-- The `k`th slab `[k/n, (k+1)/n)`. -/
def slab (n k : ℕ) : Set ℝ := Set.Ico ((k : ℝ) / n) (((k : ℝ) + 1) / n)

/-- Goodness of every entry is constant on the closed `k`th slab. -/
def GoodConst (L : List ((ℤ × ℤ) × P.Lst)) (n k : ℕ) : Prop :=
  ∀ q ∈ L, ∀ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
    ∀ r' ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n), goodR P q r ↔ goodR P q r'

/-- A bad slab: all `τ(k/n) > 1/32` but some goodness is not constant. -/
def BadSlab (L : List ((ℤ × ℤ) × P.Lst)) (n k : ℕ) : Prop :=
  (∀ q ∈ L, 1 / 32 < tau0 ((k : ℝ) / n) q) ∧ ¬ GoodConst P L n k

open Classical in
/-- The box-sum oracle for a weight `Φ` with density `m` and error `ε`. -/
def Oracle (n : ℕ) (Φ : ℕ × ℕ → ℝ) (m ε : ℝ) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : ℝ, ∀ k : ℕ, 1 ≤ a₁ → b₁ ≤ 16 → 1 ≤ a₂ → b₂ ≤ 2 → k < n →
    |∑ P₀ ∈ posBox P.U P.V, (if normRoot P P₀ ∈ Set.Icc a₁ b₁ ×ˢ (Set.Icc a₂ b₂ ×ˢ slab n k)
        then Φ P₀ else 0) -
      6 / π ^ 2 * (P.U * P.V) * (len a₁ b₁ * len a₂ b₂ * (1 / n)) * m| ≤ ε

/-! ## Slabs partition `[0, 1)` -/

lemma mem_slab_iff {n : ℕ} (hn : 0 < n) {r : ℝ} (hr0 : 0 ≤ r) (k : ℕ) :
    r ∈ slab n k ↔ ⌊r * n⌋₊ = k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold slab
  rw [Set.mem_Ico, div_le_iff₀ hn', lt_div_iff₀ hn', Nat.floor_eq_iff (by positivity)]

open Classical in
lemma sum_slab_one {n : ℕ} (hn : 0 < n) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑ k ∈ range n, (if r ∈ slab n k then (1 : ℝ) else 0) = 1 := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [mem_slab_iff hn hr0]
  rw [sum_ite_eq, if_pos]
  rw [mem_range, Nat.floor_lt (by positivity)]
  nlinarith

lemma measurableSet_slab3 (n k : ℕ) :
    MeasurableSet {p : ℝ × ℝ × ℝ | p.2.2 ∈ slab n k} :=
  measurableSet_Ico.preimage (measurable_snd.snd)

lemma volume_inter_iUnion (A : Set (ℝ × ℝ × ℝ)) (S : ℕ → Set (ℝ × ℝ × ℝ))
    (hS : ∀ k, MeasurableSet (S k)) (hdisj : ∀ j k, j ≠ k → Disjoint (S j) (S k)) (s : Finset ℕ) :
    volume (A ∩ ⋃ k ∈ s, S k) = ∑ k ∈ s, volume (A ∩ S k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, ← ih, ← measure_inter_add_sdiff (A ∩ ⋃ k ∈ insert j s, S k) (hS j)]
    congr 1
    · congr 1; ext p
      simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_insert, exists_prop]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, j, Or.inl rfl, h2⟩, h2⟩
    · congr 1; ext p
      simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_iUnion, mem_insert, exists_prop]
      constructor
      · rintro ⟨⟨h1, k, hk, h2⟩, h3⟩
        rcases hk with rfl | hk
        · exact absurd h2 h3
        · exact ⟨h1, k, hk, h2⟩
      · rintro ⟨h1, k, hk, h2⟩
        refine ⟨⟨h1, k, Or.inr hk, h2⟩, fun h3 => ?_⟩
        have hjk : j ≠ k := fun e => hj (e ▸ hk)
        exact Set.disjoint_left.1 (hdisj j k hjk) h3 h2

lemma slab_disjoint (n : ℕ) (hn : 0 < n) (j k : ℕ) (hjk : j ≠ k) :
    Disjoint {p : ℝ × ℝ × ℝ | p.2.2 ∈ slab n j} {p : ℝ × ℝ × ℝ | p.2.2 ∈ slab n k} := by
  rw [Set.disjoint_left]
  intro p h1 h2
  have h0 : 0 ≤ p.2.2 := by
    have := h1.1; have : (0 : ℝ) ≤ (j : ℝ) / n := by positivity
    linarith
  exact hjk (((mem_slab_iff hn h0 j).1 h1).symm.trans ((mem_slab_iff hn h0 k).1 h2))

/-! ## Box volumes -/

lemma volume_box (a₁ b₁ a₂ b₂ : ℝ) (n k : ℕ) (hn : 0 < n) :
    (volume (Set.Icc a₁ b₁ ×ˢ (Set.Icc a₂ b₂ ×ˢ slab n k))).toReal =
      len a₁ b₁ * len a₂ b₂ * (1 / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc]
  unfold slab
  rw [Real.volume_Ico, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal',
    ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
  have e3 : max (((k : ℝ) + 1) / n - k / n) 0 = 1 / n := by
    have : ((k : ℝ) + 1) / n - k / n = 1 / n := by field_simp; ring
    rw [this]; exact max_eq_left (by positivity)
  rw [e3]
  unfold len
  ring

lemma volume_box_lt_top (a₁ b₁ a₂ b₂ : ℝ) (n k : ℕ) :
    volume (Set.Icc a₁ b₁ ×ˢ (Set.Icc a₂ b₂ ×ˢ slab n k)) < ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc]
  unfold slab
  rw [Real.volume_Ico]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ENNReal.ofReal_lt_top)

/-! ## Containments on one slab -/

section OneSlab

variable {P} (L : List ((ℤ × ℤ) × P.Lst)) {Zb : ℝ} {n : ℕ}

lemma slab_abs_sub {k : ℕ} {r : ℝ} (hr : r ∈ slab n k) (hn : 0 < n) :
    |r - (k : ℝ) / n| ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := hr
  rw [abs_le]
  constructor
  · have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  · have : ((k : ℝ) + 1) / n = k / n + 1 / n := by ring
    linarith

lemma slab_empty (hU : 0 < P.U) (hV : 0 < P.V) (hZ : 0 ≤ Zb)
    (hz : ∀ q ∈ L, |((q.1.2 : ℤ) : ℝ)| ≤ Zb) (hn : 0 < n) (hZn : Zb / n ≤ 1 / 64) {k : ℕ}
    (hA : ∃ q ∈ L, tau0 ((k : ℝ) / n) q ≤ 1 / 32) {p : ℝ × ℝ × ℝ} (hp : RegionN P L p)
    (hs : p.2.2 ∈ slab n k) : False := by
  obtain ⟨q, hq, ht⟩ := hA
  obtain ⟨hu1, hu2, -, -, -, -, hall⟩ := hp
  have hu0 : 0 < p.1 := by linarith
  have hb := ((inBox_norm P hU hV hu0 q.1).1 (hall q hq).1).1
  have hc : |tauAt q.1 p.2.2 - tau0 ((k : ℝ) / n) q| ≤ Zb / n := by
    unfold tau0
    rw [abs_tauAt_sub]
    calc |((q.1.2 : ℤ) : ℝ)| * |p.2.2 - (k : ℝ) / n| ≤ Zb * (1 / n) :=
          mul_le_mul (hz q hq) (slab_abs_sub hs hn) (abs_nonneg _) hZ
      _ = Zb / n := by ring
  have := (abs_le.1 hc).2
  nlinarith

lemma slab_outer (hU : 0 < P.U) (hV : 0 < P.V) (hZ : 0 ≤ Zb)
    (hz : ∀ q ∈ L, |((q.1.2 : ℤ) : ℝ)| ≤ Zb) (hn : 0 < n) {k : ℕ}
    (hτ : ∀ q ∈ L, 1 / 32 < tau0 ((k : ℝ) / n) q) {p : ℝ × ℝ × ℝ} (hp : RegionN P L p)
    (hs : p.2.2 ∈ slab n k) :
    p ∈ Set.Icc (A1p L ((k : ℝ) / n) (Zb / n)) (B1p L ((k : ℝ) / n) (Zb / n)) ×ˢ
      (Set.Icc (A2p L ((k : ℝ) / n) (Zb / n) (Zb / (P.U * P.V)))
        (B2p L ((k : ℝ) / n) (Zb / n) (Zb / (P.U * P.V))) ×ˢ slab n k) := by
  obtain ⟨hu1, hu2, hv1, hv2, -, -, hall⟩ := hp
  have H : SlabHyp P L Zb n ((k : ℝ) / n) p.2.2 :=
    ⟨hU, hV, hn, hZ, hz, hτ, slab_abs_sub hs hn⟩
  obtain ⟨a1, a2, a3, a4⟩ := outer_sup H hu1 hu2 hv1 hv2 fun q hq => (hall q hq).1
  exact ⟨⟨a1, a2⟩, ⟨a3, a4⟩, hs⟩

lemma slab_inner (hU : 0 < P.U) (hV : 0 < P.V) (hZ : 0 ≤ Zb)
    (hz : ∀ q ∈ L, |((q.1.2 : ℤ) : ℝ)| ≤ Zb) (hn : 0 < n) {k : ℕ} (hk : k < n)
    (hτ : ∀ q ∈ L, 1 / 32 < tau0 ((k : ℝ) / n) q)
    (hg : ∀ q ∈ L, ∀ r ∈ slab n k, goodR P q r) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ Set.Icc (A1m L ((k : ℝ) / n) (Zb / n)) (B1m L ((k : ℝ) / n) (Zb / n)) ×ˢ
      (Set.Icc (A2m L ((k : ℝ) / n) (Zb / n) (Zb / (P.U * P.V)))
        (B2m L ((k : ℝ) / n) (Zb / n) (Zb / (P.U * P.V))) ×ˢ slab n k)) :
    RegionN P L p ∧ p.2.2 ∈ slab n k := by
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩, hs⟩ := hp
  have H : SlabHyp P L Zb n ((k : ℝ) / n) p.2.2 :=
    ⟨hU, hV, hn, hZ, hz, hτ, slab_abs_sub hs hn⟩
  obtain ⟨hu1, hu2, hv1, hv2, hbox⟩ := inner_sub H a1 a2 a3 a4
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : 0 ≤ p.2.2 := le_trans (by positivity) hs.1
  have hr1 : p.2.2 < 1 := by
    have := hs.2
    have : ((k : ℝ) + 1) / n ≤ 1 := by
      rw [div_le_one hn']; exact_mod_cast hk
    linarith
  exact ⟨⟨hu1, hu2, hv1, hv2, hr0, hr1, fun q hq => ⟨hbox q hq, hg q hq _ hs⟩⟩, hs⟩

end OneSlab

/-! ## Sums of a weight between two predicates -/

lemma sum_between (S : Finset (ℕ × ℕ)) (Φ : ℕ × ℕ → ℝ) (hΦ : ∀ x ∈ S, 0 ≤ Φ x ∧ Φ x ≤ 1)
    (A B C : ℕ × ℕ → Prop) [DecidablePred A] [DecidablePred B] [DecidablePred C] (hAB : ∀ x ∈ S, A x → B x) (hBC : ∀ x ∈ S, B x → C x) :
    (∑ x ∈ S, if A x then Φ x else 0) ≤ ∑ x ∈ S, (if B x then Φ x else 0) ∧
      (∑ x ∈ S, if B x then Φ x else 0) ≤ (∑ x ∈ S, if A x then Φ x else 0) +
        ((∑ x ∈ S, if C x then (1 : ℝ) else 0) - ∑ x ∈ S, if A x then (1 : ℝ) else 0) := by
  constructor
  · refine sum_le_sum fun x hx => ?_
    by_cases hA : A x
    · rw [if_pos hA, if_pos (hAB x hx hA)]
    · rw [if_neg hA]; split_ifs
      · exact (hΦ x hx).1
      · exact le_rfl
  · rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_le_sum fun x hx => ?_
    have h01 := hΦ x hx
    by_cases hA : A x
    · rw [if_pos hA, if_pos (hAB x hx hA), if_pos (hBC x hx (hAB x hx hA)), if_pos hA]; ring_nf
      exact le_rfl
    · rw [if_neg hA, if_neg hA]
      by_cases hB : B x
      · rw [if_pos hB, if_pos (hBC x hx hB)]; linarith
      · rw [if_neg hB]; split_ifs <;> linarith

/-! ## One slab -/

lemma oracle_nonneg {n : ℕ} (hn : 0 < n) {Φ : ℕ × ℕ → ℝ} {m ε : ℝ} (h : Oracle P n Φ m ε) :
    0 ≤ ε := (abs_nonneg _).trans (h 1 1 1 1 0 le_rfl (by norm_num) le_rfl (by norm_num) hn)

/-- The arithmetic of a good slab. -/
lemma good_slab_arith {c m S V Sin Cout Cin vin vout εΦ εc G : ℝ} (hc0 : 0 ≤ c) (hm0 : 0 ≤ m)
    (hm1 : m ≤ 1) (hεc : 0 ≤ εc) (hS1 : Sin ≤ S) (hS2 : S ≤ Sin + (Cout - Cin)) (hO : |Sin - c * vin * m| ≤ εΦ)
    (hCo : Cout ≤ c * vout + εc) (hCi : c * vin - εc ≤ Cin) (hV1 : vin ≤ V) (hV2 : V ≤ vout)
    (hgap : c * (vout - vin) ≤ G) :
    |S - c * m * V| ≤ εΦ + 2 * εc + G := by
  rw [show c * vin * m = c * m * vin by ring] at hO
  obtain ⟨hO1, hO2⟩ := abs_le.1 hO
  have h1 : c * m * vin ≤ c * m * V := by gcongr
  have h2 : c * m * V ≤ c * m * vout := by gcongr
  have h3 : c * m * (vout - vin) ≤ c * (vout - vin) := by
    have : 0 ≤ vout - vin := by linarith
    have : c * m * (vout - vin) ≤ c * 1 * (vout - vin) := by gcongr
    linarith
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- The arithmetic of a bad slab. -/
lemma bad_slab_arith {c m S V Cout vout εc B : ℝ} (hc0 : 0 ≤ c) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hS0 : 0 ≤ S) (hS : S ≤ Cout) (hCo : Cout ≤ c * vout + εc) (hV0 : 0 ≤ V) (hV : V ≤ vout)
    (hB : vout ≤ B) : |S - c * m * V| ≤ 2 * (c * B) + εc := by
  have h1 : c * m * V ≤ c * B := by
    calc c * m * V ≤ c * 1 * vout := by gcongr
      _ ≤ c * B := by rw [mul_one]; gcongr
  have h2 : 0 ≤ c * m * V := by positivity
  have h3 : c * vout ≤ c * B := by gcongr
  rw [abs_le]
  constructor <;> nlinarith

open Classical in
theorem slab_bound (hU : 0 < P.U) (hV : 0 < P.V) (L : List ((ℤ × ℤ) × P.Lst)) {Zb : ℝ}
    (hZ : 0 ≤ Zb) (hz : ∀ q ∈ L, |((q.1.2 : ℤ) : ℝ)| ≤ Zb) {n : ℕ} (hn : 0 < n)
    (hZn : Zb / n ≤ 1 / 64) (Φ : ℕ × ℕ → ℝ)
    (hΦ : ∀ P₀ ∈ posBox P.U P.V, 0 ≤ Φ P₀ ∧ Φ P₀ ≤ 1) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    {εΦ εc : ℝ} (hO : Oracle P n Φ m εΦ) (hC : Oracle P n (fun _ => 1) 1 εc) {k : ℕ}
    (hk : k < n) :
    |(∑ P₀ ∈ posBox P.U P.V, if RegionN P L (normRoot P P₀) ∧ (normRoot P P₀).2.2 ∈ slab n k
        then Φ P₀ else 0) -
      6 / π ^ 2 * (P.U * P.V) * m *
        (volume {p : ℝ × ℝ × ℝ | RegionN P L p ∧ p.2.2 ∈ slab n k}).toReal| ≤
      εΦ + 2 * εc + 6 / π ^ 2 * (P.U * P.V) * (6000 * (Zb / n + Zb / (P.U * P.V))) / n +
        (if BadSlab P L n k then 30 * (6 / π ^ 2 * (P.U * P.V)) / n + εc else 0) := by
  set c := 6 / π ^ 2 * (P.U * P.V) with hc
  have hc0 : 0 ≤ c := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hεΦ := oracle_nonneg P hn hO
  have hεc := oracle_nonneg P hn hC
  have hΔ : 0 ≤ Zb / n := by positivity
  have hε' : 0 ≤ Zb / (P.U * P.V) := by have := mul_pos hU hV; positivity
  set G := c * (6000 * (Zb / n + Zb / (P.U * P.V))) / n with hG
  have hG0 : 0 ≤ G := by positivity
  set Sk := ∑ P₀ ∈ posBox P.U P.V, if RegionN P L (normRoot P P₀) ∧
    (normRoot P P₀).2.2 ∈ slab n k then Φ P₀ else 0 with hSk
  set Rk := {p : ℝ × ℝ × ℝ | RegionN P L p ∧ p.2.2 ∈ slab n k} with hRk
  have hextra0 : 0 ≤ (if BadSlab P L n k then 30 * c / n + εc else 0) := by
    split_ifs <;> positivity
  -- the slab misses the region
  have hmiss : (∀ p, ¬ (RegionN P L p ∧ p.2.2 ∈ slab n k)) →
      |Sk - c * m * (volume Rk).toReal| ≤
        εΦ + 2 * εc + G + (if BadSlab P L n k then 30 * c / n + εc else 0) := by
    intro hempty
    have hS : Sk = 0 := sum_eq_zero fun P₀ _ => if_neg (hempty _)
    have hV0 : Rk = ∅ := Set.eq_empty_of_forall_notMem fun p hp => hempty p hp
    rw [hS, hV0]
    simp only [measure_empty, ENNReal.toReal_zero, mul_zero, sub_zero, abs_zero]
    linarith
  by_cases hA : ∃ q ∈ L, tau0 ((k : ℝ) / n) q ≤ 1 / 32
  · exact hmiss fun p hp => slab_empty L hU hV hZ hz hn hZn hA hp.1 hp.2
  push Not at hA
  set Δ := Zb / n with hΔdef
  set ε := Zb / (P.U * P.V) with hεdef
  set a1p := A1p L ((k : ℝ) / n) Δ
  set b1p := B1p L ((k : ℝ) / n) Δ
  set a2p := A2p L ((k : ℝ) / n) Δ ε
  set b2p := B2p L ((k : ℝ) / n) Δ ε
  set a1m := A1m L ((k : ℝ) / n) Δ
  set b1m := B1m L ((k : ℝ) / n) Δ
  set a2m := A2m L ((k : ℝ) / n) Δ ε
  set b2m := B2m L ((k : ℝ) / n) Δ ε
  set Bp := Set.Icc a1p b1p ×ˢ (Set.Icc a2p b2p ×ˢ slab n k) with hBpdef
  set Bm := Set.Icc a1m b1m ×ˢ (Set.Icc a2m b2m ×ˢ slab n k) with hBmdef
  set vout := len a1p b1p * len a2p b2p * (1 / (n : ℝ)) with hvout
  set vin := len a1m b1m * len a2m b2m * (1 / (n : ℝ)) with hvin
  have hout : ∀ p, RegionN P L p ∧ p.2.2 ∈ slab n k → p ∈ Bp := fun p hp =>
    slab_outer L hU hV hZ hz hn hA hp.1 hp.2
  have hBpfin : volume Bp < ⊤ := volume_box_lt_top a1p b1p a2p b2p n k
  have hBp : (volume Bp).toReal = vout := volume_box a1p b1p a2p b2p n k hn
  have hBm : (volume Bm).toReal = vin := volume_box a1m b1m a2m b2m n k hn
  have hVup : (volume Rk).toReal ≤ vout := by
    rw [← hBp]; exact ENNReal.toReal_mono hBpfin.ne (measure_mono fun p hp => hout p hp)
  have hV0 : 0 ≤ (volume Rk).toReal := ENNReal.toReal_nonneg
  set Cp := ∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ Bp then (1 : ℝ) else 0 with hCpdef
  set Cm := ∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ Bm then (1 : ℝ) else 0 with hCmdef
  set Sm := ∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ Bm then Φ P₀ else 0 with hSmdef
  have hCp : Cp ≤ c * vout + εc := by
    have h := hC a1p b1p a2p b2p k (base_le_lmax _ _ _) (lmin_le_base _ _ _)
      (base_le_lmax _ _ _) (lmin_le_base _ _ _) hk
    have := (abs_le.1 h).2
    simp only [mul_one] at this
    linarith
  have hvout15 : vout ≤ 15 / n := by
    have l1 : len a1p b1p ≤ 15 :=
      (len_le (base_le_lmax _ _ _) (lmin_le_base _ _ _) (by norm_num)).trans (by norm_num)
    have l2 : len a2p b2p ≤ 1 :=
      (len_le (base_le_lmax _ _ _) (lmin_le_base _ _ _) (by norm_num)).trans (by norm_num)
    have := len_nonneg a1p b1p
    have := len_nonneg a2p b2p
    calc vout ≤ (15 : ℝ) * 1 * (1 / (n : ℝ)) := by rw [hvout]; gcongr
      _ = 15 / n := by ring
  have hRB : ∀ P₀ ∈ posBox P.U P.V, RegionN P L (normRoot P P₀) ∧
      (normRoot P P₀).2.2 ∈ slab n k → normRoot P P₀ ∈ Bp := fun P₀ _ h => hout _ h
  by_cases hbad : BadSlab P L n k
  · rw [if_pos hbad]
    have hS1 := sum_between (posBox P.U P.V) Φ hΦ (fun _ => False)
      (fun P₀ => RegionN P L (normRoot P P₀) ∧ (normRoot P P₀).2.2 ∈ slab n k)
      (fun P₀ => normRoot P P₀ ∈ Bp) (fun _ _ h => h.elim) hRB
    simp only [if_false, sum_const_zero, zero_add, sub_zero] at hS1
    have hb := bad_slab_arith (S := Sk) (V := (volume Rk).toReal) hc0 hm0 hm1 hS1.1 hS1.2 hCp
      hV0 hVup hvout15
    have : 2 * (c * (15 / n)) = 30 * c / n := by ring
    rw [this] at hb
    linarith
  rw [if_neg hbad, add_zero]
  have hconst : GoodConst P L n k := by
    by_contra h; exact hbad ⟨hA, h⟩
  have hk0 : (k : ℝ) / n ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n) :=
    ⟨le_rfl, by gcongr; linarith⟩
  by_cases hg0 : ∀ q ∈ L, goodR P q ((k : ℝ) / n)
  · have hg : ∀ q ∈ L, ∀ r ∈ slab n k, goodR P q r := fun q hq r hr =>
      (hconst q hq r ⟨hr.1, hr.2.le⟩ _ hk0).2 (hg0 q hq)
    have hin : ∀ p ∈ Bm, RegionN P L p ∧ p.2.2 ∈ slab n k := fun p hp =>
      slab_inner L hU hV hZ hz hn hk hA hg hp
    have hVlo : vin ≤ (volume Rk).toReal := by
      rw [← hBm]
      exact ENNReal.toReal_mono ((measure_mono fun p hp => hout p hp).trans_lt hBpfin).ne
        (measure_mono fun p hp => hin p hp)
    have hS := sum_between (posBox P.U P.V) Φ hΦ (fun P₀ => normRoot P P₀ ∈ Bm)
      (fun P₀ => RegionN P L (normRoot P P₀) ∧ (normRoot P P₀).2.2 ∈ slab n k)
      (fun P₀ => normRoot P P₀ ∈ Bp) (fun P₀ _ h => hin _ h) hRB
    have hOm : |Sm - c * vin * m| ≤ εΦ :=
      hO a1m b1m a2m b2m k (base_le_lmax _ _ _) (lmin_le_base _ _ _) (base_le_lmax _ _ _)
        (lmin_le_base _ _ _) hk
    have hCm : c * vin - εc ≤ Cm := by
      have h := hC a1m b1m a2m b2m k (base_le_lmax _ _ _) (lmin_le_base _ _ _)
        (base_le_lmax _ _ _) (lmin_le_base _ _ _) hk
      have := (abs_le.1 h).1
      simp only [mul_one] at this
      linarith
    have hdiff := area_diff L (r₀ := (k : ℝ) / n) hΔ hε' hA
    have hgap : c * (vout - vin) ≤ G := by
      rw [hG, hvout, hvin]
      rw [show len a1p b1p * len a2p b2p * (1 / (n : ℝ)) - len a1m b1m * len a2m b2m * (1 / n) =
        (len a1p b1p * len a2p b2p - len a1m b1m * len a2m b2m) / n by ring]
      rw [mul_div_assoc]
      gcongr
    exact good_slab_arith hc0 hm0 hm1 hεc hS.1 hS.2 hOm hCp hCm hVlo hVup hgap
  · push Not at hg0
    obtain ⟨q, hq, hbq⟩ := hg0
    refine (hmiss ?_).trans (by rw [if_neg hbad, add_zero])
    rintro p ⟨hp, hs⟩
    have := (hp.2.2.2.2.2.2 q hq).2
    exact hbq ((hconst q hq _ ⟨hs.1, hs.2.le⟩ _ hk0).1 this)

/-! ## The region comparison -/

open Classical in
/-- **Region comparison** over `n` slabs. -/
theorem region_compare (hU : 0 < P.U) (hV : 0 < P.V) (L : List ((ℤ × ℤ) × P.Lst)) {Zb : ℝ}
    (hZ : 0 ≤ Zb) (hz : ∀ q ∈ L, |((q.1.2 : ℤ) : ℝ)| ≤ Zb) {n : ℕ} (hn : 0 < n)
    (hZn : Zb / n ≤ 1 / 64) (Φ : ℕ × ℕ → ℝ)
    (hΦ : ∀ P₀ ∈ posBox P.U P.V, 0 ≤ Φ P₀ ∧ Φ P₀ ≤ 1) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    {εΦ εc : ℝ} (hO : Oracle P n Φ m εΦ) (hC : Oracle P n (fun _ => 1) 1 εc) {Bad : ℕ}
    (hBad : ((range n).filter fun k => BadSlab P L n k).card ≤ Bad) :
    |(∑ P₀ ∈ posBox P.U P.V, if RegionN P L (normRoot P P₀) then Φ P₀ else 0) -
      6 / π ^ 2 * (P.U * P.V) * m * (volume {p : ℝ × ℝ × ℝ | RegionN P L p}).toReal| ≤
      n * (εΦ + 2 * εc) + 6 / π ^ 2 * (P.U * P.V) * (6000 * (Zb / n + Zb / (P.U * P.V))) +
        Bad * (30 * (6 / π ^ 2 * (P.U * P.V)) / n + εc) := by
  set c := 6 / π ^ 2 * (P.U * P.V) with hc
  have hc0 : 0 ≤ c := by positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hεc := oracle_nonneg P hn hC
  -- the physical sum over slabs
  have hphys : (∑ P₀ ∈ posBox P.U P.V, if RegionN P L (normRoot P P₀) then Φ P₀ else 0) =
      ∑ k ∈ range n, ∑ P₀ ∈ posBox P.U P.V, if RegionN P L (normRoot P P₀) ∧
        (normRoot P P₀).2.2 ∈ slab n k then Φ P₀ else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun P₀ _ => ?_
    by_cases hR : RegionN P L (normRoot P P₀)
    · rw [if_pos hR]
      have h1 := sum_slab_one hn hR.2.2.2.2.1 hR.2.2.2.2.2.1
      calc Φ P₀ = Φ P₀ * ∑ k ∈ range n, (if (normRoot P P₀).2.2 ∈ slab n k then (1 : ℝ) else 0) :=
            by rw [h1, mul_one]
        _ = _ := by
            rw [mul_sum]
            refine sum_congr rfl fun k _ => ?_
            by_cases hs : (normRoot P P₀).2.2 ∈ slab n k
            · rw [if_pos hs, if_pos ⟨hR, hs⟩, mul_one]
            · rw [if_neg hs, if_neg fun h => hs h.2, mul_zero]
    · rw [if_neg hR]
      exact (sum_eq_zero fun k _ => if_neg fun h => hR h.1).symm
  -- the volume over slabs
  have hfin : ∀ k, volume {p : ℝ × ℝ × ℝ | RegionN P L p ∧ p.2.2 ∈ slab n k} ≠ ⊤ := by
    intro k
    refine ne_top_of_le_ne_top (volume_box_lt_top 1 16 1 2 n k).ne (measure_mono ?_)
    rintro p ⟨hp, hs⟩
    exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2.1⟩, hs⟩
  have hvol : (volume {p : ℝ × ℝ × ℝ | RegionN P L p}).toReal =
      ∑ k ∈ range n, (volume {p : ℝ × ℝ × ℝ | RegionN P L p ∧ p.2.2 ∈ slab n k}).toReal := by
    have h := volume_inter_iUnion {p : ℝ × ℝ × ℝ | RegionN P L p}
      (fun k => {p : ℝ × ℝ × ℝ | p.2.2 ∈ slab n k}) (fun k => measurableSet_slab3 n k)
      (slab_disjoint n hn) (range n)
    have e1 : {p : ℝ × ℝ × ℝ | RegionN P L p} ∩
        ⋃ k ∈ range n, {p : ℝ × ℝ × ℝ | p.2.2 ∈ slab n k} = {p | RegionN P L p} := by
      refine Set.inter_eq_left.2 fun p hp => ?_
      simp only [Set.mem_iUnion, mem_range, Set.mem_setOf_eq, exists_prop]
      have hp0 := hp.2.2.2.2.1
      have hp1 := hp.2.2.2.2.2.1
      refine ⟨⌊p.2.2 * n⌋₊, ?_, (mem_slab_iff hn hp0 _).2 rfl⟩
      rw [Nat.floor_lt (by positivity)]; nlinarith
    rw [e1] at h
    rw [h, ENNReal.toReal_sum]
    · rfl
    · intro k _; exact hfin k
  rw [hphys, hvol, mul_sum, ← sum_sub_distrib]
  calc |∑ k ∈ range n, ((∑ P₀ ∈ posBox P.U P.V, if RegionN P L (normRoot P P₀) ∧
          (normRoot P P₀).2.2 ∈ slab n k then Φ P₀ else 0) -
        c * m * (volume {p : ℝ × ℝ × ℝ | RegionN P L p ∧ p.2.2 ∈ slab n k}).toReal)|
      ≤ ∑ k ∈ range n, |(∑ P₀ ∈ posBox P.U P.V, if RegionN P L (normRoot P P₀) ∧
          (normRoot P P₀).2.2 ∈ slab n k then Φ P₀ else 0) -
        c * m * (volume {p : ℝ × ℝ × ℝ | RegionN P L p ∧ p.2.2 ∈ slab n k}).toReal| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range n, (εΦ + 2 * εc + c * (6000 * (Zb / n + Zb / (P.U * P.V))) / n +
          (if BadSlab P L n k then 30 * c / n + εc else 0)) :=
        sum_le_sum fun k hk => slab_bound P hU hV L hZ hz hn hZn Φ hΦ hm0 hm1 hO hC
          (mem_range.1 hk)
    _ = n * (εΦ + 2 * εc) + c * (6000 * (Zb / n + Zb / (P.U * P.V))) +
          ((range n).filter fun k => BadSlab P L n k).card * (30 * c / n + εc) := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_filter, sum_const,
          nsmul_eq_mul]
        field_simp
    _ ≤ n * (εΦ + 2 * εc) + c * (6000 * (Zb / n + Zb / (P.U * P.V))) +
          Bad * (30 * c / n + εc) := by
        gcongr

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): goodness changes only at crossings

Goodness of a ratio `ρ` depends only on the finitely many indicators
`[circNorm(Nρ) < θ]`, `[circNorm(Nρ) ≤ θ]` over the test pairs `(N, θ)` of the two tests
(`tests`, `isGoodRatio_congr_tests`). In root coordinates the ratio of a primitive `z` is
`ρ(r) = τ(w)/τ(z)` with `ρ(r) − ρ(r') = (r − r')/(τ(r)τ(r'))` (`rho_sub`); so on a slab where
`τ ≥ 1/64` goodness is constant unless some `circNorm(Nρ(r*)) = θ` (IVT), and such crossing points
`r*` are injectively labelled by `(N, θ, sign, Nρ(r*) ∓ θ ∈ ℤ)`. Hence the number of slabs on which
the goodness of one entry changes is `≤ 2 · #tests · 2 · (2⌈4096 M⌉ + 1)` (`card_bad_q`). -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset

/-! ## The ratio as a function of `r` -/

lemma detZ_complVec' {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) : detZ z (complVec z) = 1 := by
  unfold detZ complVec; dsimp only
  have := Int.gcd_eq_gcd_ab z.1 z.2
  rw [hz] at this; push_cast at this
  linarith

/-- `ρ(r) = τ(w)/τ(z)`, `w` the complement of `z`. -/
noncomputable def rho (z : ℤ × ℤ) (r : ℝ) : ℝ := tauAt (complVec z) r / tauAt z r

lemma rho_sub {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) {r r' : ℝ} (h : tauAt z r ≠ 0)
    (h' : tauAt z r' ≠ 0) : rho z r - rho z r' = (r - r') / (tauAt z r * tauAt z r') := by
  have hd := detZ_complVec' hz
  unfold detZ at hd
  have hd' : ((z.1 : ℝ) * (complVec z).2 - z.2 * (complVec z).1) = 1 := by exact_mod_cast hd
  unfold rho
  rw [div_sub_div _ _ h h']
  congr 1
  unfold tauAt
  linear_combination (r - r') * hd'

lemma continuousOn_rho (z : ℤ × ℤ) {s : Set ℝ} (h : ∀ r ∈ s, tauAt z r ≠ 0) :
    ContinuousOn (rho z) s := by
  unfold rho tauAt
  exact ContinuousOn.div (by fun_prop) (by fun_prop) h

/-! ## The test pairs -/

section Tests

variable (x Y : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ)

/-- The pairs `(l D, Y^{-0.7})` of test (i). -/
noncomputable def tests1 : Finset (ℤ × ℝ) :=
  ((univ : Finset (Fin K → Fin M)) ×ˢ Finset.Icc 1 ⌊Y ^ (0.2 : ℝ)⌋₊).image fun ol =>
    (((ol.2 * omitProd ℓ ol.1 : ℕ) : ℤ), Y ^ (-0.7 : ℝ))

/-- The pairs `((DZ − D'Z') T, 100 e^{-L^{a_{i*}}})` of test (ii) for one `I`. -/
noncomputable def tests2I (I : Finset (Fin K)) : Finset (ℤ × ℝ) :=
  if h : I.Nonempty then
    ((univ : Finset (Fin K → Fin M)) ×ˢ ((univ : Finset (Fin K → Fin M)) ×ˢ
      (zTuples x a I (I.max' h) ×ˢ (zTuples x a I (I.max' h) ×ˢ freshTuples x a I)))).image
      fun q => ((((omitProd ℓ q.1 * ∏ i, q.2.2.1 i : ℕ) : ℤ) -
          ((omitProd ℓ q.2.1 * ∏ i, q.2.2.2.1 i : ℕ) : ℤ)) * ((∏ i, q.2.2.2.2 i : ℕ) : ℤ),
        100 * exp (-(log x ^ a (I.max' h))))
  else ∅

/-- All test pairs. -/
noncomputable def tests : Finset (ℤ × ℝ) :=
  tests1 Y ℓ ∪ (univ : Finset (Finset (Fin K))).biUnion (tests2I x a ℓ)

/-- Goodness depends only on the test indicators. -/
theorem isGoodRatio_congr_tests (ρ₁ ρ₂ : ℝ)
    (h : ∀ t ∈ tests x Y a ℓ, (circNorm ((t.1 : ℝ) * ρ₁) < t.2 ↔ circNorm ((t.1 : ℝ) * ρ₂) < t.2) ∧
      (circNorm ((t.1 : ℝ) * ρ₁) ≤ t.2 ↔ circNorm ((t.1 : ℝ) * ρ₂) ≤ t.2)) :
    IsGoodRatio x Y a ℓ ρ₁ ↔ IsGoodRatio x Y a ℓ ρ₂ := by
  classical
  have h1 : ∀ o : Fin K → Fin M, ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (0.2 : ℝ) →
      (Y ^ (-0.7 : ℝ) < circNorm (((l * omitProd ℓ o : ℕ) : ℝ) * ρ₁) ↔
        Y ^ (-0.7 : ℝ) < circNorm (((l * omitProd ℓ o : ℕ) : ℝ) * ρ₂)) := by
    intro o l hl hlY
    have ht : ((((l * omitProd ℓ o : ℕ) : ℤ), Y ^ (-0.7 : ℝ)) : ℤ × ℝ) ∈ tests x Y a ℓ := by
      refine mem_union_left _ (mem_image.2 ⟨(o, l), ?_, rfl⟩)
      exact mem_product.2 ⟨mem_univ _, mem_Icc.2 ⟨hl, Nat.le_floor hlY⟩⟩
    have := (h _ ht).2
    simp only [Int.cast_natCast] at this
    rw [← not_le, ← not_le, this]
  have h2 : ∀ I : Finset (Fin K), ∀ hI : I.Nonempty, ∀ T ∈ freshTuples x a I,
      (SepFails x a ℓ I (I.max' hI) T ρ₁ ↔ SepFails x a ℓ I (I.max' hI) T ρ₂) := by
    intro I hI T hT
    have key : ∀ o o' : Fin K → Fin M, ∀ Z Z' : Fin K → ℕ, Z ∈ zTuples x a I (I.max' hI) →
        Z' ∈ zTuples x a I (I.max' hI) →
        (circNorm ((((((omitProd ℓ o * ∏ i, Z i : ℕ) : ℤ) - ((omitProd ℓ o' * ∏ i, Z' i : ℕ) : ℤ)) *
          ((∏ i, T i : ℕ) : ℤ) : ℤ) : ℝ) * ρ₁) < 100 * exp (-(log x ^ a (I.max' hI))) ↔
        circNorm ((((((omitProd ℓ o * ∏ i, Z i : ℕ) : ℤ) - ((omitProd ℓ o' * ∏ i, Z' i : ℕ) : ℤ)) *
          ((∏ i, T i : ℕ) : ℤ) : ℤ) : ℝ) * ρ₂) < 100 * exp (-(log x ^ a (I.max' hI)))) := by
      intro o o' Z Z' hZ hZ'
      have ht : ((((((omitProd ℓ o * ∏ i, Z i : ℕ) : ℤ) - ((omitProd ℓ o' * ∏ i, Z' i : ℕ) : ℤ)) *
          ((∏ i, T i : ℕ) : ℤ)), 100 * exp (-(log x ^ a (I.max' hI)))) : ℤ × ℝ) ∈
          tests x Y a ℓ := by
        refine mem_union_right _ (mem_biUnion.2 ⟨I, mem_univ _, ?_⟩)
        unfold tests2I
        rw [dif_pos hI]
        exact mem_image.2 ⟨(o, o', Z, Z', T), mem_product.2 ⟨mem_univ _, mem_product.2
          ⟨mem_univ _, mem_product.2 ⟨hZ, mem_product.2 ⟨hZ', hT⟩⟩⟩⟩, rfl⟩
      exact (h _ ht).1
    unfold SepFails
    constructor
    · rintro ⟨o, o', Z, Z', hZ, hZ', hne, hlt⟩
      exact ⟨o, o', Z, Z', hZ, hZ', hne, (key o o' Z Z' hZ hZ').1 hlt⟩
    · rintro ⟨o, o', Z, Z', hZ, hZ', hne, hlt⟩
      exact ⟨o, o', Z, Z', hZ, hZ', hne, (key o o' Z Z' hZ hZ').2 hlt⟩
  unfold IsGoodRatio GoodTestOne GoodTestTwo
  constructor
  · rintro ⟨g1, g2⟩
    refine ⟨fun o l hl hlY => (h1 o l hl hlY).1 (g1 o l hl hlY), fun I hI => ?_⟩
    refine le_of_eq_of_le (sum_congr rfl fun T hT => ?_) (g2 I hI)
    by_cases hs : SepFails x a ℓ I (I.max' hI) T ρ₂
    · rw [if_pos hs, if_pos ((h2 I hI T hT).2 hs)]
    · rw [if_neg hs, if_neg fun h' => hs ((h2 I hI T hT).1 h')]
  · rintro ⟨g1, g2⟩
    refine ⟨fun o l hl hlY => (h1 o l hl hlY).2 (g1 o l hl hlY), fun I hI => ?_⟩
    refine le_of_eq_of_le (sum_congr rfl fun T hT => ?_) (g2 I hI)
    by_cases hs : SepFails x a ℓ I (I.max' hI) T ρ₁
    · rw [if_pos hs, if_pos ((h2 I hI T hT).1 hs)]
    · rw [if_neg hs, if_neg fun h' => hs ((h2 I hI T hT).2 h')]

end Tests

/-! ## Crossings -/

lemma crossing_ivt {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) {r₁ r₂ : ℝ}
    (h₁ : r₁ ∈ Set.Icc a b) (h₂ : r₂ ∈ Set.Icc a b) {θ : ℝ}
    (hch : ¬ ((f r₁ < θ ↔ f r₂ < θ) ∧ (f r₁ ≤ θ ↔ f r₂ ≤ θ))) :
    ∃ r ∈ Set.Icc a b, f r = θ := by
  have hsub : Set.uIcc r₁ r₂ ⊆ Set.Icc a b := Set.uIcc_subset_Icc h₁ h₂
  have hθ : θ ∈ Set.uIcc (f r₁) (f r₂) := by
    rw [Set.mem_uIcc]
    by_contra hc
    apply hch
    rcases lt_trichotomy (f r₁) θ with h1 | h1 | h1 <;>
      rcases lt_trichotomy (f r₂) θ with h2 | h2 | h2 <;>
      first
      | exact ⟨iff_of_true h1 h2, iff_of_true h1.le h2.le⟩
      | exact ⟨iff_of_false (not_lt.2 h1.le) (not_lt.2 h2.le), iff_of_false (not_le.2 h1) (not_le.2 h2)⟩
      | (exfalso; apply hc; first
          | exact Or.inl ⟨by linarith, by linarith⟩
          | exact Or.inr ⟨by linarith, by linarith⟩)
  obtain ⟨r, hr, hfr⟩ := intermediate_value_uIcc (hf.mono hsub) hθ
  exact ⟨r, hsub hr, hfr⟩

lemma slab_mem_card_le (n : ℕ) (hn : 0 < n) (r : ℝ) :
    ((range n).filter fun k : ℕ => r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)).card ≤ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_or_ge r 0 with hr | hr
  · have : ((range n).filter fun k : ℕ => r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) = ∅ :=
      filter_false_of_mem fun k _ hk => by
        have := hk.1; have : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
        linarith
    rw [this]; simp
  · refine (card_le_card (t := Finset.Icc (⌊r * n⌋₊ - 1) ⌊r * n⌋₊) fun k hk => ?_).trans ?_
    · obtain ⟨-, h1, h2⟩ := mem_filter.1 hk
      rw [div_le_iff₀ hn'] at h1
      rw [le_div_iff₀ hn'] at h2
      rw [mem_Icc]
      constructor
      · have : (⌊r * n⌋₊ : ℝ) ≤ k + 1 := (Nat.floor_le (mul_nonneg hr hn'.le)).trans h2
        have : ⌊r * n⌋₊ ≤ k + 1 := by exact_mod_cast this
        omega
      · exact Nat.le_floor h1
    · rw [Nat.card_Icc]; omega

lemma card_image_diam {α : Type*} (s : Finset α) (g : α → ℤ) (M : ℕ)
    (h : ∀ x ∈ s, ∀ y ∈ s, |g x - g y| ≤ M) : (s.image g).card ≤ 2 * M + 1 := by
  classical
  rcases s.eq_empty_or_nonempty with hs | ⟨x₀, hx₀⟩
  · rw [hs]; simp
  · refine (card_le_card (t := Finset.Icc (g x₀ - M) (g x₀ + M)) fun j hj => ?_).trans ?_
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hj
      have := abs_le.1 (h x hx x₀ hx₀)
      rw [mem_Icc]; constructor <;> linarith
    · rw [Int.card_Icc]; omega

open Classical in
/-- **Bad slabs of one entry.** -/
theorem card_bad_q (x Y : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ) {z : ℤ × ℤ}
    (hz : Int.gcd z.1 z.2 = 1) {Zb : ℝ} (hZ : |(z.2 : ℝ)| ≤ Zb) {n : ℕ} (hn : 0 < n)
    (hZn : Zb / n ≤ 1 / 64) {Mt : ℝ} (hMt : ∀ t ∈ tests x Y a ℓ, |(t.1 : ℝ)| ≤ Mt) :
    ((range n).filter fun k : ℕ => 1 / 32 < tauAt z ((k : ℝ) / n) ∧
      ¬ ∀ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        ∀ r' ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
          (IsGoodRatio x Y a ℓ (rho z r) ↔ IsGoodRatio x Y a ℓ (rho z r'))).card ≤
      2 * ((tests x Y a ℓ).card * 2 * (2 * ⌈4096 * Mt⌉₊ + 1)) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set Bk := (range n).filter fun k : ℕ => 1 / 32 < tauAt z ((k : ℝ) / n) ∧
      ¬ ∀ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
        ∀ r' ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
          (IsGoodRatio x Y a ℓ (rho z r) ↔ IsGoodRatio x Y a ℓ (rho z r'))
  -- `τ ≥ 1/64` on a slab with `τ(k/n) > 1/32`
  have htau : ∀ k ∈ Bk, ∀ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n), 1 / 64 ≤ tauAt z r := by
    intro k hk r hr
    have h1 := (mem_filter.1 hk).2.1
    have hc := abs_tauAt_sub z r ((k : ℝ) / n)
    have hr' : |r - (k : ℝ) / n| ≤ 1 / n := by
      rw [abs_le]; constructor
      · have : (0 : ℝ) ≤ 1 / n := by positivity
        linarith [hr.1]
      · have : ((k : ℝ) + 1) / n = k / n + 1 / n := by ring
        linarith [hr.2]
    have : |(z.2 : ℝ)| * |r - (k : ℝ) / n| ≤ Zb * (1 / n) :=
      mul_le_mul hZ hr' (abs_nonneg _) ((abs_nonneg _).trans hZ)
    have := (abs_le.1 (le_of_eq hc)).1
    have : Zb * (1 / n) = Zb / n := by ring
    nlinarith
  have hr01 : ∀ k ∈ Bk, ∀ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n), 0 ≤ r ∧ r ≤ 1 := by
    intro k hk r hr
    have hk' := mem_range.1 (mem_filter.1 hk).1
    refine ⟨le_trans (by positivity) hr.1, hr.2.trans ?_⟩
    rw [div_le_one hn']; exact_mod_cast hk'
  -- a crossing in every bad slab
  have hcross : ∀ k ∈ Bk, ∃ t ∈ tests x Y a ℓ, ∃ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
      t.1 ≠ 0 ∧ circNorm ((t.1 : ℝ) * rho z r) = t.2 := by
    intro k hk
    obtain ⟨-, -, hnot⟩ := mem_filter.1 hk
    simp only [not_forall] at hnot
    obtain ⟨r₁, h₁, r₂, h₂, hne⟩ := hnot
    have hex : ∃ t ∈ tests x Y a ℓ, ¬ ((circNorm ((t.1 : ℝ) * rho z r₁) < t.2 ↔
        circNorm ((t.1 : ℝ) * rho z r₂) < t.2) ∧ (circNorm ((t.1 : ℝ) * rho z r₁) ≤ t.2 ↔
        circNorm ((t.1 : ℝ) * rho z r₂) ≤ t.2)) := by
      by_contra hall
      push Not at hall
      apply hne
      exact isGoodRatio_congr_tests x Y a ℓ _ _ fun t ht => by
        by_contra h; exact absurd (hall t ht) (by tauto)
    obtain ⟨t, ht, hch⟩ := hex
    have hcont : ContinuousOn (fun r => circNorm ((t.1 : ℝ) * rho z r))
        (Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n)) := by
      refine L102D.continuous_circNorm.comp_continuousOn (ContinuousOn.mul continuousOn_const ?_)
      exact continuousOn_rho z fun r hr => (by linarith [htau k hk r hr] : tauAt z r ≠ 0)
    obtain ⟨r, hr, hfr⟩ := crossing_ivt hcont h₁ h₂ hch
    refine ⟨t, ht, r, hr, fun h0 => hch ?_, hfr⟩
    simp [h0]
  choose! tt htt rr hrr ht0 hcr using hcross
  -- the label of a crossing
  set y : ℕ → ℝ := fun k => ((tt k).1 : ℝ) * rho z (rr k)
  set jj : ℕ → ℤ := fun k => round (y k)
  set σ : ℕ → Bool := fun k => decide (y k - jj k = (tt k).2)
  have hyj : ∀ k ∈ Bk, y k - jj k = if σ k then (tt k).2 else -(tt k).2 := by
    intro k hk
    have h := hcr k hk
    unfold circNorm at h
    have hθ : 0 ≤ (tt k).2 := h ▸ abs_nonneg _
    by_cases hs : y k - jj k = (tt k).2
    · simp only [σ, hs, decide_true, if_true]
    · have : y k - jj k = -(tt k).2 := by
        rcases abs_eq hθ |>.1 h with h1 | h1
        · exact absurd h1 hs
        · exact h1
      simp only [σ, hs, decide_false, if_false, Bool.false_eq_true]; exact this
  set F : ℕ → (ℤ × ℝ) × Bool × ℤ := fun k => (tt k, σ k, jj k)
  -- `ρ` is injective and `4096`-Lipschitz on the bad slabs
  have hrho : ∀ k ∈ Bk, ∀ k' ∈ Bk, rho z (rr k) - rho z (rr k') =
      (rr k - rr k') / (tauAt z (rr k) * tauAt z (rr k')) := fun k hk k' hk' =>
    rho_sub hz (by linarith [htau k hk _ (hrr k hk)]) (by linarith [htau k' hk' _ (hrr k' hk')])
  -- fibres have at most two slabs
  have hfib : ∀ b ∈ Bk.image F, (Bk.filter fun k => F k = b).card ≤ 2 := by
    intro b hb
    obtain ⟨k₀, hk₀, rfl⟩ := mem_image.1 hb
    refine (card_le_card fun k hk => ?_).trans (slab_mem_card_le n hn (rr k₀))
    obtain ⟨hkB, hFk⟩ := mem_filter.1 hk
    simp only [F, Prod.mk.injEq] at hFk
    obtain ⟨e1, e2, e3⟩ := hFk
    have hy : y k = y k₀ := by
      have a1 := hyj k hkB
      have a2 := hyj k₀ hk₀
      rw [e1, e2] at a1
      rw [e3] at a1
      linarith
    have hr : rr k = rr k₀ := by
      have h0 := ht0 k₀ hk₀
      simp only [y, e1] at hy
      have h0' : ((tt k₀).1 : ℝ) ≠ 0 := by exact_mod_cast h0
      have hρ : rho z (rr k) = rho z (rr k₀) := mul_left_cancel₀ h0' hy
      have := hrho k hkB k₀ hk₀
      rw [hρ, sub_self] at this
      have hpos : 0 < tauAt z (rr k) * tauAt z (rr k₀) := by
        have := htau k hkB _ (hrr k hkB); have := htau k₀ hk₀ _ (hrr k₀ hk₀)
        positivity
      have := (div_eq_zero_iff.1 this.symm).resolve_right hpos.ne'
      linarith
    exact mem_filter.2 ⟨(mem_filter.1 hkB).1, hr ▸ hrr k hkB⟩
  have h1 := Finset.card_le_mul_card_image Bk 2 hfib
  -- the image: per test and sign, the labels have diameter `≤ 4096 Mt`
  set Mn := ⌈4096 * Mt⌉₊
  have hsub : Bk.image F ⊆ ((tests x Y a ℓ) ×ˢ (univ : Finset Bool)).biUnion fun ts =>
      (Bk.filter fun k => (tt k, σ k) = ts).image fun k => (ts.1, ts.2, jj k) := by
    intro b hb
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hb
    refine mem_biUnion.2 ⟨(tt k, σ k), mem_product.2 ⟨htt k hk, mem_univ _⟩, ?_⟩
    exact mem_image.2 ⟨k, mem_filter.2 ⟨hk, rfl⟩, rfl⟩
  have h2 : (Bk.image F).card ≤ (tests x Y a ℓ).card * 2 * (2 * Mn + 1) := by
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    calc ∑ ts ∈ (tests x Y a ℓ) ×ˢ (univ : Finset Bool),
          ((Bk.filter fun k => (tt k, σ k) = ts).image fun k => (ts.1, ts.2, jj k)).card
        ≤ ∑ _ts ∈ (tests x Y a ℓ) ×ˢ (univ : Finset Bool), (2 * Mn + 1) := by
          refine sum_le_sum fun ts _ => ?_
          have : ((Bk.filter fun k => (tt k, σ k) = ts).image fun k => (ts.1, ts.2, jj k)) =
              ((Bk.filter fun k => (tt k, σ k) = ts).image jj).image
                fun j : ℤ => (ts.1, ts.2, j) := by
            rw [image_image]; rfl
          rw [this]
          refine card_image_le.trans ?_
          refine card_image_diam _ jj Mn fun k hk k' hk' => ?_
          obtain ⟨hkB, hks⟩ := mem_filter.1 hk
          obtain ⟨hkB', hks'⟩ := mem_filter.1 hk'
          have e := hks.trans hks'.symm
          simp only [Prod.mk.injEq] at e
          have a1 := hyj k hkB
          have a2 := hyj k' hkB'
          rw [e.1, e.2] at a1
          have hjj : (jj k : ℝ) - jj k' = y k - y k' := by linarith
          have hyy : y k - y k' = ((tt k').1 : ℝ) * (rho z (rr k) - rho z (rr k')) := by
            simp only [y, e.1]; ring
          have hρ := hrho k hkB k' hkB'
          have t1 := htau k hkB _ (hrr k hkB)
          have t2 := htau k' hkB' _ (hrr k' hkB')
          have r1 := hr01 k hkB _ (hrr k hkB)
          have r2 := hr01 k' hkB' _ (hrr k' hkB')
          have hlip : |rho z (rr k) - rho z (rr k')| ≤ 4096 := by
            rw [hρ, abs_div, abs_of_pos (by positivity : 0 < tauAt z (rr k) * tauAt z (rr k'))]
            rw [div_le_iff₀ (by positivity)]
            have : |rr k - rr k'| ≤ 1 := by rw [abs_le]; constructor <;> linarith
            nlinarith
          have hM := hMt _ (htt k' hkB')
          have : |((jj k - jj k' : ℤ) : ℝ)| ≤ 4096 * Mt := by
            push_cast; rw [hjj, hyy, abs_mul]
            calc |((tt k').1 : ℝ)| * |rho z (rr k) - rho z (rr k')| ≤ Mt * 4096 :=
                  mul_le_mul hM hlip (abs_nonneg _) ((abs_nonneg _).trans hM)
              _ = 4096 * Mt := by ring
          have h4 : 4096 * Mt ≤ (Mn : ℝ) := Nat.le_ceil _
          have : |((jj k - jj k' : ℤ) : ℝ)| ≤ (Mn : ℝ) := this.trans h4
          exact_mod_cast this
      _ = (tests x Y a ℓ).card * 2 * (2 * Mn + 1) := by
          rw [sum_const, card_product, card_univ, Fintype.card_bool, smul_eq_mul]
  calc Bk.card ≤ 2 * (Bk.image F).card := h1
    _ ≤ 2 * ((tests x Y a ℓ).card * 2 * (2 * Mn + 1)) := by gcongr

/-! ## Bad slabs of a list -/

open Classical in
/-- **Bad slabs of a list**: at most `|L| · 4 T (2(4096 M + 1) + 1)`. -/
theorem card_badSlab_le (P : MemParams) (L : List ((ℤ × ℤ) × P.Lst))
    (hz : ∀ q ∈ L, Int.gcd q.1.1 q.1.2 = 1) {Zb : ℝ} (hZ : ∀ q ∈ L, |(q.1.2 : ℝ)| ≤ Zb)
    {n : ℕ} (hn : 0 < n) (hZn : Zb / n ≤ 1 / 64) {Mt : ℝ} (hMt0 : 0 ≤ Mt)
    (hMt : ∀ q ∈ L, ∀ t ∈ tests P.x P.Y P.a q.2, |(t.1 : ℝ)| ≤ Mt) {Tc : ℝ}
    (hTc : ∀ q ∈ L, ((tests P.x P.Y P.a q.2).card : ℝ) ≤ Tc) :
    (((range n).filter fun k => BadSlab P L n k).card : ℝ) ≤
      L.length * (4 * Tc * (2 * (4096 * Mt + 1) + 1)) := by
  have hsub : ((range n).filter fun k => BadSlab P L n k) ⊆ L.toFinset.biUnion fun q =>
      (range n).filter fun k : ℕ => 1 / 32 < tauAt q.1 ((k : ℝ) / n) ∧
        ¬ ∀ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
          ∀ r' ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
            (IsGoodRatio P.x P.Y P.a q.2 (rho q.1 r) ↔ IsGoodRatio P.x P.Y P.a q.2 (rho q.1 r')) := by
    intro k hk
    obtain ⟨hkr, htau, hgc⟩ := mem_filter.1 hk
    unfold GoodConst at hgc
    simp only [not_forall] at hgc
    obtain ⟨q, hq, r, hr, r', hr', hne⟩ := hgc
    refine mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, mem_filter.2 ⟨hkr, htau q hq, ?_⟩⟩
    intro hall
    exact hne (hall r hr r' hr')
  have hTc0 : ∀ q ∈ L, 0 ≤ Tc := fun q hq => (Nat.cast_nonneg _).trans (hTc q hq)
  have hceil : ((⌈4096 * Mt⌉₊ : ℕ) : ℝ) ≤ 4096 * Mt + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hbound : ∀ q ∈ L.toFinset, ((((range n).filter fun k : ℕ => 1 / 32 < tauAt q.1 ((k : ℝ) / n) ∧
        ¬ ∀ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
          ∀ r' ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
            (IsGoodRatio P.x P.Y P.a q.2 (rho q.1 r) ↔
              IsGoodRatio P.x P.Y P.a q.2 (rho q.1 r'))).card : ℕ) : ℝ) ≤
        4 * Tc * (2 * (4096 * Mt + 1) + 1) := by
    intro q hq
    have hq' := List.mem_toFinset.1 hq
    have h := card_bad_q P.x P.Y P.a q.2 (hz q hq') (hZ q hq') hn hZn (hMt q hq')
    have h' : (((range n).filter fun k : ℕ => 1 / 32 < tauAt q.1 ((k : ℝ) / n) ∧
        ¬ ∀ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
          ∀ r' ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
            (IsGoodRatio P.x P.Y P.a q.2 (rho q.1 r) ↔
              IsGoodRatio P.x P.Y P.a q.2 (rho q.1 r'))).card : ℝ) ≤
        2 * (((tests P.x P.Y P.a q.2).card : ℝ) * 2 * (2 * (⌈4096 * Mt⌉₊ : ℝ) + 1)) := by
      exact_mod_cast h
    refine h'.trans ?_
    have := hTc q hq'
    have hc0 : (0 : ℝ) ≤ (⌈4096 * Mt⌉₊ : ℝ) := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ ((tests P.x P.Y P.a q.2).card : ℝ) := Nat.cast_nonneg _
    calc 2 * (((tests P.x P.Y P.a q.2).card : ℝ) * 2 * (2 * (⌈4096 * Mt⌉₊ : ℝ) + 1))
        = 4 * ((tests P.x P.Y P.a q.2).card : ℝ) * (2 * (⌈4096 * Mt⌉₊ : ℝ) + 1) := by ring
      _ ≤ 4 * Tc * (2 * (4096 * Mt + 1) + 1) := by
          have := hTc0 q hq'
          apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have h1 := card_le_card hsub
  have h2 := card_biUnion_le (s := L.toFinset) (t := fun q =>
      (range n).filter fun k : ℕ => 1 / 32 < tauAt q.1 ((k : ℝ) / n) ∧
        ¬ ∀ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
          ∀ r' ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
            (IsGoodRatio P.x P.Y P.a q.2 (rho q.1 r) ↔ IsGoodRatio P.x P.Y P.a q.2 (rho q.1 r')))
  have h3 : (((range n).filter fun k => BadSlab P L n k).card : ℝ) ≤
      ∑ q ∈ L.toFinset, ((((range n).filter fun k : ℕ => 1 / 32 < tauAt q.1 ((k : ℝ) / n) ∧
        ¬ ∀ r ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
          ∀ r' ∈ Set.Icc ((k : ℝ) / n) (((k : ℝ) + 1) / n),
            (IsGoodRatio P.x P.Y P.a q.2 (rho q.1 r) ↔
              IsGoodRatio P.x P.Y P.a q.2 (rho q.1 r'))).card : ℕ) : ℝ) := by
    exact_mod_cast h1.trans h2
  refine h3.trans ((sum_le_sum hbound).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  by_cases hL : L = []
  · simp [hL]
  · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil L hL
    have : (0 : ℝ) ≤ 4 * Tc * (2 * (4096 * Mt + 1) + 1) := by
      have := hTc0 q hq; positivity
    gcongr
    exact_mod_cast List.toFinset_card_le L

/-! ## Size of the tests -/

lemma omitProd_le {K M : ℕ} {ℓ : Fin K → Fin M → ℕ} {Bp : ℝ} (hBp : 1 ≤ Bp)
    (hℓ : ∀ i j, (ℓ i j : ℝ) ≤ Bp) (o : Fin K → Fin M) :
    ((omitProd ℓ o : ℕ) : ℝ) ≤ Bp ^ (K * M) := by
  unfold omitProd
  push_cast
  calc ∏ i, ∏ j ∈ univ.erase (o i), (ℓ i j : ℝ) ≤ ∏ _i : Fin K, ∏ _j : Fin M, Bp := by
        refine prod_le_prod (fun i _ => prod_nonneg fun j _ => by positivity) fun i _ => ?_
        calc ∏ j ∈ univ.erase (o i), (ℓ i j : ℝ) ≤ ∏ _j ∈ univ.erase (o i), Bp :=
              prod_le_prod (fun j _ => by positivity) fun j _ => hℓ i j
          _ ≤ ∏ _j : Fin M, Bp := by
              rw [prod_const, prod_const]
              exact pow_le_pow_right₀ hBp (card_le_card (erase_subset _ _))
    _ = Bp ^ (K * M) := by
        simp only [prod_const, card_univ, Fintype.card_fin]; rw [← pow_mul, mul_comm]

lemma tuple_prod_le {K : ℕ} {T : Fin K → ℕ} {Bp : ℝ} (hBp : 1 ≤ Bp) (hT : ∀ i, (T i : ℝ) ≤ Bp) :
    ((∏ i, T i : ℕ) : ℝ) ≤ Bp ^ K := by
  push_cast
  calc ∏ i, (T i : ℝ) ≤ ∏ _i : Fin K, Bp := prod_le_prod (fun i _ => by positivity) fun i _ => hT i
    _ = Bp ^ K := by simp

lemma mem_tuples_le {K : ℕ} {s : Fin K → Finset ℕ} {T : Fin K → ℕ} (hT : T ∈ Fintype.piFinset s)
    {Bp : ℝ} (hBp : 1 ≤ Bp) (hs : ∀ i, ∀ p ∈ s i, (p : ℝ) ≤ Bp) (i : Fin K) : (T i : ℝ) ≤ Bp :=
  hs i _ (Fintype.mem_piFinset.1 hT i)

/-- The test integers are `≤ (Y^{0.2} + 2) B^{KM + 2K}`. -/
theorem tests_le (x Y : ℝ) (hY : 1 ≤ Y) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ)
    {Bp : ℝ} (hBp : 1 ≤ Bp) (hℓ : ∀ i j, (ℓ i j : ℝ) ≤ Bp)
    (hG : ∀ i, ∀ p ∈ primeGroup x (a i), (p : ℝ) ≤ Bp) :
    ∀ t ∈ tests x Y a ℓ, |(t.1 : ℝ)| ≤ (Y ^ (0.2 : ℝ) + 2) * Bp ^ (K * M + 2 * K) := by
  have hY2 : 0 ≤ Y ^ (0.2 : ℝ) := by positivity
  have hB1 : Bp ^ (K * M) ≤ Bp ^ (K * M + 2 * K) := pow_le_pow_right₀ hBp (by omega)
  have hB0 : 0 ≤ Bp ^ (K * M) := by positivity
  intro t ht
  rcases mem_union.1 ht with ht | ht
  · obtain ⟨ol, hol, rfl⟩ := mem_image.1 ht
    obtain ⟨-, hl⟩ := mem_product.1 hol
    have hl' : (ol.2 : ℝ) ≤ Y ^ (0.2 : ℝ) :=
      (Nat.cast_le.2 (mem_Icc.1 hl).2).trans (Nat.floor_le hY2)
    have e : ((((ol.2 * omitProd ℓ ol.1 : ℕ) : ℤ) : ℝ)) = (ol.2 : ℝ) * (omitProd ℓ ol.1 : ℝ) := by
      push_cast; ring
    show |((((ol.2 * omitProd ℓ ol.1 : ℕ) : ℤ) : ℝ))| ≤ _
    rw [e, abs_of_nonneg (by positivity)]
    have h1 := omitProd_le hBp hℓ ol.1
    calc (ol.2 : ℝ) * (omitProd ℓ ol.1 : ℝ) ≤ Y ^ (0.2 : ℝ) * Bp ^ (K * M) :=
          mul_le_mul hl' h1 (by positivity) hY2
      _ ≤ (Y ^ (0.2 : ℝ) + 2) * Bp ^ (K * M + 2 * K) := by
          apply mul_le_mul (by linarith) hB1 hB0 (by positivity)
  · obtain ⟨I, -, hI⟩ := mem_biUnion.1 ht
    unfold tests2I at hI
    split_ifs at hI with hne
    · obtain ⟨q, hq, rfl⟩ := mem_image.1 hI
      simp only [mem_product, mem_univ, true_and] at hq
      obtain ⟨hZ, hZ', hT⟩ := hq
      have hzs : ∀ i, ∀ p ∈ (if i ∈ I ∧ i ≠ I.max' hne then primeGroup x (a i) else {1}),
          (p : ℝ) ≤ Bp := by
        intro i p hp
        split_ifs at hp with h
        · exact hG i p hp
        · rw [mem_singleton.1 hp]; simpa using hBp
      have hfs : ∀ i, ∀ p ∈ (if i ∈ I then {1} else primeGroup x (a i)), (p : ℝ) ≤ Bp := by
        intro i p hp
        split_ifs at hp with h
        · rw [mem_singleton.1 hp]; simpa using hBp
        · exact hG i p hp
      have h1 := omitProd_le hBp hℓ q.1
      have h2 := omitProd_le hBp hℓ q.2.1
      have h3 := tuple_prod_le hBp (mem_tuples_le hZ hBp hzs)
      have h4 := tuple_prod_le hBp (mem_tuples_le hZ' hBp hzs)
      have h5 := tuple_prod_le hBp (mem_tuples_le hT hBp hfs)
      have hBK : 0 ≤ Bp ^ K := by positivity
      push_cast
      rw [abs_mul]
      have hA : |((omitProd ℓ q.1 : ℝ) * ∏ i, (q.2.2.1 i : ℝ)) -
          (omitProd ℓ q.2.1 : ℝ) * ∏ i, (q.2.2.2.1 i : ℝ)| ≤ 2 * (Bp ^ (K * M) * Bp ^ K) := by
        push_cast at h3 h4
        have p1 : 0 ≤ (omitProd ℓ q.1 : ℝ) * ∏ i, (q.2.2.1 i : ℝ) := by positivity
        have p2 : 0 ≤ (omitProd ℓ q.2.1 : ℝ) * ∏ i, (q.2.2.2.1 i : ℝ) := by positivity
        have q1 : (omitProd ℓ q.1 : ℝ) * ∏ i, (q.2.2.1 i : ℝ) ≤ Bp ^ (K * M) * Bp ^ K :=
          mul_le_mul h1 h3 (by positivity) hB0
        have q2 : (omitProd ℓ q.2.1 : ℝ) * ∏ i, (q.2.2.2.1 i : ℝ) ≤ Bp ^ (K * M) * Bp ^ K :=
          mul_le_mul h2 h4 (by positivity) hB0
        rw [abs_le]; constructor <;> nlinarith
      push_cast at h5
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ∏ i, (q.2.2.2.2 i : ℝ))]
      calc |((omitProd ℓ q.1 : ℝ) * ∏ i, (q.2.2.1 i : ℝ)) -
            (omitProd ℓ q.2.1 : ℝ) * ∏ i, (q.2.2.2.1 i : ℝ)| * ∏ i, (q.2.2.2.2 i : ℝ)
          ≤ 2 * (Bp ^ (K * M) * Bp ^ K) * Bp ^ K := mul_le_mul hA h5 (by positivity) (by positivity)
        _ = 2 * Bp ^ (K * M + 2 * K) := by ring
        _ ≤ (Y ^ (0.2 : ℝ) + 2) * Bp ^ (K * M + 2 * K) := by
            apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    · simp at hI

lemma card_tuples_le {K : ℕ} (s : Fin K → Finset ℕ) {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hs : ∀ i, ((s i).card : ℝ) ≤ Cg) : ((Fintype.piFinset s).card : ℝ) ≤ Cg ^ K := by
  rw [Fintype.card_piFinset]
  push_cast
  calc ∏ i, ((s i).card : ℝ) ≤ ∏ _i : Fin K, Cg := prod_le_prod (fun i _ => by positivity)
        fun i _ => hs i
    _ = Cg ^ K := by simp

/-- The number of tests is `≤ M^K Y^{0.2} + 2^K M^{2K} C^{3K}`. -/
theorem card_tests_le (x Y : ℝ) (hY : 1 ≤ Y) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ)
    {Cg : ℝ} (hCg : 1 ≤ Cg) (hG : ∀ i, ((primeGroup x (a i)).card : ℝ) ≤ Cg) :
    ((tests x Y a ℓ).card : ℝ) ≤
      (M : ℝ) ^ K * Y ^ (0.2 : ℝ) + 2 ^ K * ((M : ℝ) ^ (2 * K) * Cg ^ (3 * K)) := by
  have hY2 : 0 ≤ Y ^ (0.2 : ℝ) := by positivity
  have h1 : ((tests1 Y ℓ).card : ℝ) ≤ (M : ℝ) ^ K * Y ^ (0.2 : ℝ) := by
    unfold tests1
    refine (Nat.cast_le.2 card_image_le).trans ?_
    rw [card_product, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      Nat.card_Icc]
    push_cast
    gcongr
    calc ((⌊Y ^ (0.2 : ℝ)⌋₊ + 1 - 1 : ℕ) : ℝ) = (⌊Y ^ (0.2 : ℝ)⌋₊ : ℝ) := by simp
      _ ≤ Y ^ (0.2 : ℝ) := Nat.floor_le hY2
  have hzs : ∀ I : Finset (Fin K), ∀ i₀ : Fin K, ∀ i,
      (((if i ∈ I ∧ i ≠ i₀ then primeGroup x (a i) else {1}) : Finset ℕ).card : ℝ) ≤ Cg := by
    intro I i₀ i; split_ifs
    · exact hG i
    · simpa using hCg
  have hfs : ∀ I : Finset (Fin K), ∀ i,
      (((if i ∈ I then {1} else primeGroup x (a i)) : Finset ℕ).card : ℝ) ≤ Cg := by
    intro I i; split_ifs
    · simpa using hCg
    · exact hG i
  have h2 : ∀ I : Finset (Fin K), ((tests2I x a ℓ I).card : ℝ) ≤
      (M : ℝ) ^ (2 * K) * Cg ^ (3 * K) := by
    intro I
    unfold tests2I
    split_ifs with hne
    · refine (Nat.cast_le.2 card_image_le).trans ?_
      simp only [card_product, card_univ, Fintype.card_fun, Fintype.card_fin]
      push_cast
      have a1 := card_tuples_le _ hCg (hzs I (I.max' hne))
      have a2 := card_tuples_le _ hCg (hfs I)
      unfold zTuples freshTuples
      calc (M : ℝ) ^ K * ((M : ℝ) ^ K * (((Fintype.piFinset fun i =>
              if i ∈ I ∧ i ≠ I.max' hne then primeGroup x (a i) else {1}).card : ℝ) *
            (((Fintype.piFinset fun i =>
              if i ∈ I ∧ i ≠ I.max' hne then primeGroup x (a i) else {1}).card : ℝ) *
            ((Fintype.piFinset fun i => if i ∈ I then {1} else primeGroup x (a i)).card : ℝ))))
          ≤ (M : ℝ) ^ K * ((M : ℝ) ^ K * (Cg ^ K * (Cg ^ K * Cg ^ K))) := by gcongr
        _ = (M : ℝ) ^ (2 * K) * Cg ^ (3 * K) := by ring
    · simp; positivity
  unfold tests
  refine (Nat.cast_le.2 (card_union_le _ _)).trans ?_
  push_cast
  refine add_le_add h1 ?_
  refine (Nat.cast_le.2 card_biUnion_le).trans ?_
  push_cast
  calc ∑ I : Finset (Fin K), ((tests2I x a ℓ I).card : ℝ)
      ≤ ∑ _I : Finset (Fin K), (M : ℝ) ^ (2 * K) * Cg ^ (3 * K) := sum_le_sum fun I _ => h2 I
    _ = 2 ^ K * ((M : ℝ) ^ (2 * K) * Cg ^ (3 * K)) := by
        rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): measurability of the regions and the triple integral

* Goodness depends on finitely many measurable test sets, so `{ρ | IsGoodRatio ρ}` is measurable
  (`measurableSet_of_tests`, `measurableSet_isGoodRatio`), and so are the archimedean sets
  `AL L = {p | ∀ q ∈ L, box ∧ goodness}` and the regions `RegionN L = AL L ∩ boxN`.
* The iterated interval integral over `[1,16] × [1,2] × [0,1]` is the integral over
  `boxN = [1,16] × [1,2] × [0,1)` (`fubini3`), and indicator integrals are volumes. -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory

/-- A predicate determined by finitely many measurable sets is measurable. -/
lemma measurableSet_of_tests {α ι : Type*} [MeasurableSpace α] (T : Finset ι) (B : ι → Set α)
    (hB : ∀ i ∈ T, MeasurableSet (B i)) (Q : α → Prop)
    (hQ : ∀ x y, (∀ i ∈ T, (x ∈ B i ↔ y ∈ B i)) → (Q x ↔ Q y)) : MeasurableSet {x | Q x} := by
  classical
  set pat : α → Finset ι := fun x => T.filter fun i => x ∈ B i with hpat
  set atom : Finset ι → Set α := fun s => ⋂ i ∈ T, (if i ∈ s then B i else (B i)ᶜ) with hatomd
  have hatom : ∀ s, MeasurableSet (atom s) := fun s =>
    Finset.measurableSet_biInter T fun i hi => by
      split_ifs
      · exact hB i hi
      · exact (hB i hi).compl
  have hmem : ∀ x y, y ∈ atom (pat x) ↔ ∀ i ∈ T, (x ∈ B i ↔ y ∈ B i) := by
    intro x y
    simp only [hatomd, hpat, Set.mem_iInter, mem_filter]
    refine forall₂_congr fun i hi => ?_
    by_cases hx : x ∈ B i
    · simp [hi, hx]
    · simp [hx]
  have hset : {x | Q x} = ⋃ s ∈ (T.powerset.filter fun s => ∃ x, Q x ∧ pat x = s), atom s := by
    ext y
    constructor
    · intro hy
      exact Set.mem_iUnion₂.2 ⟨pat y, mem_filter.2 ⟨mem_powerset.2 (filter_subset _ _), y, hy, rfl⟩,
        (hmem y y).2 fun i _ => Iff.rfl⟩
    · intro hy
      obtain ⟨s, hs, hys⟩ := Set.mem_iUnion₂.1 hy
      obtain ⟨-, x, hx, rfl⟩ := mem_filter.1 hs
      exact (hQ x y ((hmem x y).1 hys)).1 hx
  rw [hset]
  exact Finset.measurableSet_biUnion _ fun s _ => hatom s

lemma measurableSet_isGoodRatio (x Y : ℝ) {K M : ℕ} (a : Fin K → ℝ) (ℓ : Fin K → Fin M → ℕ) :
    MeasurableSet {ρ : ℝ | IsGoodRatio x Y a ℓ ρ} := by
  classical
  refine measurableSet_of_tests (tests x Y a ℓ ×ˢ (univ : Finset Bool))
    (fun tb => if tb.2 then {ρ : ℝ | circNorm ((tb.1.1 : ℝ) * ρ) < tb.1.2}
      else {ρ : ℝ | circNorm ((tb.1.1 : ℝ) * ρ) ≤ tb.1.2}) ?_ _ ?_
  · intro tb _
    have hc : Continuous fun ρ : ℝ => circNorm ((tb.1.1 : ℝ) * ρ) :=
      L102D.continuous_circNorm.comp (continuous_const.mul continuous_id)
    split_ifs
    · exact measurableSet_lt hc.measurable measurable_const
    · exact measurableSet_le hc.measurable measurable_const
  · intro ρ₁ ρ₂ h
    refine isGoodRatio_congr_tests x Y a ℓ ρ₁ ρ₂ fun t ht => ⟨?_, ?_⟩
    · have := h (t, true) (mem_product.2 ⟨ht, mem_univ _⟩)
      simpa using this
    · have := h (t, false) (mem_product.2 ⟨ht, mem_univ _⟩)
      simpa using this

lemma measurable_tauAt (z : ℤ × ℤ) : Measurable (tauAt z) := by
  unfold tauAt; fun_prop

lemma measurable_rho (z : ℤ × ℤ) : Measurable (rho z) := by
  unfold rho
  exact (measurable_tauAt _).div (measurable_tauAt _)

variable (P : MemParams)

/-- The archimedean set of a list in normalized coordinates (no box conditions). -/
def AL (L : List ((ℤ × ℤ) × P.Lst)) : Set (ℝ × ℝ × ℝ) :=
  {p | ∀ q ∈ L, P.InBox (P.U * p.1, P.V * p.2.1, p.2.2) q.1 ∧ goodR P q p.2.2}

/-- The normalized box `[1,16] × [1,2] × [0,1)`. -/
def boxN : Set (ℝ × ℝ × ℝ) := Set.Icc 1 16 ×ˢ (Set.Icc 1 2 ×ˢ Set.Ico 0 1)

lemma regionN_eq (L : List ((ℤ × ℤ) × P.Lst)) : {p | RegionN P L p} = AL P L ∩ boxN := by
  ext p
  simp only [Set.mem_setOf_eq, RegionN, AL, boxN, Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc,
    Set.mem_Ico]
  tauto

lemma measurableSet_entry (q : (ℤ × ℤ) × P.Lst) :
    MeasurableSet {p : ℝ × ℝ × ℝ | P.InBox (P.U * p.1, P.V * p.2.1, p.2.2) q.1 ∧
      goodR P q p.2.2} := by
  have hτ : Measurable fun p : ℝ × ℝ × ℝ => (q.1.1 : ℝ) + p.2.2 * q.1.2 := by fun_prop
  have h1 : Measurable fun p : ℝ × ℝ × ℝ => P.U * p.1 * ((q.1.1 : ℝ) + p.2.2 * q.1.2) := by
    fun_prop
  have h2 : Measurable fun p : ℝ × ℝ × ℝ =>
      P.V * p.2.1 * ((q.1.1 : ℝ) + p.2.2 * q.1.2) + (q.1.2 : ℝ) / (P.U * p.1) := by
    fun_prop
  refine MeasurableSet.inter ?_ ?_
  · refine (measurableSet_le measurable_const h1).inter ((measurableSet_le h1 measurable_const).inter
      ((measurableSet_le measurable_const h2).inter (measurableSet_le h2 measurable_const)))
  · have hm : Measurable fun p : ℝ × ℝ × ℝ => rho q.1 p.2.2 :=
      (measurable_rho q.1).comp (measurable_snd.snd)
    exact hm (measurableSet_isGoodRatio P.x P.Y P.a q.2)

lemma measurableSet_AL (L : List ((ℤ × ℤ) × P.Lst)) : MeasurableSet (AL P L) := by
  have : AL P L = ⋂ q ∈ L.toFinset, {p : ℝ × ℝ × ℝ | P.InBox (P.U * p.1, P.V * p.2.1, p.2.2) q.1 ∧
      goodR P q p.2.2} := by
    ext p; simp [AL]
  rw [this]
  exact Finset.measurableSet_biInter _ fun q _ => measurableSet_entry P q

lemma volume_boxN_lt_top : volume boxN < ⊤ := by
  unfold boxN
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc, Real.volume_Ico]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ENNReal.ofReal_lt_top)

/-- **Fubini** for the normalized box. -/
lemma fubini3 (G : ℝ × ℝ × ℝ → ℂ) (hG : IntegrableOn G boxN) :
    ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, G (u, v, r) = ∫ p in boxN, G p := by
  simp only [intervalIntegral.integral_of_le (show (1 : ℝ) ≤ 16 by norm_num),
    intervalIntegral.integral_of_le (show (1 : ℝ) ≤ 2 by norm_num),
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hr : ∀ f : ℝ → ℂ, ∫ r in Set.Ioc (0 : ℝ) 1, f r = ∫ r in Set.Ico (0 : ℝ) 1, f r :=
    fun f => by rw [integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]
  have hu : ∀ f : ℝ → ℂ, ∫ u in Set.Ioc (1 : ℝ) 16, f u = ∫ u in Set.Icc (1 : ℝ) 16, f u :=
    fun f => integral_Icc_eq_integral_Ioc.symm
  have hv : ∀ f : ℝ → ℂ, ∫ v in Set.Ioc (1 : ℝ) 2, f v = ∫ v in Set.Icc (1 : ℝ) 2, f v :=
    fun f => integral_Icc_eq_integral_Ioc.symm
  simp only [hr, hu, hv]
  have e1 : (volume : Measure (ℝ × ℝ × ℝ)).restrict boxN =
      (volume.restrict (Set.Icc (1 : ℝ) 16)).prod ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod
        (volume.restrict (Set.Ico (0 : ℝ) 1))) := by
    unfold boxN
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.volume_eq_prod,
      ← Measure.prod_restrict]
  have hG' : Integrable G ((volume.restrict (Set.Icc (1 : ℝ) 16)).prod
      ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod (volume.restrict (Set.Ico (0 : ℝ) 1)))) := by
    rw [← e1]; exact hG
  rw [e1, integral_prod _ hG']
  refine integral_congr_ae ?_
  filter_upwards [hG'.prod_right_ae] with u hu
  exact (integral_prod _ hu).symm

lemma integrableOn_ite (A : Set (ℝ × ℝ × ℝ)) [DecidablePred (· ∈ A)] (hA : MeasurableSet A)
    (c : ℂ) :
    IntegrableOn (fun p => if p ∈ A then c else 0) boxN := by
  have : (fun p => if p ∈ A then c else 0) = A.indicator fun _ => c := by
    funext p; simp [Set.indicator]
  rw [this]
  exact (integrableOn_const (C := c) volume_boxN_lt_top.ne).indicator hA

lemma integral_ite (A : Set (ℝ × ℝ × ℝ)) [DecidablePred (· ∈ A)] (hA : MeasurableSet A) (c : ℂ) :
    ∫ p in boxN, (if p ∈ A then c else 0) = ((volume (A ∩ boxN)).toReal : ℂ) * c := by
  have : (fun p => if p ∈ A then c else 0) = A.indicator fun _ => c := by
    funext p; simp [Set.indicator]
  rw [this, integral_indicator hA, setIntegral_const, measureReal_restrict_apply hA]
  simp [Complex.real_smul, Measure.real]

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): live paths

* `archList`: the `(position, list)` pairs at both ends of every edge of a path;
  `archP ω ↔ ∀ q ∈ archList, box ∧ goodness at ω` (`archP_iff`), i.e. membership in `AL` / `RegionN`.
* A path of nonzero weight whose archimedean conditions hold at a root `ω` with `u ∈ [U, 16U]`
  has all positions bounded: `|z₂| ≤ 4096 N Hd`, `Hd = 10 d₀ Y` (`live_bound`), since
  `z'₂/τ' − z₂/τ = det(z, z')/(ττ')`, `τ ∈ [1/16, 16]` and `|det| < 10 d₀ Y` on live edges.
* The weights of bounded paths sum to `≤ β^k` (`sum_wNon_bdd`).
* For a prime never active along the path, `∑_{t ≤ p} (1 − h_p(t)) ≤ k + 1` (`sum_one_sub_hpL`). -/

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

namespace ArtinPrimitiveRoots.L102E

open Real Finset

namespace PE

variable (P : MemParams)

/-- The archimedean list of a path: both ends of every edge. -/
def archList : (k : ℕ) → St P → (Fin k → StepT P) → List (St P)
  | 0, _, _ => []
  | k + 1, s, cs => (s.1, permL P s.2 (cs 0).1.1) :: nxt P s (cs 0).1 ::
      archList k (nxt P s (cs 0).1) (Fin.tail cs)

lemma archP_iff (ω : ℝ × ℝ × ℝ) : ∀ (k : ℕ) (s : St P) (cs : Fin k → StepT P),
    archP P ω k s cs ↔ ∀ q ∈ archList P k s cs, P.InBox ω q.1 ∧ P.GoodAt ω q.1 q.2
  | 0, s, cs => by simp [archP, archList]
  | k + 1, s, cs => by
    rw [archP, archList, archP_iff ω k, List.forall_mem_cons, List.forall_mem_cons]
    unfold ArchStep nxt
    tauto

lemma archP_norm (p : ℝ × ℝ × ℝ) (k : ℕ) (s : St P) (cs : Fin k → StepT P) :
    archP P (P.U * p.1, P.V * p.2.1, p.2.2) k s cs ↔ p ∈ AL P (archList P k s cs) := by
  rw [archP_iff]; rfl

lemma archP_root (hU : 0 < P.U) (hV : 0 < P.V) {P₀ : ℕ × ℕ} (hP₀ : P₀ ∈ posBox P.U P.V)
    (k : ℕ) (s : St P) (cs : Fin k → StepT P) :
    archP P (rootOf P₀) k s cs ↔ RegionN P (archList P k s cs) (normRoot P P₀) := by
  obtain ⟨h1, h2, h3, h4, hcop⟩ := posBox_bounds hU hV hP₀
  have hu : 0 < P₀.1 := by
    have : (0 : ℝ) < P₀.1 := hU.trans_le h1
    exact_mod_cast this
  have hr := rootRatio_mem hu P₀.2
  have e : (P.U * (normRoot P P₀).1, P.V * (normRoot P P₀).2.1, (normRoot P P₀).2.2) =
      rootOf P₀ := by
    simp only [normRoot, rootOf]
    rw [mul_div_cancel₀ _ hU.ne', mul_div_cancel₀ _ hV.ne']
  rw [← e, archP_iff]
  unfold RegionN
  simp only [normRoot]
  rw [le_div_iff₀ hU, div_le_iff₀ hU, le_div_iff₀ hV, div_le_iff₀ hV]
  constructor
  · intro h
    exact ⟨by linarith, by linarith, by linarith, by linarith, hr.1, hr.2, h⟩
  · intro h; exact h.2.2.2.2.2.2

/-! ## Invariants along a path -/

lemma archList_fst (k : ℕ) : ∀ (s : St P) (cs : Fin k → StepT P),
    ∀ q ∈ archList P k s cs, q.1 = s.1 ∨ q.1 ∈ P.zSet := by
  induction k with
  | zero => intro s cs q hq; simp [archList] at hq
  | succ k ih =>
    intro s cs q hq
    rw [archList, List.mem_cons, List.mem_cons] at hq
    rcases hq with hq | hq | hq
    · exact Or.inl ((congrArg Prod.fst hq).trans rfl)
    · refine Or.inr ?_
      have : q.1 = (cs 0).1.2.1 := congrArg Prod.fst hq
      rw [this]; exact step_z_mem P (cs 0)
    · refine Or.inr ?_
      have h := ih _ _ q hq
      rcases h with h | h
      · have h2 : q.1 = (cs 0).1.2.1 := h.trans (nxt_fst P s (cs 0).1)
        rw [h2]; exact step_z_mem P (cs 0)
      · exact h

lemma archList_gcd {k : ℕ} {s : St P} (hs : Int.gcd s.1.1 s.1.2 = 1) (cs : Fin k → StepT P) :
    ∀ q ∈ archList P k s cs, Int.gcd q.1.1 q.1.2 = 1 := by
  intro q hq
  rcases archList_fst P k s cs q hq with h | h
  · rw [h]; exact hs
  · exact gcd_of_mem_zSet P h

lemma newList_mem {ℓ : P.Lst} (hℓ : ∀ i j, ℓ i j ∈ P.grp i) {nw : Fin P.K → ℕ}
    (hnw : nw ∈ Fintype.piFinset P.grp) : ∀ i j, P.newList ℓ nw i j ∈ P.grp i := by
  intro i j
  unfold MemParams.newList
  induction j using Fin.lastCases with
  | last => rw [Fin.lastCases_last]; exact Fintype.mem_piFinset.1 hnw i
  | cast j => rw [Fin.lastCases_castSucc]; exact hℓ i _

lemma archList_grp : ∀ (k : ℕ) (s : St P) (cs : Fin k → StepT P),
    (∀ i j, s.2 i j ∈ P.grp i) → ∀ q ∈ archList P k s cs, ∀ i j, q.2 i j ∈ P.grp i
  | 0, s, cs => by simp [archList]
  | k + 1, s, cs => by
    intro hs q hq
    have hperm : ∀ i j, permL P s.2 (cs 0).1.1 i j ∈ P.grp i := fun i j => hs i _
    have hnxt : ∀ i j, (nxt P s (cs 0).1).2 i j ∈ P.grp i :=
      newList_mem P hperm (step_nw_mem P (cs 0))
    simp only [archList, List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact hperm
    · exact hnxt
    · exact archList_grp k _ _ hnxt q hq

/-! ## Live edges have bounded determinant -/

lemma abs_arcCutoff_le'' (u : ℝ) : |arcCutoff u| ≤ if |u| < 5 then 1 else 0 := by
  unfold arcCutoff
  have h1 := Real.smoothTransition.nonneg (5 - u)
  have h2 := Real.smoothTransition.nonneg (5 + u)
  have h3 := Real.smoothTransition.le_one (5 - u)
  have h4 := Real.smoothTransition.le_one (5 + u)
  rw [abs_of_nonneg (mul_nonneg h1 h2)]
  split_ifs with hu
  · nlinarith
  · rw [abs_lt] at hu
    push Not at hu
    by_cases hu' : u ≤ -5
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 + u ≤ 0), mul_zero]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith [hu (not_le.1 hu')] : 5 - u ≤ 0),
        zero_mul]

lemma norm_minorKernel_le' (x A₀ Y : ℝ) (t a b : ℤ) :
    ‖minorKernel x A₀ Y t a b‖ ≤ if |(t : ℝ) / Y| < 5 then 1 else 0 := by
  unfold minorKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hint : ‖∫ θ in Set.Ico (0 : ℝ) 1 \ majorArcs x A₀ Y,
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))‖ ≤ 1 := by
    have hfin : MeasureTheory.volume (Set.Ico (0 : ℝ) 1 \ majorArcs x A₀ Y) < ⊤ :=
      (MeasureTheory.measure_mono Set.diff_subset).trans_lt (by simp)
    refine (MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin (C := 1) fun θ _ => ?_).trans ?_
    · rw [Complex.norm_exp]; simp
    · rw [one_mul]
      have : MeasureTheory.volume.real (Set.Ico (0 : ℝ) 1 \ majorArcs x A₀ Y) ≤
          MeasureTheory.volume.real (Set.Ico (0 : ℝ) 1) :=
        MeasureTheory.measureReal_mono Set.diff_subset (by simp)
      simpa using this
  have h1 := abs_arcCutoff_le'' ((t : ℝ) / Y)
  split_ifs at h1 ⊢
  · calc |arcCutoff ((t : ℝ) / Y)| * _ ≤ 1 * 1 :=
          mul_le_mul h1 hint (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  · have : arcCutoff ((t : ℝ) / Y) = 0 := abs_nonpos_iff.1 h1
    rw [this]; simp

lemma abs_dyadicBump_le_one'' (u : ℝ) : |dyadicBump u| ≤ 1 := by
  have h0 : 0 ≤ dyadicBump u := by
    unfold dyadicBump
    rcases le_or_gt u 0 with hu | hu
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
        Real.smoothTransition.zero_of_nonpos (by linarith)]; simp
    · exact sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))
  rw [abs_of_nonneg h0]
  unfold dyadicBump
  linarith [Real.smoothTransition.le_one (u - 1), Real.smoothTransition.nonneg (u / 2 - 1)]

lemma dyadicBump_eq_zero {u : ℝ} (hu : u ≤ 1) : dyadicBump u = 0 := by
  unfold dyadicBump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]; simp

/-- The norm of an edge multiplier and its support. -/
lemma norm_edgeMult_le (j : ℕ) (t : ℤ) (a b D : ℕ) (hD : P.d₀ ≤ D) (hD0 : 0 < D) :
    ‖P.edgeMult j t a b D‖ ≤ if |(t : ℝ) / P.Y| < 5 then 1 else 0 := by
  unfold MemParams.edgeMult
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD0
  have h1 : |(P.d₀ : ℝ) / D * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (P.d₀ : ℝ) / D)]
    have : (P.d₀ : ℝ) / D ≤ 1 := by rw [div_le_one hD']; exact_mod_cast hD
    have h2 := abs_dyadicBump_le_one'' ((b : ℝ) / P.Y)
    have h3 := abs_dyadicBump_le_one'' ((a : ℝ) / P.Y)
    calc (P.d₀ : ℝ) / D * |dyadicBump ((b : ℝ) / P.Y)| * |dyadicBump ((a : ℝ) / P.Y)| ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul this h2 (abs_nonneg _) (by norm_num)) h3 (abs_nonneg _)
            (by norm_num)
      _ = 1 := by ring
  have h2 : ‖(if Even j then minorKernel P.x P.A₀ P.Y t a b
      else (starRingEnd ℂ) (minorKernel P.x P.A₀ P.Y (-t) b a))‖ ≤
      if |(t : ℝ) / P.Y| < 5 then 1 else 0 := by
    by_cases hj : Even j
    · rw [if_pos hj]; exact norm_minorKernel_le' _ _ _ _ _ _
    · rw [if_neg hj, Complex.norm_conj]
      have := norm_minorKernel_le' P.x P.A₀ P.Y (-t) b a
      simpa [neg_div, abs_neg] using this
  calc |(P.d₀ : ℝ) / D * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y)| * _
      ≤ 1 * (if |(t : ℝ) / P.Y| < 5 then 1 else 0) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

lemma norm_facInv : ‖facInv P‖ = (((P.J + 1).factorial ^ P.K : ℕ) : ℝ)⁻¹ := by
  unfold facInv
  rw [norm_inv, Complex.norm_natCast]

/-- `‖stepNon‖ ≤ facInv ∏Vᵢ⁻¹`, and a live step has `|det| < 10 d₀ Y`. -/
lemma stepNon_facts (hY : 0 < P.Y) (hd₀ : 0 < P.d₀) (hV : ∀ i, 0 ≤ P.Vg i) (j : ℕ) (s : St P)
    (c : Stp P) :
    ‖stepNon P j s c‖ ≤ (((P.J + 1).factorial ^ P.K : ℕ) : ℝ)⁻¹ * ∏ i, (P.Vg i)⁻¹ ∧
      (stepNon P j s c ≠ 0 → NonArch P s c ∧
        |(detZ s.1 c.2.1 : ℝ)| ≤ 10 * P.d₀ * P.Y) := by
  classical
  have hVi : 0 ≤ ∏ i, (P.Vg i)⁻¹ := prod_nonneg fun i _ => inv_nonneg.2 (hV i)
  unfold stepNon
  by_cases hN : NonArch P s c
  · rw [if_pos hN]
    obtain ⟨hinj, hban, hD1, hD2, hdvd⟩ := hN
    have hD0 : 0 < padProd (permL P s.2 c.1) := lt_of_lt_of_le hd₀ hD1
    have hE := norm_edgeMult_le P j (detZ s.1 c.2.1 / padProd (permL P s.2 c.1))
      (∏ i, c.2.2 i) (lastProd (permL P s.2 c.1)) (padProd (permL P s.2 c.1)) hD1 hD0
    refine ⟨?_, fun hne => ⟨⟨hinj, hban, hD1, hD2, hdvd⟩, ?_⟩⟩
    · rw [norm_mul, norm_mul, norm_facInv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hVi]
      have : ‖P.edgeMult j (detZ s.1 c.2.1 / padProd (permL P s.2 c.1)) (∏ i, c.2.2 i)
          (lastProd (permL P s.2 c.1)) (padProd (permL P s.2 c.1))‖ ≤ 1 :=
        hE.trans (by split_ifs <;> norm_num)
      calc (((P.J + 1).factorial ^ P.K : ℕ) : ℝ)⁻¹ * ((∏ i, (P.Vg i)⁻¹) * ‖_‖)
          ≤ (((P.J + 1).factorial ^ P.K : ℕ) : ℝ)⁻¹ * ((∏ i, (P.Vg i)⁻¹) * 1) := by
            gcongr
        _ = _ := by ring
    · by_contra hbig
      apply hne
      have h0 : P.edgeMult j (detZ s.1 c.2.1 / padProd (permL P s.2 c.1)) (∏ i, c.2.2 i)
          (lastProd (permL P s.2 c.1)) (padProd (permL P s.2 c.1)) = 0 := by
        rw [← norm_le_zero_iff]
        refine hE.trans (le_of_eq ?_)
        rw [if_neg]
        intro hlt
        apply hbig
        obtain ⟨t, ht⟩ := hdvd
        have hq : detZ s.1 c.2.1 / (padProd (permL P s.2 c.1) : ℤ) = t := by
          rw [ht]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hD0.ne')
        rw [hq] at hlt
        rw [ht]
        push_cast
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (padProd (permL P s.2 c.1) : ℝ))]
        rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at hlt
        have hD2' : (padProd (permL P s.2 c.1) : ℝ) ≤ 2 * P.d₀ := by exact_mod_cast hD2.le
        nlinarith [abs_nonneg (t : ℝ)]
      rw [h0]; simp
  · rw [if_neg hN, mul_zero, norm_zero]
    refine ⟨by positivity, fun h => absurd rfl h⟩

/-! ## Positions of live paths -/

lemma tau_bounds (hU : 0 < P.U) {ω : ℝ × ℝ × ℝ} (hω1 : P.U ≤ ω.1) (hω2 : ω.1 ≤ 16 * P.U)
    {z : ℤ × ℤ} (h : P.InBox ω z) : 1 / 16 ≤ tauR ω z ∧ tauR ω z ≤ 16 := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hω : 0 < ω.1 := hU.trans_le hω1
  constructor
  · by_contra hc
    push Not at hc
    have : ω.1 * tauR ω z < ω.1 * (1 / 16) := mul_lt_mul_of_pos_left hc hω
    linarith
  · by_contra hc
    push Not at hc
    have : ω.1 * 16 < ω.1 * tauR ω z := mul_lt_mul_of_pos_left hc hω
    nlinarith

lemma ratio_step (ω : ℝ × ℝ × ℝ) (z z' : ℤ × ℤ) (hτ : tauR ω z ≠ 0) (hτ' : tauR ω z' ≠ 0) :
    (z'.2 : ℝ) / tauR ω z' - (z.2 : ℝ) / tauR ω z = (detZ z z' : ℝ) / (tauR ω z * tauR ω z') := by
  rw [div_sub_div _ _ hτ' hτ, mul_comm (tauR ω z') (tauR ω z)]
  congr 1
  unfold detZ tauR; push_cast; ring

/-- **Live paths have bounded positions.** -/
theorem live_bound (hU : 0 < P.U) (hY : 0 < P.Y) (hd₀ : 0 < P.d₀) (hV : ∀ i, 0 ≤ P.Vg i)
    {ω : ℝ × ℝ × ℝ} (hω1 : P.U ≤ ω.1) (hω2 : ω.1 ≤ 16 * P.U) :
    ∀ (k : ℕ) (s : St P) (cs : Fin k → StepT P) (B : ℝ), wNon P k s cs ≠ 0 →
      archP P ω k s cs → |(s.1.2 : ℝ) / tauR ω s.1| ≤ B →
      ∀ q ∈ archList P k s cs, |(q.1.2 : ℝ) / tauR ω q.1| ≤ B + 256 * (10 * P.d₀ * P.Y) * k
  | 0, s, cs, B => by simp [archList]
  | k + 1, s, cs, B => by
    intro hw ha hB q hq
    simp only [wNon] at hw
    have hw1 : stepNon P (P.N - (k + 1)) s (cs 0).1 ≠ 0 := left_ne_zero_of_mul hw
    have hw2 := right_ne_zero_of_mul hw
    simp only [archP] at ha
    obtain ⟨⟨hb1, hb2, -, -⟩, ha2⟩ := ha
    obtain ⟨-, hdet⟩ := (stepNon_facts P hY hd₀ hV _ s (cs 0).1).2 hw1
    have ht1 := tau_bounds P hU hω1 hω2 hb1
    have ht2 := tau_bounds P hU hω1 hω2 hb2
    have hH : 0 ≤ 10 * (P.d₀ : ℝ) * P.Y := by positivity
    have hstep : |((cs 0).1.2.1.2 : ℝ) / tauR ω (cs 0).1.2.1| ≤ B + 256 * (10 * P.d₀ * P.Y) := by
      have e := ratio_step ω s.1 (cs 0).1.2.1 (by linarith) (by linarith)
      have hpos : 1 / 256 ≤ tauR ω s.1 * tauR ω (cs 0).1.2.1 := by nlinarith
      have hq' : |(detZ s.1 (cs 0).1.2.1 : ℝ) / (tauR ω s.1 * tauR ω (cs 0).1.2.1)| ≤
          256 * (10 * P.d₀ * P.Y) := by
        have hpos' : 0 < tauR ω s.1 * tauR ω (cs 0).1.2.1 := by linarith
        rw [abs_div, abs_of_pos hpos', div_le_iff₀ hpos']
        have := mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ 256 * (tauR ω s.1 * tauR ω (cs 0).1.2.1) by linarith) hH
        nlinarith
      have := abs_sub_abs_le_abs_sub ((cs 0).1.2.1.2 / tauR ω (cs 0).1.2.1 : ℝ)
        ((s.1.2 : ℝ) / tauR ω s.1)
      rw [e] at this
      linarith
    simp only [archList, List.mem_cons] at hq
    have hk : (0 : ℝ) ≤ 256 * (10 * P.d₀ * P.Y) * k := by positivity
    have hkk : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by push_cast; ring
    rw [hkk]
    rcases hq with hq | hq | hq
    · rw [hq]
      show |(s.1.2 : ℝ) / tauR ω s.1| ≤ _
      nlinarith
    · rw [hq]
      show |((cs 0).1.2.1.2 : ℝ) / tauR ω (cs 0).1.2.1| ≤ _
      nlinarith
    · have := live_bound hU hY hd₀ hV hω1 hω2 k _ _ _ hw2 ha2 (by simpa [nxt] using hstep) q hq
      push_cast
      linarith

/-! ## Weights of bounded paths -/

/-- All positions of the path are bounded. -/
def BddP (Zb : ℝ) (k : ℕ) (s : St P) (cs : Fin k → StepT P) : Prop :=
  ∀ q ∈ archList P k s cs, |(q.1.2 : ℝ)| ≤ Zb ∧ |(q.1.1 : ℝ)| ≤ Zb + 16

/-- A bounded step target. -/
def BddZ (Zb : ℝ) (z : ℤ × ℤ) : Prop := |(z.2 : ℝ)| ≤ Zb ∧ |(z.1 : ℝ)| ≤ Zb + 16

lemma bddP_succ {Zb : ℝ} {k : ℕ} {s : St P} {c : StepT P} {cs : Fin k → StepT P}
    (h : BddP P Zb (k + 1) s (Fin.cons c cs)) :
    BddZ Zb c.1.2.1 ∧ BddP P Zb k (nxt P s c.1) cs := by
  unfold BddP at h
  simp only [archList, Fin.cons_zero, Fin.tail_cons, List.mem_cons] at h
  exact ⟨h _ (Or.inr (Or.inl rfl)), fun q hq => h q (Or.inr (Or.inr hq))⟩

open Classical in
/-- **The weight sum of bounded paths.** -/
theorem sum_wNon_bdd (Zb β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : ∀ j (s : St P), ∑ c : StepT P, (if BddZ Zb c.1.2.1 then ‖stepNon P j s c.1‖ else 0) ≤ β) :
    ∀ (k : ℕ) (s : St P), ∑ cs : Fin k → StepT P,
      (if BddP P Zb k s cs then ‖wNon P k s cs‖ else 0) ≤ β ^ k
  | 0, s => by
    rw [Fintype.sum_unique]
    split_ifs <;> simp [wNon]
  | k + 1, s => by
    rw [sum_fin_succ_paths]
    calc ∑ c : StepT P, ∑ cs : Fin k → StepT P,
          (if BddP P Zb (k + 1) s (Fin.cons c cs) then ‖wNon P (k + 1) s (Fin.cons c cs)‖ else 0)
        ≤ ∑ c : StepT P, (if BddZ Zb c.1.2.1 then ‖stepNon P (P.N - (k + 1)) s c.1‖ else 0) *
            ∑ cs : Fin k → StepT P,
              (if BddP P Zb k (nxt P s c.1) cs then ‖wNon P k (nxt P s c.1) cs‖ else 0) := by
          refine sum_le_sum fun c _ => ?_
          rw [mul_sum]
          refine sum_le_sum fun cs _ => ?_
          by_cases h : BddP P Zb (k + 1) s (Fin.cons c cs)
          · obtain ⟨h1, h2⟩ := bddP_succ P h
            rw [if_pos h, if_pos h1, if_pos h2]
            simp only [wNon, Fin.cons_zero, Fin.tail_cons, norm_mul, le_refl]
          · rw [if_neg h]
            exact mul_nonneg (by split_ifs <;> positivity) (by split_ifs <;> positivity)
      _ ≤ ∑ c : StepT P, (if BddZ Zb c.1.2.1 then ‖stepNon P (P.N - (k + 1)) s c.1‖ else 0) *
            β ^ k := by
          refine sum_le_sum fun c _ => ?_
          exact mul_le_mul_of_nonneg_left (sum_wNon_bdd Zb β hβ0 hβ k _)
            (by split_ifs <;> positivity)
      _ ≤ β * β ^ k := by
          rw [← sum_mul]
          exact mul_le_mul_of_nonneg_right (hβ _ s) (pow_nonneg hβ0 k)
      _ = β ^ (k + 1) := by ring

/-! ## Inactive primes -/

/-- All labels in the states visited by a path. -/
def labs : (k : ℕ) → St P → (Fin k → StepT P) → Finset ℕ
  | 0, s, _ => univ.image fun ij : Fin P.K × Fin (P.J + 1) => s.2 ij.1 ij.2
  | k + 1, s, cs => (univ.image fun ij : Fin P.K × Fin (P.J + 1) => s.2 ij.1 ij.2) ∪
      labs k (nxt P s (cs 0).1) (Fin.tail cs)

lemma card_labs : ∀ (k : ℕ) (s : St P) (cs : Fin k → StepT P),
    (labs P k s cs).card ≤ (k + 1) * (P.K * (P.J + 1))
  | 0, s, cs => by
    simp only [labs]
    refine card_image_le.trans ?_
    simp
  | k + 1, s, cs => by
    simp only [labs]
    refine (card_union_le _ _).trans ?_
    have h1 : (univ.image fun ij : Fin P.K × Fin (P.J + 1) => s.2 ij.1 ij.2).card ≤
        P.K * (P.J + 1) := card_image_le.trans (by simp)
    have h2 := card_labs k (nxt P s (cs 0).1) (Fin.tail cs)
    nlinarith

lemma inactive_of_not_labs {p : ℕ} {s : St P} (h : p ∉ univ.image fun ij : Fin P.K × Fin (P.J + 1) =>
    s.2 ij.1 ij.2) : ¬ ∃ i k, s.2 i k = p := by
  rintro ⟨i, k, h'⟩
  exact h (mem_image.2 ⟨(i, k), mem_univ _, h'⟩)

lemma one_sub_primeFac_inactive (p t j : ℕ) [NeZero p] (s : St P) (h : ¬ ∃ i k, s.2 i k = p) :
    ∑ t ∈ range (p + 1), (1 - P.primeFac (fun _ z => lineOf p z = t) j p s) ≤ 1 := by
  classical
  have e : ∀ t, 1 - P.primeFac (fun _ z => lineOf p z = t) j p s =
      (1 - P.qv j) * (if lineOf p s.1 = t then 1 else 0) := by
    intro t
    unfold MemParams.primeFac
    rw [if_neg h]
    split_ifs <;> ring
  simp only [e]
  rw [← mul_sum, sum_ite_eq, if_pos (mem_range.2 (Nat.lt_succ_of_le (lineOf_le p s.1)))]
  have : 0 ≤ P.qv j := by unfold MemParams.qv; split_ifs <;> norm_num
  linarith

/-- For a prime never active along the path, `∑_{t ≤ p} (1 − h_p(t)) ≤ k + 1`. -/
theorem sum_one_sub_hpL (p : ℕ) [NeZero p] : ∀ (k : ℕ) (s : St P) (cs : Fin k → StepT P),
    p ∉ labs P k s cs → ∑ t ∈ range (p + 1), (1 - hpL P p t k s cs) ≤ k + 1
  | 0, s, cs => by
    intro h
    simp only [labs] at h
    have := one_sub_primeFac_inactive P p 0 P.N s (inactive_of_not_labs P h)
    simpa [hpL, hpP] using this
  | k + 1, s, cs => by
    intro h
    simp only [labs, mem_union, not_or] at h
    obtain ⟨h1, h2⟩ := h
    have ih := sum_one_sub_hpL p k (nxt P s (cs 0).1) (Fin.tail cs) h2
    have hs := one_sub_primeFac_inactive P p 0 (P.N - (k + 1)) s (inactive_of_not_labs P h1)
    have hle : ∀ t ∈ range (p + 1), 1 - hpL P p t (k + 1) s cs ≤
        (1 - P.primeFac (fun _ z => lineOf p z = t) (P.N - (k + 1)) p s) +
          (1 - hpL P p t k (nxt P s (cs 0).1) (Fin.tail cs)) := by
      intro t _
      have ha := primeFac_mem P (fun _ z => lineOf p z = t) (P.N - (k + 1)) p s
      have hb := hpP_mem P (fun _ z => lineOf p z = t) p k (nxt P s (cs 0).1) (Fin.tail cs)
      simp only [hpL, hpP]
      unfold hpL at hb
      nlinarith
    calc ∑ t ∈ range (p + 1), (1 - hpL P p t (k + 1) s cs)
        ≤ ∑ t ∈ range (p + 1), ((1 - P.primeFac (fun _ z => lineOf p z = t) (P.N - (k + 1)) p s) +
          (1 - hpL P p t k (nxt P s (cs 0).1) (Fin.tail cs))) := sum_le_sum hle
      _ ≤ 1 + (k + 1) := by rw [sum_add_distrib]; linarith
      _ = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

lemma hpL_mem (p t k : ℕ) (s : St P) (cs : Fin k → StepT P) :
    0 ≤ hpL P p t k s cs ∧ hpL P p t k s cs ≤ 1 := hpP_mem P _ p k s cs

end PE

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): box sums of the residue lines (Lemma 3.3 summed over residue classes)

For a product box `I₁ × I₂ × I₃` of normalized roots `(u/U, v/V, r) ∈ [1,16] × [1,2] × [0,1]`,
a finite set `Q` of primes and functions `f_p` with `|f_p| ≤ 1`:

`|∑_{P₀ ∈ Ω, root ∈ box} ∏_{p ∈ Q} f_p(κ_p(P₀)) − (6/π²) U V |I₁||I₂||I₃| ∏_p avg_{λ ≤ p} f_p(λ)|
  ≤ |SL₂(ℤ/S)| U V x^{-c}` (`box_sum`). -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset

/-- The predicate of [21] Lemma 3.3 for general intervals. -/
def RootPred3 (S : ℕ) (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V : ℝ)
    (I₁ I₂ I₃ : Set ℝ) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Prop :=
  (g 0 0 : ℝ) / U ∈ I₁ ∧ (g 1 0 : ℝ) / V ∈ I₂ ∧ 0 ≤ g 0 1 ∧ g 0 1 < g 0 0 ∧
    (g 0 1 : ℝ) / (g 0 0 : ℝ) ∈ I₃ ∧
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) g = g₀

/-- [21] Lemma 3.3 at one `x` (two-sided), for intervals given by endpoints. -/
def RootCount2At (x U V c : ℝ) : Prop :=
  ∀ S : ℕ, 0 < S → Squarefree S → (S : ℝ) ≤ exp (log x ^ (0.98 : ℝ)) →
    ∀ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
    ∀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ, 1 ≤ a₁ → a₁ ≤ b₁ → b₁ ≤ 16 → 1 ≤ a₂ → a₂ ≤ b₂ → b₂ ≤ 2 →
      0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
    ∀ I₁ I₂ I₃ : Set ℝ, Set.Ioo a₁ b₁ ⊆ I₁ → I₁ ⊆ Set.Icc a₁ b₁ →
      Set.Ioo a₂ b₂ ⊆ I₂ → I₂ ⊆ Set.Icc a₂ b₂ → Set.Ioo a₃ b₃ ⊆ I₃ → I₃ ⊆ Set.Icc a₃ b₃ →
    |(Nat.card {g // RootPred3 S g₀ U V I₁ I₂ I₃ g} : ℝ) -
      U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) /
        ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
      U * V * x ^ (-c)

lemma rootCount2At_of {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ U V : ℝ, x ^ δ ≤ U → x ^ δ ≤ V →
      RootCount2At x U V c := by
  obtain ⟨c, hc, hall⟩ := ArtinPrimitiveRoots.abs_card_specialLinearGroup_box_sub_le δ hδ
  obtain ⟨x₀, hx₀⟩ := hall 1
  refine ⟨c, hc, x₀, fun x hx U V hU hV S hS0 hS hSx g₀ a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂
    hb₂ ha₃ hab₃ hb₃ I₁ I₂ I₃ h1 h1' h2 h2' h3 h3' => ?_⟩
  exact hx₀ x hx U V hU hV S hS0 hS (by simpa using hSx) g₀ a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁
    ha₂ hab₂ hb₂ ha₃ hab₃ hb₃ I₁ I₂ I₃ h1 h1' h2 h2' h3 h3'

/-! ## Box points and `SL₂(ℤ)` elements -/

lemma rootG_eq_of (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hu : 0 < g 0 0) (h1 : 0 ≤ g 0 1)
    (h2 : g 0 1 < g 0 0) (hv : 0 ≤ g 1 0) :
    rootG (g 0 0).toNat (g 1 0).toNat = g := by
  set u := (g 0 0).toNat
  set v := (g 1 0).toNat
  have hu' : (u : ℤ) = g 0 0 := Int.toNat_of_nonneg hu.le
  have hv' : (v : ℤ) = g 1 0 := Int.toNat_of_nonneg hv
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact g.2
  have hu0 : 0 < u := by omega
  have hcop : Nat.Coprime u v :=
    Nat.isCoprime_iff_coprime.1 ⟨g 1 1, -g 0 1, by rw [hu', hv']; linarith⟩
  have : NeZero u := ⟨hu0.ne'⟩
  -- `g₀₁ = rootC u v`
  have hc : g 0 1 = (rootC u v : ℤ) := by
    have h3 : ((g 0 1 : ℤ) : ZMod u) * (v : ZMod u) = -1 := by
      have e : (((g 0 0 * g 1 1 - g 0 1 * g 1 0 : ℤ)) : ZMod u) = 1 := by rw [hdet]; simp
      push_cast at e
      rw [← hu', ← hv'] at e
      push_cast at e
      rw [ZMod.natCast_self] at e
      linear_combination -e
    have hvu : (v : ZMod u) * (v : ZMod u)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one v hcop.symm
    have h4 : ((g 0 1 : ℤ) : ZMod u) = -(v : ZMod u)⁻¹ := by
      linear_combination (v : ZMod u)⁻¹ * h3 - ((g 0 1 : ℤ) : ZMod u) * hvu
    have h5 : ((g 0 1).toNat : ZMod u) = ((g 0 1 : ℤ) : ZMod u) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
    have h6 : (g 0 1).toNat < u := by omega
    unfold rootC
    rw [← h4, ← h5, ZMod.val_natCast, Nat.mod_eq_of_lt h6, Int.toNat_of_nonneg h1]
  have hd : g 1 1 = (rootD u v : ℤ) := by
    have h7 := rootDet hu0 hcop
    rw [← hc, hu', hv'] at h7
    have : g 0 0 * (g 1 1 - rootD u v) = 0 := by linear_combination hdet - h7
    rcases mul_eq_zero.1 this with h | h
    · omega
    · linarith
  have := rootG_coe hu0 hcop
  apply Subtype.ext
  rw [this]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, hu', hv', hc, hd]

open Classical in
/-- The box points of a residue class are counted by Lemma 3.3. -/
lemma card_box_class {U V : ℝ} (hU : 0 < U) (hV : 0 < V) (S : ℕ)
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (I₁ I₂ I₃ : Set ℝ)
    (hI₁ : I₁ ⊆ Set.Icc 1 16) (hI₂ : I₂ ⊆ Set.Icc 1 2) :
    ((posBox U V).filter fun P₀ => (P₀.1 : ℝ) / U ∈ I₁ ∧ (P₀.2 : ℝ) / V ∈ I₂ ∧
      rootRatio P₀.1 P₀.2 ∈ I₃ ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) (rootG P₀.1 P₀.2) = g₀).card =
      Nat.card {g // RootPred3 S g₀ U V I₁ I₂ I₃ g} := by
  set F := (posBox U V).filter fun P₀ => (P₀.1 : ℝ) / U ∈ I₁ ∧ (P₀.2 : ℝ) / V ∈ I₂ ∧
      rootRatio P₀.1 P₀.2 ∈ I₃ ∧
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) (rootG P₀.1 P₀.2) = g₀
  have hpos : ∀ P ∈ F, 0 < P.1 ∧ Nat.Coprime P.1 P.2 := by
    intro P hP
    have hb := posBox_bounds hU hV (mem_filter.1 hP).1
    refine ⟨?_, hb.2.2.2.2⟩
    have : (0 : ℝ) < P.1 := lt_of_lt_of_le hU hb.1
    exact_mod_cast this
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective (fun P : F => (⟨rootG P.1.1 P.1.2, ?_⟩ :
    {g // RootPred3 S g₀ U V I₁ I₂ I₃ g})) ⟨?_, ?_⟩)
  · obtain ⟨hPF, h1, h2, h3, h4⟩ := mem_filter.1 P.2
    obtain ⟨hu, hcop⟩ := hpos P.1 P.2
    obtain ⟨g00, g01, g10, -⟩ := rootG_apply hu hcop
    refine ⟨?_, ?_, ?_, ?_, ?_, h4⟩
    · rw [g00]; push_cast; exact h1
    · rw [g10]; push_cast; exact h2
    · rw [g01]; positivity
    · rw [g01, g00]; exact_mod_cast rootC_lt hu P.1.2
    · rw [g01, g00]; push_cast; rw [← rootRatio_eq]; exact h3
  · intro P P' h
    have h' := congrArg (fun g : {g // RootPred3 S g₀ U V I₁ I₂ I₃ g} =>
      ((g.1 0 0 : ℤ), (g.1 1 0 : ℤ))) h
    simp only at h'
    obtain ⟨hu, hcop⟩ := hpos P.1 P.2
    obtain ⟨hu', hcop'⟩ := hpos P'.1 P'.2
    rw [(rootG_apply hu hcop).1, (rootG_apply hu' hcop').1, (rootG_apply hu hcop).2.2.1,
      (rootG_apply hu' hcop').2.2.1] at h'
    simp only [Prod.mk.injEq, Nat.cast_inj] at h'
    exact Subtype.ext (Prod.ext h'.1 h'.2)
  · rintro ⟨g, h1, h2, h3, h4, h5, h6⟩
    have hgu : U ≤ (g 0 0 : ℝ) := by
      have := (hI₁ h1).1; rwa [le_div_iff₀ hU, one_mul] at this
    have hgu' : (g 0 0 : ℝ) ≤ 16 * U := by
      have := (hI₁ h1).2; rwa [div_le_iff₀ hU] at this
    have hgv : V ≤ (g 1 0 : ℝ) := by
      have := (hI₂ h2).1; rwa [le_div_iff₀ hV, one_mul] at this
    have hgv' : (g 1 0 : ℝ) ≤ 2 * V := by
      have := (hI₂ h2).2; rwa [div_le_iff₀ hV] at this
    have hu : 0 < g 0 0 := by
      have : (0 : ℝ) < g 0 0 := lt_of_lt_of_le hU hgu
      exact_mod_cast this
    have hv : 0 ≤ g 1 0 := by
      have : (0 : ℝ) ≤ g 1 0 := le_trans hV.le hgv
      exact_mod_cast this
    have hgP := rootG_eq_of g hu h3 h4 hv
    set P : ℕ × ℕ := ((g 0 0).toNat, (g 1 0).toNat)
    have hu' : ((g 0 0).toNat : ℝ) = (g 0 0 : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hu.le]
    have hv' : ((g 1 0).toNat : ℝ) = (g 1 0 : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hv]
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact g.2
    have hPbox : P ∈ posBox U V := by
      simp only [posBox, mem_filter, mem_product, mem_Icc, P]
      refine ⟨⟨⟨Nat.ceil_le.2 (by rw [hu']; exact hgu), Nat.le_floor (by rw [hu']; exact hgu')⟩,
        Nat.ceil_le.2 (by rw [hv']; exact hgv), Nat.le_floor (by rw [hv']; exact hgv')⟩, ?_⟩
      have h0 : ((g 0 0).toNat : ℤ) = g 0 0 := Int.toNat_of_nonneg hu.le
      have h0' : ((g 1 0).toNat : ℤ) = g 1 0 := Int.toNat_of_nonneg hv
      exact Nat.isCoprime_iff_coprime.1 ⟨g 1 1, -g 0 1, by rw [h0, h0']; linarith⟩
    have hPu : 0 < P.1 := by simp only [P]; omega
    have hPc : Nat.Coprime P.1 P.2 := (posBox_bounds hU hV hPbox).2.2.2.2
    obtain ⟨-, g01, -, -⟩ := rootG_apply hPu hPc
    have hPF : P ∈ F := by
      refine mem_filter.2 ⟨hPbox, ?_, ?_, ?_, ?_⟩
      · simp only [P]; rw [hu']; exact h1
      · simp only [P]; rw [hv']; exact h2
      · rw [rootRatio_eq]
        have h01 : (g 0 1 : ℤ) = (rootC P.1 P.2 : ℤ) :=
          (congrArg (fun h : Matrix.SpecialLinearGroup (Fin 2) ℤ => h 0 1) hgP).symm.trans g01
        have : ((rootC P.1 P.2 : ℕ) : ℝ) = (g 0 1 : ℝ) := by exact_mod_cast h01.symm
        rw [this]; simp only [P]; rw [hu']; exact h5
      · simp only [P]; rw [hgP]; exact h6
    exact ⟨⟨P, hPF⟩, Subtype.ext hgP⟩

lemma natCast_mod_dvd {u S i : ℕ} (h : i ∣ S) : ((u % S : ℕ) : ZMod i) = (u : ZMod i) := by
  rw [← ZMod.natCast_mod (u % S) i, Nat.mod_mod_of_dvd u h, ZMod.natCast_mod]

lemma rootCode_eq_rowCode {S i : ℕ} [NeZero S] (hiS : i ∣ S) {P₀ : ℕ × ℕ} (hu : 0 < P₀.1)
    (hcop : Nat.Coprime P₀.1 P₀.2) {g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)}
    (h : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) (rootG P₀.1 P₀.2) = g₀) :
    rootCode i P₀ = rowCode S i (g₀ 0 0) (g₀ 0 1) := by
  obtain ⟨g00, g01, -, -⟩ := rootG_apply hu hcop
  have e00 : g₀ 0 0 = (P₀.1 : ZMod S) := by
    rw [← h]; simp [g00]
  have e01 : g₀ 0 1 = (rootC P₀.1 P₀.2 : ZMod S) := by
    rw [← h]; simp [g01]
  unfold rootCode rowCode
  rw [e00, e01, ZMod.val_natCast, ZMod.val_natCast, natCast_mod_dvd hiS, natCast_mod_dvd hiS]

lemma squarefree_prod_primes' {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) :
    Squarefree (∏ i : Q, (i : ℕ)) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun i _ => Irreducible.squarefree (hQ _ i.2)
  intro i _ j _ hij
  exact Nat.coprime_iff_isRelPrime.1 (pairwise_coprime_of_primes hQ hij)

lemma card_SL2_eq {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) [NeZero (∏ i : Q, (i : ℕ))]
    [∀ i : Q, NeZero (i : ℕ)] :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (∏ i : Q, (i : ℕ)))) : ℝ) =
      ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) * ∏ i : Q, ((((i : ℕ) : ℝ) - 1) * (((i : ℕ) : ℝ) + 1)) := by
  have h := sum_SL2_prod_rowCode hQ (fun _ _ => (1 : ℝ))
  simp only [prod_const_one, sum_const, card_univ, nsmul_eq_mul, mul_one, card_range] at h
  rw [Nat.card_eq_fintype_card, h]
  refine congrArg _ (prod_congr rfl fun i _ => ?_)
  push_cast; ring

open Classical in
/-- **Box sums of line products.** -/
theorem box_sum {x U V c : ℝ} (hRC : RootCount2At x U V c) (hU : 0 < U) (hV : 0 < V)
    {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime)
    (hSx : ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) ≤ exp (log x ^ (0.98 : ℝ)))
    (f : ℕ → ℕ → ℝ) (hf : ∀ i t, |f i t| ≤ 1)
    {a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (ha₁ : 1 ≤ a₁) (hab₁ : a₁ ≤ b₁) (hb₁ : b₁ ≤ 16) (ha₂ : 1 ≤ a₂)
    (hab₂ : a₂ ≤ b₂) (hb₂ : b₂ ≤ 2) (ha₃ : 0 ≤ a₃) (hab₃ : a₃ ≤ b₃) (hb₃ : b₃ ≤ 1)
    {I₁ I₂ I₃ : Set ℝ} (h1 : Set.Ioo a₁ b₁ ⊆ I₁) (h1' : I₁ ⊆ Set.Icc a₁ b₁)
    (h2 : Set.Ioo a₂ b₂ ⊆ I₂) (h2' : I₂ ⊆ Set.Icc a₂ b₂) (h3 : Set.Ioo a₃ b₃ ⊆ I₃)
    (h3' : I₃ ⊆ Set.Icc a₃ b₃) :
    |∑ P₀ ∈ posBox U V, (if (P₀.1 : ℝ) / U ∈ I₁ ∧ (P₀.2 : ℝ) / V ∈ I₂ ∧
        rootRatio P₀.1 P₀.2 ∈ I₃ then ∏ i : Q, f i (rootCode i P₀) else 0) -
      6 / π ^ 2 * (U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) *
        ∏ i : Q, ((∑ t ∈ range ((i : ℕ) + 1), f i t) / (((i : ℕ) : ℝ) + 1))| ≤
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (∏ i : Q, (i : ℕ)))) : ℝ) *
        (U * V * x ^ (-c)) := by
  set S := ∏ i : Q, (i : ℕ) with hSdef
  have hS0 : 0 < S := prod_primes_pos hQ
  have : NeZero S := ⟨hS0.ne'⟩
  have : ∀ i : Q, NeZero (i : ℕ) := fun i => ⟨(hQ _ i.2).ne_zero⟩
  have hI₁ : I₁ ⊆ Set.Icc 1 16 := fun t ht => ⟨ha₁.trans (h1' ht).1, (h1' ht).2.trans hb₁⟩
  have hI₂ : I₂ ⊆ Set.Icc 1 2 := fun t ht => ⟨ha₂.trans (h2' ht).1, (h2' ht).2.trans hb₂⟩
  set Fg : Matrix.SpecialLinearGroup (Fin 2) (ZMod S) → ℝ := fun g₀ =>
    ∏ i : Q, f i (rowCode S i (g₀ 0 0) (g₀ 0 1))
  set φ : ℕ × ℕ → Matrix.SpecialLinearGroup (Fin 2) (ZMod S) := fun P₀ =>
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) (rootG P₀.1 P₀.2)
  set B := (posBox U V).filter fun P₀ => (P₀.1 : ℝ) / U ∈ I₁ ∧ (P₀.2 : ℝ) / V ∈ I₂ ∧
    rootRatio P₀.1 P₀.2 ∈ I₃
  -- step 1: the sum as a sum over residue classes
  have hstep : ∑ P₀ ∈ posBox U V, (if (P₀.1 : ℝ) / U ∈ I₁ ∧ (P₀.2 : ℝ) / V ∈ I₂ ∧
        rootRatio P₀.1 P₀.2 ∈ I₃ then ∏ i : Q, f i (rootCode i P₀) else 0) =
      ∑ g₀, Fg g₀ * (Nat.card {g // RootPred3 S g₀ U V I₁ I₂ I₃ g} : ℝ) := by
    rw [← sum_filter]
    have e1 : ∑ P₀ ∈ B, ∏ i : Q, f i (rootCode i P₀) = ∑ P₀ ∈ B, Fg (φ P₀) := by
      refine sum_congr rfl fun P₀ hP => ?_
      have hb := posBox_bounds hU hV (mem_filter.1 hP).1
      have hu : 0 < P₀.1 := by
        have : (0 : ℝ) < P₀.1 := lt_of_lt_of_le hU hb.1
        exact_mod_cast this
      refine prod_congr rfl fun i _ => ?_
      rw [rootCode_eq_rowCode (dvd_prod_of_mem (fun i : Q => (i : ℕ)) (mem_univ i)) hu hb.2.2.2.2
        rfl]
    rw [e1, ← sum_fiberwise_of_maps_to (g := φ) (t := univ) (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun g₀ _ => ?_
    rw [sum_congr rfl (g := fun _ => Fg g₀) fun P₀ hP => by rw [(mem_filter.1 hP).2]]
    rw [sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    rw [← card_box_class hU hV S g₀ I₁ I₂ I₃ hI₁ hI₂, filter_filter]
    congr 2
    ext P₀
    simp only [φ, and_assoc]
  rw [hstep]
  -- step 2: the main term
  have hz : (riemannZeta 2).re = π ^ 2 / 6 := zeta_two_re
  set cSL := (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)
  have hcSL : cSL = (S : ℝ) * ∏ i : Q, ((((i : ℕ) : ℝ) - 1) * (((i : ℕ) : ℝ) + 1)) :=
    card_SL2_eq hQ
  have hpos : ∀ i : Q, (0 : ℝ) < ((i : ℕ) : ℝ) - 1 := fun i => by
    have := (hQ _ i.2).two_le; have : (2 : ℝ) ≤ (i : ℕ) := by exact_mod_cast this
    linarith
  have hcSL0 : 0 < cSL := by
    rw [hcSL]
    refine mul_pos (by exact_mod_cast hS0) (prod_pos fun i _ => mul_pos (hpos i) (by positivity))
  set M₀ := U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) / ((riemannZeta 2).re * cSL)
  have hsumF := sum_SL2_prod_rowCode hQ f
  have hmain : ∑ g₀, Fg g₀ * M₀ = 6 / π ^ 2 * (U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) *
      ∏ i : Q, ((∑ t ∈ range ((i : ℕ) + 1), f i t) / (((i : ℕ) : ℝ) + 1)) := by
    rw [← sum_mul]
    have e2 : ∑ g₀, Fg g₀ = (S : ℝ) * ∏ i : Q, ((((i : ℕ) : ℝ) - 1) *
        ∑ t ∈ range ((i : ℕ) + 1), f i t) := hsumF
    rw [e2]
    simp only [M₀]
    rw [hcSL, hz, prod_div_distrib]
    have hP1 : ∏ i : Q, ((((i : ℕ) : ℝ) - 1) * (((i : ℕ) : ℝ) + 1)) =
        (∏ i : Q, (((i : ℕ) : ℝ) - 1)) * ∏ i : Q, (((i : ℕ) : ℝ) + 1) := prod_mul_distrib
    have hP2 : ∏ i : Q, ((((i : ℕ) : ℝ) - 1) * ∑ t ∈ range ((i : ℕ) + 1), f i t) =
        (∏ i : Q, (((i : ℕ) : ℝ) - 1)) * ∏ i : Q, ∑ t ∈ range ((i : ℕ) + 1), f i t :=
      prod_mul_distrib
    rw [hP1, hP2]
    have h0 : (∏ i : Q, (((i : ℕ) : ℝ) - 1)) ≠ 0 := (prod_pos fun i _ => hpos i).ne'
    have h0' : (∏ i : Q, (((i : ℕ) : ℝ) + 1)) ≠ 0 := (prod_pos fun i _ => by positivity).ne'
    have hS' : (S : ℝ) ≠ 0 := by exact_mod_cast hS0.ne'
    have hpi : π ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [← hmain, ← sum_sub_distrib]
  -- step 3: the error
  have hSq : Squarefree S := squarefree_prod_primes' hQ
  calc |∑ g₀, (Fg g₀ * (Nat.card {g // RootPred3 S g₀ U V I₁ I₂ I₃ g} : ℝ) - Fg g₀ * M₀)|
      ≤ ∑ g₀, |Fg g₀ * (Nat.card {g // RootPred3 S g₀ U V I₁ I₂ I₃ g} : ℝ) - Fg g₀ * M₀| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S), U * V * x ^ (-c) := by
        refine sum_le_sum fun g₀ _ => ?_
        rw [← mul_sub, abs_mul]
        have hF : |Fg g₀| ≤ 1 := by
          simp only [Fg]
          rw [abs_prod]
          exact prod_le_one (fun i _ => abs_nonneg _) fun i _ => hf _ _
        have hE := hRC S hS0 hSq hSx g₀ a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃ hab₃
          hb₃ I₁ I₂ I₃ h1 h1' h2 h2' h3 h3'
        calc |Fg g₀| * |(Nat.card {g // RootPred3 S g₀ U V I₁ I₂ I₃ g} : ℝ) - M₀|
            ≤ 1 * (U * V * x ^ (-c)) := mul_le_mul hF hE (abs_nonneg _) zero_le_one
          _ = U * V * x ^ (-c) := one_mul _
    _ = cSL * (U * V * x ^ (-c)) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        simp only [cSL, Nat.card_eq_fintype_card]

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): Bonferroni inequalities

For `0 ≤ X_i ≤ 1` on a finite set `s`, with `e_k = ∑_{|t| = k} ∏_{i ∈ t} X_i`:
`0 ≤ (−1)^T (∏_{i ∈ s} (1 − X_i) − ∑_{k < T} (−1)^k e_k) ≤ e_T` (`bonferroni`), and
`e_T ≤ (∑ X)^T / T!` (`esymm_le`). -/

namespace ArtinPrimitiveRoots.L102E

open Finset

/-- `e_k = ∑_{t ⊆ s, |t| = k} ∏_{i ∈ t} X_i`. -/
def esymmR {ι : Type*} (s : Finset ι) (X : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard k, ∏ i ∈ t, X i

/-- The Bonferroni polynomial `∑_{k < T} (−1)^k e_k`. -/
def bonfR {ι : Type*} (s : Finset ι) (X : ι → ℝ) (T : ℕ) : ℝ :=
  ∑ k ∈ range T, (-1) ^ k * esymmR s X k

lemma esymmR_zero {ι : Type*} (s : Finset ι) (X : ι → ℝ) : esymmR s X 0 = 1 := by
  simp [esymmR]

lemma esymmR_empty_succ {ι : Type*} (X : ι → ℝ) (k : ℕ) : esymmR (∅ : Finset ι) X (k + 1) = 0 := by
  unfold esymmR
  rw [powersetCard_eq_empty.2 (by simp), sum_empty]

lemma esymmR_insert {ι : Type*} [DecidableEq ι] {s : Finset ι} {a : ι} (ha : a ∉ s)
    (X : ι → ℝ) (k : ℕ) :
    esymmR (insert a s) X (k + 1) = esymmR s X (k + 1) + X a * esymmR s X k := by
  unfold esymmR
  rw [powersetCard_succ_insert ha, sum_union]
  · congr 1
    rw [sum_image]
    · rw [mul_sum]
      refine sum_congr rfl fun t ht => ?_
      have hat : a ∉ t := fun h => ha (mem_powersetCard.1 ht |>.1 h)
      rw [prod_insert hat]
    · intro t ht t' ht' h
      have hat : a ∉ t := fun h => ha (mem_powersetCard.1 ht |>.1 h)
      have hat' : a ∉ t' := fun h => ha (mem_powersetCard.1 ht' |>.1 h)
      have := congrArg (fun u : Finset ι => u.erase a) h
      simp only [erase_insert hat, erase_insert hat'] at this
      exact this
  · rw [disjoint_left]
    intro t ht ht'
    obtain ⟨t', -, rfl⟩ := mem_image.1 ht'
    exact ha ((mem_powersetCard.1 ht).1 (mem_insert_self a t'))

lemma esymmR_nonneg {ι : Type*} (s : Finset ι) (X : ι → ℝ) (hX : ∀ i ∈ s, 0 ≤ X i) (k : ℕ) :
    0 ≤ esymmR s X k :=
  sum_nonneg fun _ ht => prod_nonneg fun i hi => hX i ((mem_powersetCard.1 ht).1 hi)

/-- **Bonferroni inequalities.** -/
theorem bonferroni {ι : Type*} [DecidableEq ι] (s : Finset ι) (X : ι → ℝ)
    (hX : ∀ i ∈ s, 0 ≤ X i ∧ X i ≤ 1) (T : ℕ) :
    0 ≤ (-1) ^ T * (∏ i ∈ s, (1 - X i) - bonfR s X T) ∧
      (-1) ^ T * (∏ i ∈ s, (1 - X i) - bonfR s X T) ≤ esymmR s X T := by
  induction s using Finset.induction_on generalizing T with
  | empty =>
    rcases T with _ | T
    · simp [bonfR, esymmR]
    · have : bonfR (∅ : Finset ι) X (T + 1) = 1 := by
        unfold bonfR
        rw [sum_range_succ']
        simp [esymmR_empty_succ, esymmR_zero]
      rw [this, esymmR_empty_succ]; simp
  | insert a s ha ih =>
    have hXs : ∀ i ∈ s, 0 ≤ X i ∧ X i ≤ 1 := fun i hi => hX i (mem_insert_of_mem hi)
    have hXa := hX a (mem_insert_self a s)
    rcases T with _ | T
    · simp only [pow_zero, one_mul, bonfR, range_zero, sum_empty, sub_zero, esymmR_zero]
      constructor
      · exact prod_nonneg fun i hi => by linarith [(hX i hi).2]
      · exact prod_le_one (fun i hi => by linarith [(hX i hi).2])
          fun i hi => by linarith [(hX i hi).1]
    · -- the recurrence `R(insert a s, T+1) = R(s, T+1) − X_a R(s, T)`
      have hB : bonfR (insert a s) X (T + 1) = bonfR s X (T + 1) - X a * bonfR s X T := by
        unfold bonfR
        rw [sum_range_succ', sum_range_succ' (fun k => (-1) ^ k * esymmR s X k)]
        simp only [esymmR_insert ha, esymmR_zero, pow_zero, one_mul]
        rw [mul_sum]
        have : ∀ k ∈ range T, (-1 : ℝ) ^ (k + 1) * (esymmR s X (k + 1) + X a * esymmR s X k) =
            (-1) ^ (k + 1) * esymmR s X (k + 1) - X a * ((-1) ^ k * esymmR s X k) := by
          intro k _; ring
        rw [sum_congr rfl this, sum_sub_distrib]
        ring
      have hP : ∏ i ∈ insert a s, (1 - X i) = (1 - X a) * ∏ i ∈ s, (1 - X i) := prod_insert ha
      have hE : esymmR (insert a s) X (T + 1) = esymmR s X (T + 1) + X a * esymmR s X T :=
        esymmR_insert ha X T
      have h1 := ih hXs (T + 1)
      have h2 := ih hXs T
      have key : (-1) ^ (T + 1) * (∏ i ∈ insert a s, (1 - X i) - bonfR (insert a s) X (T + 1)) =
          (-1) ^ (T + 1) * (∏ i ∈ s, (1 - X i) - bonfR s X (T + 1)) +
            X a * ((-1) ^ T * (∏ i ∈ s, (1 - X i) - bonfR s X T)) := by
        rw [hP, hB]; ring
      rw [key, hE]
      constructor
      · exact add_nonneg h1.1 (mul_nonneg hXa.1 h2.1)
      · exact add_le_add h1.2 (mul_le_mul_of_nonneg_left h2.2 hXa.1)

lemma abs_prod_sub_bonf_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (X : ι → ℝ)
    (hX : ∀ i ∈ s, 0 ≤ X i ∧ X i ≤ 1) (T : ℕ) :
    |∏ i ∈ s, (1 - X i) - bonfR s X T| ≤ esymmR s X T := by
  obtain ⟨h1, h2⟩ := bonferroni s X hX T
  have : |(-1 : ℝ) ^ T * (∏ i ∈ s, (1 - X i) - bonfR s X T)| =
      |∏ i ∈ s, (1 - X i) - bonfR s X T| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [← this, abs_of_nonneg h1]
  exact h2

lemma add_pow_ge (A b : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) (T : ℕ) :
    A ^ (T + 1) + (T + 1) * b * A ^ T ≤ (A + b) ^ (T + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hAT : 0 ≤ A ^ T := pow_nonneg hA T
    calc A ^ (T + 1 + 1) + ((T + 1 : ℕ) + 1 : ℝ) * b * A ^ (T + 1)
        ≤ (A + b) * (A ^ (T + 1) + (T + 1) * b * A ^ T) := by
          have e : (A + b) * (A ^ (T + 1) + (T + 1) * b * A ^ T) -
              (A ^ (T + 1 + 1) + ((T + 1 : ℕ) + 1 : ℝ) * b * A ^ (T + 1)) =
              (T + 1) * b ^ 2 * A ^ T := by push_cast; ring
          have : 0 ≤ ((T : ℝ) + 1) * b ^ 2 * A ^ T := by positivity
          linarith
      _ ≤ (A + b) * (A + b) ^ (T + 1) := by gcongr
      _ = (A + b) ^ (T + 1 + 1) := by ring

/-- `e_T ≤ (∑ X)^T / T!`. -/
theorem esymm_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (X : ι → ℝ)
    (hX : ∀ i ∈ s, 0 ≤ X i) (T : ℕ) :
    esymmR s X T ≤ (∑ i ∈ s, X i) ^ T / (T.factorial : ℝ) := by
  induction s using Finset.induction_on generalizing T with
  | empty =>
    rcases T with _ | T
    · simp [esymmR_zero]
    · rw [esymmR_empty_succ]; simp
  | insert a s ha ih =>
    have hXs : ∀ i ∈ s, 0 ≤ X i := fun i hi => hX i (mem_insert_of_mem hi)
    have hXa := hX a (mem_insert_self a s)
    have hA : 0 ≤ ∑ i ∈ s, X i := sum_nonneg hXs
    rcases T with _ | T
    · simp [esymmR_zero]
    · rw [esymmR_insert ha, sum_insert ha]
      have h1 := ih hXs (T + 1)
      have h2 := ih hXs T
      have hf : (0 : ℝ) < T.factorial := by exact_mod_cast T.factorial_pos
      have hf1 : ((T + 1).factorial : ℝ) = (T + 1) * T.factorial := by
        push_cast [Nat.factorial_succ]; ring
      calc esymmR s X (T + 1) + X a * esymmR s X T
          ≤ (∑ i ∈ s, X i) ^ (T + 1) / ((T + 1).factorial : ℝ) +
              X a * ((∑ i ∈ s, X i) ^ T / (T.factorial : ℝ)) := by gcongr
        _ = ((∑ i ∈ s, X i) ^ (T + 1) + (T + 1) * X a * (∑ i ∈ s, X i) ^ T) /
              ((T + 1).factorial : ℝ) := by
            rw [hf1]; field_simp
        _ ≤ (∑ i ∈ s, X i + X a) ^ (T + 1) / ((T + 1).factorial : ℝ) := by
            gcongr
            exact add_pow_ge _ _ hA hXa T
        _ = (X a + ∑ i ∈ s, X i) ^ (T + 1) / ((T + 1).factorial : ℝ) := by ring

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): the box-sum oracle of a product weight (Bonferroni + Lemma 3.3)

For primes `G`, any `A ⊆ G`, and `f_p : ℕ → [0,1]`, the weight `Φ(P₀) = ∏_{p ∈ G} f_p(κ_p(P₀))`
has box sums `(6/π²) UV vol ∏_p avg f_p` up to
`2 (6/π²) UV (15/n) e_T(avg(1 − f)) + (|G| + 1)^T e^{3L^{0.98}} UV x^{-c}` (`oracle_bonf`):
Bonferroni at order `T` in the primes of `G \ A`, and Lemma 3.3 for the moduli `∏_{A ∪ t} p`. -/

namespace ArtinPrimitiveRoots.L102E

open Real Finset

/-- The average `avg_{t ≤ p} g p t`. -/
noncomputable def avgL (g : ℕ → ℕ → ℝ) (p : ℕ) : ℝ :=
  (∑ t ∈ range (p + 1), g p t) / ((p : ℝ) + 1)

lemma avgL_one_sub (f : ℕ → ℕ → ℝ) (p : ℕ) :
    avgL (fun p t => 1 - f p t) p = 1 - avgL f p := by
  unfold avgL
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
  have : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  push_cast; ring

lemma avgL_mem {f : ℕ → ℕ → ℝ} (hf : ∀ p t, 0 ≤ f p t ∧ f p t ≤ 1) (p : ℕ) :
    0 ≤ avgL f p ∧ avgL f p ≤ 1 := by
  unfold avgL
  have hp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  refine ⟨div_nonneg (sum_nonneg fun t _ => (hf p t).1) hp.le, ?_⟩
  rw [div_le_one hp]
  calc ∑ t ∈ range (p + 1), f p t ≤ ∑ _t ∈ range (p + 1), (1 : ℝ) := sum_le_sum fun t _ => (hf p t).2
    _ = (p : ℝ) + 1 := by simp

lemma card_SL2_le_cube {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) [NeZero (∏ i : Q, (i : ℕ))]
    [∀ i : Q, NeZero (i : ℕ)] :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod (∏ i : Q, (i : ℕ)))) : ℝ) ≤
      ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) ^ 3 := by
  rw [card_SL2_eq hQ]
  have h : ∏ i : Q, ((((i : ℕ) : ℝ) - 1) * (((i : ℕ) : ℝ) + 1)) ≤ ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) ^ 2 := by
    push_cast
    rw [← prod_pow]
    refine prod_le_prod (fun i _ => ?_) fun i _ => ?_
    · have : (1 : ℝ) ≤ (i : ℕ) := by exact_mod_cast (hQ _ i.2).one_lt.le
      nlinarith
    · nlinarith
  have h0 : (0 : ℝ) ≤ ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) := by positivity
  calc ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) * ∏ i : Q, ((((i : ℕ) : ℝ) - 1) * (((i : ℕ) : ℝ) + 1))
      ≤ ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) * ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left h h0
    _ = _ := by ring

variable (P : MemParams)

open Classical in
/-- Box sums over one oracle box, as products over a `Finset` of primes. -/
lemma box_sum' {x c : ℝ} (hx : 0 ≤ x) (hRC : RootCount2At x P.U P.V c) (hU : 0 < P.U) (hV : 0 < P.V)
    {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) {Pm : ℝ} (hPm : ∀ p ∈ Q, (p : ℝ) ≤ Pm)
    (hQc : Pm ^ Q.card ≤ exp (log x ^ (0.98 : ℝ)))
    (g : ℕ → ℕ → ℝ) (hg : ∀ p t, |g p t| ≤ 1) (a₁ b₁ a₂ b₂ : ℝ) (k n : ℕ) (ha₁ : 1 ≤ a₁)
    (hb₁ : b₁ ≤ 16) (ha₂ : 1 ≤ a₂) (hb₂ : b₂ ≤ 2) (hk : k < n) :
    |(∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ Set.Icc a₁ b₁ ×ˢ (Set.Icc a₂ b₂ ×ˢ slab n k)
        then ∏ p ∈ Q, g p (rootCode p P₀) else 0) -
      6 / π ^ 2 * (P.U * P.V) * (len a₁ b₁ * len a₂ b₂ * (1 / n)) * ∏ p ∈ Q, avgL g p| ≤
      exp (log x ^ (0.98 : ℝ)) ^ 3 * (P.U * P.V * x ^ (-c)) := by
  have hE : 0 ≤ exp (log x ^ (0.98 : ℝ)) ^ 3 * (P.U * P.V * x ^ (-c)) := by
    have := rpow_nonneg hx (-c); positivity
  have hn : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases lt_or_ge b₁ a₁ with h1 | h1
  · have : ∀ P₀ ∈ posBox P.U P.V, (if normRoot P P₀ ∈ Set.Icc a₁ b₁ ×ˢ (Set.Icc a₂ b₂ ×ˢ slab n k)
        then ∏ p ∈ Q, g p (rootCode p P₀) else 0) = 0 := fun P₀ _ => by
      rw [if_neg]; rintro ⟨h, -⟩; exact absurd (h.1.trans h.2) (not_le.2 h1)
    rw [sum_congr rfl this, sum_const_zero, show len a₁ b₁ = 0 from max_eq_right (by linarith)]
    simpa using hE
  rcases lt_or_ge b₂ a₂ with h2 | h2
  · have : ∀ P₀ ∈ posBox P.U P.V, (if normRoot P P₀ ∈ Set.Icc a₁ b₁ ×ˢ (Set.Icc a₂ b₂ ×ˢ slab n k)
        then ∏ p ∈ Q, g p (rootCode p P₀) else 0) = 0 := fun P₀ _ => by
      rw [if_neg]; rintro ⟨-, h, -⟩; exact absurd (h.1.trans h.2) (not_le.2 h2)
    rw [sum_congr rfl this, sum_const_zero, show len a₂ b₂ = 0 from max_eq_right (by linarith)]
    simpa using hE
  have hS : ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) ≤ exp (log x ^ (0.98 : ℝ)) := by
    refine le_trans ?_ hQc
    push_cast
    rw [prod_coe_sort Q (fun i => (i : ℝ))]
    calc ∏ i ∈ Q, (i : ℝ) ≤ ∏ _i ∈ Q, Pm :=
          prod_le_prod (fun i _ => by positivity) fun i hi => hPm i hi
      _ = Pm ^ Q.card := prod_const _
  have hk1 : ((k : ℝ) + 1) / n ≤ 1 := by
    rw [div_le_one hn']; exact_mod_cast hk
  have hb := box_sum hRC hU hV hQ hS g hg ha₁ h1 hb₁ ha₂ h2 hb₂ (by positivity : (0 : ℝ) ≤ k / n)
    (by rw [div_le_div_iff_of_pos_right hn']; linarith) hk1 (I₁ := Set.Icc a₁ b₁)
    (I₂ := Set.Icc a₂ b₂) (I₃ := slab n k) Set.Ioo_subset_Icc_self subset_rfl
    Set.Ioo_subset_Icc_self subset_rfl Set.Ioo_subset_Ico_self Set.Ico_subset_Icc_self
  have : NeZero (∏ i : Q, (i : ℕ)) := ⟨(prod_primes_pos hQ).ne'⟩
  have : ∀ i : Q, NeZero (i : ℕ) := fun i => ⟨(hQ _ i.2).ne_zero⟩
  have hcard := card_SL2_le_cube hQ
  have hcube : ((∏ i : Q, (i : ℕ) : ℕ) : ℝ) ^ 3 ≤ exp (log x ^ (0.98 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hS 3
  have hUVx : 0 ≤ P.U * P.V * x ^ (-c) := by
    have := rpow_nonneg hx (-c); positivity
  refine le_trans (le_of_eq ?_) (hb.trans (mul_le_mul_of_nonneg_right (hcard.trans hcube) hUVx))
  congr 1
  rw [len, len, max_eq_left (by linarith), max_eq_left (by linarith)]
  have e3 : ((k : ℝ) + 1) / n - k / n = 1 / n := by ring
  rw [e3, ← prod_coe_sort Q (fun p => avgL g p)]
  congr 1
  · refine sum_congr rfl fun P₀ _ => ?_
    rw [← prod_coe_sort Q (fun p => g p (rootCode p P₀))]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rfl
  · unfold avgL; ring

lemma sum_choose_le_pow (g T : ℕ) :
    (∑ k ∈ range (T + 1), (g.choose k : ℝ)) ≤ ((g : ℝ) + 1) ^ T := by
  have h1 : ∀ k ∈ range (T + 1), (g.choose k : ℝ) ≤ (T.choose k : ℝ) * (g : ℝ) ^ k := by
    intro k hk
    have hk' : k ≤ T := Nat.lt_succ_iff.1 (mem_range.1 hk)
    have h1 : (g.choose k : ℝ) ≤ (g : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow g k
    have h2 : (1 : ℝ) ≤ T.choose k := by exact_mod_cast Nat.choose_pos hk'
    nlinarith [pow_nonneg (Nat.cast_nonneg g : (0 : ℝ) ≤ g) k]
  refine (sum_le_sum h1).trans (le_of_eq ?_)
  rw [add_pow]
  refine sum_congr rfl fun k _ => ?_
  rw [one_pow, mul_one, mul_comm]

open Classical in
/-- **The oracle of a product weight.** -/
theorem oracle_bonf {x c : ℝ} (hx : 0 ≤ x) (hRC : RootCount2At x P.U P.V c) (hU : 0 < P.U) (hV : 0 < P.V)
    {G A : Finset ℕ} (hAG : A ⊆ G) (hG : ∀ p ∈ G, p.Prime) {Pm : ℝ} (hPm1 : 1 ≤ Pm)
    (hPm : ∀ p ∈ G, (p : ℝ) ≤ Pm) {T : ℕ} (hPT : Pm ^ (A.card + T) ≤ exp (log x ^ (0.98 : ℝ)))
    (f : ℕ → ℕ → ℝ) (hf : ∀ p t, 0 ≤ f p t ∧ f p t ≤ 1) (n : ℕ) :
    Oracle P n (fun P₀ => ∏ p ∈ G, f p (rootCode p P₀)) (∏ p ∈ G, avgL f p)
      (2 * (6 / π ^ 2) * (P.U * P.V) * (15 / n) *
          esymmR (G \ A) (avgL fun p t => 1 - f p t) T +
        ((G.card : ℝ) + 1) ^ T * (exp (log x ^ (0.98 : ℝ)) ^ 3 * (P.U * P.V * x ^ (-c)))) := by
  intro a₁ b₁ a₂ b₂ k ha₁ hb₁ ha₂ hb₂ hk
  set E := exp (log x ^ (0.98 : ℝ)) ^ 3 * (P.U * P.V * x ^ (-c)) with hEdef
  set B : Set (ℝ × ℝ × ℝ) := Set.Icc a₁ b₁ ×ˢ (Set.Icc a₂ b₂ ×ˢ slab n k) with hBdef
  set c₀ := 6 / π ^ 2 * (P.U * P.V) * (len a₁ b₁ * len a₂ b₂ * (1 / n)) with hc₀
  have hn : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc₀0 : 0 ≤ c₀ := by
    have := len_nonneg a₁ b₁; have := len_nonneg a₂ b₂; positivity
  have hc₀le : c₀ ≤ 6 / π ^ 2 * (P.U * P.V) * (15 / n) := by
    rw [hc₀]
    have h1 : len a₁ b₁ ≤ 15 := by unfold len; exact max_le (by linarith) (by norm_num)
    have h2 : len a₂ b₂ ≤ 1 := by unfold len; exact max_le (by linarith) (by norm_num)
    have : len a₁ b₁ * len a₂ b₂ * (1 / n) ≤ 15 / n := by
      have := len_nonneg a₁ b₁; have := len_nonneg a₂ b₂
      calc len a₁ b₁ * len a₂ b₂ * (1 / n) ≤ 15 * 1 * (1 / n) := by gcongr
        _ = 15 / n := by ring
    gcongr
  -- the functions
  set g : ℕ → ℕ → ℝ := fun p t => if p ∈ A then f p t else 1 - f p t with hg
  have hg1 : ∀ p t, |g p t| ≤ 1 := fun p t => by
    simp only [hg]; split_ifs
    · rw [abs_le]; constructor <;> linarith [hf p t]
    · rw [abs_le]; constructor <;> linarith [hf p t]
  set X : ℕ → ℕ → ℝ := fun p t => 1 - f p t with hX
  have hX1 : ∀ p t, |X p t| ≤ 1 := fun p t => by
    simp only [hX]; rw [abs_le]; constructor <;> linarith [hf p t]
  have hXm : ∀ p t, 0 ≤ X p t ∧ X p t ≤ 1 := fun p t => by
    simp only [hX]; constructor <;> linarith [hf p t]
  set S := G \ A with hS
  have hSG : S ⊆ G := sdiff_subset
  set Fa : ℕ × ℕ → ℝ := fun P₀ => ∏ p ∈ A, f p (rootCode p P₀) with hFa
  have hFa : ∀ P₀, 0 ≤ Fa P₀ ∧ Fa P₀ ≤ 1 := fun P₀ =>
    ⟨prod_nonneg fun p _ => (hf p _).1, prod_le_one (fun p _ => (hf p _).1) fun p _ => (hf p _).2⟩
  set mA := ∏ p ∈ A, avgL f p with hmA
  have hmA : 0 ≤ mA ∧ mA ≤ 1 := ⟨prod_nonneg fun p _ => (avgL_mem hf p).1,
    prod_le_one (fun p _ => (avgL_mem hf p).1) fun p _ => (avgL_mem hf p).2⟩
  set aX : ℕ → ℝ := avgL X with haX
  have haXm : ∀ p, 0 ≤ aX p ∧ aX p ≤ 1 := fun p => avgL_mem hXm p
  -- box sums of the product over `A ∪ t`
  have hQ : ∀ t ∈ S.powerset, t.card ≤ T →
      |(∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then Fa P₀ * ∏ p ∈ t, X p (rootCode p P₀)
          else 0) - c₀ * (mA * ∏ p ∈ t, aX p)| ≤ E := by
    intro t ht htc
    have htS : t ⊆ S := mem_powerset.1 ht
    have hdisj : Disjoint A t := disjoint_of_subset_right htS disjoint_sdiff
    have hQp : ∀ p ∈ A ∪ t, p.Prime := fun p hp => hG p (union_subset hAG (htS.trans hSG) hp)
    have hQm : ∀ p ∈ A ∪ t, (p : ℝ) ≤ Pm := fun p hp => hPm p (union_subset hAG (htS.trans hSG) hp)
    have hQc : Pm ^ (A ∪ t).card ≤ exp (log x ^ (0.98 : ℝ)) := by
      refine le_trans (pow_le_pow_right₀ hPm1 ?_) hPT
      rw [card_union_of_disjoint hdisj]; omega
    have hb := box_sum' P hx hRC hU hV hQp hQm hQc g hg1 a₁ b₁ a₂ b₂ k n ha₁ hb₁ ha₂ hb₂ hk
    have e1 : ∀ P₀, ∏ p ∈ A ∪ t, g p (rootCode p P₀) = Fa P₀ * ∏ p ∈ t, X p (rootCode p P₀) := by
      intro P₀
      rw [prod_union hdisj]
      congr 1
      · exact prod_congr rfl fun p hp => by simp only [hg, if_pos hp]
      · exact prod_congr rfl fun p hp => by
          simp only [hg, hX, if_neg (disjoint_left.1 hdisj.symm hp)]
    have e2 : ∏ p ∈ A ∪ t, avgL g p = mA * ∏ p ∈ t, aX p := by
      rw [prod_union hdisj]
      congr 1
      · refine prod_congr rfl fun p hp => ?_
        unfold avgL; simp only [hg, if_pos hp]
      · refine prod_congr rfl fun p hp => ?_
        unfold avgL; simp only [hg, haX, hX, if_neg (disjoint_left.1 hdisj.symm hp)]
        rfl
    simp only [e1, e2] at hb
    rw [hc₀]
    exact hb
  -- the box sum of the Bonferroni error
  have hQ2 : ∀ t ∈ S.powerset, t.card ≤ T →
      |(∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then ∏ p ∈ t, X p (rootCode p P₀) else 0) -
        c₀ * ∏ p ∈ t, aX p| ≤ E := by
    intro t ht htc
    have htS : t ⊆ S := mem_powerset.1 ht
    have hQp : ∀ p ∈ t, p.Prime := fun p hp => hG p (hSG (htS hp))
    have hQm : ∀ p ∈ t, (p : ℝ) ≤ Pm := fun p hp => hPm p (hSG (htS hp))
    have hQc : Pm ^ t.card ≤ exp (log x ^ (0.98 : ℝ)) :=
      le_trans (pow_le_pow_right₀ hPm1 (by omega)) hPT
    have hb := box_sum' P hx hRC hU hV hQp hQm hQc X hX1 a₁ b₁ a₂ b₂ k n ha₁ hb₁ ha₂ hb₂ hk
    rw [hc₀]
    exact hb
  -- pointwise Bonferroni
  have hpt : ∀ P₀, ∏ p ∈ G, f p (rootCode p P₀) =
      Fa P₀ * bonfR S (fun p => X p (rootCode p P₀)) T +
        Fa P₀ * (∏ p ∈ S, (1 - X p (rootCode p P₀)) - bonfR S (fun p => X p (rootCode p P₀)) T) := by
    intro P₀
    have : ∏ p ∈ S, (1 - X p (rootCode p P₀)) = ∏ p ∈ S, f p (rootCode p P₀) :=
      prod_congr rfl fun p _ => by simp only [hX]; ring
    rw [this, ← prod_sdiff hAG]
    ring
  have hRpt : ∀ P₀, |Fa P₀ * (∏ p ∈ S, (1 - X p (rootCode p P₀)) -
      bonfR S (fun p => X p (rootCode p P₀)) T)| ≤ esymmR S (fun p => X p (rootCode p P₀)) T := by
    intro P₀
    rw [abs_mul, abs_of_nonneg (hFa P₀).1]
    have := abs_prod_sub_bonf_le S (fun p => X p (rootCode p P₀)) (fun p _ => hXm p _) T
    exact (mul_le_of_le_one_left (abs_nonneg _) (hFa P₀).2).trans this
  -- expand the Bonferroni main part
  have hmain : (∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then
        Fa P₀ * bonfR S (fun p => X p (rootCode p P₀)) T else 0) =
      ∑ k ∈ range T, (-1) ^ k * ∑ t ∈ S.powersetCard k, ∑ P₀ ∈ posBox P.U P.V,
        if normRoot P P₀ ∈ B then Fa P₀ * ∏ p ∈ t, X p (rootCode p P₀) else 0 := by
    have : ∀ P₀, (if normRoot P P₀ ∈ B then Fa P₀ * bonfR S (fun p => X p (rootCode p P₀)) T
        else 0) = ∑ k ∈ range T, (-1) ^ k * ∑ t ∈ S.powersetCard k,
          (if normRoot P P₀ ∈ B then Fa P₀ * ∏ p ∈ t, X p (rootCode p P₀) else 0) := by
      intro P₀
      split_ifs
      · unfold bonfR esymmR
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [← mul_sum]; ring
      · simp
    rw [sum_congr rfl fun P₀ _ => this P₀, sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_sum, sum_comm]
  have hsplit : (∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then ∏ p ∈ G, f p (rootCode p P₀)
        else 0) =
      (∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then
        Fa P₀ * bonfR S (fun p => X p (rootCode p P₀)) T else 0) +
      ∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then Fa P₀ * (∏ p ∈ S, (1 - X p (rootCode p P₀)) -
        bonfR S (fun p => X p (rootCode p P₀)) T) else 0 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun P₀ _ => ?_
    split_ifs
    · exact hpt P₀
    · simp
  have hE0 : 0 ≤ E := by have := rpow_nonneg hx (-c); positivity
  -- the main part
  have hM : |(∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then
        Fa P₀ * bonfR S (fun p => X p (rootCode p P₀)) T else 0) - c₀ * mA * bonfR S aX T| ≤
      (∑ k ∈ range T, (S.card.choose k : ℝ)) * E := by
    rw [hmain]
    have : c₀ * mA * bonfR S aX T = ∑ k ∈ range T, (-1) ^ k *
        ∑ t ∈ S.powersetCard k, c₀ * (mA * ∏ p ∈ t, aX p) := by
      unfold bonfR esymmR
      rw [mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [← mul_sum, ← mul_sum]; ring
    rw [this, ← sum_sub_distrib, sum_mul]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
    rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ t ∈ S.powersetCard k, |(∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then
            Fa P₀ * ∏ p ∈ t, X p (rootCode p P₀) else 0) - c₀ * (mA * ∏ p ∈ t, aX p)|
        ≤ ∑ _t ∈ S.powersetCard k, E := sum_le_sum fun t ht =>
          hQ t (mem_powerset.2 (mem_powersetCard.1 ht).1)
            (by rw [(mem_powersetCard.1 ht).2]; exact (mem_range.1 hk).le)
      _ = (S.card.choose k : ℝ) * E := by rw [sum_const, card_powersetCard, nsmul_eq_mul]
  -- the remainder
  have hR : |∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then Fa P₀ * (∏ p ∈ S,
        (1 - X p (rootCode p P₀)) - bonfR S (fun p => X p (rootCode p P₀)) T) else 0| ≤
      c₀ * esymmR S aX T + (S.card.choose T : ℝ) * E := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have e1 : ∀ P₀, (if normRoot P P₀ ∈ B then esymmR S (fun p => X p (rootCode p P₀)) T else 0) =
        ∑ t ∈ S.powersetCard T, (if normRoot P P₀ ∈ B then ∏ p ∈ t, X p (rootCode p P₀) else 0) := by
      intro P₀; split_ifs
      · rfl
      · simp
    calc ∑ P₀ ∈ posBox P.U P.V, |if normRoot P P₀ ∈ B then Fa P₀ * (∏ p ∈ S,
            (1 - X p (rootCode p P₀)) - bonfR S (fun p => X p (rootCode p P₀)) T) else 0|
        ≤ ∑ P₀ ∈ posBox P.U P.V,
            (if normRoot P P₀ ∈ B then esymmR S (fun p => X p (rootCode p P₀)) T else 0) :=
          sum_le_sum fun P₀ _ => by
            split_ifs
            · exact hRpt P₀
            · simp
      _ = ∑ t ∈ S.powersetCard T, ∑ P₀ ∈ posBox P.U P.V,
            (if normRoot P P₀ ∈ B then ∏ p ∈ t, X p (rootCode p P₀) else 0) := by
          rw [sum_congr rfl fun P₀ _ => e1 P₀, sum_comm]
      _ ≤ ∑ t ∈ S.powersetCard T, (c₀ * ∏ p ∈ t, aX p + E) := sum_le_sum fun t ht => by
          have := hQ2 t (mem_powerset.2 (mem_powersetCard.1 ht).1) (mem_powersetCard.1 ht).2.le
          linarith [(abs_le.1 this).2]
      _ = c₀ * esymmR S aX T + (S.card.choose T : ℝ) * E := by
          rw [sum_add_distrib, ← mul_sum, sum_const, card_powersetCard, nsmul_eq_mul]; rfl
  -- the mean
  have hm_eq : ∏ p ∈ G, avgL f p = mA * ∏ p ∈ S, (1 - aX p) := by
    rw [← prod_sdiff hAG, mul_comm]
    congr 1
    refine prod_congr rfl fun p _ => ?_
    simp only [haX, hX]; rw [avgL_one_sub]; ring
  have he0 := esymmR_nonneg S aX (fun p _ => (haXm p).1) T
  have hB2 : |c₀ * mA * bonfR S aX T - c₀ * ∏ p ∈ G, avgL f p| ≤ c₀ * esymmR S aX T := by
    rw [hm_eq]
    have h := abs_prod_sub_bonf_le S aX (fun p _ => haXm p) T
    have e : c₀ * mA * bonfR S aX T - c₀ * (mA * ∏ p ∈ S, (1 - aX p)) =
        -(c₀ * mA) * (∏ p ∈ S, (1 - aX p) - bonfR S aX T) := by ring
    rw [e, abs_mul, abs_neg, abs_of_nonneg (mul_nonneg hc₀0 hmA.1)]
    calc c₀ * mA * |∏ p ∈ S, (1 - aX p) - bonfR S aX T| ≤ c₀ * 1 * esymmR S aX T :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmA.2 hc₀0) h (abs_nonneg _) (by positivity)
      _ = c₀ * esymmR S aX T := by ring
  have hT : (∑ k ∈ range T, (S.card.choose k : ℝ)) + S.card.choose T ≤ ((G.card : ℝ) + 1) ^ T := by
    rw [← sum_range_succ (fun k => (S.card.choose k : ℝ)) T]
    refine (sum_choose_le_pow S.card T).trans ?_
    have : (S.card : ℝ) ≤ G.card := by exact_mod_cast card_le_card hSG
    gcongr
  have h1 : (∑ k ∈ range T, (S.card.choose k : ℝ)) * E + (S.card.choose T : ℝ) * E ≤
      ((G.card : ℝ) + 1) ^ T * E := by
    rw [← add_mul]; exact mul_le_mul_of_nonneg_right hT hE0
  have h2 : c₀ * esymmR S aX T ≤ 6 / π ^ 2 * (P.U * P.V) * (15 / n) * esymmR S aX T :=
    mul_le_mul_of_nonneg_right hc₀le he0
  show |(∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then ∏ p ∈ G, f p (rootCode p P₀) else 0) -
    c₀ * ∏ p ∈ G, avgL f p| ≤ _
  rw [hsplit]
  have key := abs_add_three ((∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then
        Fa P₀ * bonfR S (fun p => X p (rootCode p P₀)) T else 0) - c₀ * mA * bonfR S aX T)
    (c₀ * mA * bonfR S aX T - c₀ * ∏ p ∈ G, avgL f p)
    (∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then Fa P₀ * (∏ p ∈ S,
        (1 - X p (rootCode p P₀)) - bonfR S (fun p => X p (rootCode p P₀)) T) else 0)
  have e : (∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then
        Fa P₀ * bonfR S (fun p => X p (rootCode p P₀)) T else 0) +
      (∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then Fa P₀ * (∏ p ∈ S,
        (1 - X p (rootCode p P₀)) - bonfR S (fun p => X p (rootCode p P₀)) T) else 0) -
      c₀ * ∏ p ∈ G, avgL f p =
      ((∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then
        Fa P₀ * bonfR S (fun p => X p (rootCode p P₀)) T else 0) - c₀ * mA * bonfR S aX T) +
      (c₀ * mA * bonfR S aX T - c₀ * ∏ p ∈ G, avgL f p) +
      (∑ P₀ ∈ posBox P.U P.V, if normRoot P P₀ ∈ B then Fa P₀ * (∏ p ∈ S,
        (1 - X p (rootCode p P₀)) - bonfR S (fun p => X p (rootCode p P₀)) T) else 0) := by ring
  rw [e]
  linarith

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): both sides as sums over paths

With `W = wNon`, `E` the end indicator, `L = archList`:
* `∑_{P₀ ∈ Ω} pathPhi(root P₀, physDelta P₀) = σ ∑_{ℓ₀, cs} W E ∑_{P₀} 1[RegionN L (P₀/UV)] Φ(P₀)`, with
  `Φ(P₀) = ∏_{p ∈ 𝒢} h_p(κ_p(P₀))` (`phys_expand`);
* `∫∫∫ rootIL(Uu, Vv, r) = σ ∑_{ℓ₀, cs} W E m vol(RegionN L)` with `m = ∏_p avg_t h_p(t)`
  (`integral_rootIL`);
* hence the difference of the two sides of D7r is `σ ∑ W E · Epath` (`diff_expand`). -/

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory

namespace PE

variable (P : MemParams)

/-- The end indicator. -/
def endF (s : (ℤ × ℤ) × P.Lst) : ℂ := if s.1 = (1, 0) then 1 else 0

/-- The start state. -/
def st0 (ℓ₀ : P.Lst) : St P := ((1, 0), ℓ₀)

lemma gcd_st0 (ℓ₀ : P.Lst) : Int.gcd (st0 P ℓ₀).1.1 (st0 P ℓ₀).1.2 = 1 := by
  simp [st0]

/-- The physical line weight of a path. -/
noncomputable def PhiP (ℓ₀ : P.Lst) (cs : Fin P.N → StepT P) (P₀ : ℕ × ℕ) : ℝ :=
  ∏ p ∈ P.gPrimes, hpL P p (rootCode p P₀) P.N (st0 P ℓ₀) cs

/-- The mean line weight of a path. -/
noncomputable def mP (ℓ₀ : P.Lst) (cs : Fin P.N → StepT P) : ℝ :=
  ∏ p ∈ P.gPrimes, avgL (fun p t => hpL P p t P.N (st0 P ℓ₀) cs) p

open Classical in
/-- The error of one path. -/
noncomputable def Epath (ℓ₀ : P.Lst) (cs : Fin P.N → StepT P) : ℝ :=
  (∑ P₀ ∈ posBox P.U P.V, if RegionN P (archList P P.N (st0 P ℓ₀) cs) (normRoot P P₀)
      then PhiP P ℓ₀ cs P₀ else 0) -
    6 / π ^ 2 * (P.U * P.V) * mP P ℓ₀ cs *
      (volume {p | RegionN P (archList P P.N (st0 P ℓ₀) cs) p}).toReal

open Classical in
lemma pathPhi_expand (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) :
    P.pathPhi ω δ = (stateNorm P.x P.a P.J : ℂ) * ∑ ℓ₀ ∈ listCands P.x P.a P.J,
      ∑ cs : Fin P.N → StepT P, wNon P P.N (st0 P ℓ₀) cs *
        (if archP P ω P.N (st0 P ℓ₀) cs then 1 else 0) * (visP P δ P.N (st0 P ℓ₀) cs : ℂ) *
          endF P (endSt P P.N (st0 P ℓ₀) cs) := by
  unfold MemParams.pathPhi
  congr 1
  refine sum_congr rfl fun ℓ₀ _ => ?_
  exact physTail_expand P ω δ (endF P) (fun _ _ _ => rfl) P.N (st0 P ℓ₀)

lemma visP_phys (hG : ∀ p ∈ P.gPrimes, p.Prime) {P₀ : ℕ × ℕ} (hu : 0 < P₀.1)
    (hcop : Nat.Coprime P₀.1 P₀.2) (ℓ₀ : P.Lst) (cs : Fin P.N → StepT P) :
    visP P (physDelta P₀) P.N (st0 P ℓ₀) cs = PhiP P ℓ₀ cs P₀ := by
  rw [visP_eq_prod]
  unfold PhiP
  refine prod_congr rfl fun p hp => ?_
  unfold hpL
  exact hpP_congr P (fun z hz => physDelta_iff_lineOf (hG p hp) hu hcop hz) _ _ (gcd_st0 P ℓ₀) _

lemma visP_lam (lam : ∀ p ∈ P.gPrimes, ℕ) (ℓ₀ : P.Lst) (cs : Fin P.N → StepT P) :
    visP P (fun p z => ∃ h : p ∈ P.gPrimes, lineOf p z = lam p h) P.N (st0 P ℓ₀) cs =
      ∏ x ∈ P.gPrimes.attach, hpL P x.1 (lam x.1 x.2) P.N (st0 P ℓ₀) cs := by
  rw [visP_eq_prod, ← prod_attach]
  refine prod_congr rfl fun x _ => ?_
  unfold hpL
  exact hpP_congr P (fun z _ => ⟨fun ⟨_, e⟩ => e, fun e => ⟨x.2, e⟩⟩) _ _ (gcd_st0 P ℓ₀) _

lemma lam_avg (G : Finset ℕ) (F : ℕ → ℕ → ℝ) :
    (∏ p ∈ G, ((p : ℝ) + 1))⁻¹ * ∑ lam ∈ G.pi (fun p => range (p + 1)),
      ∏ x ∈ G.attach, F x.1 (lam x.1 x.2) = ∏ p ∈ G, avgL F p := by
  rw [← prod_sum (s := G) (t := fun p => range (p + 1)) (f := fun p t => F p t)]
  unfold avgL
  rw [prod_div_distrib, div_eq_inv_mul]

open Classical in
lemma rootIL_expand (ω : ℝ × ℝ × ℝ) :
    P.rootIL ω = (stateNorm P.x P.a P.J : ℂ) * ∑ ℓ₀ ∈ listCands P.x P.a P.J,
      ∑ cs : Fin P.N → StepT P, wNon P P.N (st0 P ℓ₀) cs *
        (if archP P ω P.N (st0 P ℓ₀) cs then 1 else 0) * endF P (endSt P P.N (st0 P ℓ₀) cs) *
          ((mP P ℓ₀ cs : ℝ) : ℂ) := by
  unfold MemParams.rootIL
  simp only [pathPhi_expand, visP_lam]
  unfold mP
  simp only [← lam_avg]
  push_cast
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun ℓ₀ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun cs _ => ?_
  refine sum_congr rfl fun lam _ => ?_
  ring

open Classical in
/-- **The physical side as a sum over paths.** -/
theorem phys_expand (hU : 0 < P.U) (hV : 0 < P.V) (hG : ∀ p ∈ P.gPrimes, p.Prime) :
    ∑ P₀ ∈ posBox P.U P.V, P.pathPhi (rootOf P₀) (physDelta P₀) =
      (stateNorm P.x P.a P.J : ℂ) * ∑ ℓ₀ ∈ listCands P.x P.a P.J,
        ∑ cs : Fin P.N → StepT P, wNon P P.N (st0 P ℓ₀) cs * endF P (endSt P P.N (st0 P ℓ₀) cs) *
          (((∑ P₀ ∈ posBox P.U P.V, if RegionN P (archList P P.N (st0 P ℓ₀) cs) (normRoot P P₀)
            then PhiP P ℓ₀ cs P₀ else 0 : ℝ)) : ℂ) := by
  have hpt : ∀ P₀ ∈ posBox P.U P.V, P.pathPhi (rootOf P₀) (physDelta P₀) =
      (stateNorm P.x P.a P.J : ℂ) * ∑ ℓ₀ ∈ listCands P.x P.a P.J,
        ∑ cs : Fin P.N → StepT P, wNon P P.N (st0 P ℓ₀) cs * endF P (endSt P P.N (st0 P ℓ₀) cs) *
          (((if RegionN P (archList P P.N (st0 P ℓ₀) cs) (normRoot P P₀)
            then PhiP P ℓ₀ cs P₀ else 0 : ℝ)) : ℂ) := by
    intro P₀ hP₀
    obtain ⟨h1, -, -, -, hcop⟩ := posBox_bounds hU hV hP₀
    have hu : 0 < P₀.1 := by
      have : (0 : ℝ) < P₀.1 := hU.trans_le h1
      exact_mod_cast this
    rw [pathPhi_expand]
    congr 1
    refine sum_congr rfl fun ℓ₀ _ => sum_congr rfl fun cs _ => ?_
    rw [visP_phys P hG hu hcop, archP_root P hU hV hP₀]
    split_ifs <;> push_cast <;> ring
  rw [sum_congr rfl hpt, ← mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun ℓ₀ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun cs _ => ?_
  rw [← mul_sum]
  push_cast
  rfl

open Classical in
/-- **The integral side as a sum over paths.** -/
theorem integral_rootIL :
    ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, P.rootIL (P.U * u, P.V * v, r) =
      (stateNorm P.x P.a P.J : ℂ) * ∑ ℓ₀ ∈ listCands P.x P.a P.J,
        ∑ cs : Fin P.N → StepT P, wNon P P.N (st0 P ℓ₀) cs * endF P (endSt P P.N (st0 P ℓ₀) cs) *
          ((mP P ℓ₀ cs * (volume {p | RegionN P (archList P P.N (st0 P ℓ₀) cs) p}).toReal : ℝ) : ℂ) := by
  set c : P.Lst → (Fin P.N → StepT P) → ℂ := fun ℓ₀ cs => (stateNorm P.x P.a P.J : ℂ) *
    (wNon P P.N (st0 P ℓ₀) cs * endF P (endSt P P.N (st0 P ℓ₀) cs) * ((mP P ℓ₀ cs : ℝ) : ℂ)) with hc
  have hpt : ∀ p : ℝ × ℝ × ℝ, P.rootIL (P.U * p.1, P.V * p.2.1, p.2.2) =
      ∑ ℓ₀ ∈ listCands P.x P.a P.J, ∑ cs : Fin P.N → StepT P,
        (if p ∈ AL P (archList P P.N (st0 P ℓ₀) cs) then c ℓ₀ cs else 0) := by
    intro p
    rw [rootIL_expand, mul_sum]
    refine sum_congr rfl fun ℓ₀ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun cs _ => ?_
    rw [archP_norm]
    by_cases h : p ∈ AL P (archList P P.N (st0 P ℓ₀) cs)
    · rw [if_pos h, if_pos h, hc]; ring
    · rw [if_neg h, if_neg h]; ring
  have hint : IntegrableOn (fun p : ℝ × ℝ × ℝ => P.rootIL (P.U * p.1, P.V * p.2.1, p.2.2)) boxN := by
    rw [show (fun p : ℝ × ℝ × ℝ => P.rootIL (P.U * p.1, P.V * p.2.1, p.2.2)) = fun p =>
      ∑ ℓ₀ ∈ listCands P.x P.a P.J, ∑ cs : Fin P.N → StepT P,
        (if p ∈ AL P (archList P P.N (st0 P ℓ₀) cs) then c ℓ₀ cs else 0) from funext hpt]
    refine integrable_finsetSum _ fun ℓ₀ _ => integrable_finsetSum _ fun cs _ => ?_
    exact integrableOn_ite _ (measurableSet_AL P _) _
  have hf := fubini3 _ hint
  simp only at hf
  rw [hf]
  rw [show (fun p : ℝ × ℝ × ℝ => P.rootIL (P.U * p.1, P.V * p.2.1, p.2.2)) = fun p =>
      ∑ ℓ₀ ∈ listCands P.x P.a P.J, ∑ cs : Fin P.N → StepT P,
        (if p ∈ AL P (archList P P.N (st0 P ℓ₀) cs) then c ℓ₀ cs else 0) from funext hpt]
  rw [integral_finsetSum _ fun ℓ₀ _ => integrable_finsetSum _ fun cs _ =>
    integrableOn_ite _ (measurableSet_AL P _) _]
  rw [mul_sum]
  refine sum_congr rfl fun ℓ₀ _ => ?_
  rw [integral_finsetSum _ fun cs _ => integrableOn_ite _ (measurableSet_AL P _) _, mul_sum]
  refine sum_congr rfl fun cs _ => ?_
  rw [integral_ite _ (measurableSet_AL P _), ← regionN_eq]
  simp only [hc]
  push_cast
  ring

open Classical in
/-- **The difference of the two sides of D7r as a sum over paths.** -/
theorem diff_expand (hU : 0 < P.U) (hV : 0 < P.V) (hG : ∀ p ∈ P.gPrimes, p.Prime) :
    ∑ P₀ ∈ posBox P.U P.V, P.pathPhi (rootOf P₀) (physDelta P₀) -
        ((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) *
          ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, P.rootIL (P.U * u, P.V * v, r) =
      (stateNorm P.x P.a P.J : ℂ) * ∑ ℓ₀ ∈ listCands P.x P.a P.J,
        ∑ cs : Fin P.N → StepT P, wNon P P.N (st0 P ℓ₀) cs * endF P (endSt P P.N (st0 P ℓ₀) cs) *
          ((Epath P ℓ₀ cs : ℝ) : ℂ) := by
  rw [phys_expand P hU hV hG, integral_rootIL, mul_left_comm ((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ),
    ← mul_sub]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine sum_congr rfl fun ℓ₀ _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine sum_congr rfl fun cs _ => ?_
  unfold Epath
  push_cast
  ring

end PE

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): the error of one path

For a path of nonzero weight:
* if its positions are not all bounded by `Zb = 4096 N · 10 d₀ Y`, its region is empty and its
  error vanishes (`epath_eq_zero`);
* otherwise `region_compare` with the oracles of `oracle_bonf` (Bonferroni over the primes never
  active on the path, `A` = the active ones) and the crossing count `card_badSlab_le` bound its
  error (`epath_le`). -/

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

namespace ArtinPrimitiveRoots.L102E

open Real Finset MeasureTheory

namespace PE

variable (P : MemParams)

lemma PhiP_mem (ℓ₀ : P.Lst) (cs : Fin P.N → StepT P) (P₀ : ℕ × ℕ) :
    0 ≤ PhiP P ℓ₀ cs P₀ ∧ PhiP P ℓ₀ cs P₀ ≤ 1 :=
  ⟨prod_nonneg fun p _ => (hpL_mem P _ _ _ _ _).1,
    prod_le_one (fun p _ => (hpL_mem P _ _ _ _ _).1) fun p _ => (hpL_mem P _ _ _ _ _).2⟩

lemma mP_mem (ℓ₀ : P.Lst) (cs : Fin P.N → StepT P) : 0 ≤ mP P ℓ₀ cs ∧ mP P ℓ₀ cs ≤ 1 := by
  have hf : ∀ p t, 0 ≤ hpL P p t P.N (st0 P ℓ₀) cs ∧ hpL P p t P.N (st0 P ℓ₀) cs ≤ 1 :=
    fun p t => hpL_mem P _ _ _ _ _
  exact ⟨prod_nonneg fun p _ => (avgL_mem hf p).1,
    prod_le_one (fun p _ => (avgL_mem hf p).1) fun p _ => (avgL_mem hf p).2⟩

lemma archList_length : ∀ (k : ℕ) (s : St P) (cs : Fin k → StepT P),
    (archList P k s cs).length = 2 * k
  | 0, s, cs => rfl
  | k + 1, s, cs => by
    simp only [archList, List.length_cons, archList_length k]
    ring

/-- A point of the region of a live path forces bounded positions. -/
lemma bdd_of_region (hU : 0 < P.U) (hY : 0 < P.Y) (hd₀ : 0 < P.d₀) (hV : ∀ i, 0 ≤ P.Vg i)
    {ℓ₀ : P.Lst} {cs : Fin P.N → StepT P} (hw : wNon P P.N (st0 P ℓ₀) cs ≠ 0)
    {p : ℝ × ℝ × ℝ} (hp : RegionN P (archList P P.N (st0 P ℓ₀) cs) p) :
    BddP P (4096 * P.N * (10 * P.d₀ * P.Y)) P.N (st0 P ℓ₀) cs := by
  obtain ⟨hp1, hp2, -, -, hr0, hr1, hAL⟩ := hp
  set ω : ℝ × ℝ × ℝ := (P.U * p.1, P.V * p.2.1, p.2.2) with hω
  have hω1 : P.U ≤ ω.1 := by simp only [hω]; nlinarith
  have hω2 : ω.1 ≤ 16 * P.U := by simp only [hω]; nlinarith
  have ha : archP P ω P.N (st0 P ℓ₀) cs := (archP_norm P p _ _ _).2 hAL
  have hB : |((st0 P ℓ₀).1.2 : ℝ) / tauR ω (st0 P ℓ₀).1| ≤ 0 := by simp [st0]
  have hlb := live_bound P hU hY hd₀ hV hω1 hω2 P.N (st0 P ℓ₀) cs 0 hw ha hB
  have hbox := (archP_iff P ω _ _ _).1 ha
  intro q hq
  have h1 := hlb q hq
  have ht := tau_bounds P hU hω1 hω2 (hbox q hq).1
  have hH : 0 ≤ 256 * (10 * (P.d₀ : ℝ) * P.Y) * P.N := by positivity
  have hz2 : |(q.1.2 : ℝ)| ≤ 4096 * P.N * (10 * P.d₀ * P.Y) := by
    have hτ0 : tauR ω q.1 ≠ 0 := by linarith
    have e : (q.1.2 : ℝ) = (q.1.2 : ℝ) / tauR ω q.1 * tauR ω q.1 := (div_mul_cancel₀ _ hτ0).symm
    rw [e, abs_mul, abs_of_pos (by linarith : 0 < tauR ω q.1)]
    calc |(q.1.2 : ℝ) / tauR ω q.1| * tauR ω q.1 ≤ (0 + 256 * (10 * P.d₀ * P.Y) * P.N) * 16 :=
          mul_le_mul h1 ht.2 (by linarith) (by linarith)
      _ = 4096 * P.N * (10 * P.d₀ * P.Y) := by ring
  refine ⟨hz2, ?_⟩
  have hτ : tauR ω q.1 = q.1.1 + p.2.2 * q.1.2 := rfl
  have e : (q.1.1 : ℝ) = tauR ω q.1 - p.2.2 * q.1.2 := by rw [hτ]; ring
  rw [e]
  have : |p.2.2 * (q.1.2 : ℝ)| ≤ |(q.1.2 : ℝ)| := by
    rw [abs_mul, abs_of_nonneg hr0]
    exact mul_le_of_le_one_left (abs_nonneg _) hr1.le
  have := abs_sub (tauR ω q.1) (p.2.2 * q.1.2)
  rw [abs_of_pos (by linarith : 0 < tauR ω q.1)] at this
  linarith [ht.2]

open Classical in
/-- **An unbounded live path has no error.** -/
lemma epath_eq_zero (hU : 0 < P.U) (hY : 0 < P.Y) (hd₀ : 0 < P.d₀) (hV : ∀ i, 0 ≤ P.Vg i)
    {ℓ₀ : P.Lst} {cs : Fin P.N → StepT P} (hw : wNon P P.N (st0 P ℓ₀) cs ≠ 0)
    (hnb : ¬ BddP P (4096 * P.N * (10 * P.d₀ * P.Y)) P.N (st0 P ℓ₀) cs) : Epath P ℓ₀ cs = 0 := by
  have hemp : ∀ p, ¬ RegionN P (archList P P.N (st0 P ℓ₀) cs) p := fun p hp =>
    hnb (bdd_of_region P hU hY hd₀ hV hw hp)
  unfold Epath
  have h1 : (∑ P₀ ∈ posBox P.U P.V, if RegionN P (archList P P.N (st0 P ℓ₀) cs) (normRoot P P₀)
      then PhiP P ℓ₀ cs P₀ else 0) = 0 := sum_eq_zero fun P₀ _ => if_neg (hemp _)
  have h2 : {p | RegionN P (archList P P.N (st0 P ℓ₀) cs) p} = ∅ := by
    ext p; simp [hemp p]
  rw [h1, h2]
  simp

/-- The size of the test integers. -/
noncomputable def Mtb (Pm : ℝ) : ℝ := (P.Y ^ (0.2 : ℝ) + 2) * Pm ^ (P.K * (P.J + 1) + 2 * P.K)

/-- The number of tests. -/
noncomputable def Tcb (Cg : ℝ) : ℝ :=
  ((P.J + 1 : ℕ) : ℝ) ^ P.K * P.Y ^ (0.2 : ℝ) +
    2 ^ P.K * (((P.J + 1 : ℕ) : ℝ) ^ (2 * P.K) * Cg ^ (3 * P.K))

/-- The Lemma 3.3 error. -/
noncomputable def Eb (x c : ℝ) : ℝ := exp (log x ^ (0.98 : ℝ)) ^ 3 * (P.U * P.V * x ^ (-c))

lemma mem_gPrimes {p : ℕ} (hp : p ∈ P.gPrimes) : ∃ i, p ∈ P.grp i := by
  unfold MemParams.gPrimes groupPrimes at hp
  obtain ⟨i, -, hi⟩ := mem_biUnion.1 hp
  exact ⟨i, hi⟩

lemma const_oracle {x c : ℝ} (hx1 : 1 ≤ x) (hRC : RootCount2At x P.U P.V c) (hU : 0 < P.U)
    (hV : 0 < P.V) (n : ℕ) : Oracle P n (fun _ => 1) 1 (Eb P x c) := by
  have hx : 0 ≤ x := by linarith
  have h := oracle_bonf P hx hRC hU hV (G := ∅) (A := ∅) subset_rfl (by simp) (Pm := 1) le_rfl
    (by simp) (T := 1) (by simp; exact rpow_nonneg (log_nonneg hx1) _) (fun _ _ => 1) (by simp) n
  have he : esymmR ((∅ : Finset ℕ) \ ∅) (avgL fun p t => 1 - (fun _ _ => (1 : ℝ)) p t) 1 = 0 := by
    rw [sdiff_self]; exact esymmR_empty_succ _ 0
  rw [he] at h
  intro a₁ b₁ a₂ b₂ k h1 h2 h3 h4 h5
  have := h a₁ b₁ a₂ b₂ k h1 h2 h3 h4 h5
  simp only [prod_empty, mul_zero, zero_add, card_empty, Nat.cast_zero, pow_one, one_mul] at this
  exact this

open Classical in
/-- **The error of a bounded path.** -/
theorem epath_le {x c : ℝ} (hx1 : 1 ≤ x) (hRC : RootCount2At x P.U P.V c) (hU : 0 < P.U)
    (hV : 0 < P.V) (hG : ∀ p ∈ P.gPrimes, p.Prime) {Pm : ℝ} (hPm1 : 1 ≤ Pm)
    (hgrp : ∀ i, ∀ p ∈ P.grp i, (p : ℝ) ≤ Pm) {T : ℕ}
    (hPT : Pm ^ ((P.N + 1) * (P.K * (P.J + 1)) + T) ≤ exp (log x ^ (0.98 : ℝ)))
    (hY1 : 1 ≤ P.Y) {Cg : ℝ} (hCg : 1 ≤ Cg) (hcard : ∀ i, ((P.grp i).card : ℝ) ≤ Cg)
    {ℓ₀ : P.Lst} (hℓ₀ : ℓ₀ ∈ listCands P.x P.a P.J) (cs : Fin P.N → StepT P) {Zb : ℝ}
    (hZ0 : 0 ≤ Zb) (hbdd : BddP P Zb P.N (st0 P ℓ₀) cs) {n : ℕ} (hn : 0 < n)
    (hZn : Zb / n ≤ 1 / 64) :
    |Epath P ℓ₀ cs| ≤ n * ((2 * (6 / π ^ 2) * (P.U * P.V) * (15 / n) *
          (((P.N + 1 : ℝ) * ∑ p ∈ P.gPrimes, 1 / ((p : ℝ) + 1)) ^ T / (T.factorial : ℝ)) +
        ((P.gPrimes.card : ℝ) + 1) ^ T * Eb P x c) + 2 * Eb P x c) +
      6 / π ^ 2 * (P.U * P.V) * (6000 * (Zb / n + Zb / (P.U * P.V))) +
      ((2 * P.N : ℕ) : ℝ) * (4 * Tcb P Cg * (2 * (4096 * Mtb P Pm + 1) + 1)) *
        (30 * (6 / π ^ 2 * (P.U * P.V)) / n + Eb P x c) := by
  have hx : 0 ≤ x := by linarith
  set L := archList P P.N (st0 P ℓ₀) cs with hL
  set lb := labs P P.N (st0 P ℓ₀) cs with hlb
  set A := P.gPrimes.filter (· ∈ lb) with hA
  have hAG : A ⊆ P.gPrimes := filter_subset _ _
  have hAc : A.card ≤ (P.N + 1) * (P.K * (P.J + 1)) :=
    (card_le_card fun p hp => (mem_filter.1 hp).2).trans (card_labs P _ _ _)
  have hPT' : Pm ^ (A.card + T) ≤ exp (log x ^ (0.98 : ℝ)) :=
    le_trans (pow_le_pow_right₀ hPm1 (by omega)) hPT
  have hPmG : ∀ p ∈ P.gPrimes, (p : ℝ) ≤ Pm := fun p hp => by
    obtain ⟨i, hi⟩ := mem_gPrimes P hp
    exact hgrp i p hi
  set f : ℕ → ℕ → ℝ := fun p t => hpL P p t P.N (st0 P ℓ₀) cs with hf
  have hfm : ∀ p t, 0 ≤ f p t ∧ f p t ≤ 1 := fun p t => hpL_mem P _ _ _ _ _
  have hO := oracle_bonf P hx hRC hU hV hAG hG hPm1 hPmG hPT' f hfm n
  have hC := const_oracle P hx1 hRC hU hV n
  -- the list
  have hz : ∀ q ∈ L, |((q.1.2 : ℤ) : ℝ)| ≤ Zb := fun q hq => (hbdd q hq).1
  have hgcd : ∀ q ∈ L, Int.gcd q.1.1 q.1.2 = 1 := archList_gcd P (gcd_st0 P ℓ₀) cs
  have hgrpL : ∀ q ∈ L, ∀ i j, q.2 i j ∈ P.grp i :=
    archList_grp P P.N (st0 P ℓ₀) cs (fun i j => Fintype.mem_piFinset.1
      (Fintype.mem_piFinset.1 hℓ₀ i) j)
  have hMt0 : 0 ≤ Mtb P Pm := by unfold Mtb; positivity
  have hMt : ∀ q ∈ L, ∀ t ∈ tests P.x P.Y P.a q.2, |(t.1 : ℝ)| ≤ Mtb P Pm := by
    intro q hq
    exact tests_le P.x P.Y hY1 P.a q.2 hPm1 (fun i j => hgrp i _ (hgrpL q hq i j))
      (fun i p hp => hgrp i p hp)
  have hTc : ∀ q ∈ L, ((tests P.x P.Y P.a q.2).card : ℝ) ≤ Tcb P Cg := by
    intro q hq
    exact card_tests_le P.x P.Y hY1 P.a q.2 hCg hcard
  have hBad := card_badSlab_le P L hgcd hz hn hZn hMt0 hMt hTc
  rw [archList_length] at hBad
  have hrc := region_compare P hU hV L hZ0 hz hn hZn (PhiP P ℓ₀ cs)
    (fun P₀ _ => PhiP_mem P ℓ₀ cs P₀) (mP_mem P ℓ₀ cs).1 (mP_mem P ℓ₀ cs).2 hO hC le_rfl
  -- the Bonferroni error
  have hX : ∀ p ∈ P.gPrimes \ A, avgL (fun p t => 1 - f p t) p ≤ (P.N + 1 : ℝ) / ((p : ℝ) + 1) := by
    intro p hp
    obtain ⟨hpG, hpA⟩ := mem_sdiff.1 hp
    have hpl : p ∉ lb := fun h => hpA (mem_filter.2 ⟨hpG, h⟩)
    have : NeZero p := ⟨(hG p hpG).ne_zero⟩
    have := sum_one_sub_hpL P p P.N (st0 P ℓ₀) cs hpl
    unfold avgL
    exact div_le_div_of_nonneg_right (by simpa [hf] using this) (by positivity)
  have hXm : ∀ p t, 0 ≤ 1 - f p t ∧ 1 - f p t ≤ 1 := fun p t => by
    constructor <;> linarith [hfm p t]
  have hS : ∑ p ∈ P.gPrimes \ A, avgL (fun p t => 1 - f p t) p ≤
      (P.N + 1 : ℝ) * ∑ p ∈ P.gPrimes, 1 / ((p : ℝ) + 1) := by
    calc ∑ p ∈ P.gPrimes \ A, avgL (fun p t => 1 - f p t) p
        ≤ ∑ p ∈ P.gPrimes \ A, (P.N + 1 : ℝ) / ((p : ℝ) + 1) := sum_le_sum hX
      _ ≤ ∑ p ∈ P.gPrimes, (P.N + 1 : ℝ) / ((p : ℝ) + 1) :=
          sum_le_sum_of_subset_of_nonneg sdiff_subset fun p _ _ => by positivity
      _ = (P.N + 1 : ℝ) * ∑ p ∈ P.gPrimes, 1 / ((p : ℝ) + 1) := by
          rw [mul_sum]; refine sum_congr rfl fun p _ => ?_; ring
  have he := esymm_le (P.gPrimes \ A) (avgL fun p t => 1 - f p t)
    (fun p _ => (avgL_mem hXm p).1) T
  have hS0 : 0 ≤ ∑ p ∈ P.gPrimes \ A, avgL (fun p t => 1 - f p t) p :=
    sum_nonneg fun p _ => (avgL_mem hXm p).1
  have he' : esymmR (P.gPrimes \ A) (avgL fun p t => 1 - f p t) T ≤
      ((P.N + 1 : ℝ) * ∑ p ∈ P.gPrimes, 1 / ((p : ℝ) + 1)) ^ T / (T.factorial : ℝ) :=
    he.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ hS0 hS T) (by positivity))
  -- assemble
  have hc0 : 0 ≤ 6 / π ^ 2 * (P.U * P.V) := by positivity
  have hE0 : 0 ≤ Eb P x c := by unfold Eb; have := rpow_nonneg hx (-c); positivity
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk1 : (2 * (6 / π ^ 2) * (P.U * P.V) * (15 / n) *
      esymmR (P.gPrimes \ A) (avgL fun p t => 1 - f p t) T) ≤ 2 * (6 / π ^ 2) * (P.U * P.V) *
        (15 / n) * (((P.N + 1 : ℝ) * ∑ p ∈ P.gPrimes, 1 / ((p : ℝ) + 1)) ^ T /
          (T.factorial : ℝ)) :=
    mul_le_mul_of_nonneg_left he' (by positivity)
  have hk2 : 0 ≤ 30 * (6 / π ^ 2 * (P.U * P.V)) / n + Eb P x c := by positivity
  have hBad' : (((range n).filter fun k => BadSlab P L n k).card : ℝ) *
      (30 * (6 / π ^ 2 * (P.U * P.V)) / n + Eb P x c) ≤
      ((2 * P.N : ℕ) : ℝ) * (4 * Tcb P Cg * (2 * (4096 * Mtb P Pm + 1) + 1)) *
        (30 * (6 / π ^ 2 * (P.U * P.V)) / n + Eb P x c) :=
    mul_le_mul_of_nonneg_right hBad hk2
  have hnk := mul_le_mul_of_nonneg_left (add_le_add_right (add_le_add_right hk1
    (((P.gPrimes.card : ℝ) + 1) ^ T * Eb P x c)) (2 * Eb P x c)) hn'.le
  have key : |Epath P ℓ₀ cs| ≤ (n : ℝ) * (2 * (6 / π ^ 2) * (P.U * P.V) * (15 / (n : ℝ)) *
      esymmR (P.gPrimes \ A) (avgL fun p t => 1 - f p t) T +
        ((P.gPrimes.card : ℝ) + 1) ^ T * Eb P x c + 2 * Eb P x c) +
      6 / π ^ 2 * (P.U * P.V) * (6000 * (Zb / n + Zb / (P.U * P.V))) +
      (((range n).filter fun k => BadSlab P L n k).card : ℝ) *
        (30 * (6 / π ^ 2 * (P.U * P.V)) / n + Eb P x c) := hrc
  linarith

end PE

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): sizes at a dyad

Bounds for the parameters of a path sum (`B₀ = e^{2L^{0.2}}` bounds every group prime):
* `Vᵢ⁻¹ ≤ B₀`, `σ ≤ B₀^{K(J+1)}`, `#listCands ≤ C^{K(J+1)}`, `∑_{p ∈ 𝒢} 1/(p+1) ≤ K(2 + 2L^{0.2})`;
* a path of nonzero weight forces `d₀ ≤ B₀^{KJ}` and `Y < B₀^K` (`live_params`);
* the bounded steps from a state weigh `≤ ∏Vᵢ⁻¹ (2Z+33)(2Z+1) C^K` (`step_sum_le`). -/

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

namespace ArtinPrimitiveRoots.L102E

open Real Finset

namespace PE

variable (P : MemParams)

lemma Vg_nonneg (i : Fin P.K) : 0 ≤ P.Vg i := by
  unfold MemParams.Vg groupReciprocalSum
  exact sum_nonneg fun p _ => by positivity

lemma inv_Vg_le {i : Fin P.K} {Pm : ℝ} (hPm : ∀ p ∈ P.grp i, (p : ℝ) ≤ Pm) (hPm0 : 0 ≤ Pm) :
    (P.Vg i)⁻¹ ≤ Pm := by
  rcases (P.grp i).eq_empty_or_nonempty with he | ⟨p, hp⟩
  · have : P.Vg i = 0 := by
      unfold MemParams.Vg groupReciprocalSum
      rw [show primeGroup P.x (P.a i) = P.grp i from rfl, he, sum_empty]
    rw [this, inv_zero]; exact hPm0
  · have hp0 : (0 : ℝ) < p := by
      have := L102D.pos_of_mem_primeGroup hp
      exact_mod_cast this
    have h1 : 1 / (p : ℝ) ≤ P.Vg i := by
      unfold MemParams.Vg groupReciprocalSum
      exact single_le_sum (f := fun q : ℕ => 1 / (q : ℝ)) (fun q _ => by positivity) hp
    have h2 : 0 < P.Vg i := lt_of_lt_of_le (by positivity) h1
    rw [inv_le_comm₀ h2 (lt_of_lt_of_le hp0 (hPm p hp))]
    rw [inv_eq_one_div]
    exact le_trans (one_div_le_one_div_of_le hp0 (hPm p hp)) h1

lemma stateNorm_le {Pm : ℝ} (hPm : ∀ i, ∀ p ∈ P.grp i, (p : ℝ) ≤ Pm) (hPm0 : 0 ≤ Pm) :
    stateNorm P.x P.a P.J ≤ Pm ^ (P.K * (P.J + 1)) := by
  unfold stateNorm
  calc ∏ i, (groupReciprocalSum P.x (P.a i))⁻¹ ^ (P.J + 1) ≤ ∏ _i : Fin P.K, Pm ^ (P.J + 1) := by
        refine prod_le_prod (fun i _ => pow_nonneg (inv_nonneg.2 (Vg_nonneg P i)) _) fun i _ => ?_
        exact pow_le_pow_left₀ (inv_nonneg.2 (Vg_nonneg P i)) (inv_Vg_le P (hPm i) hPm0) _
    _ = Pm ^ (P.K * (P.J + 1)) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul,
        mul_comm]

lemma prod_inv_Vg_le {Pm : ℝ} (hPm : ∀ i, ∀ p ∈ P.grp i, (p : ℝ) ≤ Pm) (hPm0 : 0 ≤ Pm) :
    ∏ i, (P.Vg i)⁻¹ ≤ Pm ^ P.K := by
  calc ∏ i, (P.Vg i)⁻¹ ≤ ∏ _i : Fin P.K, Pm :=
        prod_le_prod (fun i _ => inv_nonneg.2 (Vg_nonneg P i))
          fun i _ => inv_Vg_le P (hPm i) hPm0
    _ = Pm ^ P.K := by simp

lemma card_listCands_le {Cg : ℝ} (hcard : ∀ i, ((P.grp i).card : ℝ) ≤ Cg) :
    ((listCands P.x P.a P.J).card : ℝ) ≤ Cg ^ (P.K * (P.J + 1)) := by
  unfold listCands
  rw [Fintype.card_piFinset]
  push_cast
  calc ∏ i, (((Fintype.piFinset fun _ : Fin (P.J + 1) => primeGroup P.x (P.a i)).card : ℕ) : ℝ)
      ≤ ∏ _i : Fin P.K, Cg ^ (P.J + 1) := by
        refine prod_le_prod (fun i _ => by positivity) fun i _ => ?_
        rw [Fintype.card_piFinset]
        push_cast
        rw [prod_const, card_univ, Fintype.card_fin]
        exact pow_le_pow_left₀ (by positivity) (hcard i) _
    _ = Cg ^ (P.K * (P.J + 1)) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul,
        mul_comm]

lemma sum_biUnion_le' {ι : Type*} (s : Finset ι) (t : ι → Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p, 0 ≤ f p) : ∑ p ∈ s.biUnion t, f p ≤ ∑ i ∈ s, ∑ p ∈ t i, f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    have h := sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ p ∈ t a ∩ s.biUnion t, f p := sum_nonneg fun p _ => hf p
    linarith

lemma sum_inv_group_le (x b : ℝ) (hL : 0 ≤ log x ^ b) :
    ∑ p ∈ primeGroup x b, 1 / ((p : ℝ) + 1) ≤ 2 + 2 * log x ^ b := by
  set n := ⌊exp (2 * log x ^ b)⌋₊ with hn
  have hsub : ∀ p ∈ primeGroup x b, p ∈ Finset.Icc 1 n := by
    intro p hp
    unfold primeGroup at hp
    simp only [mem_filter, mem_range] at hp
    exact mem_Icc.2 ⟨hp.2.1.one_lt.le, Nat.lt_succ_iff.1 hp.1⟩
  have h1 : ∑ p ∈ primeGroup x b, 1 / ((p : ℝ) + 1) ≤ ∑ i ∈ Finset.Icc 1 n, ((i : ℝ))⁻¹ := by
    calc ∑ p ∈ primeGroup x b, 1 / ((p : ℝ) + 1) ≤ ∑ p ∈ primeGroup x b, ((p : ℝ))⁻¹ := by
          refine sum_le_sum fun p hp => ?_
          have : (1 : ℝ) ≤ p := by exact_mod_cast (mem_Icc.1 (hsub p hp)).1
          rw [one_div]
          exact inv_anti₀ (by linarith) (by linarith)
      _ ≤ ∑ i ∈ Finset.Icc 1 n, ((i : ℝ))⁻¹ :=
          sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
  have h2 : ∑ i ∈ Finset.Icc 1 n, ((i : ℝ))⁻¹ = (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have h3 := harmonic_le_one_add_log n
  have h4 : log (n : ℝ) ≤ 2 * log x ^ b + 1 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]; simp; positivity
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast h0
      have : (n : ℝ) ≤ exp (2 * log x ^ b) := Nat.floor_le (exp_pos _).le
      have := log_le_log hn0 this
      rw [log_exp] at this
      linarith
  linarith

lemma sum_inv_gPrimes_le (hL : 0 ≤ log P.x) (hb : ∀ i, log P.x ^ P.a i ≤ log P.x ^ (0.2 : ℝ)) :
    ∑ p ∈ P.gPrimes, 1 / ((p : ℝ) + 1) ≤ P.K * (2 + 2 * log P.x ^ (0.2 : ℝ)) := by
  unfold MemParams.gPrimes groupPrimes
  refine (sum_biUnion_le' _ _ _ fun p => by positivity).trans ?_
  calc ∑ i : Fin P.K, ∑ p ∈ primeGroup P.x (P.a i), 1 / ((p : ℝ) + 1)
      ≤ ∑ _i : Fin P.K, (2 + 2 * log P.x ^ (0.2 : ℝ)) := by
        refine sum_le_sum fun i _ => ?_
        refine (sum_inv_group_le P.x (P.a i) (rpow_nonneg hL _)).trans ?_
        linarith [hb i]
    _ = P.K * (2 + 2 * log P.x ^ (0.2 : ℝ)) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma card_gPrimes_le {Cg : ℝ} (hcard : ∀ i, ((P.grp i).card : ℝ) ≤ Cg) :
    (P.gPrimes.card : ℝ) ≤ P.K * Cg := by
  unfold MemParams.gPrimes groupPrimes
  calc (((univ : Finset (Fin P.K)).biUnion fun i => primeGroup P.x (P.a i)).card : ℝ)
      ≤ ∑ i : Fin P.K, ((primeGroup P.x (P.a i)).card : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _i : Fin P.K, Cg := sum_le_sum fun i _ => hcard i
    _ = P.K * Cg := by simp

/-! ## Live paths fix the dyad and the label scale -/

lemma padProd_le {Pm : ℝ} (hPm1 : 1 ≤ Pm) {ℓ : P.Lst} (hℓ : ∀ i j, (ℓ i j : ℝ) ≤ Pm) :
    (padProd ℓ : ℝ) ≤ Pm ^ (P.K * P.J) := by
  unfold padProd
  push_cast
  calc ∏ i, ∏ j : Fin P.J, (ℓ i j.castSucc : ℝ) ≤ ∏ _i : Fin P.K, ∏ _j : Fin P.J, Pm :=
        prod_le_prod (fun i _ => prod_nonneg fun j _ => by positivity) fun i _ =>
          prod_le_prod (fun j _ => by positivity) fun j _ => hℓ i _
    _ = Pm ^ (P.K * P.J) := by
        simp only [prod_const, card_univ, Fintype.card_fin]; rw [← pow_mul, mul_comm]

/-- **A path of nonzero weight forces `d₀ ≤ B₀^{KJ}` and `Y < B₀^K`.** -/
theorem live_params {Pm : ℝ} (hPm1 : 1 ≤ Pm) (hgrp : ∀ i, ∀ p ∈ P.grp i, (p : ℝ) ≤ Pm)
    (hY : 0 < P.Y) {s : St P} (hs : ∀ i j, s.2 i j ∈ P.grp i) {j : ℕ} {c : StepT P}
    (hne : stepNon P j s c.1 ≠ 0) :
    (P.d₀ : ℝ) ≤ Pm ^ (P.K * P.J) ∧ P.Y < Pm ^ P.K := by
  classical
  unfold stepNon at hne
  by_cases hN : NonArch P s c.1
  · rw [if_pos hN] at hne
    obtain ⟨-, -, hD1, -, -⟩ := hN
    refine ⟨?_, ?_⟩
    · refine (Nat.cast_le.2 hD1).trans (padProd_le P hPm1 fun i j => hgrp i _ (hs i _))
    · by_contra hYb
      push Not at hYb
      apply hne
      have hnw : ((∏ i, c.1.2.2 i : ℕ) : ℝ) ≤ Pm ^ P.K := by
        push_cast
        calc ∏ i, (c.1.2.2 i : ℝ) ≤ ∏ _i : Fin P.K, Pm :=
              prod_le_prod (fun i _ => by positivity) fun i _ =>
                hgrp i _ (Fintype.mem_piFinset.1 (step_nw_mem P c) i)
          _ = Pm ^ P.K := by simp
      have hb : dyadicBump (((∏ i, c.1.2.2 i : ℕ) : ℝ) / P.Y) = 0 :=
        dyadicBump_eq_zero (by rw [div_le_one hY]; linarith)
      unfold MemParams.edgeMult
      rw [hb]; simp
  · rw [if_neg hN, mul_zero] at hne
    exact absurd rfl hne

/-- The first step of a path of nonzero weight. -/
lemma stepNon_ne_of_wNon {k : ℕ} {s : St P} {cs : Fin (k + 1) → StepT P}
    (h : wNon P (k + 1) s cs ≠ 0) : stepNon P (P.N - (k + 1)) s (cs 0).1 ≠ 0 := by
  simp only [wNon] at h
  exact left_ne_zero_of_mul h

/-! ## The bounded steps -/

open Classical in
lemma card_bddZ_le (Zb : ℝ) (hZ0 : 0 ≤ Zb) :
    ((P.zSet.filter fun z => BddZ Zb z).card : ℝ) ≤ (2 * Zb + 33) * (2 * Zb + 1) := by
  classical
  obtain ⟨M1, hM1⟩ : ∃ M : ℤ, M = ⌊Zb + 16⌋ := ⟨_, rfl⟩
  obtain ⟨M2, hM2⟩ : ∃ M : ℤ, M = ⌊Zb⌋ := ⟨_, rfl⟩
  have hM1' : (M1 : ℝ) ≤ Zb + 16 := hM1 ▸ Int.floor_le _
  have hM2' : (M2 : ℝ) ≤ Zb := hM2 ▸ Int.floor_le _
  have hM10 : 0 ≤ M1 := hM1 ▸ Int.floor_nonneg.2 (by linarith)
  have hM20 : 0 ≤ M2 := hM2 ▸ Int.floor_nonneg.2 hZ0
  have hsub : (P.zSet.filter fun z => BddZ Zb z) ⊆ Finset.Icc (-M1) M1 ×ˢ Finset.Icc (-M2) M2 := by
    intro z hz
    obtain ⟨-, h2, h1⟩ := mem_filter.1 hz
    obtain ⟨h1a, h1b⟩ := abs_le.1 h1
    obtain ⟨h2a, h2b⟩ := abs_le.1 h2
    refine mem_product.2 ⟨mem_Icc.2 ⟨?_, ?_⟩, mem_Icc.2 ⟨?_, ?_⟩⟩
    · have : (-z.1 : ℤ) ≤ M1 := hM1 ▸ Int.le_floor.2 (by push_cast; linarith)
      linarith
    · exact hM1 ▸ Int.le_floor.2 (by linarith)
    · have : (-z.2 : ℤ) ≤ M2 := hM2 ▸ Int.le_floor.2 (by push_cast; linarith)
      linarith
    · exact hM2 ▸ Int.le_floor.2 (by linarith)
  have hc := card_le_card hsub
  rw [card_product, Int.card_Icc, Int.card_Icc] at hc
  have e1 : ((M1 + 1 - -M1).toNat : ℝ) = 2 * M1 + 1 := by
    have h : ((M1 + 1 - -M1).toNat : ℤ) = 2 * M1 + 1 := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have h' : (((M1 + 1 - -M1).toNat : ℤ) : ℝ) = ((2 * M1 + 1 : ℤ) : ℝ) := by rw [h]
    push_cast at h'
    exact h'
  have e2 : ((M2 + 1 - -M2).toNat : ℝ) = 2 * M2 + 1 := by
    have h : ((M2 + 1 - -M2).toNat : ℤ) = 2 * M2 + 1 := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    have h' : (((M2 + 1 - -M2).toNat : ℤ) : ℝ) = ((2 * M2 + 1 : ℤ) : ℝ) := by rw [h]
    push_cast at h'
    exact h'
  have hc' : ((P.zSet.filter fun z => BddZ Zb z).card : ℝ) ≤
      ((M1 + 1 - -M1).toNat : ℝ) * ((M2 + 1 - -M2).toNat : ℝ) := by exact_mod_cast hc
  rw [e1, e2] at hc'
  have hM10' : (0 : ℝ) ≤ M1 := by exact_mod_cast hM10
  have hM20' : (0 : ℝ) ≤ M2 := by exact_mod_cast hM20
  have h0' : (0 : ℝ) ≤ 2 * M2 + 1 := by linarith
  calc _ ≤ (2 * (M1 : ℝ) + 1) * (2 * M2 + 1) := hc'
    _ ≤ (2 * Zb + 33) * (2 * Zb + 1) := mul_le_mul (by linarith) (by linarith) h0' (by linarith)

open Classical in
/-- **The bounded steps from a state.** -/
theorem step_sum_le (hY : 0 < P.Y) (hd₀ : 0 < P.d₀) {Zb : ℝ} (hZ0 : 0 ≤ Zb) {Cg : ℝ}
    (hCg : 0 ≤ Cg) (hcard : ∀ i, ((P.grp i).card : ℝ) ≤ Cg) {Vb : ℝ}
    (hVb : ∏ i, (P.Vg i)⁻¹ ≤ Vb) (j : ℕ) (s : St P) :
    ∑ c : StepT P, (if BddZ Zb c.1.2.1 then ‖stepNon P j s c.1‖ else 0) ≤
      Vb * ((2 * Zb + 33) * (2 * Zb + 1)) * Cg ^ P.K := by
  set fi : ℝ := (((P.J + 1).factorial ^ P.K : ℕ) : ℝ)⁻¹ with hfi
  have hV : ∀ i, 0 ≤ P.Vg i := Vg_nonneg P
  have hVb0 : 0 ≤ ∏ i, (P.Vg i)⁻¹ := prod_nonneg fun i _ => inv_nonneg.2 (hV i)
  have h1 : ∑ c : StepT P, (if BddZ Zb c.1.2.1 then ‖stepNon P j s c.1‖ else 0) ≤
      ∑ c ∈ stepSet P, (if BddZ Zb c.2.1 then fi * Vb else 0) := by
    rw [← sum_coe_sort (stepSet P)]
    refine sum_le_sum fun c _ => ?_
    split_ifs
    · exact (stepNon_facts P hY hd₀ hV j s c.1).1.trans
        (mul_le_mul_of_nonneg_left hVb (by positivity))
    · exact le_rfl
  have h2 : ∑ c ∈ stepSet P, (if BddZ Zb c.2.1 then fi * Vb else 0) =
      (((P.J + 1).factorial ^ P.K : ℕ) : ℝ) * ((P.zSet.filter fun z => BddZ Zb z).card *
        (((Fintype.piFinset P.grp).card : ℝ) * (fi * Vb))) := by
    unfold stepSet
    rw [sum_product]
    have hin : ∀ pr : Fin P.K → Equiv.Perm (Fin (P.J + 1)),
        ∑ y ∈ P.zSet ×ˢ Fintype.piFinset P.grp,
          (if BddZ Zb ((pr, y) : Stp P).2.1 then fi * Vb else 0) =
        (P.zSet.filter fun z => BddZ Zb z).card *
          (((Fintype.piFinset P.grp).card : ℝ) * (fi * Vb)) := by
      intro pr
      calc ∑ y ∈ P.zSet ×ˢ Fintype.piFinset P.grp,
            (if BddZ Zb ((pr, y) : Stp P).2.1 then fi * Vb else 0)
          = ∑ z ∈ P.zSet, ∑ _nw ∈ Fintype.piFinset P.grp, (if BddZ Zb z then fi * Vb else 0) :=
            sum_product _ _ _
        _ = ∑ z ∈ P.zSet, (if BddZ Zb z then
              ((Fintype.piFinset P.grp).card : ℝ) * (fi * Vb) else 0) := by
            refine sum_congr rfl fun z _ => ?_
            split_ifs <;> simp
        _ = _ := by rw [← sum_filter, sum_const, nsmul_eq_mul]
    rw [sum_congr rfl fun pr _ => hin pr, sum_const, card_univ, Fintype.card_pi, prod_const,
      card_univ, Fintype.card_fin, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hfact : (((P.J + 1).factorial ^ P.K : ℕ) : ℝ) * fi = 1 := by
    rw [hfi]; exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 (by positivity))
  have hpi : ((Fintype.piFinset P.grp).card : ℝ) ≤ Cg ^ P.K := by
    rw [Fintype.card_piFinset]; push_cast
    calc ∏ i, ((P.grp i).card : ℝ) ≤ ∏ _i : Fin P.K, Cg :=
          prod_le_prod (fun i _ => by positivity) fun i _ => hcard i
      _ = Cg ^ P.K := by simp
  have hVb' : 0 ≤ Vb := hVb0.trans hVb
  have hcz := card_bddZ_le P Zb hZ0
  rw [h2] at h1
  refine h1.trans ?_
  calc (((P.J + 1).factorial ^ P.K : ℕ) : ℝ) * ((P.zSet.filter fun z => BddZ Zb z).card *
        (((Fintype.piFinset P.grp).card : ℝ) * (fi * Vb)))
      = ((((P.J + 1).factorial ^ P.K : ℕ) : ℝ) * fi) * (Vb * ((P.zSet.filter fun z => BddZ Zb z).card *
          ((Fintype.piFinset P.grp).card : ℝ))) := by ring
    _ = Vb * ((P.zSet.filter fun z => BddZ Zb z).card * ((Fintype.piFinset P.grp).card : ℝ)) := by
        rw [hfact, one_mul]
    _ ≤ Vb * (((2 * Zb + 33) * (2 * Zb + 1)) * Cg ^ P.K) := by gcongr
    _ = Vb * ((2 * Zb + 33) * (2 * Zb + 1)) * Cg ^ P.K := by ring

end PE

end ArtinPrimitiveRoots.L102E
end

section
/-! # L102E (D7r): the numerics

In the variable `l = L^{1/100}` every size is `exp(poly(l))`: the path weights are
`≤ exp(l^{73})`, the Bonferroni tail is `≤ exp(-l^{76})`, the polynomial errors are
`≤ exp(l^{99}) x^{-η} = exp(l^{99} - η l^{100})`, while the target is `L^{-AN} ≥ exp(-300 A l^{51})`
(`num_main`). -/

namespace ArtinPrimitiveRoots.L102E.Num

open Real

lemma le_exp_self (c : ℝ) : c ≤ exp c := by linarith [add_one_le_exp c]

lemma pow_le_exp (l : ℝ) (hl : 0 ≤ l) (m : ℕ) : l ^ m ≤ exp (m * l) := by
  rw [exp_nat_mul]; exact pow_le_pow_left₀ hl (le_exp_self l) m

lemma absorb4 {l : ℝ} (hl : 1 ≤ l) {a b c d x y z w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hs : a + b + c + d ≤ l) {m : ℕ} (hx : x ≤ l ^ m) (hy : y ≤ l ^ m)
    (hz : z ≤ l ^ m) (hw : w ≤ l ^ m) : a * x + b * y + c * z + d * w ≤ l ^ (m + 1) := by
  have hm : 0 ≤ l ^ m := by positivity
  calc a * x + b * y + c * z + d * w ≤ a * l ^ m + b * l ^ m + c * l ^ m + d * l ^ m := by
        gcongr
    _ = (a + b + c + d) * l ^ m := by ring
    _ ≤ l * l ^ m := mul_le_mul_of_nonneg_right hs hm
    _ = l ^ (m + 1) := by ring

lemma pmono {l : ℝ} (hl : 1 ≤ l) {a b : ℕ} (h : a ≤ b) : l ^ a ≤ l ^ b := pow_le_pow_right₀ hl h

/-- `M^T/T! ≤ e^{-T}` when `9M ≤ T`. -/
lemma pow_div_factorial_le {M : ℝ} (hM : 0 ≤ M) {T : ℕ} (h : 9 * M ≤ T) :
    M ^ T / (T.factorial : ℝ) ≤ exp (-(T : ℝ)) := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 := Real.pow_div_factorial_le_exp (T : ℝ) hT'.le T
  have hf : (0 : ℝ) < T.factorial := by exact_mod_cast T.factorial_pos
  have hM9 : M ≤ T / 9 := by linarith
  have he2 : exp 2 ≤ 9 := by
    have := Real.exp_one_lt_d9
    have h : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
    rw [h]; nlinarith [exp_pos 1]
  have hsplit : exp (T : ℝ) = exp (-(T : ℝ)) * exp 2 ^ T := by
    rw [← exp_nat_mul, ← exp_add]; congr 1; ring
  calc M ^ T / (T.factorial : ℝ) ≤ ((T : ℝ) / 9) ^ T / T.factorial := by gcongr
    _ = (T : ℝ) ^ T / T.factorial / 9 ^ T := by rw [div_pow]; ring
    _ ≤ exp (T : ℝ) / 9 ^ T := by gcongr
    _ = exp (-(T : ℝ)) * (exp 2 ^ T / 9 ^ T) := by rw [hsplit]; ring
    _ ≤ exp (-(T : ℝ)) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le
        rw [div_le_one (by positivity)]
        exact pow_le_pow_left₀ (exp_pos 2).le he2 T
    _ = exp (-(T : ℝ)) := mul_one _

/-- The threshold. -/
noncomputable def l0 (K : ℕ) (A η : ℝ) : ℝ := 200000 + 200 * K + 400 * A + (400 + 400 * A) / η

/-- The hypotheses of the numerics. -/
structure NumHyp (K : ℕ) (A η l : ℝ) (J N T : ℕ) (d₀ Y G S₁ : ℝ) : Prop where
  hA : 0 < A
  hη : 0 < η
  hl : l0 K A η ≤ l
  hJ : (J : ℝ) ≤ l
  hN : (N : ℝ) ≤ l ^ 50 + 2
  hT1 : l ^ 76 ≤ T
  hT2 : (T : ℝ) ≤ l ^ 76 + 1
  hd0 : 0 ≤ d₀
  hd : d₀ ≤ exp (2 * l ^ 20) ^ (K * J)
  hY1 : 1 ≤ Y
  hY : Y ≤ exp (2 * l ^ 20) ^ K
  hG0 : 0 ≤ G
  hG : G ≤ K * (exp (2 * l ^ 20) + 1)
  hS0 : 0 ≤ S₁
  hS : S₁ ≤ K * (2 + 2 * l ^ 20)

section
variable {K : ℕ} {A η l : ℝ} {J N T : ℕ} {d₀ Y G S₁ : ℝ}

lemma NumHyp.l1 (H : NumHyp K A η l J N T d₀ Y G S₁) : 1 ≤ l := by
  have := H.hl; unfold l0 at this
  have : 0 ≤ (400 + 400 * A) / η := div_nonneg (by linarith [H.hA]) H.hη.le
  have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith [H.hA]

lemma NumHyp.lK (H : NumHyp K A η l J N T d₀ Y G S₁) : 200000 + 200 * (K : ℝ) + 400 * A ≤ l := by
  have := H.hl; unfold l0 at this
  have : 0 ≤ (400 + 400 * A) / η := div_nonneg (by linarith [H.hA]) H.hη.le
  linarith

lemma NumHyp.lη (H : NumHyp K A η l J N T d₀ Y G S₁) : 400 + 400 * A ≤ η * l := by
  have h := H.hl; unfold l0 at h
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h2 : (400 + 400 * A) / η ≤ l := by linarith [H.hA]
  have := (div_le_iff₀ H.hη).1 h2; linarith

lemma NumHyp.one_le (H : NumHyp K A η l J N T d₀ Y G S₁) (a : ℕ) : 1 ≤ l ^ a :=
  one_le_pow₀ H.l1

lemma NumHyp.p (H : NumHyp K A η l J N T d₀ Y G S₁) {a b : ℕ} (h : a ≤ b) : l ^ a ≤ l ^ b :=
  pmono H.l1 h

lemma NumHyp.lpow (H : NumHyp K A η l J N T d₀ Y G S₁) {b : ℕ} (h : 1 ≤ b) : l ≤ l ^ b := by
  simpa using H.p h

lemma NumHyp.Pmpow (n : ℕ) : exp (2 * l ^ 20) ^ n = exp (n * (2 * l ^ 20)) :=
  (exp_nat_mul _ n).symm

lemma NumHyp.Cg (H : NumHyp K A η l J N T d₀ Y G S₁) :
    exp (2 * l ^ 20) + 1 ≤ exp (1 + 2 * l ^ 20) := by
  rw [exp_add]
  have : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hP1 : 1 ≤ exp (2 * l ^ 20) := one_le_exp (by have := H.l1; positivity)
  nlinarith

lemma NumHyp.Cgpow (H : NumHyp K A η l J N T d₀ Y G S₁) (n : ℕ) :
    (exp (2 * l ^ 20) + 1) ^ n ≤ exp (n * (1 + 2 * l ^ 20)) := by
  rw [exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) H.Cg n

lemma NumHyp.dY (H : NumHyp K A η l J N T d₀ Y G S₁) : d₀ * Y ≤ exp (4 * K * l ^ 21) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : d₀ ≤ exp (2 * K * l ^ 21) := by
    refine H.hd.trans ?_
    rw [NumHyp.Pmpow]; push_cast
    apply exp_le_exp.2
    have e : (K : ℝ) * J * (2 * l ^ 20) ≤ (K : ℝ) * l * (2 * l ^ 20) := by
      have : (K : ℝ) * J ≤ K * l := mul_le_mul_of_nonneg_left H.hJ hK0
      exact mul_le_mul_of_nonneg_right this (by positivity)
    calc (K : ℝ) * J * (2 * l ^ 20) ≤ (K : ℝ) * l * (2 * l ^ 20) := e
      _ = 2 * K * l ^ 21 := by ring
  have h2 : Y ≤ exp (2 * K * l ^ 21) := by
    refine H.hY.trans ?_
    rw [NumHyp.Pmpow]
    apply exp_le_exp.2
    have := H.p (show 20 ≤ 21 by norm_num)
    have : (K : ℝ) * (2 * l ^ 20) ≤ K * (2 * l ^ 21) := by gcongr
    linarith
  calc d₀ * Y ≤ exp (2 * K * l ^ 21) * exp (2 * K * l ^ 21) :=
        mul_le_mul h1 h2 (by linarith [H.hY1]) (exp_pos _).le
    _ = exp (4 * K * l ^ 21) := by rw [← exp_add]; ring_nf

lemma NumHyp.N3 (H : NumHyp K A η l J N T d₀ Y G S₁) : (N : ℝ) ≤ 3 * l ^ 50 := by
  have := H.one_le 50; linarith [H.hN]

lemma NumHyp.Zb (H : NumHyp K A η l J N T d₀ Y G S₁) :
    4096 * (N : ℝ) * (10 * d₀ * Y) ≤ exp (l ^ 22) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hl50 := pow_le_exp l hl0 50
  have hdY0 : 0 ≤ d₀ * Y := mul_nonneg H.hd0 (by linarith [H.hY1])
  calc 4096 * (N : ℝ) * (10 * d₀ * Y) = 40960 * N * (d₀ * Y) := by ring
    _ ≤ 40960 * (3 * l ^ 50) * exp (4 * K * l ^ 21) := by
        have := H.N3; have := H.dY
        gcongr
    _ = 122880 * l ^ 50 * exp (4 * K * l ^ 21) := by ring
    _ ≤ exp 122880 * exp ((50 : ℕ) * l) * exp (4 * K * l ^ 21) := by
        gcongr
        exact le_exp_self _
    _ = exp (122880 * 1 + 50 * l + 4 * K * l ^ 21 + 0 * 0) := by
        rw [← exp_add, ← exp_add]; push_cast; ring_nf
    _ ≤ exp (l ^ 22) := by
        apply exp_le_exp.2
        exact absorb4 H.l1 (by norm_num) (by norm_num) (by positivity) le_rfl
          (by linarith [H.lK, H.hA]) (H.one_le 21) (H.lpow (by norm_num)) le_rfl (by positivity)

/-- The weights of the bounded paths. -/
theorem num_W (H : NumHyp K A η l J N T d₀ Y G S₁) :
    exp (2 * l ^ 20) ^ (K * (J + 1)) * (exp (2 * l ^ 20) + 1) ^ (K * (J + 1)) *
        (exp (2 * l ^ 20) ^ K * ((2 * (4096 * N * (10 * d₀ * Y)) + 33) *
          (2 * (4096 * N * (10 * d₀ * Y)) + 1)) * (exp (2 * l ^ 20) + 1) ^ K) ^ N ≤
        exp (l ^ 73) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  set M0 := exp (l ^ 22) with hM0
  have hM01 : 1 ≤ M0 := one_le_exp (by positivity)
  have hZb := H.Zb
  have hZb0 : 0 ≤ 4096 * (N : ℝ) * (10 * d₀ * Y) := by
    have := H.hd0; have := H.hY1; positivity
  set Zb := 4096 * (N : ℝ) * (10 * d₀ * Y) with hZbdef
  have hβ : exp (2 * l ^ 20) ^ K * ((2 * Zb + 33) * (2 * Zb + 1)) * (exp (2 * l ^ 20) + 1) ^ K ≤
      exp (3 * l ^ 22) := by
    have e1 : (2 * Zb + 33) * (2 * Zb + 1) ≤ exp 1225 * M0 ^ 2 := by
      have h1 : 2 * Zb + 33 ≤ 35 * M0 := by linarith
      have h2 : 2 * Zb + 1 ≤ 35 * M0 := by linarith
      calc (2 * Zb + 33) * (2 * Zb + 1) ≤ (35 * M0) * (35 * M0) :=
            mul_le_mul h1 h2 (by linarith) (by positivity)
        _ = 1225 * M0 ^ 2 := by ring
        _ ≤ exp 1225 * M0 ^ 2 := by gcongr; exact le_exp_self _
    calc exp (2 * l ^ 20) ^ K * ((2 * Zb + 33) * (2 * Zb + 1)) * (exp (2 * l ^ 20) + 1) ^ K
        ≤ exp (K * (2 * l ^ 20)) * (exp 1225 * M0 ^ 2) * exp (K * (1 + 2 * l ^ 20)) := by
          rw [NumHyp.Pmpow]; gcongr; exact H.Cgpow K
      _ = exp (K * 1 + 4 * K * l ^ 20 + 1225 * 1 + 0 * 0 + 2 * l ^ 22) := by
          rw [hM0, ← exp_nat_mul, ← exp_add, ← exp_add, ← exp_add]; push_cast; ring_nf
      _ ≤ exp (3 * l ^ 22) := by
          apply exp_le_exp.2
          have : (K : ℝ) * 1 + 4 * K * l ^ 20 + 1225 * 1 + 0 * 0 ≤ l ^ 21 :=
            absorb4 H.l1 (a := K) (b := 4 * K) (c := 1225) (d := 0) (x := 1) (y := l ^ 20)
            (z := 1) (w := 0) (m := 20) (by positivity) (by positivity) (by norm_num) le_rfl
            (by linarith [H.lK, H.hA]) (H.one_le 20) le_rfl (H.one_le 20) (by positivity)
          have h2 : l ^ 21 ≤ l ^ 22 := H.p (by norm_num)
          linarith
  have hβN : (exp (2 * l ^ 20) ^ K * ((2 * Zb + 33) * (2 * Zb + 1)) *
      (exp (2 * l ^ 20) + 1) ^ K) ^ N ≤ exp (9 * l ^ 72) := by
    calc (exp (2 * l ^ 20) ^ K * ((2 * Zb + 33) * (2 * Zb + 1)) * (exp (2 * l ^ 20) + 1) ^ K) ^ N
        ≤ exp (3 * l ^ 22) ^ N := pow_le_pow_left₀ (by positivity) hβ N
      _ = exp (N * (3 * l ^ 22)) := (exp_nat_mul _ N).symm
      _ ≤ exp (9 * l ^ 72) := by
          apply exp_le_exp.2
          have : (N : ℝ) * (3 * l ^ 22) ≤ 3 * l ^ 50 * (3 * l ^ 22) :=
            mul_le_mul_of_nonneg_right H.N3 (by positivity)
          calc (N : ℝ) * (3 * l ^ 22) ≤ 3 * l ^ 50 * (3 * l ^ 22) := this
            _ = 9 * l ^ 72 := by ring
  have hσ : exp (2 * l ^ 20) ^ (K * (J + 1)) * (exp (2 * l ^ 20) + 1) ^ (K * (J + 1)) ≤
      exp (10 * K * l ^ 21) := by
    have hKJ : ((K * (J + 1) : ℕ) : ℝ) ≤ 2 * K * l := by
      push_cast
      have : (J : ℝ) + 1 ≤ 2 * l := by linarith [H.hJ, H.l1]
      calc (K : ℝ) * (J + 1) ≤ K * (2 * l) := mul_le_mul_of_nonneg_left this hK0
        _ = 2 * K * l := by ring
    calc exp (2 * l ^ 20) ^ (K * (J + 1)) * (exp (2 * l ^ 20) + 1) ^ (K * (J + 1)) ≤
          exp (((K * (J + 1) : ℕ) : ℝ) * (2 * l ^ 20)) *
            exp (((K * (J + 1) : ℕ) : ℝ) * (1 + 2 * l ^ 20)) := by
          rw [NumHyp.Pmpow]; gcongr; exact H.Cgpow _
      _ = exp (((K * (J + 1) : ℕ) : ℝ) * (1 + 4 * l ^ 20)) := by rw [← exp_add]; ring_nf
      _ ≤ exp (10 * K * l ^ 21) := by
          apply exp_le_exp.2
          have h1 : ((K * (J + 1) : ℕ) : ℝ) * (1 + 4 * l ^ 20) ≤ 2 * K * l * (1 + 4 * l ^ 20) :=
            mul_le_mul_of_nonneg_right hKJ (by positivity)
          have h2 : 1 ≤ l ^ 20 := H.one_le 20
          have h3 : 2 * (K : ℝ) * l * 1 ≤ 2 * K * l * l ^ 20 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          calc ((K * (J + 1) : ℕ) : ℝ) * (1 + 4 * l ^ 20) ≤ 2 * K * l * (1 + 4 * l ^ 20) := h1
            _ = 2 * K * l * 1 + 8 * (K * (l * l ^ 20)) := by ring
            _ ≤ 2 * K * l * l ^ 20 + 8 * (K * (l * l ^ 20)) := by linarith
            _ = 10 * K * l ^ 21 := by ring
  calc exp (2 * l ^ 20) ^ (K * (J + 1)) * (exp (2 * l ^ 20) + 1) ^ (K * (J + 1)) *
        (exp (2 * l ^ 20) ^ K * ((2 * Zb + 33) * (2 * Zb + 1)) * (exp (2 * l ^ 20) + 1) ^ K) ^ N
      ≤ exp (10 * K * l ^ 21) * exp (9 * l ^ 72) := by gcongr
    _ = exp (10 * K * l ^ 21 + 9 * l ^ 72 + 0 * 0 + 0 * 0) := by rw [← exp_add]; ring_nf
    _ ≤ exp (l ^ 73) := by
        apply exp_le_exp.2
        exact absorb4 H.l1 (by positivity) (by norm_num) le_rfl le_rfl
          (by linarith [H.lK, H.hA]) (H.p (by norm_num)) le_rfl (by positivity) (by positivity)

/-- The Bonferroni tail. -/
theorem num_tail (H : NumHyp K A η l J N T d₀ Y G S₁) :
    ((N + 1 : ℝ) * S₁) ^ T / (T.factorial : ℝ) ≤ exp (-(l ^ 76)) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hM : (N + 1 : ℝ) * S₁ ≤ 16 * K * l ^ 70 := by
    have h1 : (N + 1 : ℝ) ≤ 4 * l ^ 50 := by have := H.one_le 50; linarith [H.hN]
    have h2 : S₁ ≤ 4 * K * l ^ 20 := by
      have := H.one_le 20
      have : (K : ℝ) * 2 ≤ K * (2 * l ^ 20) := mul_le_mul_of_nonneg_left (by linarith) hK0
      linarith [H.hS]
    calc (N + 1 : ℝ) * S₁ ≤ 4 * l ^ 50 * (4 * K * l ^ 20) :=
          mul_le_mul h1 h2 H.hS0 (by positivity)
      _ = 16 * K * l ^ 70 := by ring
  have h9 : 9 * ((N + 1 : ℝ) * S₁) ≤ T := by
    have : 144 * (K : ℝ) * l ^ 70 ≤ l ^ 76 := by
      have h6 : l ≤ l ^ 6 := H.lpow (by norm_num)
      have : 144 * (K : ℝ) ≤ l := by linarith [H.lK, H.hA]
      calc 144 * (K : ℝ) * l ^ 70 ≤ l ^ 6 * l ^ 70 :=
            mul_le_mul_of_nonneg_right (this.trans h6) (by positivity)
        _ = l ^ 76 := by ring
    linarith [H.hT1]
  refine (pow_div_factorial_le (mul_nonneg (by positivity) H.hS0) h9).trans ?_
  exact exp_le_exp.2 (by linarith [H.hT1])

lemma NumHyp.Y02 (H : NumHyp K A η l J N T d₀ Y G S₁) : Y ^ (0.2 : ℝ) ≤ exp (2 * K * l ^ 20) := by
  have h1 : Y ^ (0.2 : ℝ) ≤ Y := by
    calc Y ^ (0.2 : ℝ) ≤ Y ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le H.hY1 (by norm_num)
      _ = Y := rpow_one Y
  refine h1.trans (H.hY.trans (le_of_eq ?_))
  rw [NumHyp.Pmpow]; ring_nf

lemma NumHyp.Mpow (H : NumHyp K A η l J N T d₀ Y G S₁) (n : ℕ) :
    ((J + 1 : ℕ) : ℝ) ^ n ≤ exp (n * (2 * l)) := by
  have hM : ((J + 1 : ℕ) : ℝ) ≤ 2 * l := by push_cast; linarith [H.hJ, H.l1]
  rw [exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) (hM.trans (le_exp_self _)) n

lemma NumHyp.Tcb (H : NumHyp K A η l J N T d₀ Y G S₁) :
    ((J + 1 : ℕ) : ℝ) ^ K * Y ^ (0.2 : ℝ) +
      2 ^ K * (((J + 1 : ℕ) : ℝ) ^ (2 * K) * (exp (2 * l ^ 20) + 1) ^ (3 * K)) ≤ exp (l ^ 22) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hY0 : 0 ≤ Y ^ (0.2 : ℝ) := by have := H.hY1; positivity
  have h2K : (2 : ℝ) ^ K ≤ exp K := by
    rw [← exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [add_one_le_exp (1 : ℝ)]) K
  have t1 : ((J + 1 : ℕ) : ℝ) ^ K * Y ^ (0.2 : ℝ) ≤ exp (K * (2 * l) + 2 * K * l ^ 20) := by
    rw [exp_add]; exact mul_le_mul (H.Mpow K) H.Y02 hY0 (exp_pos _).le
  have t2 : 2 ^ K * (((J + 1 : ℕ) : ℝ) ^ (2 * K) * (exp (2 * l ^ 20) + 1) ^ (3 * K)) ≤
      exp (K + (((2 * K : ℕ) : ℝ) * (2 * l) + ((3 * K : ℕ) : ℝ) * (1 + 2 * l ^ 20))) := by
    rw [exp_add, exp_add]
    exact mul_le_mul h2K (mul_le_mul (H.Mpow _) (H.Cgpow _) (by positivity) (exp_pos _).le)
      (by positivity) (exp_pos _).le
  have e1 : (K : ℝ) * (2 * l) + 2 * K * l ^ 20 ≤ l ^ 22 - 1 := by
    have h : 2 * (K : ℝ) * l + 2 * K * l ^ 20 + 1 * 1 + 0 * 0 ≤ l ^ 21 :=
      absorb4 H.l1 (by positivity) (by positivity) (by norm_num) le_rfl
        (by linarith [H.lK, H.hA]) (H.lpow (by norm_num)) (H.p (by norm_num)) (H.one_le 20)
        (by positivity)
    have := H.p (show 21 ≤ 22 by norm_num)
    linarith
  have e2 : (K : ℝ) + (((2 * K : ℕ) : ℝ) * (2 * l) + ((3 * K : ℕ) : ℝ) * (1 + 2 * l ^ 20)) ≤
      l ^ 22 - 1 := by
    push_cast
    have h : (4 * K + 2 : ℝ) * 1 + 4 * K * l + 6 * K * l ^ 20 + 0 * 0 ≤ l ^ 21 :=
      absorb4 H.l1 (by positivity) (by positivity) (by positivity) le_rfl
        (by linarith [H.lK, H.hA]) (H.one_le 20) (H.lpow (by norm_num)) (H.p (by norm_num))
        (by positivity)
    have := H.p (show 21 ≤ 22 by norm_num)
    linarith
  have h2 : exp (l ^ 22 - 1) * 2 ≤ exp (l ^ 22) := by
    have : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
    calc exp (l ^ 22 - 1) * 2 ≤ exp (l ^ 22 - 1) * exp 1 :=
          mul_le_mul_of_nonneg_left this (exp_pos _).le
      _ = exp (l ^ 22) := by rw [← exp_add]; ring_nf
  have := add_le_add (t1.trans (exp_le_exp.2 e1)) (t2.trans (exp_le_exp.2 e2))
  linarith

lemma NumHyp.Mtb (H : NumHyp K A η l J N T d₀ Y G S₁) :
    (Y ^ (0.2 : ℝ) + 2) * exp (2 * l ^ 20) ^ (K * (J + 1) + 2 * K) ≤ exp (l ^ 22) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : Y ^ (0.2 : ℝ) + 2 ≤ exp (2 + 2 * K * l ^ 20) := by
    rw [exp_add]
    have : (3 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
    have hY' := H.Y02
    have : 1 ≤ exp (2 * K * l ^ 20) := one_le_exp (by positivity)
    nlinarith
  have hKJ : ((K * (J + 1) + 2 * K : ℕ) : ℝ) ≤ 4 * K * l := by
    push_cast
    have : (J : ℝ) + 3 ≤ 4 * l := by linarith [H.hJ, H.l1]
    calc (K : ℝ) * (J + 1) + 2 * K = K * (J + 3) := by ring
      _ ≤ K * (4 * l) := mul_le_mul_of_nonneg_left this hK0
      _ = 4 * K * l := by ring
  calc (Y ^ (0.2 : ℝ) + 2) * exp (2 * l ^ 20) ^ (K * (J + 1) + 2 * K)
      ≤ exp (2 + 2 * K * l ^ 20) * exp (((K * (J + 1) + 2 * K : ℕ) : ℝ) * (2 * l ^ 20)) := by
        rw [NumHyp.Pmpow]; gcongr
    _ = exp (2 + 2 * K * l ^ 20 + ((K * (J + 1) + 2 * K : ℕ) : ℝ) * (2 * l ^ 20)) := by
        rw [← exp_add]
    _ ≤ exp (l ^ 22) := by
        apply exp_le_exp.2
        have h3 : ((K * (J + 1) + 2 * K : ℕ) : ℝ) * (2 * l ^ 20) ≤ 4 * K * l * (2 * l ^ 20) :=
          mul_le_mul_of_nonneg_right hKJ (by positivity)
        have h4 : (2 : ℝ) * 1 + 2 * K * l ^ 20 + 8 * K * l ^ 21 + 0 * 0 ≤ l ^ 22 :=
          absorb4 H.l1 (by norm_num) (by positivity) (by positivity) le_rfl
            (by linarith [H.lK, H.hA]) (H.one_le 21) (H.p (by norm_num)) le_rfl (by positivity)
        have h5 : 4 * (K : ℝ) * l * (2 * l ^ 20) = 8 * K * l ^ 21 := by ring
        linarith

lemma NumHyp.big (H : NumHyp K A η l J N T d₀ Y G S₁) : (32780 : ℝ) ≤ exp (l ^ 22) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  calc (32780 : ℝ) ≤ l ^ 22 := by
        have : (32780 : ℝ) ≤ l := by linarith [H.lK, H.hA, (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
        exact this.trans (H.lpow (by norm_num))
    _ ≤ exp (l ^ 22) := le_exp_self _

lemma NumHyp.NM (H : NumHyp K A η l J N T d₀ Y G S₁) : (N : ℝ) ≤ exp (l ^ 22) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  refine H.N3.trans ?_
  calc 3 * l ^ 50 ≤ exp 3 * exp ((50 : ℕ) * l) :=
        mul_le_mul (le_exp_self 3) (pow_le_exp l hl0 50) (by positivity) (exp_pos _).le
    _ = exp (3 * 1 + 50 * l + 0 * 0 + 0 * 0) := by rw [← exp_add]; push_cast; ring_nf
    _ ≤ exp (l ^ 22) := by
        apply exp_le_exp.2
        have h : (3 : ℝ) * 1 + 50 * l + 0 * 0 + 0 * 0 ≤ l ^ 21 :=
          absorb4 H.l1 (by norm_num) (by norm_num) le_rfl le_rfl
            (by linarith [H.lK, H.hA, (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]) (H.one_le 20)
            (H.lpow (by norm_num)) (by positivity) (by positivity)
        have := H.p (show 21 ≤ 22 by norm_num)
        linarith

lemma NumHyp.G1 (H : NumHyp K A η l J N T d₀ Y G S₁) : (G + 1) ^ T ≤ exp (2 * l ^ 98) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : G + 1 ≤ exp (l ^ 22) := by
    have : G + 1 ≤ (K + 1) * (exp (2 * l ^ 20) + 1) := by
      have : 1 ≤ exp (2 * l ^ 20) + 1 := by have := exp_pos (2 * l ^ 20); linarith
      nlinarith [H.hG]
    refine this.trans ?_
    calc ((K : ℝ) + 1) * (exp (2 * l ^ 20) + 1) ≤ exp K * exp (1 + 2 * l ^ 20) :=
          mul_le_mul (by linarith [add_one_le_exp (K : ℝ)]) H.Cg (by positivity) (exp_pos _).le
      _ = exp (K * 1 + 1 * 1 + 2 * l ^ 20 + 0 * 0) := by rw [← exp_add]; ring_nf
      _ ≤ exp (l ^ 22) := by
          apply exp_le_exp.2
          have h : (K : ℝ) * 1 + 1 * 1 + 2 * l ^ 20 + 0 * 0 ≤ l ^ 21 :=
            absorb4 H.l1 (by positivity) (by norm_num) (by norm_num) le_rfl
              (by linarith [H.lK, H.hA]) (H.one_le 20) (H.one_le 20) le_rfl (by positivity)
          have := H.p (show 21 ≤ 22 by norm_num)
          linarith
  calc (G + 1) ^ T ≤ exp (l ^ 22) ^ T := pow_le_pow_left₀ (by linarith [H.hG0]) h1 T
    _ = exp (T * l ^ 22) := (exp_nat_mul _ T).symm
    _ ≤ exp (2 * l ^ 98) := by
        apply exp_le_exp.2
        have : (T : ℝ) * l ^ 22 ≤ (2 * l ^ 76) * l ^ 22 :=
          mul_le_mul_of_nonneg_right (by have := H.one_le 76; linarith [H.hT2]) (by positivity)
        calc (T : ℝ) * l ^ 22 ≤ (2 * l ^ 76) * l ^ 22 := this
          _ = 2 * l ^ 98 := by ring

/-- The polynomial errors. -/
theorem num_Q (H : NumHyp K A η l J N T d₀ Y G S₁) :
    2 * (G + 1) ^ T * exp (l ^ 98) ^ 3 + 4 * exp (l ^ 98) ^ 3 +
        12000 * (4096 * N * (10 * d₀ * Y)) +
        60 * N * (4 * (((J + 1 : ℕ) : ℝ) ^ K * Y ^ (0.2 : ℝ) +
          2 ^ K * (((J + 1 : ℕ) : ℝ) ^ (2 * K) * (exp (2 * l ^ 20) + 1) ^ (3 * K))) *
          (2 * (4096 * ((Y ^ (0.2 : ℝ) + 2) * exp (2 * l ^ 20) ^ (K * (J + 1) + 2 * K)) + 1) + 1)) +
        2 * N * (4 * (((J + 1 : ℕ) : ℝ) ^ K * Y ^ (0.2 : ℝ) +
          2 ^ K * (((J + 1 : ℕ) : ℝ) ^ (2 * K) * (exp (2 * l ^ 20) + 1) ^ (3 * K))) *
          (2 * (4096 * ((Y ^ (0.2 : ℝ) + 2) * exp (2 * l ^ 20) ^ (K * (J + 1) + 2 * K)) + 1) + 1)) *
          exp (l ^ 98) ^ 3 ≤ exp (l ^ 99) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  set M0 := exp (l ^ 22) with hM0
  have hM01 : 1 ≤ M0 := one_le_exp (by positivity)
  have hY1 := H.hY1
  have hY0 : 0 ≤ Y ^ (0.2 : ℝ) := by positivity
  set Bq := 4 * (((J + 1 : ℕ) : ℝ) ^ K * Y ^ (0.2 : ℝ) +
      2 ^ K * (((J + 1 : ℕ) : ℝ) ^ (2 * K) * (exp (2 * l ^ 20) + 1) ^ (3 * K))) *
      (2 * (4096 * ((Y ^ (0.2 : ℝ) + 2) * exp (2 * l ^ 20) ^ (K * (J + 1) + 2 * K)) + 1) + 1)
    with hBq
  have hB0 : 0 ≤ Bq := by rw [hBq]; positivity
  have hBq' : Bq ≤ M0 ^ 3 := by
    have hT := H.Tcb
    have hMt := H.Mtb
    have hbig := H.big
    have h0' : 0 ≤ (Y ^ (0.2 : ℝ) + 2) * exp (2 * l ^ 20) ^ (K * (J + 1) + 2 * K) := by positivity
    calc Bq ≤ 4 * M0 * (2 * (4096 * M0 + 1) + 1) := by rw [hBq]; gcongr
      _ ≤ 4 * M0 * (8195 * M0) := by gcongr; linarith
      _ = 32780 * M0 * M0 := by ring
      _ ≤ M0 * M0 * M0 := by gcongr
      _ = M0 ^ 3 := by ring
  have he3 : exp (l ^ 98) ^ 3 = exp (3 * l ^ 98) := by rw [← exp_nat_mul]; push_cast; ring_nf
  have hM04 : M0 ^ 4 ≤ exp (l ^ 98) := by
    rw [hM0, ← exp_nat_mul]
    apply exp_le_exp.2
    push_cast
    have : (4 : ℝ) ≤ l := by linarith [H.lK, H.hA]
    calc (4 : ℝ) * l ^ 22 ≤ l * l ^ 22 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = l ^ 23 := by ring
      _ ≤ l ^ 98 := H.p (by norm_num)
  set E5 := exp (5 * l ^ 98) with hE5
  have h98 := H.one_le 98
  have hE3 : exp (3 * l ^ 98) ≤ E5 := exp_le_exp.2 (by linarith)
  have hE1 : exp (l ^ 98) ≤ E5 := exp_le_exp.2 (by linarith)
  have hNB : (N : ℝ) * Bq ≤ exp (l ^ 98) := by
    calc (N : ℝ) * Bq ≤ M0 * M0 ^ 3 := mul_le_mul H.NM hBq' hB0 (by positivity)
      _ = M0 ^ 4 := by ring
      _ ≤ exp (l ^ 98) := hM04
  have hM0E : M0 ≤ E5 := by
    have : M0 ≤ M0 ^ 4 := by
      calc M0 = M0 ^ 1 := (pow_one _).symm
        _ ≤ M0 ^ 4 := pow_le_pow_right₀ hM01 (by norm_num)
    linarith
  have t1 : 2 * (G + 1) ^ T * exp (l ^ 98) ^ 3 ≤ 2 * E5 := by
    rw [he3, mul_assoc]
    have : (G + 1) ^ T * exp (3 * l ^ 98) ≤ E5 := by
      calc (G + 1) ^ T * exp (3 * l ^ 98) ≤ exp (2 * l ^ 98) * exp (3 * l ^ 98) :=
            mul_le_mul_of_nonneg_right H.G1 (exp_pos _).le
        _ = E5 := by rw [hE5, ← exp_add]; ring_nf
    linarith
  have t2 : 4 * exp (l ^ 98) ^ 3 ≤ 4 * E5 := by rw [he3]; linarith
  have t3 : 12000 * (4096 * N * (10 * d₀ * Y)) ≤ 12000 * E5 := by linarith [H.Zb]
  have t4 : 60 * (N : ℝ) * Bq ≤ 60 * E5 := by nlinarith
  have t5 : 2 * (N : ℝ) * Bq * exp (l ^ 98) ^ 3 ≤ 2 * E5 := by
    rw [he3]
    have : (N : ℝ) * Bq * exp (3 * l ^ 98) ≤ E5 := by
      calc (N : ℝ) * Bq * exp (3 * l ^ 98) ≤ exp (l ^ 98) * exp (3 * l ^ 98) :=
            mul_le_mul_of_nonneg_right hNB (exp_pos _).le
        _ = exp (4 * l ^ 98) := by rw [← exp_add]; ring_nf
        _ ≤ E5 := exp_le_exp.2 (by linarith)
    linarith
  have hsum : 2 * E5 + 4 * E5 + 12000 * E5 + 60 * E5 + 2 * E5 ≤ exp (l ^ 99) := by
    calc 2 * E5 + 4 * E5 + 12000 * E5 + 60 * E5 + 2 * E5 = 12068 * E5 := by ring
      _ ≤ exp 12068 * E5 := by gcongr; exact le_exp_self _
      _ = exp (12068 * 1 + 5 * l ^ 98 + 0 * 0 + 0 * 0) := by rw [hE5, ← exp_add]; ring_nf
      _ ≤ exp (l ^ 99) := by
          apply exp_le_exp.2
          exact absorb4 H.l1 (by norm_num) (by norm_num) le_rfl le_rfl
            (by linarith [H.lK, H.hA]) (H.one_le 98) le_rfl (by positivity) (by positivity)
  have e : 2 * (N : ℝ) * Bq * exp (l ^ 98) ^ 3 = 2 * N * Bq * exp (l ^ 98) ^ 3 := rfl
  linarith

/-- The final comparison. -/
theorem num_fin (H : NumHyp K A η l J N T d₀ Y G S₁) :
    exp (l ^ 73) * (30 * exp (-(l ^ 76)) + exp (l ^ 99) * exp (-(η * l ^ 100))) ≤
      exp (-(A * (l ^ 50 + 2) * (100 * l))) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have hA := H.hA
  have hAl : A * (l ^ 50 + 2) * (100 * l) ≤ 300 * A * l ^ 51 := by
    have : l ^ 50 + 2 ≤ 3 * l ^ 50 := by have := H.one_le 50; linarith
    calc A * (l ^ 50 + 2) * (100 * l) ≤ A * (3 * l ^ 50) * (100 * l) := by gcongr
      _ = 300 * A * l ^ 51 := by ring
  have f1 : exp (l ^ 73) * (30 * exp (-(l ^ 76))) * 2 ≤ exp (-(A * (l ^ 50 + 2) * (100 * l))) := by
    calc exp (l ^ 73) * (30 * exp (-(l ^ 76))) * 2 = 60 * exp (l ^ 73 - l ^ 76) := by
          rw [sub_eq_add_neg, exp_add]; ring
      _ ≤ exp 60 * exp (l ^ 73 - l ^ 76) := by gcongr; exact le_exp_self _
      _ = exp (60 + l ^ 73 - l ^ 76) := by rw [← exp_add]; ring_nf
      _ ≤ exp (-(A * (l ^ 50 + 2) * (100 * l))) := by
          apply exp_le_exp.2
          have h : (60 : ℝ) * 1 + 1 * l ^ 73 + 300 * A * l ^ 51 + 0 * 0 ≤ l ^ 76 :=
            absorb4 H.l1 (by norm_num) (by norm_num) (by positivity) le_rfl
              (by linarith [H.lK, (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]) (H.one_le 75)
              (H.p (by norm_num)) (H.p (by norm_num)) (by positivity)
          linarith
  have f2 : exp (l ^ 73) * (exp (l ^ 99) * exp (-(η * l ^ 100))) * 2 ≤
      exp (-(A * (l ^ 50 + 2) * (100 * l))) := by
    have hηl := H.lη
    calc exp (l ^ 73) * (exp (l ^ 99) * exp (-(η * l ^ 100))) * 2
        ≤ exp (l ^ 73) * (exp (l ^ 99) * exp (-(η * l ^ 100))) * exp 2 := by
          gcongr; linarith [add_one_le_exp (2 : ℝ)]
      _ = exp (2 + l ^ 73 + l ^ 99 - η * l ^ 100) := by
          rw [← exp_add, ← exp_add, ← exp_add]; ring_nf
      _ ≤ exp (-(A * (l ^ 50 + 2) * (100 * l))) := by
          apply exp_le_exp.2
          have h1 : (2 : ℝ) * 1 + 1 * l ^ 73 + 1 * l ^ 99 + 300 * A * l ^ 51 ≤ (4 + 300 * A) * l ^ 99 := by
            have a1 := H.one_le 99
            have a2 : l ^ 73 ≤ l ^ 99 := H.p (by norm_num)
            have a3 : l ^ 51 ≤ l ^ 99 := H.p (by norm_num)
            have a4 : 300 * A * l ^ 51 ≤ 300 * A * l ^ 99 := by gcongr
            nlinarith
          have h2 : (4 + 300 * A) * l ^ 99 ≤ η * l ^ 100 := by
            calc (4 + 300 * A) * l ^ 99 ≤ η * l * l ^ 99 :=
                  mul_le_mul_of_nonneg_right (by linarith) (by positivity)
              _ = η * l ^ 100 := by ring
          linarith
  rw [mul_add]
  linarith

/-- The moduli of the Bonferroni terms are admissible for Lemma 3.3. -/
theorem num_PT (H : NumHyp K A η l J N T d₀ Y G S₁) :
    exp (2 * l ^ 20) ^ ((N + 1) * (K * (J + 1)) + T) ≤ exp (l ^ 98) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [NumHyp.Pmpow]
  apply exp_le_exp.2
  push_cast
  have h1 : (N : ℝ) + 1 ≤ 4 * l ^ 50 := by have := H.one_le 50; linarith [H.hN]
  have h2 : (J : ℝ) + 1 ≤ 2 * l := by linarith [H.hJ, H.l1]
  have h3 : (T : ℝ) ≤ 2 * l ^ 76 := by have := H.one_le 76; linarith [H.hT2]
  have h4 : ((N : ℝ) + 1) * (K * (J + 1)) ≤ 4 * l ^ 50 * (K * (2 * l)) := by
    have : (K : ℝ) * (J + 1) ≤ K * (2 * l) := mul_le_mul_of_nonneg_left h2 hK0
    exact mul_le_mul h1 this (by positivity) (by positivity)
  have h5 : 4 * l ^ 50 * (K * (2 * l)) = 8 * K * l ^ 51 := by ring
  have h6 : (8 * K : ℝ) * l ^ 51 + 2 * l ^ 76 + 0 * 0 + 0 * 0 ≤ l ^ 77 :=
    absorb4 H.l1 (by positivity) (by norm_num) le_rfl le_rfl (by linarith [H.lK, H.hA])
      (H.p (by norm_num)) le_rfl (by positivity) (by positivity)
  have h7 : (((N : ℝ) + 1) * (K * (J + 1)) + T) ≤ l ^ 77 := by linarith
  have h8 : (2 : ℝ) * l ^ 97 ≤ l ^ 98 := by
    have : (2 : ℝ) ≤ l := by linarith [H.lK, H.hA]
    calc (2 : ℝ) * l ^ 97 ≤ l * l ^ 97 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = l ^ 98 := by ring
  calc (((N : ℝ) + 1) * (K * (J + 1)) + T) * (2 * l ^ 20) ≤ l ^ 77 * (2 * l ^ 20) :=
        mul_le_mul_of_nonneg_right h7 (by positivity)
    _ = 2 * l ^ 97 := by ring
    _ ≤ l ^ 98 := h8

/-- The slab width beats the position bound. -/
theorem num_Zn (H : NumHyp K A η l J N T d₀ Y G S₁) : exp (l ^ 22) * 64 ≤ exp (η * l ^ 100) := by
  have hl0 : 0 ≤ l := by linarith [H.l1]
  have h64 : (64 : ℝ) ≤ exp 64 := le_exp_self _
  calc exp (l ^ 22) * 64 ≤ exp (l ^ 22) * exp 64 := mul_le_mul_of_nonneg_left h64 (exp_pos _).le
    _ = exp (l ^ 22 + 64) := by rw [← exp_add]
    _ ≤ exp (η * l ^ 100) := by
        apply exp_le_exp.2
        have hηl := H.lη
        have h1 : l ^ 22 + 64 ≤ 65 * l ^ 99 := by
          have := H.one_le 99
          have : l ^ 22 ≤ l ^ 99 := H.p (by norm_num)
          linarith
        have h2 : (65 : ℝ) * l ^ 99 ≤ η * l ^ 100 := by
          calc (65 : ℝ) * l ^ 99 ≤ η * l * l ^ 99 :=
                mul_le_mul_of_nonneg_right (by linarith [H.hA]) (by positivity)
            _ = η * l ^ 100 := by ring
        linarith

end

end ArtinPrimitiveRoots.L102E.Num
end

section
/-! # L102D: the cuts of D1c (`minor_square_bound`) and the reduction

Four statements about the operator model of `L102D_OpDefs` (draft bundle
`Def_ArtinMinorOperator`):

* `MomentBoundStmt` (D7, [21] (3.19)/(4.1)): the moment of `(AA*)^R` is `≤ UV L^{-E₀ N}`;
* `PairingFromMomentStmt` (D5, [21] (3.20)): the pairing `⟨f, A f⟩_σ` is controlled by the moment;
* `GoodnessRemovalStmt` (D8a, [21] (4.56)–(4.57)): removing `G` from the pairing costs `UV L^{-A}`;
* `PadLiftStmt` (D8bc, [21] (4.58)–(4.63)): `Q^min = ∑_{dyads} d₀⁻¹ ⟨f, S T S f⟩_σ + O(XY L^{-A})`.

`minor_square_bound_of_cuts` proves the D1c statement from the four. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the cuts of D7 (the moment (4.1)) and the reduction

Seven statements about the draft model `L102D_OpDefs` + `L102D_MemDefs`, in the order of the
proof of [21] Proposition 4.1:

* `PathExpansionStmt` (D7p, exact): the physical moment is the sum over primitive roots `P₀` of
  the path functional in root coordinates, [21] §3.5 (3.30)–(3.32).
* `RootReplacementStmt` (D7r, [21] Lemma 3.4): the sum over roots is `UV/ζ(2)` times the integral
  of the independent-line moment over `[1,16] × [1,2] × [0,1]`, up to `UV L^{-AN}`.
* `MemoryIdentityStmt` (D7a, exact, [21] (4.5)–(4.15)): the independent-line moment is the
  baseline times the memory moment with global birth distinctness (no truncation).
* `TruncationStmt` (D7b, [21] (4.16)): truncating the memory at `B = ⌈L²⌉` costs `L^{-AN}`.
* `GhostBoundStmt` (D7c, [21] (4.19)–(4.22)): `‖G_j‖ ≤ C_K` on `H_B`.
* `EdgeBoundStmt` (D7d, [21] (4.23)–(4.42)): `‖E_j‖ ≤ L^{-G}` on `H_B`, `A₀` and then `K` large.
* `DistinctnessStmt` (D7e, [21] (4.43)–(4.55)): given D7c and D7d, the truncated memory moment
  with global birth distinctness is `≤ L^{-(G-1)N}`.

`moment_bound_of_cuts` proves `MomentBoundStmt` (D7) from them. -/

-- `MemParams.RootIn` now lives in the bundle `Def_ArtinMemoryModel` (round 5).

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- **D7r** ([21] Lemma 3.4, root replacement). The sum over primitive roots of the path
functional is `UV/ζ(2) = 6UV/π²` times the integral of the independent-line moment over the
normalized roots `(u/U, v/V, r) ∈ [1,16] × [1,2] × [0,1]`, with error `UV L^{-AN}`. -/
def RootReplacementStmt (δ c₁ c₂ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
        let P := dyadParams x a A₀ Y Hm Hn k
        ‖∑ P₀ ∈ posBox P.U P.V, P.pathPhi (rootOf P₀) (physDelta P₀) -
            ((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) *
              ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
                P.rootIL (P.U * u, P.V * v, r)‖ ≤
          P.U * P.V * log x ^ (-(A * P.N))

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102E (D7r): `RootReplacementStmt` ([21] Lemma 3.4)

The difference of the two sides is `σ ∑_{paths} W E · Epath` (`diff_expand`). Paths of zero
weight do not count; a live path with an unbounded position has no region (`epath_eq_zero`); a
bounded one has `|Epath| ≤ UV (30 e_T + x^{-η} Q)` (`epath_le`, `eps_split`) with `η = min(c/2, 2δ)`,
`n = ⌈x^{c/2}⌉` slabs and `T = ⌈L^{0.76}⌉` Bonferroni terms; the bounded paths weigh
`≤ σ #listCands β^N` (`sum_wNon_bdd`, `step_sum_le`). A live path forces `d₀ ≤ B₀^{KJ}` and
`Y < B₀^K` (`live_params`), so everything is `exp(poly(L^{1/100}))` and `num_*` conclude. -/

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

namespace ArtinPrimitiveRoots.L102E

open Real Finset PE

/-- Splitting the error of a bounded path. -/
lemma eps_split {x c δ η UV eT Gt e3 Zb Nr Bq : ℝ} {n : ℕ} (hx : 1 ≤ x) (hc : 0 < c)
    (hηc : η ≤ c / 2) (hηδ : η ≤ 2 * δ) (hUV : x ^ (2 * δ) ≤ UV) (hn1 : x ^ (c / 2) ≤ n)
    (hn2 : (n : ℝ) ≤ 2 * x ^ (c / 2)) (heT : 0 ≤ eT) (hGt : 0 ≤ Gt) (he3 : 0 ≤ e3) (hZb : 0 ≤ Zb)
    (hNr : 0 ≤ Nr) (hBq : 0 ≤ Bq) :
    n * (2 * (6 / π ^ 2) * UV * (15 / n) * eT + Gt * (e3 * (UV * x ^ (-c))) +
        2 * (e3 * (UV * x ^ (-c)))) + 6 / π ^ 2 * UV * (6000 * (Zb / n + Zb / UV)) +
      (2 * Nr) * Bq * (30 * (6 / π ^ 2 * UV) / n + e3 * (UV * x ^ (-c))) ≤
      UV * (30 * eT + x ^ (-η) * (2 * Gt * e3 + 4 * e3 + 12000 * Zb + 60 * Nr * Bq +
        2 * Nr * Bq * e3)) := by
  have hx0 : 0 < x := by linarith
  have hπ : 6 / π ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [pi_gt_three]
  have hπ0 : 0 ≤ 6 / π ^ 2 := by positivity
  have hxc : 1 ≤ x ^ (c / 2) := one_le_rpow hx (by positivity)
  have hn0 : (0 : ℝ) < n := by linarith
  have hUV0 : 0 < UV := lt_of_lt_of_le (rpow_pos_of_pos hx0 _) hUV
  have hxη : 0 ≤ x ^ (-η) := (rpow_pos_of_pos hx0 _).le
  -- the powers of `x`
  have hcη : x ^ (-c) ≤ x ^ (-η) := rpow_le_rpow_of_exponent_le hx (by linarith)
  have hc2 : x ^ (-(c / 2)) ≤ x ^ (-η) := rpow_le_rpow_of_exponent_le hx (by linarith)
  have hnx : (n : ℝ) * x ^ (-c) ≤ 2 * x ^ (-η) := by
    have e : x ^ (c / 2) * x ^ (-c) = x ^ (-(c / 2)) := by rw [← rpow_add hx0]; ring_nf
    calc (n : ℝ) * x ^ (-c) ≤ 2 * x ^ (c / 2) * x ^ (-c) :=
          mul_le_mul_of_nonneg_right hn2 (rpow_pos_of_pos hx0 _).le
      _ = 2 * x ^ (-(c / 2)) := by rw [mul_assoc, e]
      _ ≤ 2 * x ^ (-η) := by linarith
  have hinvn : 1 / (n : ℝ) ≤ x ^ (-η) := by
    have : 1 / (n : ℝ) ≤ x ^ (-(c / 2)) := by
      rw [rpow_neg hx0.le, ← one_div]
      exact one_div_le_one_div_of_le (rpow_pos_of_pos hx0 _) hn1
    linarith
  have hUVη : 1 ≤ UV * x ^ (-η) := by
    have h1 : x ^ (-(2 * δ)) ≤ x ^ (-η) := rpow_le_rpow_of_exponent_le hx (by linarith)
    have h2 : 1 ≤ UV * x ^ (-(2 * δ)) := by
      rw [rpow_neg hx0.le, ← div_eq_mul_inv, le_div_iff₀ (rpow_pos_of_pos hx0 _)]; linarith
    calc (1 : ℝ) ≤ UV * x ^ (-(2 * δ)) := h2
      _ ≤ UV * x ^ (-η) := mul_le_mul_of_nonneg_left h1 hUV0.le
  -- the seven terms
  have t1 : (n : ℝ) * (2 * (6 / π ^ 2) * UV * (15 / n) * eT) ≤ 30 * UV * eT := by
    have : (n : ℝ) * (2 * (6 / π ^ 2) * UV * (15 / n) * eT) = 30 * (6 / π ^ 2) * UV * eT := by
      field_simp; ring
    rw [this]
    have : 0 ≤ UV * eT := mul_nonneg hUV0.le heT
    nlinarith
  have t2 : (n : ℝ) * (Gt * (e3 * (UV * x ^ (-c)))) ≤ 2 * (UV * x ^ (-η) * (Gt * e3)) := by
    have : (n : ℝ) * (Gt * (e3 * (UV * x ^ (-c)))) = (Gt * e3 * UV) * (n * x ^ (-c)) := by ring
    rw [this]
    calc Gt * e3 * UV * (n * x ^ (-c)) ≤ Gt * e3 * UV * (2 * x ^ (-η)) :=
          mul_le_mul_of_nonneg_left hnx (by positivity)
      _ = 2 * (UV * x ^ (-η) * (Gt * e3)) := by ring
  have t3 : (n : ℝ) * (2 * (e3 * (UV * x ^ (-c)))) ≤ 4 * (UV * x ^ (-η) * e3) := by
    have : (n : ℝ) * (2 * (e3 * (UV * x ^ (-c)))) = (2 * e3 * UV) * (n * x ^ (-c)) := by ring
    rw [this]
    calc 2 * e3 * UV * (n * x ^ (-c)) ≤ 2 * e3 * UV * (2 * x ^ (-η)) :=
          mul_le_mul_of_nonneg_left hnx (by positivity)
      _ = 4 * (UV * x ^ (-η) * e3) := by ring
  have t4 : 6 / π ^ 2 * UV * (6000 * (Zb / n)) ≤ 6000 * (UV * x ^ (-η) * Zb) := by
    have : 6 / π ^ 2 * UV * (6000 * (Zb / n)) = (6 / π ^ 2) * (6000 * UV * Zb) * (1 / n) := by
      ring
    rw [this]
    have h0 : 0 ≤ 6000 * UV * Zb := by positivity
    calc (6 / π ^ 2) * (6000 * UV * Zb) * (1 / n) ≤ 1 * (6000 * UV * Zb) * x ^ (-η) := by
          gcongr
      _ = 6000 * (UV * x ^ (-η) * Zb) := by ring
  have t5 : 6 / π ^ 2 * UV * (6000 * (Zb / UV)) ≤ 6000 * (UV * x ^ (-η) * Zb) := by
    have : 6 / π ^ 2 * UV * (6000 * (Zb / UV)) = (6 / π ^ 2) * (6000 * Zb) := by
      field_simp
    rw [this]
    calc (6 / π ^ 2) * (6000 * Zb) ≤ 1 * (6000 * Zb) := by gcongr
      _ ≤ (UV * x ^ (-η)) * (6000 * Zb) := by gcongr
      _ = 6000 * (UV * x ^ (-η) * Zb) := by ring
  have t6 : 2 * Nr * Bq * (30 * (6 / π ^ 2 * UV) / n) ≤ 60 * (UV * x ^ (-η) * (Nr * Bq)) := by
    have : 2 * Nr * Bq * (30 * (6 / π ^ 2 * UV) / n) =
        (6 / π ^ 2) * (60 * UV * (Nr * Bq)) * (1 / n) := by ring
    rw [this]
    have h0 : 0 ≤ 60 * UV * (Nr * Bq) := by positivity
    calc (6 / π ^ 2) * (60 * UV * (Nr * Bq)) * (1 / n) ≤ 1 * (60 * UV * (Nr * Bq)) * x ^ (-η) := by
          gcongr
      _ = 60 * (UV * x ^ (-η) * (Nr * Bq)) := by ring
  have t7 : 2 * Nr * Bq * (e3 * (UV * x ^ (-c))) ≤ 2 * (UV * x ^ (-η) * (Nr * Bq * e3)) := by
    have : 2 * Nr * Bq * (e3 * (UV * x ^ (-c))) = (2 * Nr * Bq * e3 * UV) * x ^ (-c) := by ring
    rw [this]
    calc (2 * Nr * Bq * e3 * UV) * x ^ (-c) ≤ (2 * Nr * Bq * e3 * UV) * x ^ (-η) :=
          mul_le_mul_of_nonneg_left hcη (by positivity)
      _ = 2 * (UV * x ^ (-η) * (Nr * Bq * e3)) := by ring
  calc n * (2 * (6 / π ^ 2) * UV * (15 / n) * eT + Gt * (e3 * (UV * x ^ (-c))) +
        2 * (e3 * (UV * x ^ (-c)))) + 6 / π ^ 2 * UV * (6000 * (Zb / n + Zb / UV)) +
      (2 * Nr) * Bq * (30 * (6 / π ^ 2 * UV) / n + e3 * (UV * x ^ (-c)))
      = (n : ℝ) * (2 * (6 / π ^ 2) * UV * (15 / n) * eT) + (n : ℝ) * (Gt * (e3 * (UV * x ^ (-c)))) +
        (n : ℝ) * (2 * (e3 * (UV * x ^ (-c)))) + 6 / π ^ 2 * UV * (6000 * (Zb / n)) +
        6 / π ^ 2 * UV * (6000 * (Zb / UV)) + 2 * Nr * Bq * (30 * (6 / π ^ 2 * UV) / n) +
        2 * Nr * Bq * (e3 * (UV * x ^ (-c))) := by ring
    _ ≤ 30 * UV * eT + 2 * (UV * x ^ (-η) * (Gt * e3)) + 4 * (UV * x ^ (-η) * e3) +
        6000 * (UV * x ^ (-η) * Zb) + 6000 * (UV * x ^ (-η) * Zb) +
        60 * (UV * x ^ (-η) * (Nr * Bq)) + 2 * (UV * x ^ (-η) * (Nr * Bq * e3)) := by
        linarith
    _ = UV * (30 * eT + x ^ (-η) * (2 * Gt * e3 + 4 * e3 + 12000 * Zb + 60 * Nr * Bq +
        2 * Nr * Bq * e3)) := by ring

lemma first_step (P : MemParams) : ∀ (k : ℕ) (s : St P) (cs : Fin k → StepT P), 0 < k →
    wNon P k s cs ≠ 0 → ∃ j, ∃ c : StepT P, stepNon P j s c.1 ≠ 0
  | 0, _, _, hk, _ => absurd hk (lt_irrefl 0)
  | k + 1, _, _, _, h => ⟨_, _, stepNon_ne_of_wNon P h⟩

lemma rpow_hundredth {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    (L ^ ((1 : ℝ) / 100)) ^ n = L ^ ((n : ℝ) / 100) := by
  rw [← rpow_natCast, ← rpow_mul hL]; ring_nf

open Classical in
/-- The sum over paths, given the per-path bounds. -/
lemma path_sum_bound (P : MemParams) {Zb εq β : ℝ} (hεq0 : 0 ≤ εq)
    (hσ0 : 0 ≤ stateNorm P.x P.a P.J)
    (hbnd : ∀ ℓ₀ ∈ listCands P.x P.a P.J, ∀ cs : Fin P.N → StepT P,
      BddP P Zb P.N (st0 P ℓ₀) cs → |Epath P ℓ₀ cs| ≤ εq)
    (hz : ∀ ℓ₀ ∈ listCands P.x P.a P.J, ∀ cs : Fin P.N → StepT P,
      wNon P P.N (st0 P ℓ₀) cs ≠ 0 → ¬ BddP P Zb P.N (st0 P ℓ₀) cs → Epath P ℓ₀ cs = 0)
    (hpaths : ∀ s : St P, ∑ cs : Fin P.N → StepT P,
      (if BddP P Zb P.N s cs then ‖wNon P P.N s cs‖ else 0) ≤ β ^ P.N) :
    ‖(stateNorm P.x P.a P.J : ℂ) * ∑ ℓ₀ ∈ listCands P.x P.a P.J,
      ∑ cs : Fin P.N → StepT P, wNon P P.N (st0 P ℓ₀) cs * endF P (endSt P P.N (st0 P ℓ₀) cs) *
        ((Epath P ℓ₀ cs : ℝ) : ℂ)‖ ≤
      stateNorm P.x P.a P.J * (((listCands P.x P.a P.J).card : ℝ) * β ^ P.N) * εq := by
  have hterm : ∀ ℓ₀ ∈ listCands P.x P.a P.J, ∀ cs : Fin P.N → StepT P,
      ‖wNon P P.N (st0 P ℓ₀) cs * endF P (endSt P P.N (st0 P ℓ₀) cs) * ((Epath P ℓ₀ cs : ℝ) : ℂ)‖ ≤
        (if BddP P Zb P.N (st0 P ℓ₀) cs then ‖wNon P P.N (st0 P ℓ₀) cs‖ else 0) * εq := by
    intro ℓ₀ hℓ₀ cs
    have hif0 : 0 ≤ (if BddP P Zb P.N (st0 P ℓ₀) cs then ‖wNon P P.N (st0 P ℓ₀) cs‖ else 0) := by
      split_ifs
      · exact norm_nonneg _
      · exact le_rfl
    have hE : ‖endF P (endSt P P.N (st0 P ℓ₀) cs)‖ ≤ 1 := by
      unfold endF
      split_ifs
      · rw [norm_one]
      · rw [norm_zero]; exact zero_le_one
    by_cases hw : wNon P P.N (st0 P ℓ₀) cs = 0
    · have h0 : ‖wNon P P.N (st0 P ℓ₀) cs * endF P (endSt P P.N (st0 P ℓ₀) cs) *
          ((Epath P ℓ₀ cs : ℝ) : ℂ)‖ = 0 := by rw [hw, zero_mul, zero_mul, norm_zero]
      rw [h0]; exact mul_nonneg hif0 hεq0
    by_cases hb : BddP P Zb P.N (st0 P ℓ₀) cs
    · rw [if_pos hb, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖wNon P P.N (st0 P ℓ₀) cs‖ * ‖endF P (endSt P P.N (st0 P ℓ₀) cs)‖ * |Epath P ℓ₀ cs|
          ≤ ‖wNon P P.N (st0 P ℓ₀) cs‖ * 1 * εq := by
            gcongr
            exact hbnd ℓ₀ hℓ₀ cs hb
        _ = ‖wNon P P.N (st0 P ℓ₀) cs‖ * εq := by ring
    · rw [hz ℓ₀ hℓ₀ cs hw hb, Complex.ofReal_zero, mul_zero, norm_zero]
      exact mul_nonneg hif0 hεq0
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ0, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hσ0
  refine (norm_sum_le _ _).trans ?_
  calc ∑ ℓ₀ ∈ listCands P.x P.a P.J, ‖∑ cs : Fin P.N → StepT P, wNon P P.N (st0 P ℓ₀) cs *
        endF P (endSt P P.N (st0 P ℓ₀) cs) * ((Epath P ℓ₀ cs : ℝ) : ℂ)‖
      ≤ ∑ _ℓ₀ ∈ listCands P.x P.a P.J, β ^ P.N * εq := by
        refine sum_le_sum fun ℓ₀ hℓ₀ => (norm_sum_le _ _).trans ?_
        calc ∑ cs : Fin P.N → StepT P, ‖wNon P P.N (st0 P ℓ₀) cs *
              endF P (endSt P P.N (st0 P ℓ₀) cs) * ((Epath P ℓ₀ cs : ℝ) : ℂ)‖
            ≤ ∑ cs : Fin P.N → StepT P, (if BddP P Zb P.N (st0 P ℓ₀) cs then
                ‖wNon P P.N (st0 P ℓ₀) cs‖ else 0) * εq := sum_le_sum fun cs _ => hterm ℓ₀ hℓ₀ cs
          _ = (∑ cs : Fin P.N → StepT P, (if BddP P Zb P.N (st0 P ℓ₀) cs then
                ‖wNon P P.N (st0 P ℓ₀) cs‖ else 0)) * εq := by rw [sum_mul]
          _ ≤ β ^ P.N * εq := mul_le_mul_of_nonneg_right (hpaths _) hεq0
    _ = ((listCands P.x P.a P.J).card : ℝ) * β ^ P.N * εq := by
        rw [sum_const, nsmul_eq_mul, mul_assoc]

/-- The error of a bounded path, in the form of the numerics. -/
lemma bounded_err (P : MemParams) {c δ η : ℝ} (hx1 : 1 ≤ P.x) (hc : 0 < c) (hηc : η ≤ c / 2)
    (hηδ : η ≤ 2 * δ) (hRC : RootCount2At P.x P.U P.V c) (hU : 0 < P.U) (hV : 0 < P.V)
    (hUV : P.x ^ (2 * δ) ≤ P.U * P.V) (hG : ∀ p ∈ P.gPrimes, p.Prime) {Pm : ℝ} (hPm1 : 1 ≤ Pm)
    (hgrp : ∀ i, ∀ p ∈ P.grp i, (p : ℝ) ≤ Pm) {T : ℕ}
    (hPT : Pm ^ ((P.N + 1) * (P.K * (P.J + 1)) + T) ≤ exp (log P.x ^ (0.98 : ℝ)))
    (hY1 : 1 ≤ P.Y) (hcard : ∀ i, ((P.grp i).card : ℝ) ≤ Pm + 1) {n : ℕ} (hn : 0 < n)
    (hn1 : P.x ^ (c / 2) ≤ n) (hn2 : (n : ℝ) ≤ 2 * P.x ^ (c / 2)) {Zb : ℝ} (hZ0 : 0 ≤ Zb)
    (hZn : Zb / n ≤ 1 / 64) {ℓ₀ : P.Lst} (hℓ₀ : ℓ₀ ∈ listCands P.x P.a P.J)
    (cs : Fin P.N → StepT P) (hb : BddP P Zb P.N (st0 P ℓ₀) cs) :
    |Epath P ℓ₀ cs| ≤ P.U * P.V * (30 * (((P.N + 1 : ℝ) * ∑ p ∈ P.gPrimes, 1 / ((p : ℝ) + 1)) ^ T /
        (T.factorial : ℝ)) + P.x ^ (-η) * (2 * ((P.gPrimes.card : ℝ) + 1) ^ T *
          exp (log P.x ^ (0.98 : ℝ)) ^ 3 + 4 * exp (log P.x ^ (0.98 : ℝ)) ^ 3 + 12000 * Zb +
          60 * (P.N : ℝ) * (4 * Tcb P (Pm + 1) * (2 * (4096 * Mtb P Pm + 1) + 1)) +
          2 * (P.N : ℝ) * (4 * Tcb P (Pm + 1) * (2 * (4096 * Mtb P Pm + 1) + 1)) *
            exp (log P.x ^ (0.98 : ℝ)) ^ 3)) := by
  have hY0 : 0 ≤ P.Y ^ (0.2 : ℝ) := by have := hY1; positivity
  have hBq : 0 ≤ 4 * Tcb P (Pm + 1) * (2 * (4096 * Mtb P Pm + 1) + 1) := by
    unfold Tcb Mtb
    have : 0 ≤ Pm := by linarith
    positivity
  refine (epath_le P hx1 hRC hU hV hG hPm1 hgrp hPT hY1 (by linarith) hcard hℓ₀ cs hZ0 hb hn
    hZn).trans ?_
  have hsplit := eps_split (x := P.x) (c := c) (δ := δ) (η := η) (UV := P.U * P.V)
    (eT := ((P.N + 1 : ℝ) * ∑ p ∈ P.gPrimes, 1 / ((p : ℝ) + 1)) ^ T / (T.factorial : ℝ))
    (Gt := ((P.gPrimes.card : ℝ) + 1) ^ T) (e3 := exp (log P.x ^ (0.98 : ℝ)) ^ 3) (Zb := Zb)
    (Nr := (P.N : ℝ)) (Bq := 4 * Tcb P (Pm + 1) * (2 * (4096 * Mtb P Pm + 1) + 1)) (n := n)
    hx1 hc hηc hηδ hUV hn1 hn2 (by positivity) (by positivity) (by positivity) hZ0
    (Nat.cast_nonneg _) hBq
  have e : ((2 * P.N : ℕ) : ℝ) = 2 * (P.N : ℝ) := by push_cast; ring
  unfold Eb
  rw [e]
  refine le_trans (le_of_eq ?_) (hsplit.trans (le_of_eq ?_))
  · ring
  · ring

/-- The final numerics at one dyad. -/
lemma final_numeric (P : MemParams) {A η l L : ℝ} {T : ℕ} {S₁ : ℝ}
    (H : Num.NumHyp P.K A η l P.J P.N T (P.d₀ : ℝ) P.Y (P.gPrimes.card : ℝ) S₁)
    (hUV0 : 0 ≤ P.U * P.V) (hL1 : 1 ≤ L) (hLl : L = l ^ 100) (hx0 : 0 < P.x) (hLx : L = log P.x)
    (hL98 : log P.x ^ (0.98 : ℝ) = l ^ 98)
    {σ LC : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ exp (2 * l ^ 20) ^ (P.K * (P.J + 1)))
    (hLC0 : 0 ≤ LC) (hLC : LC ≤ (exp (2 * l ^ 20) + 1) ^ (P.K * (P.J + 1))) :
    σ * (LC * (exp (2 * l ^ 20) ^ P.K *
        ((2 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) + 33) *
          (2 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) + 1)) * (exp (2 * l ^ 20) + 1) ^ P.K) ^ P.N) *
      (P.U * P.V * (30 * (((P.N + 1 : ℝ) * S₁) ^ T / (T.factorial : ℝ)) +
        P.x ^ (-η) * (2 * ((P.gPrimes.card : ℝ) + 1) ^ T * exp (log P.x ^ (0.98 : ℝ)) ^ 3 +
          4 * exp (log P.x ^ (0.98 : ℝ)) ^ 3 + 12000 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) +
          60 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
            (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) +
          2 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
            (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) * exp (log P.x ^ (0.98 : ℝ)) ^ 3))) ≤
      P.U * P.V * L ^ (-(A * P.N)) := by
  have hl1 := H.l1
  have hW := Num.num_W H
  have hTail := Num.num_tail H
  have hQ := Num.num_Q H
  have hfin := Num.num_fin H
  rw [hL98]
  set β := exp (2 * l ^ 20) ^ P.K * ((2 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) + 33) *
    (2 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) + 1)) * (exp (2 * l ^ 20) + 1) ^ P.K with hβ
  have hβ0 : 0 ≤ β := by
    rw [hβ]; have := H.hd0; have := H.hY1; positivity
  have hWb : σ * (LC * β ^ P.N) ≤ exp (l ^ 73) := by
    refine le_trans ?_ hW
    calc σ * (LC * β ^ P.N) ≤ exp (2 * l ^ 20) ^ (P.K * (P.J + 1)) *
          ((exp (2 * l ^ 20) + 1) ^ (P.K * (P.J + 1)) * β ^ P.N) := by gcongr
      _ = _ := by rw [hβ]; ring
  have hQb : 2 * ((P.gPrimes.card : ℝ) + 1) ^ T * exp (l ^ 98) ^ 3 + 4 * exp (l ^ 98) ^ 3 +
      12000 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) +
      60 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
        (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) +
      2 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
        (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) * exp (l ^ 98) ^ 3 ≤ exp (l ^ 99) := by
    unfold Tcb Mtb
    convert hQ using 2
  have hxη' : P.x ^ (-η) = exp (-(η * l ^ 100)) := by
    rw [rpow_def_of_pos hx0, ← hLx, hLl]; ring_nf
  have hQ0 : 0 ≤ 2 * ((P.gPrimes.card : ℝ) + 1) ^ T * exp (l ^ 98) ^ 3 + 4 * exp (l ^ 98) ^ 3 +
      12000 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) +
      60 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
        (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) +
      2 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
        (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) * exp (l ^ 98) ^ 3 := by
    unfold Tcb Mtb
    have := H.hd0; have := H.hY1
    positivity
  have heT0 : 0 ≤ ((P.N + 1 : ℝ) * S₁) ^ T / (T.factorial : ℝ) := by
    have := H.hS0; positivity
  have hεqb : 30 * (((P.N + 1 : ℝ) * S₁) ^ T / (T.factorial : ℝ)) +
      P.x ^ (-η) * (2 * ((P.gPrimes.card : ℝ) + 1) ^ T * exp (l ^ 98) ^ 3 + 4 * exp (l ^ 98) ^ 3 +
      12000 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) +
      60 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
        (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) +
      2 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
        (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) * exp (l ^ 98) ^ 3) ≤
      30 * exp (-(l ^ 76)) + exp (l ^ 99) * exp (-(η * l ^ 100)) := by
    rw [hxη']
    have : exp (-(η * l ^ 100)) * (2 * ((P.gPrimes.card : ℝ) + 1) ^ T * exp (l ^ 98) ^ 3 +
        4 * exp (l ^ 98) ^ 3 + 12000 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) +
        60 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
          (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) +
        2 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
          (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) * exp (l ^ 98) ^ 3) ≤
        exp (l ^ 99) * exp (-(η * l ^ 100)) := by
      rw [mul_comm (exp (l ^ 99))]; exact mul_le_mul_of_nonneg_left hQb (exp_pos _).le
    linarith
  have hLA : exp (-(A * (l ^ 50 + 2) * (100 * l))) ≤ L ^ (-(A * P.N)) := by
    rw [rpow_def_of_pos (by linarith)]
    apply exp_le_exp.2
    have hlogL : log L ≤ 100 * l := by
      rw [hLl, log_pow]; push_cast
      have := log_le_sub_one_of_pos (show 0 < l by linarith)
      linarith
    have hlogL0 : 0 ≤ log L := log_nonneg hL1
    have hNl : (P.N : ℝ) ≤ l ^ 50 + 2 := H.hN
    have hA := H.hA
    have h1 : (P.N : ℝ) * log L ≤ (l ^ 50 + 2) * (100 * l) :=
      mul_le_mul hNl hlogL hlogL0 (by positivity)
    have h2 : A * ((P.N : ℝ) * log L) ≤ A * ((l ^ 50 + 2) * (100 * l)) :=
      mul_le_mul_of_nonneg_left h1 hA.le
    linarith
  have hεq0 : 0 ≤ P.U * P.V * (30 * (((P.N + 1 : ℝ) * S₁) ^ T / (T.factorial : ℝ)) +
      P.x ^ (-η) * (2 * ((P.gPrimes.card : ℝ) + 1) ^ T * exp (l ^ 98) ^ 3 + 4 * exp (l ^ 98) ^ 3 +
      12000 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) +
      60 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
        (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) +
      2 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
        (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) * exp (l ^ 98) ^ 3)) := by
    have := rpow_nonneg hx0.le (-η)
    positivity
  calc σ * (LC * β ^ P.N) * (P.U * P.V * (30 * (((P.N + 1 : ℝ) * S₁) ^ T / (T.factorial : ℝ)) +
      P.x ^ (-η) * (2 * ((P.gPrimes.card : ℝ) + 1) ^ T * exp (l ^ 98) ^ 3 + 4 * exp (l ^ 98) ^ 3 +
      12000 * (4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y)) +
      60 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
        (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) +
      2 * (P.N : ℝ) * (4 * Tcb P (exp (2 * l ^ 20) + 1) *
        (2 * (4096 * Mtb P (exp (2 * l ^ 20)) + 1) + 1)) * exp (l ^ 98) ^ 3)))
      ≤ exp (l ^ 73) * (P.U * P.V * (30 * exp (-(l ^ 76)) + exp (l ^ 99) * exp (-(η * l ^ 100)))) :=
        mul_le_mul hWb (mul_le_mul_of_nonneg_left hεqb hUV0) hεq0 (exp_pos _).le
    _ = P.U * P.V * (exp (l ^ 73) * (30 * exp (-(l ^ 76)) + exp (l ^ 99) * exp (-(η * l ^ 100)))) := by
        ring
    _ ≤ P.U * P.V * exp (-(A * (l ^ 50 + 2) * (100 * l))) := mul_le_mul_of_nonneg_left hfin hUV0
    _ ≤ P.U * P.V * L ^ (-(A * P.N)) := mul_le_mul_of_nonneg_left hLA hUV0

lemma eq_nonneg {UV eT xη Gt e3 Zb Nr Bq : ℝ} (h1 : 0 ≤ UV) (h2 : 0 ≤ eT) (h3 : 0 ≤ xη)
    (h4 : 0 ≤ Gt) (h5 : 0 ≤ e3) (h6 : 0 ≤ Zb) (h7 : 0 ≤ Nr) (h8 : 0 ≤ Bq) :
    0 ≤ UV * (30 * eT + xη * (2 * Gt * e3 + 4 * e3 + 12000 * Zb + 60 * Nr * Bq +
      2 * Nr * Bq * e3)) := by positivity

lemma Tcb_nonneg (P : MemParams) {Cg : ℝ} (hCg : 0 ≤ Cg) (hY1 : 1 ≤ P.Y) : 0 ≤ Tcb P Cg := by
  unfold Tcb; have := hY1; positivity

lemma Mtb_nonneg (P : MemParams) {Pm : ℝ} (hPm : 0 ≤ Pm) (hY1 : 1 ≤ P.Y) : 0 ≤ Mtb P Pm := by
  unfold Mtb; have := hY1; positivity

lemma grp_bounds (P : MemParams) {L l : ℝ} (hL1 : 1 ≤ L) (hLx : L = log P.x)
    (hL20 : L ^ (0.2 : ℝ) = l ^ 20) (ha : ∀ i, P.a i ≤ 0.2) :
    (∀ i, ∀ p ∈ P.grp i, (p : ℝ) ≤ exp (2 * l ^ 20)) ∧
      (∀ i, ((P.grp i).card : ℝ) ≤ exp (2 * l ^ 20) + 1) ∧
      ∀ i, L ^ P.a i ≤ L ^ (0.2 : ℝ) := by
  have hpow02 : ∀ i, L ^ P.a i ≤ L ^ (0.2 : ℝ) := fun i => rpow_le_rpow_of_exponent_le hL1 (ha i)
  refine ⟨fun i p hp => ?_, fun i => ?_, hpow02⟩
  · unfold MemParams.grp primeGroup at hp
    simp only [mem_filter, mem_range] at hp
    have h1 : (p : ℝ) ≤ exp (2 * log P.x ^ P.a i) :=
      (Nat.cast_le.2 (Nat.lt_succ_iff.1 hp.1)).trans (Nat.floor_le (exp_pos _).le)
    refine h1.trans (exp_le_exp.2 ?_)
    rw [← hLx, ← hL20]; linarith [hpow02 i]
  · refine (L102D.card_primeGroup_le P.x (P.a i)).trans ?_
    have : exp (2 * log P.x ^ P.a i) ≤ exp (2 * l ^ 20) :=
      exp_le_exp.2 (by rw [← hLx, ← hL20]; linarith [hpow02 i])
    linarith

lemma gPrimes_prime (P : MemParams) : ∀ p ∈ P.gPrimes, p.Prime := by
  intro p hp
  obtain ⟨i, hi⟩ := mem_gPrimes P hp
  unfold MemParams.grp primeGroup at hi
  exact (mem_filter.1 hi).2.1

open Classical in
/-- **D7r at one dyad.** -/
theorem main_bound (P : MemParams) {A c δ : ℝ} (hA : 0 < A) (hc : 0 < c) (hδ : 0 < δ)
    (hx1 : 1 ≤ P.x) (hRC : RootCount2At P.x P.U P.V c) (hU : 0 < P.U) (hV : 0 < P.V)
    (hUV : P.x ^ (2 * δ) ≤ P.U * P.V) (hY1 : 1 ≤ P.Y) (hd₀ : 0 < P.d₀)
    (hJ : P.J = padCount P.x) (hN : P.N = 2 * momentPower P.x) (ha : ∀ i, P.a i ≤ 0.2)
    (hl : Num.l0 P.K A (min (c / 2) (2 * δ)) ≤ log P.x ^ ((1 : ℝ) / 100)) :
    ‖∑ P₀ ∈ posBox P.U P.V, P.pathPhi (rootOf P₀) (physDelta P₀) -
        ((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) *
          ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, P.rootIL (P.U * u, P.V * v, r)‖ ≤
      P.U * P.V * log P.x ^ (-(A * P.N)) := by
  set η := min (c / 2) (2 * δ) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  set L := log P.x with hLdef
  have hL0 : 0 ≤ L := log_nonneg hx1
  set l := L ^ ((1 : ℝ) / 100) with hldef
  have hlpow : ∀ n : ℕ, l ^ n = L ^ ((n : ℝ) / 100) := rpow_hundredth hL0
  have hl1 : 1 ≤ l := by
    have : (1 : ℝ) ≤ Num.l0 P.K A η := by
      unfold Num.l0; have : 0 ≤ (400 + 400 * A) / η := by positivity
      have : (0 : ℝ) ≤ P.K := Nat.cast_nonneg _
      linarith
    linarith
  have hLl : L = l ^ 100 := by rw [hlpow]; norm_num
  have hL20 : L ^ (0.2 : ℝ) = l ^ 20 := by rw [hlpow]; norm_num
  have hL98 : L ^ (0.98 : ℝ) = l ^ 98 := by rw [hlpow]; norm_num
  have hL50 : L ^ (0.5 : ℝ) = l ^ 50 := by rw [hlpow]; norm_num
  have hL01 : L ^ (0.01 : ℝ) = l := by
    have := hlpow 1; rw [pow_one] at this; rw [this]; norm_num
  have hL1 : 1 ≤ L := by rw [hLl]; exact one_le_pow₀ hl1
  have hx0 : 0 < P.x := by linarith
  set Pm := exp (2 * l ^ 20) with hPmdef
  have hPm1 : 1 ≤ Pm := one_le_exp (by positivity)
  obtain ⟨hgrp, hcard, hpow02⟩ := grp_bounds P hL1 hLdef hL20 ha
  have hG := gPrimes_prime P
  have hVg : ∀ i, 0 ≤ P.Vg i := Vg_nonneg P
  have hY0 : 0 < P.Y := by linarith
  have hRHS : 0 ≤ P.U * P.V * L ^ (-(A * P.N)) := by
    have := rpow_nonneg hL0 (-(A * P.N)); positivity
  rw [diff_expand P hU hV hG]
  by_cases hlive : ∃ ℓ₀ ∈ listCands P.x P.a P.J, ∃ cs : Fin P.N → StepT P,
      wNon P P.N (st0 P ℓ₀) cs ≠ 0
  swap
  · push Not at hlive
    have : ∑ ℓ₀ ∈ listCands P.x P.a P.J, ∑ cs : Fin P.N → StepT P,
        wNon P P.N (st0 P ℓ₀) cs * endF P (endSt P P.N (st0 P ℓ₀) cs) * ((Epath P ℓ₀ cs : ℝ) : ℂ) =
          0 :=
      sum_eq_zero fun ℓ₀ hℓ₀ => sum_eq_zero fun cs _ => by rw [hlive ℓ₀ hℓ₀ cs, zero_mul, zero_mul]
    rw [this, mul_zero, norm_zero]
    exact hRHS
  obtain ⟨ℓ₀', hℓ₀', cs', hw'⟩ := hlive
  have hNpos : 0 < P.N := by
    rw [hN]
    have : (0 : ℝ) < L ^ (0.5 : ℝ) / 2 := by rw [hL50]; positivity
    have : 0 < momentPower P.x := Nat.ceil_pos.2 this
    omega
  have hs0 : ∀ i j, (st0 P ℓ₀').2 i j ∈ P.grp i := fun i j =>
    Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hℓ₀' i) j
  obtain ⟨j₀, c₀, hc₀⟩ := first_step P P.N (st0 P ℓ₀') cs' hNpos hw'
  obtain ⟨hdb, hYb⟩ := live_params P hPm1 hgrp hY0 hs0 hc₀
  -- the numerical parameters
  set T := ⌈l ^ 76⌉₊ with hTdef
  set S₁ := ∑ p ∈ P.gPrimes, 1 / ((p : ℝ) + 1) with hS₁
  have H : Num.NumHyp P.K A η l P.J P.N T (P.d₀ : ℝ) P.Y (P.gPrimes.card : ℝ) S₁ := by
    refine ⟨hA, hη0, hl, ?_, ?_, Nat.le_ceil _, (Nat.ceil_lt_add_one (by positivity)).le,
      Nat.cast_nonneg _, hdb, hY1, hYb.le, Nat.cast_nonneg _, ?_,
      sum_nonneg fun p _ => by positivity, ?_⟩
    · rw [hJ, ← hL01]; exact Nat.floor_le (by positivity)
    · rw [hN, ← hL50]; push_cast
      have := Nat.ceil_lt_add_one (show 0 ≤ L ^ (0.5 : ℝ) / 2 by positivity)
      unfold momentPower; linarith
    · exact card_gPrimes_le P hcard
    · have := sum_inv_gPrimes_le P hL0 hpow02
      rw [← hL20]; exact this
  -- slabs
  set n := ⌈P.x ^ (c / 2)⌉₊ with hndef
  have hxc1 : 1 ≤ P.x ^ (c / 2) := one_le_rpow hx1 (by positivity)
  have hn1 : P.x ^ (c / 2) ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) ≤ 2 * P.x ^ (c / 2) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ P.x ^ (c / 2) by positivity); linarith
  have hn : 0 < n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  set Zb := 4096 * (P.N : ℝ) * (10 * P.d₀ * P.Y) with hZbdef
  have hZ0 : 0 ≤ Zb := by positivity
  have hxη : exp (η * l ^ 100) ≤ P.x ^ (c / 2) := by
    rw [rpow_def_of_pos hx0, ← hLdef, hLl]
    apply exp_le_exp.2
    have : η ≤ c / 2 := min_le_left _ _
    have : 0 ≤ l ^ 100 := by positivity
    nlinarith
  have hZn : Zb / n ≤ 1 / 64 := by
    have h1 := H.Zb
    have h2 := Num.num_Zn H
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    have : exp (l ^ 22) * 64 ≤ n := h2.trans (hxη.trans hn1)
    linarith
  have hPT : Pm ^ ((P.N + 1) * (P.K * (P.J + 1)) + T) ≤ exp (log P.x ^ (0.98 : ℝ)) := by
    rw [← hLdef, hL98]; exact Num.num_PT H
  -- the per-path bounds
  have hbnd := fun ℓ₀ hℓ₀ cs hb => bounded_err P hx1 hc (min_le_left _ _) (min_le_right _ _) hRC
    hU hV hUV hG hPm1 hgrp hPT hY1 hcard hn hn1 hn2 hZ0 hZn (ℓ₀ := ℓ₀) hℓ₀ cs hb
  have hz : ∀ ℓ₀ ∈ listCands P.x P.a P.J, ∀ cs : Fin P.N → StepT P,
      wNon P P.N (st0 P ℓ₀) cs ≠ 0 → ¬ BddP P Zb P.N (st0 P ℓ₀) cs → Epath P ℓ₀ cs = 0 :=
    fun ℓ₀ _ cs hw hb => epath_eq_zero P hU hY0 hd₀ hVg hw hb
  have hσ0 : 0 ≤ stateNorm P.x P.a P.J := by
    unfold stateNorm; exact prod_nonneg fun i _ => pow_nonneg (inv_nonneg.2 (hVg i)) _
  set β := Pm ^ P.K * ((2 * Zb + 33) * (2 * Zb + 1)) * (Pm + 1) ^ P.K with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hstep : ∀ j (s : St P), ∑ c : StepT P, (if BddZ Zb c.1.2.1 then ‖stepNon P j s c.1‖ else 0) ≤
      β := fun j s => step_sum_le P hY0 hd₀ hZ0 (by positivity) hcard
        (prod_inv_Vg_le P hgrp (by linarith)) j s
  have hpaths := sum_wNon_bdd P Zb β hβ0 hstep P.N
  have hεq0 : 0 ≤ P.U * P.V * (30 * (((P.N + 1 : ℝ) * S₁) ^ T / (T.factorial : ℝ)) +
      P.x ^ (-η) * (2 * ((P.gPrimes.card : ℝ) + 1) ^ T * exp (log P.x ^ (0.98 : ℝ)) ^ 3 +
        4 * exp (log P.x ^ (0.98 : ℝ)) ^ 3 + 12000 * Zb +
        60 * (P.N : ℝ) * (4 * Tcb P (Pm + 1) * (2 * (4096 * Mtb P Pm + 1) + 1)) +
        2 * (P.N : ℝ) * (4 * Tcb P (Pm + 1) * (2 * (4096 * Mtb P Pm + 1) + 1)) *
          exp (log P.x ^ (0.98 : ℝ)) ^ 3)) := by
    have hT0 : 0 ≤ Tcb P (Pm + 1) := Tcb_nonneg P (by linarith) hY1
    have hM0 : 0 ≤ Mtb P Pm := Mtb_nonneg P (by linarith) hY1
    refine eq_nonneg (mul_nonneg hU.le hV.le) (div_nonneg (pow_nonneg (mul_nonneg
      (by linarith [(Nat.cast_nonneg P.N : (0 : ℝ) ≤ P.N)]) H.hS0) _) (Nat.cast_nonneg _))
      (rpow_nonneg hx0.le _) (pow_nonneg (by linarith [(Nat.cast_nonneg _ :
        (0 : ℝ) ≤ (P.gPrimes.card : ℝ))]) _) (pow_nonneg (exp_pos _).le _) hZ0 (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) hT0) (by linarith))
  refine (path_sum_bound P hεq0 hσ0 hbnd hz hpaths).trans ?_
  exact final_numeric P H (by positivity) hL1 hLl hx0 hLdef (by rw [← hLdef, hL98])
    hσ0 (stateNorm_le P hgrp (by linarith)) (Nat.cast_nonneg _) (card_listCands_le P hcard)

/-- **D7r** ([21] Lemma 3.4, root replacement), for every `δ > 0`. -/
theorem root_replacement (δ c₁ c₂ : ℝ) (hδ : 0 < δ) : L102D.RootReplacementStmt δ c₁ c₂ := by
  intro A hA A₀ _ K _ a _ ha_range
  obtain ⟨c, hc, x₁, hRC⟩ := rootCount2At_of hδ
  set η := min (c / 2) (2 * δ) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hl00 : 0 ≤ Num.l0 K A η := by
    unfold Num.l0; have : 0 ≤ (400 + 400 * A) / η := by positivity
    positivity
  refine ⟨max (max x₁ (exp (Num.l0 K A η ^ 100))) 1,
    fun x Hm Hn hx hHm hHn _ _ Y hY k => ?_⟩
  intro P
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxl : exp (Num.l0 K A η ^ 100) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx0 : 0 < x := by linarith
  have hxδ : 0 < x ^ δ := rpow_pos_of_pos hx0 δ
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hU : x ^ δ ≤ 2 ^ k * Y * Hm := by
    have : (1 : ℝ) ≤ 2 ^ k * Y := by nlinarith
    nlinarith
  have hUpos : 0 < P.U := by show 0 < 2 ^ k * Y * Hm; linarith
  have hVpos : 0 < P.V := by show 0 < Hn; linarith
  have hUV : P.x ^ (2 * δ) ≤ P.U * P.V := by
    show x ^ (2 * δ) ≤ 2 ^ k * Y * Hm * Hn
    rw [two_mul, rpow_add hx0]
    exact mul_le_mul hU hHn hxδ.le (by linarith)
  have hl : Num.l0 P.K A (min (c / 2) (2 * δ)) ≤ log P.x ^ ((1 : ℝ) / 100) := by
    show Num.l0 K A η ≤ log x ^ ((1 : ℝ) / 100)
    have h1 : Num.l0 K A η ^ 100 ≤ log x := by
      have := log_le_log (exp_pos _) hxl
      rwa [log_exp] at this
    calc Num.l0 K A η = (Num.l0 K A η ^ 100) ^ ((1 : ℝ) / 100) := by
          rw [← rpow_natCast, ← rpow_mul hl00]; norm_num
      _ ≤ log x ^ ((1 : ℝ) / 100) := rpow_le_rpow (by positivity) h1 (by norm_num)
  exact main_bound P hA hc hδ hx1 (hRC x hxx₁ _ _ hU hHn) hUpos hVpos hUV hY
    (by show 0 < 2 ^ k; positivity) rfl rfl (fun i => (ha_range i).2.le) hl

end ArtinPrimitiveRoots.L102E
end

section
/-! Check module: `chk_norm_sum_pathPhi_sub_integral_rootIL_le_of_pos`, the published statement
`norm_sum_pathPhi_sub_integral_rootIL_le_of_pos` verbatim, proved from the development and
the cut `abs_card_specialLinearGroup_box_sub_le` ([21] Lemma 3.3). Without `0 < δ` the box
`U = 2^k Y Hm` may be subpolynomial in `x` and Lemma 3.3 does not apply. -/

namespace ArtinPrimitiveRoots

open Real Finset


end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real Finset
theorem solution (δ c₁ c₂ : ℝ) (hδ : 0 < δ) :
    ∀ A : ℝ, 0 < A → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          let P := dyadParams x a A₀ Y Hm Hn k
          ‖∑ P₀ ∈ posBox P.U P.V, P.pathPhi (rootOf P₀) (physDelta P₀) -
              ((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) *
                ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
                  P.rootIL (P.U * u, P.V * v, r)‖ ≤
            P.U * P.V * log x ^ (-(A * P.N)) :=
  L102E.root_replacement δ c₁ c₂ hδ
end
