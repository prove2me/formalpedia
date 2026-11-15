-- Prove2me | Definitions.Def_RPLib_S4_SwanAS
-- name    : RPLib_S4_SwanAS
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:28:23.294718+00:00
-- url     : https://prove2.me/theorems/72cdbe98-77ac-478a-ab04-546cd4417704
-- title:
--   Artin-Schreier elements have a single ramification jump
-- statement:
--   For local data with group $G$, suppose $\sigma y = y + c$ with $v(c) = 0$, $v(y) = -N$ ($N \ge 1$), and that $x y^b$ is a uniformiser for some $\sigma$-fixed $x$ and some $b$ with $v(b) = 0$ (possible when $p \nmid N$). The file proves $$i(\sigma) = v(\sigma\varpi - \varpi) = N + 1,$$ and, for a ramification function constant on nontrivial elements, $i(\sigma) = N + 1$ for all $\sigma \ne 1$, that there is a single lower and upper ramification jump at $N$; it computes $\varphi$ and the upper groups for such constant functions, and shows that every nontrivial character of $G$ then has all breaks $N$ and Swan conductor $N$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), doi:10.1007/978-1-4757-5673-9, Chapter IV, Section 2, Exercise; N. M. Katz, Gauss Sums, Kloosterman Sums, and Monodromy Groups, Annals of Mathematics Studies 116, Princeton University Press (1988), Chapter 1

import Mathlib
import Definitions.Def_RPLib_S4_SwanLoc
import Definitions.Def_RPLib_S4_SwanBrk

/-!
# S4-Swan (K2), part 11: Artin-Schreier elements have one ramification jump

`LocData.ramFn_i_of_as`: if `σ y = y + c` with `v c = 0`, `v y = -N` (`N ≥ 1`), and `x y^b` is a uniformizer
for some `σ`-fixed `x` and some `b` with `v b = 0` (`p ∤ b`), then `i(σ) = N + 1` (the `L_ψ(f)` computation at
`∞`, `N = deg f`). `RamFn.ConstI R N` (every `σ ≠ 1` has `i σ = N + 1`) gives `G_u = G` for `u ≤ N`,
`G_{N+1} = 1`, `φ(m) = m` for `m ≤ N`, `G^v = G` exactly for `v ≤ N`, `Sw(ρ) = N codim V^G`, and every character
nontrivial on `G` has all breaks `N` (`ConstI.chiAllBrk`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace Swan

noncomputable section

section Val

variable {L : Type*} [Field L] (v : AddValuation L (WithTop ℤ))

theorem v_natCast_nonneg (n : ℕ) : 0 ≤ v (n : L) := by
  induction n with
  | zero => rw [Nat.cast_zero, AddValuation.map_zero]; exact le_top
  | succ n ih => rw [Nat.cast_succ]; exact v.map_le_add ih (by rw [AddValuation.map_one])

theorem coe_lt_coe_add {a : ℤ} {t : WithTop ℤ} (ht : 1 ≤ t) : (a : WithTop ℤ) < a + t := by
  induction t with
  | top => rw [WithTop.add_top]; exact WithTop.coe_lt_top a
  | coe m =>
    have hm : 1 ≤ m := by exact_mod_cast ht
    rw [← WithTop.coe_add]; exact_mod_cast (by omega : a < a + m)

theorem exists_one_add_pow {u : L} (hu : 0 ≤ v u) :
    ∀ b : ℕ, ∃ w : L, 0 ≤ v w ∧ (1 + u) ^ b = 1 + (b : L) * u + u ^ 2 * w
  | 0 => ⟨0, by rw [AddValuation.map_zero]; exact le_top, by simp⟩
  | b + 1 => by
    obtain ⟨w, hw, h⟩ := exists_one_add_pow hu b
    refine ⟨b + w + u * w, v.map_le_add (v.map_le_add (v_natCast_nonneg v b) hw) ?_, ?_⟩
    · rw [AddValuation.map_mul]; exact add_nonneg hu hw
    · rw [pow_succ, h]; push_cast; ring

/-- `v((1 + u)^b - 1) = v(u)` when `v u ≥ 1` and `v b = 0`. -/
theorem v_one_add_pow_sub_one {u : L} {N b : ℕ} (hu : v u = ((N : ℤ) : WithTop ℤ)) (hN : 1 ≤ N)
    (hb : v (b : L) = 0) : v ((1 + u) ^ b - 1) = ((N : ℤ) : WithTop ℤ) := by
  have hu0 : 0 ≤ v u := by rw [hu]; exact_mod_cast Int.natCast_nonneg N
  obtain ⟨w, hw, h⟩ := exists_one_add_pow v hu0 b
  have h1 : (1 + u) ^ b - 1 = (b : L) * u + u * (u * w) := by rw [h]; ring
  have h2 : v ((b : L) * u) = ((N : ℤ) : WithTop ℤ) := by rw [AddValuation.map_mul, hb, hu, zero_add]
  have h3 : (1 : WithTop ℤ) ≤ v (u * w) := by
    rw [AddValuation.map_mul, hu]
    calc (1 : WithTop ℤ) ≤ ((N : ℤ) : WithTop ℤ) := by exact_mod_cast hN
      _ ≤ ((N : ℤ) : WithTop ℤ) + v w := le_add_of_nonneg_right hw
  have h4 : v ((b : L) * u) < v (u * (u * w)) := by
    rw [h2, AddValuation.map_mul v u, hu]; exact coe_lt_coe_add h3
  rw [h1, AddValuation.map_add_eq_of_lt_left v h4, h2]

end Val

namespace LocData

variable {G L : Type*} [Group G] [Field L] [MulSemiringAction G L] (D : LocData G L)

/-- **Artin-Schreier jump**: `σ y = y + c`, `v c = 0`, `v y = -N`, `x y^b` a uniformizer with `σ x = x` and
`v b = 0` give `i(σ) = N + 1`. -/
theorem ramFn_i_of_as {σ : G} {x y c : L} {N b : ℕ} (hN : 1 ≤ N) (hx : σ • x = x) (hy : σ • y = y + c)
    (hc : D.v c = 0) (hyv : D.v y = ((-(N : ℤ) : ℤ) : WithTop ℤ)) (hb : D.v (b : L) = 0)
    (hϖ : D.v (x * y ^ b) = 1) : D.ramFn.i σ = (N + 1 : ℕ) := by
  have hy0 : y ≠ 0 := fun h => by
    rw [h, AddValuation.map_zero] at hyv; exact WithTop.top_ne_coe hyv
  set u := c * y⁻¹ with hu
  have huv : D.v u = ((N : ℤ) : WithTop ℤ) := by
    rw [hu, AddValuation.map_mul, hc, zero_add, AddValuation.map_inv, hyv,
      ← WithTop.LinearOrderedAddCommGroup.coe_neg, neg_neg]
  have hyc : y + c = y * (1 + u) := by
    rw [hu, mul_add, mul_one, ← mul_assoc, mul_comm y c, mul_assoc, mul_inv_cancel₀ hy0, mul_one]
  have hσ : σ • (x * y ^ b) - x * y ^ b = (x * y ^ b) * ((1 + u) ^ b - 1) := by
    rw [smul_mul', smul_pow', hx, hy, hyc, mul_pow]; ring
  rw [D.ramFn_i_of_unif hϖ σ, hσ, AddValuation.map_mul, hϖ, v_one_add_pow_sub_one D.v huv hN hb,
    ← WithTop.coe_one, ← WithTop.coe_add, toENat_coe]
  congr 1; omega

end LocData

namespace RamFn

variable {G : Type*} [Group G] [Fintype G] {R : RamFn G}

/-- One jump at `N`: every `σ ≠ 1` has `i σ = N + 1`. -/
def ConstI (R : RamFn G) (N : ℕ) : Prop := ∀ σ : G, σ ≠ 1 → R.i σ = (N + 1 : ℕ)

variable {N : ℕ} (hR : R.ConstI N)
include hR

theorem ConstI.lower_of_le {u : ℕ} (hu : u ≤ N) : R.lower u = ⊤ :=
  eq_top_iff.2 fun σ _ => by
    by_cases h : σ = 1
    · subst h; exact (R.lower u).one_mem
    · rw [mem_lower, hR σ h]; exact Nat.cast_le.2 (by omega)

theorem ConstI.lower_of_lt {u : ℕ} (hu : N < u) : R.lower u = ⊥ :=
  eq_bot_iff.2 fun σ hσ => by
    rw [Subgroup.mem_bot]
    by_contra h
    rw [mem_lower, hR σ h, Nat.cast_le] at hσ
    omega

theorem ConstI.jdx_eq {σ : G} (h : σ ≠ 1) : R.jdx σ = N := by
  rw [jdx, hR σ h, ENat.toNat_natCast]; omega

theorem ConstI.top_le : R.top ≤ N := Finset.sup_le fun σ _ => by
  by_cases h : σ = 1
  · subst h; rw [jdx, R.i_one, ENat.toNat_top]; omega
  · rw [hR.jdx_eq h]

theorem ConstI.card_div : (Nat.card (⊤ : Subgroup G) : ℚ) / Nat.card G = 1 := by
  rw [Subgroup.card_top]; exact div_self (cardG_pos (G := G)).ne'

theorem ConstI.phi_of_le {m : ℕ} (hm : m ≤ N) : R.phi m = m := by
  have h : ∀ u ∈ Finset.range m, (Nat.card (R.lower (u + 1)) : ℚ) / Nat.card G = 1 := by
    intro u hu
    rw [hR.lower_of_le (by have := Finset.mem_range.1 hu; omega), hR.card_div]
  rw [R.phi_eq_sum, Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem ConstI.mem_upper {σ : G} (h : σ ≠ 1) (v : ℚ) : σ ∈ R.upper v ↔ v ≤ N := by
  rw [R.mem_upper h, hR.jdx_eq h, hR.phi_of_le le_rfl]

theorem ConstI.upper_of_le {v : ℚ} (hv : v ≤ N) : R.upper v = ⊤ :=
  eq_top_iff.2 fun σ _ => by
    by_cases h : σ = 1
    · subst h; exact (R.upper v).one_mem
    · exact (hR.mem_upper h v).2 hv

theorem ConstI.upper_of_lt {v : ℚ} (hv : (N : ℚ) < v) : R.upper v = ⊥ :=
  eq_bot_iff.2 fun σ hσ => by
    rw [Subgroup.mem_bot]
    by_contra h
    exact absurd ((hR.mem_upper h v).1 hσ) (not_le.2 hv)

theorem ConstI.swan {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V) :
    R.swan ρ = N * cod ρ ⊤ := by
  have h : ∀ u ∈ Finset.range N,
      (Nat.card (R.lower (u + 1)) : ℚ) / Nat.card G * cod ρ (R.lower (u + 1)) = cod ρ ⊤ := by
    intro u hu
    rw [hR.lower_of_le (by have := Finset.mem_range.1 hu; omega), hR.card_div, one_mul]
  rw [R.swan_eq_range ρ hR.top_le, Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/-- A character nontrivial on `G` has all breaks `N`. -/
theorem ConstI.chiAllBrk {k : Type*} [Field k] (χ : G →* kˣ) (hχ : ∃ σ, χ σ ≠ 1) :
    R.ChiAllBrk χ N := by
  refine ⟨fun v hv σ hσ => ?_, ?_⟩
  · rw [hR.upper_of_lt hv, Subgroup.mem_bot] at hσ
    rw [hσ, map_one]
  · obtain ⟨σ, hσ⟩ := hχ
    have h1 : σ ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    exact ⟨σ, (hR.mem_upper h1 N).2 le_rfl, hσ⟩

end RamFn

end

end Swan
end RamanujanPetersson


