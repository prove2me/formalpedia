-- Prove2me | Definitions.Def_HodgeComputerFormal_LaurentJets
-- name    : HodgeComputerFormal_LaurentJets
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T03:31:36.3258+00:00
-- url     : https://prove2.me/theorems/60bbd37e-3fdf-485a-8efa-56d938fd22ea
-- title:
--   First-order dual numbers `Dual R`, formal quadratic root series, and Laurent valuation jets
-- statement:
--   Reusable local expansion and jet calculus over any field $K$:
--
--   - First-order dual numbers `Dual R` ($a + b \varepsilon$, $\varepsilon^2 = 0$) as a commutative ring with chain-rule evaluation of polynomials.
--   - Formal power-series Hensel root solver `quadRootSeries` solving $r^2 + b r + c = 0$ in $K[\![t]\!]$ whenever $b_0 \neq 0$ and $c_0 = 0$.
--   - Laurent valuation predicates `HasValGe k f`, `ValLead k f c`, and `ValDual k f d` on `LaurentSeries K`, together with full arithmetic closure laws (addition, multiplication, powers, division by nonvanishing leading terms) and polynomial evaluators `evalT` and `evalInvT`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/formal/lean/QuadraticCovers/LaurentJets.lean

import Definitions.Def_HodgeComputerFormal_PairAlgebra
import Mathlib.RingTheory.LaurentSeries

set_option autoImplicit false

/-! Formal Laurent series valuation and first-order jet calculus over any field `K`:
1. Dual numbers `Dual R = R[ε]/(ε^2)` with fast definitional projections and `invOfNe`.
2. Explicit Hensel power-series root `quadRootSeries b c` of `r^2 + b * r + c = 0`.
3. Laurent valuation predicate `HasValGe k f`, polynomial embeddings `evalT` and `evalInvT`,
   and the packaged leading-term (`ValLead`) and two-term (`ValDual`) jet predicates.

Extracted from the `symmetric-sextic-residual` construction (`benediamond`). -/

noncomputable section
namespace QuadraticCovers
open Polynomial
open scoped BigOperators LaurentSeries PowerSeries

/-- Minimal dual numbers `R[ε]/(ε^2)` with fast definitional projections. -/
@[ext]
structure Dual (R : Type*) where
  val : R
  eps : R

namespace Dual

section RingOps
variable {R : Type*} [CommRing R]

instance : Zero (Dual R) := ⟨⟨0, 0⟩⟩
instance : One (Dual R) := ⟨⟨1, 0⟩⟩
instance : Add (Dual R) := ⟨fun x y => ⟨x.val + y.val, x.eps + y.eps⟩⟩
instance : Sub (Dual R) := ⟨fun x y => ⟨x.val - y.val, x.eps - y.eps⟩⟩
instance : Neg (Dual R) := ⟨fun x => ⟨-x.val, -x.eps⟩⟩
instance : Mul (Dual R) := ⟨fun x y => ⟨x.val * y.val, x.val * y.eps + x.eps * y.val⟩⟩

@[simp] lemma zero_val : (0 : Dual R).val = 0 := rfl
@[simp] lemma zero_eps : (0 : Dual R).eps = 0 := rfl
@[simp] lemma one_val : (1 : Dual R).val = 1 := rfl
@[simp] lemma one_eps : (1 : Dual R).eps = 0 := rfl
@[simp] lemma add_val (x y : Dual R) : (x + y).val = x.val + y.val := rfl
@[simp] lemma add_eps (x y : Dual R) : (x + y).eps = x.eps + y.eps := rfl
@[simp] lemma sub_val (x y : Dual R) : (x - y).val = x.val - y.val := rfl
@[simp] lemma sub_eps (x y : Dual R) : (x - y).eps = x.eps - y.eps := rfl
@[simp] lemma neg_val (x : Dual R) : (-x).val = -x.val := rfl
@[simp] lemma neg_eps (x : Dual R) : (-x).eps = -x.eps := rfl
@[simp] lemma mul_val (x y : Dual R) : (x * y).val = x.val * y.val := rfl
@[simp] lemma mul_eps (x y : Dual R) : (x * y).eps = x.val * y.eps + x.eps * y.val := rfl

instance : CommRing (Dual R) where
  add_assoc a b c := by ext <;> simp [add_assoc]
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  neg_add_cancel a := by ext <;> simp
  add_comm a b := by ext <;> simp [add_comm]
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  mul_assoc a b c := by ext <;> simp <;> ring
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  mul_comm a b := by ext <;> simp [mul_comm, add_comm]

def C : R →+* Dual R where
  toFun c := ⟨c, 0⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp
  map_zero' := rfl
  map_add' a b := by ext <;> simp

@[simp] lemma C_val (c : R) : (C c).val = c := rfl
@[simp] lemma C_eps (c : R) : (C c).eps = 0 := rfl

lemma ofNat_val (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : Dual R).val = OfNat.ofNat n := by
  change ((n : ℕ) : Dual R).val = (n : R)
  rw [show ((n : ℕ) : Dual R) = C (n : R) from (map_natCast C n).symm]; rfl

lemma ofNat_eps (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : Dual R).eps = 0 := by
  change ((n : ℕ) : Dual R).eps = 0
  rw [show ((n : ℕ) : Dual R) = C (n : R) from (map_natCast C n).symm]; rfl

lemma pow_eq (x : Dual R) (n : ℕ) :
    x ^ n = ⟨x.val ^ n, (n : R) * x.val ^ (n - 1) * x.eps⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ k ih =>
    rw [pow_succ, ih]
    ext
    · simp [pow_succ]
    · cases k with
      | zero => simp
      | succ m =>
        simp only [mul_eps, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
        ring

lemma eval₂_eq (P : R[X]) (a e : R) :
    P.eval₂ C ⟨a, e⟩ = ⟨P.eval a, P.derivative.eval a * e⟩ := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [eval₂_add, hp, hq, eval_add, derivative_add, eval_add]
    ext
    · simp
    · simp; ring
  | monomial n c =>
    rw [eval₂_monomial, eval_monomial, derivative_monomial, eval_monomial, pow_eq]
    ext
    · simp
    · cases n with
      | zero => simp
      | succ m =>
        simp only [mul_eps, C_val, C_eps, zero_mul, add_zero, Nat.add_sub_cancel]
        ring

def invOfNe {F : Type*} [Field F] (x : Dual F) (_hx : x.val ≠ 0) : Dual F :=
  ⟨x.val⁻¹, -x.eps / x.val ^ 2⟩

lemma mul_invOfNe {F : Type*} [Field F] (x : Dual F) (hx : x.val ≠ 0) :
    x * invOfNe x hx = 1 := by
  ext
  · simp [invOfNe, mul_inv_cancel₀ hx]
  · simp only [mul_eps, invOfNe, one_eps]
    field_simp [hx]; ring

lemma invOfNe_mul {F : Type*} [Field F] (x : Dual F) (hx : x.val ≠ 0) :
    invOfNe x hx * x = 1 := by
  rw [mul_comm]; exact mul_invOfNe x hx

end RingOps
end Dual

section QuadRootAndVal
variable {K : Type*} [Field K]

/-- Recursive coefficient sequence of the formal root `r = O(t)` of `r^2 + b * r + c = 0`
when `b.coeff 0 ≠ 0` and `c.coeff 0 = 0`. -/
def quadRootCoeff (b c : PowerSeries K) : ℕ → K
  | 0 => 0
  | n + 1 =>
    -(PowerSeries.coeff (n + 1) c +
      ∑ j ∈ (Finset.Ico 1 (n + 1)).attach,
        (quadRootCoeff b c j.1 * quadRootCoeff b c (n + 1 - j.1) +
         PowerSeries.coeff (n + 1 - j.1) b * quadRootCoeff b c j.1)) /
      PowerSeries.coeff 0 b
termination_by n => n
decreasing_by
  all_goals
    have hj := Finset.mem_Ico.mp j.2
    omega

lemma quadRootCoeff_zero (b c : PowerSeries K) : quadRootCoeff b c 0 = 0 := by
  rw [quadRootCoeff]

lemma quadRootCoeff_succ (b c : PowerSeries K) (n : ℕ) :
    quadRootCoeff b c (n + 1) =
      -(PowerSeries.coeff (n + 1) c +
        ∑ j ∈ Finset.Ico 1 (n + 1),
          (quadRootCoeff b c j * quadRootCoeff b c (n + 1 - j) +
           PowerSeries.coeff (n + 1 - j) b * quadRootCoeff b c j)) /
        PowerSeries.coeff 0 b := by
  rw [quadRootCoeff]
  congr 3
  exact Finset.sum_attach (Finset.Ico 1 (n + 1)) (fun j =>
    quadRootCoeff b c j * quadRootCoeff b c (n + 1 - j) +
    PowerSeries.coeff (n + 1 - j) b * quadRootCoeff b c j)

def quadRootSeries (b c : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk (quadRootCoeff b c)

lemma quadRootSeries_coeff_zero (b c : PowerSeries K) :
    PowerSeries.coeff 0 (quadRootSeries b c) = 0 := by
  rw [quadRootSeries, PowerSeries.coeff_mk, quadRootCoeff_zero]

lemma quadRootSeries_coeff_one (b c : PowerSeries K) :
    PowerSeries.coeff 1 (quadRootSeries b c) =
      -PowerSeries.coeff 1 c / PowerSeries.coeff 0 b := by
  rw [quadRootSeries, PowerSeries.coeff_mk, quadRootCoeff_succ]
  simp

lemma quadRootSeries_coeff_two (b c : PowerSeries K) :
    PowerSeries.coeff 2 (quadRootSeries b c) =
      -(PowerSeries.coeff 2 c +
        quadRootCoeff b c 1 * quadRootCoeff b c 1 +
        PowerSeries.coeff 1 b * quadRootCoeff b c 1) / PowerSeries.coeff 0 b := by
  rw [quadRootSeries, PowerSeries.coeff_mk, quadRootCoeff_succ]
  have hico : Finset.Ico 1 2 = {1} := by decide
  rw [hico, Finset.sum_singleton]
  ring

theorem quadRootSeries_eq_zero (b c : PowerSeries K)
    (hb : PowerSeries.coeff 0 b ≠ 0) (hc : PowerSeries.coeff 0 c = 0) :
    quadRootSeries b c ^ 2 + b * quadRootSeries b c + c = 0 := by
  let r := quadRootSeries b c
  have hr0 : PowerSeries.coeff 0 r = 0 := quadRootSeries_coeff_zero b c
  ext n
  rw [map_zero, map_add, map_add, sq, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff] at hr0 hc
    simp [r, hr0, hc]
  | succ m =>
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i r * PowerSeries.coeff j r),
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => PowerSeries.coeff i b * PowerSeries.coeff j r)]
    have hsplit_r : ∑ k ∈ Finset.range (m + 2), PowerSeries.coeff k r * PowerSeries.coeff (m + 1 - k) r =
        ∑ j ∈ Finset.Ico 1 (m + 1), quadRootCoeff b c j * quadRootCoeff b c (m + 1 - j) := by
      rw [Finset.sum_range_succ, Nat.sub_self, hr0, mul_zero, add_zero]
      rw [Finset.sum_range_eq_add_Ico _ (by omega : 1 ≤ m + 1)]
      simp only [hr0, zero_mul, zero_add]
      apply Finset.sum_congr rfl; intro j _
      simp [r, quadRootSeries]
    have hsplit_b : ∑ k ∈ Finset.range (m + 2), PowerSeries.coeff k b * PowerSeries.coeff (m + 1 - k) r =
        PowerSeries.coeff 0 b * quadRootCoeff b c (m + 1) +
        ∑ j ∈ Finset.Ico 1 (m + 1), PowerSeries.coeff (m + 1 - j) b * quadRootCoeff b c j := by
      rw [Finset.sum_range_succ, Nat.sub_self, hr0, mul_zero, add_zero]
      rw [Finset.sum_range_eq_add_Ico _ (by omega : 1 ≤ m + 1)]
      simp only [Nat.sub_zero, r, quadRootSeries, PowerSeries.coeff_mk]
      congr 1
      refine Finset.sum_bij (fun k _ => m + 1 - k) ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
      · intro k1 hk1 k2 hk2 h; simp only [Finset.mem_Ico] at hk1 hk2; omega
      · intro j hj; refine ⟨m + 1 - j, ?_, ?_⟩
        · simp only [Finset.mem_Ico] at hj ⊢; omega
        · simp only [Finset.mem_Ico] at hj; omega
      · intro k hk
        simp only [Finset.mem_Ico] at hk
        rw [show m + 1 - (m + 1 - k) = k by omega]
    rw [hsplit_r, hsplit_b, quadRootCoeff_succ, Finset.sum_add_distrib]
    field_simp [hb]
    ring

/-- Predicate asserting that a Laurent series has valuation `≥ k` (all coefficients `< k` vanish). -/
def HasValGe (k : ℤ) (f : LaurentSeries K) : Prop :=
  ∀ n : ℤ, n < k → f.coeff n = 0

lemma HasValGe.mono {k1 k2 : ℤ} {f : LaurentSeries K} (hle : k2 ≤ k1) (hf : HasValGe k1 f) :
    HasValGe k2 f := fun n hn => hf n (lt_of_lt_of_le hn hle)

lemma HasValGe.zero (k : ℤ) : HasValGe k (0 : LaurentSeries K) := fun _ _ => rfl

lemma HasValGe.add {k : ℤ} {f g : LaurentSeries K} (hf : HasValGe k f) (hg : HasValGe k g) :
    HasValGe k (f + g) := fun n hn => by simp [hf n hn, hg n hn]

lemma HasValGe.sub {k : ℤ} {f g : LaurentSeries K} (hf : HasValGe k f) (hg : HasValGe k g) :
    HasValGe k (f - g) := fun n hn => by simp [hf n hn, hg n hn]

lemma HasValGe.neg {k : ℤ} {f : LaurentSeries K} (hf : HasValGe k f) :
    HasValGe k (-f) := fun n hn => by simp [hf n hn]

lemma HasValGe.mul {k l : ℤ} {f g : LaurentSeries K} (hf : HasValGe k f) (hg : HasValGe l g) :
    HasValGe (k + l) (f * g) := by
  intro n hn
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rcases p with ⟨i, j⟩
  rw [Finset.mem_antidiagonal] at hp
  by_cases hi : i < k
  · simp [hf i hi]
  · have hj : j < l := by omega
    simp [hg j hj]

lemma HasValGe.of_powerSeries (p : PowerSeries K) :
    HasValGe 0 ((p : PowerSeries K) : LaurentSeries K) := by
  intro n hn
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨m, hm⟩
  change (m : ℤ) = n at hm
  omega

lemma HasValGe.of_powerSeries_ge {p : PowerSeries K} {k : ℕ}
    (hp : ∀ j < k, PowerSeries.coeff j p = 0) :
    HasValGe (k : ℤ) ((p : PowerSeries K) : LaurentSeries K) := by
  intro n hn
  by_cases hneg : n < 0
  · exact HasValGe.of_powerSeries p n hneg
  · set m : ℕ := n.toNat
    have hnm : n = (m : ℤ) := by omega
    rw [hnm, LaurentSeries.coeff_coe_powerSeries]
    exact hp m (by omega)

lemma HasValGe.of_C (c : K) : HasValGe 0 (HahnSeries.C c : LaurentSeries K) := by
  intro n hn
  rw [HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs with h
  · omega
  · rfl

lemma HasValGe.of_nat (m : ℕ) : HasValGe 0 (m : LaurentSeries K) := by
  have : (m : LaurentSeries K) = HahnSeries.C (m : K) := by simp
  rw [this]; exact HasValGe.of_C (m : K)

lemma HasValGe.single (k : ℤ) (c : K) : HasValGe k (HahnSeries.single k c : LaurentSeries K) := by
  intro n hn
  rw [HahnSeries.coeff_single]
  split_ifs with h
  · omega
  · rfl

lemma HasValGe.pow {k : ℤ} {f : LaurentSeries K} (hf : HasValGe k f) (m : ℕ) :
    HasValGe (m * k) (f ^ m) := by
  induction m with
  | zero => simpa using HasValGe.of_C (1 : K)
  | succ m ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact ih.mul hf

lemma HasValGe.coeff_of_add {k : ℤ} {f g : LaurentSeries K} (hg : HasValGe (k + 1) g) :
    (f + g).coeff k = f.coeff k := by
  simp [hg k (by omega)]

lemma HasValGe.inc {k : ℤ} {f : LaurentSeries K} (hf : HasValGe k f) (hk : f.coeff k = 0) :
    HasValGe (k + 1) f := fun n hn => by
  by_cases h : n = k
  · subst h; exact hk
  · exact hf n (by omega)

lemma HasValGe.coeff_mul_min {k l : ℤ} {f g : LaurentSeries K} (hf : HasValGe k f) (hg : HasValGe l g) :
    (f * g).coeff (k + l) = f.coeff k * g.coeff l := by
  rw [HahnSeries.coeff_mul]
  by_cases hmem : (k, l) ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support (k + l)
  · rw [Finset.sum_eq_single (k, l)]
    · rintro ⟨i, j⟩ hij hne
      rw [Finset.mem_antidiagonal] at hij
      by_cases hi : i < k
      · simp [hf i hi]
      · have hj : j < l := by
          by_contra hge
          have : i = k ∧ j = l := by omega
          exact hne (Prod.ext this.1 this.2)
        simp [hg j hj]
    · intro h; exact absurd hmem h
  · rw [Finset.mem_antidiagonal] at hmem
    have hzero : f.coeff k * g.coeff l = 0 := by
      by_cases hfk : f.coeff k = 0
      · simp [hfk]
      · by_cases hgl : g.coeff l = 0
        · simp [hgl]
        · exact absurd ⟨hfk, hgl, rfl⟩ hmem
    rw [hzero]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij
    by_cases hi : i < k
    · simp [hf i hi]
    · by_cases hj : j < l
      · simp [hg j hj]
      · obtain ⟨rfl, rfl⟩ : i = k ∧ j = l := by omega
        exact absurd ⟨hij.1, hij.2.1, rfl⟩ hmem

lemma HasValGe.coeff_pow_min {k : ℤ} {f : LaurentSeries K} (hf : HasValGe k f) (m : ℕ) :
    (f ^ m).coeff (m * k) = f.coeff k ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      (hf.pow m).coeff_mul_min hf, ih, pow_succ]

lemma HasValGe.coeff_mul_min_plus_one {k l : ℤ} {f g : LaurentSeries K}
    (hf : HasValGe k f) (hg : HasValGe l g) :
    (f * g).coeff (k + l + 1) = f.coeff k * g.coeff (l + 1) + f.coeff (k + 1) * g.coeff l := by
  rw [HahnSeries.coeff_mul]
  let S := Finset.antidiagonal f.isPWO_support g.isPWO_support (k + l + 1)
  have hsub : ∀ p ∈ S, p ≠ (k, l + 1) → p ≠ (k + 1, l) → f.coeff p.1 * g.coeff p.2 = 0 := by
    rintro ⟨i, j⟩ hp h1 h2
    rw [Finset.mem_antidiagonal] at hp
    by_cases hi : i < k
    · simp [hf i hi]
    · by_cases hj : j < l
      · simp [hg j hj]
      · have hcases : (i = k ∧ j = l + 1) ∨ (i = k + 1 ∧ j = l) := by omega
        rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd rfl h1
        · exact absurd rfl h2
  have hsplit : ∑ p ∈ S, f.coeff p.1 * g.coeff p.2 =
      (if (k, l + 1) ∈ S then f.coeff k * g.coeff (l + 1) else 0) +
      (if (k + 1, l) ∈ S then f.coeff (k + 1) * g.coeff l else 0) := by
    let T : Finset (ℤ × ℤ) := {(k, l + 1), (k + 1, l)}
    have h1 : ∑ p ∈ S, f.coeff p.1 * g.coeff p.2 = ∑ p ∈ S ∩ T, f.coeff p.1 * g.coeff p.2 := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro p hp hnot
      simp only [Finset.mem_inter, T, Finset.mem_insert, Finset.mem_singleton, not_and, not_or] at hnot
      exact hsub p hp (hnot hp).1 (hnot hp).2
    rw [h1]
    have hne : (k, l + 1) ≠ (k + 1, l) := by intro h; have := congrArg Prod.fst h; omega
    have h2 : ∑ p ∈ S ∩ T, f.coeff p.1 * g.coeff p.2 =
        ∑ p ∈ T, if p ∈ S then f.coeff p.1 * g.coeff p.2 else 0 := by
      rw [← Finset.sum_filter]
      congr 1; ext p; simp [and_comm]
    rw [h2, Finset.sum_pair hne]
  rw [hsplit]
  have ha : (if (k, l + 1) ∈ S then f.coeff k * g.coeff (l + 1) else 0) = f.coeff k * g.coeff (l + 1) := by
    split_ifs with h
    · rfl
    · simp only [S, Finset.mem_antidiagonal, HahnSeries.mem_support, not_and] at h
      by_cases hf0 : f.coeff k = 0
      · simp [hf0]
      · by_cases hg0 : g.coeff (l + 1) = 0
        · simp [hg0]
        · exact absurd (by omega) (h hf0 hg0)
  have hb : (if (k + 1, l) ∈ S then f.coeff (k + 1) * g.coeff l else 0) = f.coeff (k + 1) * g.coeff l := by
    split_ifs with h
    · rfl
    · simp only [S, Finset.mem_antidiagonal, HahnSeries.mem_support, not_and] at h
      by_cases hf0 : f.coeff (k + 1) = 0
      · simp [hf0]
      · by_cases hg0 : g.coeff l = 0
        · simp [hg0]
        · exact absurd (by omega) (h hf0 hg0)
  rw [ha, hb]

lemma eq_ofPowerSeries_of_HasValGe_zero {f : LaurentSeries K} (hf : HasValGe 0 f) :
    f = ((PowerSeries.mk (fun n : ℕ => f.coeff (n : ℤ)) : PowerSeries K) : LaurentSeries K) := by
  ext n
  by_cases hn : n < 0
  · rw [hf n hn, HasValGe.of_powerSeries _ n hn]
  · set m : ℕ := n.toNat
    have hnm : n = (m : ℤ) := by omega
    rw [hnm, LaurentSeries.coeff_coe_powerSeries, PowerSeries.coeff_mk]

lemma HasValGe.inv_of_lead_ne {l : ℤ} {g : LaurentSeries K}
    (hg : HasValGe l g) (hl : g.coeff l ≠ 0) :
    HasValGe (-l) g⁻¹ ∧ g⁻¹.coeff (-l) = (g.coeff l)⁻¹ := by
  let p : LaurentSeries K := HahnSeries.single (-l) (1 : K) * g
  have hp0 : HasValGe 0 p := by
    have h := (HasValGe.single (-l) (1 : K)).mul hg
    simpa only [neg_add_cancel] using h
  have hp_c0 : p.coeff 0 = g.coeff l := by
    have h := (HasValGe.single (-l) (1 : K)).coeff_mul_min hg
    simp only [neg_add_cancel, HahnSeries.coeff_single_same, one_mul] at h
    exact h
  let ps : PowerSeries K := PowerSeries.mk (fun n : ℕ => p.coeff (n : ℤ))
  have hp_eq : p = ((ps : PowerSeries K) : LaurentSeries K) := eq_ofPowerSeries_of_HasValGe_zero hp0
  have hunit : IsUnit ps := PowerSeries.isUnit_iff_constantCoeff.mpr (by
    refine isUnit_iff_ne_zero.mpr ?_
    change (PowerSeries.constantCoeff ps) ≠ 0
    dsimp only [ps]
    rw [PowerSeries.constantCoeff_mk]
    simpa [hp_c0] using hl)
  obtain ⟨u, hu⟩ := hunit
  let q : LaurentSeries K := ((↑u⁻¹ : PowerSeries K) : LaurentSeries K)
  have hpq : p * q = 1 := by
    rw [hp_eq]
    dsimp only [q]
    rw [← map_mul (HahnSeries.ofPowerSeries ℤ K), ← hu, Units.mul_inv, map_one]
  have hg_eq : g = HahnSeries.single l (1 : K) * p := by
    dsimp only [p]
    rw [← mul_assoc, HahnSeries.single_mul_single, add_neg_cancel, mul_one]
    change g = 1 * g; rw [one_mul]
  have hginv : g⁻¹ = HahnSeries.single (-l) (1 : K) * q := by
    have hgne : g ≠ 0 := fun h0 => hl (by rw [h0]; rfl)
    apply mul_left_cancel₀ hgne
    rw [mul_inv_cancel₀ hgne, hg_eq]
    symm
    calc HahnSeries.single l (1 : K) * p * (HahnSeries.single (-l) (1 : K) * q)
        = (HahnSeries.single l (1 : K) * HahnSeries.single (-l) (1 : K)) * (p * q) := by ring
      _ = 1 * 1 := by rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one, hpq]; rfl
      _ = 1 := one_mul 1
  have hq0 : HasValGe 0 q := HasValGe.of_powerSeries _
  have hval : HasValGe (-l) g⁻¹ := by
    rw [hginv]
    simpa only [add_zero] using (HasValGe.single (-l) (1 : K)).mul hq0
  have hc0 : g⁻¹.coeff (-l) = (g.coeff l)⁻¹ := by
    have h1 := hg.coeff_mul_min hval
    have hgne : g ≠ 0 := fun h0 => hl (by rw [h0]; rfl)
    rw [mul_inv_cancel₀ hgne, add_neg_cancel, HahnSeries.coeff_one] at h1
    simp only [ite_true] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  exact ⟨hval, hc0⟩

lemma HasValGe.div_of_lead_ne {k l : ℤ} {f g : LaurentSeries K}
    (hf : HasValGe k f) (hg : HasValGe l g) (hl : g.coeff l ≠ 0) :
    HasValGe (k - l) (f / g) ∧ (f / g).coeff (k - l) = f.coeff k / g.coeff l := by
  obtain ⟨hgi, hgic⟩ := hg.inv_of_lead_ne hl
  rw [div_eq_mul_inv, sub_eq_add_neg]
  refine ⟨hf.mul hgi, ?_⟩
  rw [hf.coeff_mul_min hgi, hgic, div_eq_mul_inv]

/-- Evaluation of `P : K[X]` at `t = single 1 1` in `LaurentSeries K`. -/
def evalT : K[X] →+* LaurentSeries K :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (1 : ℤ) (1 : K))

lemma evalT_C (c : K) : evalT (C c) = HahnSeries.C c := by
  simp [evalT]

lemma evalT_X : evalT (X : K[X]) = HahnSeries.single (1 : ℤ) (1 : K) := by
  simp [evalT]

lemma evalT_coeff (P : K[X]) (k : ℕ) : (evalT P).coeff (k : ℤ) = P.coeff k := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, evalT_C, evalT_X,
        HahnSeries.single_pow, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
        HahnSeries.coeff_single, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [one_pow, smul_eq_mul]
    by_cases h : k = n
    · subst h; simp
    · simp [h]

lemma HasValGe.evalT (P : K[X]) : HasValGe 0 (QuadraticCovers.evalT P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, evalT_C, evalT_X]
    have h1 := HasValGe.of_C c
    have h2 := (HasValGe.single (1 : ℤ) (1 : K)).pow n
    exact (h1.mul h2).mono (by omega)

lemma coeff_eq_zero_of_HasValGe_evalT {P : K[X]} {d : ℕ}
    (h : HasValGe (d : ℤ) (evalT P)) {k : ℕ} (hk : k < d) : P.coeff k = 0 := by
  rw [← evalT_coeff]
  exact h k (by exact_mod_cast hk)

/-- Evaluation of `P : K[X]` at `t⁻¹ = single (-1) 1` in `LaurentSeries K`. -/
def evalInvT : K[X] →+* LaurentSeries K :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1 : ℤ) (1 : K))

lemma evalInvT_C (c : K) : evalInvT (C c) = HahnSeries.C c := by
  simp [evalInvT]

lemma evalInvT_X : evalInvT (X : K[X]) = HahnSeries.single (-1 : ℤ) (1 : K) := by
  simp [evalInvT]

lemma evalInvT_coeff_neg (P : K[X]) (k : ℕ) : (evalInvT P).coeff (-(k : ℤ)) = P.coeff k := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, evalInvT_C, evalInvT_X,
        HahnSeries.single_pow, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
        HahnSeries.coeff_single, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    simp only [one_pow, smul_eq_mul]
    by_cases h : k = n
    · subst h; simp
    · simp [h]

lemma HasValGe.evalInvT_of_natDegree_le (P : K[X]) {d : ℕ} (hd : P.natDegree ≤ d) :
    HasValGe (-(d : ℤ)) (evalInvT P) := by
  intro n hn
  set k : ℕ := (-n).toNat
  have hnk : n = -(k : ℤ) := by omega
  have hkd : d < k := by omega
  rw [hnk, evalInvT_coeff_neg]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hkd)

lemma natDegree_le_of_HasValGe_evalInvT {P : K[X]} {d : ℕ}
    (h : HasValGe (-(d : ℤ)) (evalInvT P)) : P.natDegree ≤ d := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [← evalInvT_coeff_neg]
  exact h (-(k : ℤ)) (by omega)

lemma HasValGe.syl5 {q2 q1 q0 e3 e2 e1 e0 : LaurentSeries K}
    {vq2 vq1 vq0 ve3 ve2 ve1 ve0 v : ℤ}
    (hq2 : HasValGe vq2 q2) (hq1 : HasValGe vq1 q1) (hq0 : HasValGe vq0 q0)
    (he3 : HasValGe ve3 e3) (he2 : HasValGe ve2 e2) (he1 : HasValGe ve1 e1) (he0 : HasValGe ve0 e0)
    (h1 : v ≤ 3 * vq0 + 2 * ve3)
    (h2 : v ≤ vq1 + 2 * vq0 + ve3 + ve2)
    (h3 : v ≤ vq2 + 2 * vq0 + 2 * ve2)
    (h4 : v ≤ 2 * vq1 + vq0 + ve3 + ve1)
    (h5 : v ≤ vq2 + 2 * vq0 + ve3 + ve1)
    (h6 : v ≤ vq2 + vq1 + vq0 + ve2 + ve1)
    (h7 : v ≤ 2 * vq2 + vq0 + 2 * ve1)
    (h8 : v ≤ 3 * vq1 + ve3 + ve0)
    (h9 : v ≤ vq2 + vq1 + vq0 + ve3 + ve0)
    (h10 : v ≤ vq2 + 2 * vq1 + ve2 + ve0)
    (h11 : v ≤ 2 * vq2 + vq0 + ve2 + ve0)
    (h12 : v ≤ 2 * vq2 + vq1 + ve1 + ve0)
    (h13 : v ≤ 3 * vq2 + 2 * ve0) :
    HasValGe v (QuadraticCovers.syl5 q2 q1 q0 e3 e2 e1 e0) := by
  rw [QuadraticCovers.syl5]
  refine ((((((((((((((hq0.pow 3).mul (he3.pow 2)).mono (by omega)).sub
    ((((hq1.mul (hq0.pow 2)).mul he3).mul he2).mono (by omega))).add
    (((hq2.mul (hq0.pow 2)).mul (he2.pow 2)).mono (by omega))).add
    ((((hq1.pow 2).mul hq0).mul he3).mul he1 |>.mono (by omega))).sub
    ((((((HasValGe.of_nat 2).mul hq2).mul (hq0.pow 2)).mul he3).mul he1).mono (by omega))).sub
    (((((hq2.mul hq1).mul hq0).mul he2).mul he1).mono (by omega))).add
    ((((hq2.pow 2).mul hq0).mul (he1.pow 2)).mono (by omega))).sub
    ((((hq1.pow 3).mul he3).mul he0).mono (by omega))).add
    ((((((HasValGe.of_nat 3).mul hq2).mul hq1).mul hq0).mul he3).mul he0 |>.mono (by omega))).add
    ((((hq2.mul (hq1.pow 2)).mul he2).mul he0).mono (by omega))).sub
    ((((((HasValGe.of_nat 2).mul (hq2.pow 2)).mul hq0).mul he2).mul he0).mono (by omega))).sub
    (((((hq2.pow 2).mul hq1).mul he1).mul he0).mono (by omega))).add
    (((hq2.pow 3).mul (he0.pow 2)).mono (by omega))

/-- Leading valuation and leading coefficient of a Laurent series over `K`. -/
structure ValLead (k : ℤ) (f : LaurentSeries K) (c0 : K) : Prop where
  val : HasValGe k f
  c0 : f.coeff k = c0

namespace ValLead

lemma of_C (c : K) : ValLead 0 (HahnSeries.C c) c :=
  ⟨HasValGe.of_C c, by simp [HahnSeries.C_apply]⟩

lemma of_nat (n : ℕ) : ValLead 0 (n : LaurentSeries K) (n : K) := by
  have h : (n : LaurentSeries K) = HahnSeries.C (n : K) := (map_natCast HahnSeries.C n).symm
  rw [h]; exact of_C (n : K)

lemma of_single (k : ℤ) (c : K) : ValLead k (HahnSeries.single k c) c :=
  ⟨HasValGe.single k c, HahnSeries.coeff_single_same k c⟩

lemma of_hasValGe_succ {k : ℤ} {f : LaurentSeries K} (hf : HasValGe (k + 1) f) :
    ValLead k f 0 :=
  ⟨hf.mono (by omega), hf k (by omega)⟩

lemma hasValGe_succ {k : ℤ} {f : LaurentSeries K} (hf : ValLead k f 0) :
    HasValGe (k + 1) f :=
  hf.val.inc hf.c0

lemma add {k : ℤ} {f g : LaurentSeries K} {a b : K}
    (hf : ValLead k f a) (hg : ValLead k g b) : ValLead k (f + g) (a + b) :=
  ⟨hf.val.add hg.val, by simp [hf.c0, hg.c0]⟩

lemma sub {k : ℤ} {f g : LaurentSeries K} {a b : K}
    (hf : ValLead k f a) (hg : ValLead k g b) : ValLead k (f - g) (a - b) :=
  ⟨hf.val.sub hg.val, by simp [hf.c0, hg.c0]⟩

lemma neg {k : ℤ} {f : LaurentSeries K} {a : K}
    (hf : ValLead k f a) : ValLead k (-f) (-a) :=
  ⟨hf.val.neg, by simp [hf.c0]⟩

lemma add_high {k : ℤ} {f g : LaurentSeries K} {a : K}
    (hf : ValLead k f a) (hg : HasValGe (k + 1) g) : ValLead k (f + g) a := by
  simpa using hf.add (of_hasValGe_succ hg)

lemma mul {k l : ℤ} {f g : LaurentSeries K} {a b : K}
    (hf : ValLead k f a) (hg : ValLead l g b) : ValLead (k + l) (f * g) (a * b) :=
  ⟨hf.val.mul hg.val, by rw [hf.val.coeff_mul_min hg.val, hf.c0, hg.c0]⟩

lemma pow {k : ℤ} {f : LaurentSeries K} {a : K} (hf : ValLead k f a) (m : ℕ) :
    ValLead (m * k) (f ^ m) (a ^ m) :=
  ⟨hf.val.pow m, by rw [hf.val.coeff_pow_min m, hf.c0]⟩

lemma div_of_ne {k l : ℤ} {f g : LaurentSeries K} {a b : K}
    (hf : ValLead k f a) (hg : ValLead l g b) (hb : b ≠ 0) :
    ValLead (k - l) (f / g) (a / b) := by
  obtain ⟨hv, hc⟩ := hf.val.div_of_lead_ne hg.val (hg.c0.symm ▸ hb)
  exact ⟨hv, by rw [hc, hf.c0, hg.c0]⟩

lemma eq_k {k k' : ℤ} {f : LaurentSeries K} {a : K} (hk : k = k') (hf : ValLead k f a) :
    ValLead k' f a := hk ▸ hf

lemma eq_c {k : ℤ} {f : LaurentSeries K} {a b : K} (hab : a = b) (hf : ValLead k f a) :
    ValLead k f b := hab ▸ hf

lemma of_evalT (P : K[X]) : ValLead 0 (evalT P) (P.coeff 0) :=
  ⟨HasValGe.evalT P, by change (evalT P).coeff (0 : ℕ) = P.coeff 0; exact evalT_coeff P 0⟩

end ValLead

/-- First two Laurent coefficients `(f.coeff k, f.coeff (k + 1))` packaged as a `Dual K`. -/
structure ValDual (k : ℤ) (f : LaurentSeries K) (d : Dual K) : Prop where
  val : HasValGe k f
  c0 : f.coeff k = d.val
  c1 : f.coeff (k + 1) = d.eps

namespace ValDual

lemma toValLead {k : ℤ} {f : LaurentSeries K} {d : Dual K} (hf : ValDual k f d) :
    ValLead k f d.val := ⟨hf.val, hf.c0⟩

lemma of_C (c : K) : ValDual 0 (HahnSeries.C c) (Dual.C c) :=
  ⟨HasValGe.of_C c, by simp [HahnSeries.C_apply], by simp [HahnSeries.C_apply]⟩

lemma of_nat (n : ℕ) : ValDual 0 (n : LaurentSeries K) (n : Dual K) := by
  have h1 : (n : LaurentSeries K) = HahnSeries.C (n : K) := (map_natCast HahnSeries.C n).symm
  have h2 : (n : Dual K) = Dual.C (n : K) := by rw [map_natCast]
  rw [h1, h2]; exact of_C (n : K)

lemma of_single (k : ℤ) (c : K) : ValDual k (HahnSeries.single k c) (Dual.C c) :=
  ⟨HasValGe.single k c, HahnSeries.coeff_single_same k c,
   by rw [HahnSeries.coeff_single, if_neg (by omega)]; rfl⟩

lemma of_evalT (P : K[X]) : ValDual 0 (evalT P) ⟨P.coeff 0, P.coeff 1⟩ :=
  ⟨HasValGe.evalT P,
   by change (evalT P).coeff (0 : ℕ) = P.coeff 0; exact evalT_coeff P 0,
   by change (evalT P).coeff (1 : ℕ) = P.coeff 1; exact evalT_coeff P 1⟩

lemma of_evalInvT (P : K[X]) {d : ℕ} (hd : P.natDegree ≤ d) (hpos : 1 ≤ d) :
    ValDual (-(d : ℤ)) (evalInvT P) ⟨P.coeff d, P.coeff (d - 1)⟩ :=
  ⟨HasValGe.evalInvT_of_natDegree_le P hd,
   evalInvT_coeff_neg P d,
   by rw [show -(d : ℤ) + 1 = -((d - 1 : ℕ) : ℤ) by omega, evalInvT_coeff_neg]⟩

lemma add {k : ℤ} {f g : LaurentSeries K} {a b : Dual K}
    (hf : ValDual k f a) (hg : ValDual k g b) : ValDual k (f + g) (a + b) :=
  ⟨hf.val.add hg.val, by simp [hf.c0, hg.c0], by simp [hf.c1, hg.c1]⟩

lemma sub {k : ℤ} {f g : LaurentSeries K} {a b : Dual K}
    (hf : ValDual k f a) (hg : ValDual k g b) : ValDual k (f - g) (a - b) :=
  ⟨hf.val.sub hg.val, by simp [hf.c0, hg.c0], by simp [hf.c1, hg.c1]⟩

lemma neg {k : ℤ} {f : LaurentSeries K} {a : Dual K}
    (hf : ValDual k f a) : ValDual k (-f) (-a) :=
  ⟨hf.val.neg, by simp [hf.c0], by simp [hf.c1]⟩

lemma add_high {k : ℤ} {f g : LaurentSeries K} {a : Dual K}
    (hf : ValDual k f a) (hg : HasValGe (k + 2) g) : ValDual k (f + g) a :=
  ⟨hf.val.add (hg.mono (by omega)), by simp [hf.c0, hg k (by omega)],
   by simp [hf.c1, hg (k + 1) (by omega)]⟩

lemma add_shift1 {k : ℤ} {f g : LaurentSeries K} {a : Dual K} {b : K}
    (hf : ValDual k f a) (hg : ValLead (k + 1) g b) :
    ValDual k (f + g) (a + ⟨0, b⟩) :=
  ⟨hf.val.add (hg.val.mono (by omega)),
   by simp [hf.c0, hg.val k (by omega)],
   by simp [hf.c1, hg.c0]⟩

lemma mul {k l : ℤ} {f g : LaurentSeries K} {a b : Dual K}
    (hf : ValDual k f a) (hg : ValDual l g b) : ValDual (k + l) (f * g) (a * b) :=
  ⟨hf.val.mul hg.val,
   by rw [hf.val.coeff_mul_min hg.val, hf.c0, hg.c0]; rfl,
   by rw [hf.val.coeff_mul_min_plus_one hg.val, hf.c0, hf.c1, hg.c0, hg.c1]; rfl⟩

lemma pow {k : ℤ} {f : LaurentSeries K} {a : Dual K} (hf : ValDual k f a) (m : ℕ) :
    ValDual (m * k) (f ^ m) (a ^ m) := by
  induction m with
  | zero => simpa using of_C (1 : K)
  | succ m ih =>
    rw [pow_succ, pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact ih.mul hf

lemma inv_of_ne {l : ℤ} {g : LaurentSeries K} {b : Dual K}
    (hg : ValDual l g b) (hb : b.val ≠ 0) :
    ValDual (-l) g⁻¹ (Dual.invOfNe b hb) := by
  obtain ⟨hvi, hci⟩ := hg.val.inv_of_lead_ne (hg.c0.symm ▸ hb)
  have hgne : g ≠ 0 := fun h0 => hb (by rw [← hg.c0, h0]; rfl)
  have h1 := hg.val.coeff_mul_min_plus_one hvi
  rw [mul_inv_cancel₀ hgne, add_neg_cancel, zero_add] at h1
  have hzero : (1 : LaurentSeries K).coeff 1 = 0 := by
    change (HahnSeries.single (0 : ℤ) (1 : K)).coeff 1 = 0
    rw [HahnSeries.coeff_single, if_neg (by omega)]
  rw [hzero, hg.c0, hg.c1, hci, hg.c0] at h1
  have hc1 : g⁻¹.coeff (-l + 1) = -b.eps / b.val ^ 2 := by
    apply mul_left_cancel₀ hb
    have hmul : b.val * (-b.eps / b.val ^ 2) = -b.eps * b.val⁻¹ := by field_simp [hb]
    rw [hmul]; linear_combination -h1
  exact ⟨hvi, by rw [hci, hg.c0]; rfl, hc1⟩

theorem div_of_ne {k l : ℤ} {f g : LaurentSeries K} {a b : Dual K}
    (hf : ValDual k f a) (hg : ValDual l g b) (hb : b.val ≠ 0) :
    ValDual (k - l) (f / g) (a * Dual.invOfNe b hb) := by
  rw [div_eq_mul_inv, sub_eq_add_neg]
  exact hf.mul (hg.inv_of_ne hb)

lemma eq_k {k k' : ℤ} {f : LaurentSeries K} {a : Dual K} (hk : k = k') (hf : ValDual k f a) :
    ValDual k' f a := hk ▸ hf

lemma eq_d {k : ℤ} {f : LaurentSeries K} {a b : Dual K} (hab : a = b) (hf : ValDual k f a) :
    ValDual k f b := hab ▸ hf

end ValDual

end QuadRootAndVal

end QuadraticCovers


