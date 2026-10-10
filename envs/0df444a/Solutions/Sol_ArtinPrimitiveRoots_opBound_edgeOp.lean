-- Prove2me | solution 1 for ArtinPrimitiveRoots.opBound_edgeOp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:47:12.07806+00:00
-- url     : https://prove2.me/submissions/4dd41697-a2d5-4b3e-bef4-5e3158d166ff

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals

section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

/-- The product of all labels of a list. -/
def listProd {K J : ℕ} (ℓ : Fin K → Fin (J + 1) → ℕ) : ℕ := ∏ i, ∏ j, ℓ i j

end ArtinPrimitiveRoots
end

section
/-! # L102D_MemDefs — alias of the bundle `Def_ArtinMemoryModel` (round 5)

The memory model (root coordinates, `pathPhi`, `rootIL`, the memory space, `ghostOp`, `edgeOp`,
`memMomentD`, `dyadParams`, and `MemParams.RootIn`) now lives in
`Definitions/Def_ArtinMemoryModel.lean` (same declarations, same names). -/
end

section
/-! # L102D: basic facts about the memory parameters (no stubs)

`etav_mem`, `bprime_mem` (`0 < b'_p ≤ 1` once `N < p`), `bprime_ge_half`, `abs_baseline_le`, and
the asymptotic fact that the group primes eventually exceed any fixed multiple of `R + 1`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

lemma etav_mem (P : MemParams) (j : ℕ) : 0 ≤ P.etav j ∧ P.etav j ≤ 1 := by
  unfold MemParams.etav MemParams.qv
  split_ifs <;> norm_num

lemma bprime_ge_half (P : MemParams) {p : ℕ} (hp : 2 * P.N + 1 ≤ p) : 1 / 2 ≤ P.bprime p := by
  have hs : ∑ j ∈ range (P.N + 1), P.etav j ≤ P.N + 1 := by
    calc ∑ j ∈ range (P.N + 1), P.etav j ≤ ∑ _j ∈ range (P.N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => (etav_mem P j).2
      _ = P.N + 1 := by simp
  have hp' : 2 * ((P.N : ℝ) + 1) ≤ p + 1 := by
    have : (2 * P.N + 1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  unfold MemParams.bprime
  have : (∑ j ∈ range (P.N + 1), P.etav j) / ((p : ℝ) + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- Eventually every group prime is at least `C (R + 1)`. -/
lemma eventually_groupPrimes_ge {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, (0.1 : ℝ) < a i) (C : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ p ∈ groupPrimes x a, C * (momentPower x + 1) ≤ p := by
  have hL : Filter.Tendsto (fun x : ℝ => log x ^ (0.1 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  filter_upwards [hL.eventually_ge_atTop (720 * (|C| + 1) + 722),
    Filter.eventually_ge_atTop (exp 1)] with x hx hx1
  intro p hp
  have hlog : 1 ≤ log x := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) hx1
  simp only [groupPrimes, mem_biUnion, mem_univ, true_and] at hp
  obtain ⟨i, hi⟩ := hp
  simp only [primeGroup, mem_filter] at hi
  have hpge : exp (log x ^ a i) ≤ p := hi.2.2
  have h1 : log x ^ (0.1 : ℝ) ≤ log x ^ a i := rpow_le_rpow_of_exponent_le hlog (ha i).le
  set y := log x ^ (0.1 : ℝ) with hy
  have hy0 : 0 ≤ y := by positivity
  have h5 : y ^ 5 = log x ^ (0.5 : ℝ) := by
    rw [hy, ← rpow_natCast, ← rpow_mul (by linarith)]; norm_num
  have hmp : (momentPower x : ℝ) + 1 ≤ y ^ 5 + 2 := by
    unfold momentPower
    have := Nat.ceil_lt_add_one (show 0 ≤ log x ^ (0.5 : ℝ) / 2 by positivity)
    have h2 : 0 ≤ log x ^ (0.5 : ℝ) := by positivity
    rw [h5]; linarith
  have h6 := Real.pow_div_factorial_le_exp y hy0 6
  have hf : ((6 : ℕ).factorial : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hf] at h6
  have hy1 : 1 ≤ y := by linarith [abs_nonneg C]
  have hy5 : 1 ≤ y ^ 5 := one_le_pow₀ hy1
  have hkey : (|C| + 1) * (y ^ 5 + 2) ≤ y ^ 6 / 720 := by
    have e : y ^ 6 / 720 = y * y ^ 5 / 720 := by ring
    rw [e, le_div_iff₀ (by norm_num)]
    have h7 : (720 * (|C| + 1) + 722) * y ^ 5 ≤ y * y ^ 5 :=
      mul_le_mul_of_nonneg_right hx (by positivity)
    have h8 : y ≤ y ^ 5 := le_self_pow₀ hy1 (by norm_num)
    have h9 : 720 * (|C| + 1) ≤ y ^ 5 := by linarith [abs_nonneg C]
    have hc0 : 0 ≤ |C| + 1 := by positivity
    nlinarith
  have hCabs : C * ((momentPower x : ℝ) + 1) ≤ (|C| + 1) * (y ^ 5 + 2) := by
    have h0 : 0 ≤ (momentPower x : ℝ) + 1 := by positivity
    calc C * ((momentPower x : ℝ) + 1) ≤ |C| * ((momentPower x : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) h0
      _ ≤ (|C| + 1) * (y ^ 5 + 2) := by
          apply mul_le_mul (by linarith) hmp h0 (by positivity)
  calc C * ((momentPower x : ℝ) + 1) ≤ (|C| + 1) * (y ^ 5 + 2) := hCabs
    _ ≤ y ^ 6 / 720 := hkey
    _ ≤ exp y := h6
    _ ≤ exp (log x ^ a i) := exp_le_exp.2 h1
    _ ≤ p := hpge

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102G: the Hilbert-space framework for the edge bound (D7d)

On `H_B = ℓ²(stSet, μ)`, `μ = stWeight`:

* `ipμ g h = Σ_s μ(s) conj(g s) h s`; `opBound_of_bilin`: a bilinear bound gives `OpBound`;
* slot permutations `permS`; `μ` and `stSet` are invariant (`stWeight_permS`, `sum_permS`);
* `symM` is self-adjoint (`ipμ_symM`), a contraction (`wNorm_symM_le`), and its images are
  symmetric (`symM_permS`); `sum_sym_avg` replaces a row sum by its permutation average;
* `ipμ_edgeOp`: `⟨g, E f⟩ = ⟨Sg, E^ord Sf⟩`;
* `piece_bound`: the Cauchy–Schwarz/Schur bound for one piece of a choice-indexed operator.
-/

namespace ArtinPrimitiveRoots.L102G

open Real Finset
open scoped ComplexConjugate

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- The slot permutations. -/
abbrev SlotPerm := Fin P.K → Equiv.Perm (Fin (P.J + 1))

/-- The action of slot permutations on lists. -/
def permL (pr : SlotPerm P) (ℓ : P.Lst) : P.Lst := fun i => ℓ i ∘ pr i

/-- The action on memory states. -/
def permS (pr : SlotPerm P) (s : P.MState) : P.MState := (s.1, permL P pr s.2.1, s.2.2)

lemma permL_permL (σ pr : SlotPerm P) (ℓ : P.Lst) :
    permL P pr (permL P σ ℓ) = permL P (σ * pr) ℓ := by
  funext i k; rfl

lemma permS_permS (σ pr : SlotPerm P) (s : P.MState) :
    permS P pr (permS P σ s) = permS P (σ * pr) s := by
  simp only [permS, permL_permL]

lemma permS_one (s : P.MState) : permS P 1 s = s := by
  rcases s with ⟨z, ℓ, m⟩; rfl

lemma permS_inv_cancel (pr : SlotPerm P) (s : P.MState) : permS P pr (permS P pr⁻¹ s) = s := by
  rw [permS_permS, inv_mul_cancel, permS_one]

lemma permS_cancel_inv (pr : SlotPerm P) (s : P.MState) : permS P pr⁻¹ (permS P pr s) = s := by
  rw [permS_permS, mul_inv_cancel, permS_one]

lemma listWeight_permL (pr : SlotPerm P) (ℓ : P.Lst) :
    P.listWeight (permL P pr ℓ) = P.listWeight ℓ := by
  unfold MemParams.listWeight permL
  refine prod_congr rfl fun i _ => ?_
  exact Equiv.prod_comp (pr i) (fun k => P.nu i (ℓ i k))

lemma stWeight_permS (pr : SlotPerm P) (s : P.MState) :
    P.stWeight (permS P pr s) = P.stWeight s := by
  unfold MemParams.stWeight permS; rw [listWeight_permL]

lemma mem_listCands_permL (pr : SlotPerm P) (ℓ : P.Lst) :
    permL P pr ℓ ∈ listCands P.x P.a P.J ↔ ℓ ∈ listCands P.x P.a P.J := by
  simp only [listCands, Fintype.mem_piFinset, permL, Function.comp]
  constructor
  · intro h i k; simpa using h i ((pr i).symm k)
  · intro h i k; exact h i _

lemma mem_stSet_permS (pr : SlotPerm P) (s : P.MState) :
    permS P pr s ∈ P.stSet ↔ s ∈ P.stSet := by
  simp only [MemParams.stSet, mem_product, permS, mem_listCands_permL]

lemma sum_permS {M : Type*} [AddCommMonoid M] (pr : SlotPerm P) (φ : P.MState → M) :
    ∑ s ∈ P.stSet, φ (permS P pr s) = ∑ s ∈ P.stSet, φ s := by
  refine sum_nbij' (permS P pr) (permS P pr⁻¹) (fun s hs => (mem_stSet_permS P pr s).2 hs)
    (fun s hs => (mem_stSet_permS P pr⁻¹ s).2 hs) (fun s _ => permS_cancel_inv P pr s)
    (fun s _ => permS_inv_cancel P pr s) (fun s _ => rfl)

/-- The number of slot permutations. -/
lemma card_slotPerm : Fintype.card (SlotPerm P) = (P.J + 1).factorial ^ P.K := by
  rw [Fintype.card_pi, prod_const, card_univ, Fintype.card_fin, Fintype.card_perm,
    Fintype.card_fin]

lemma symM_eq (f : P.MState → ℂ) (s : P.MState) :
    P.symM f s = (((Fintype.card (SlotPerm P) : ℕ) : ℂ))⁻¹ *
      ∑ pr : SlotPerm P, f (permS P pr s) := by
  rw [card_slotPerm]; rfl

lemma symM_permS (f : P.MState → ℂ) (σ : SlotPerm P) (s : P.MState) :
    P.symM f (permS P σ s) = P.symM f s := by
  rw [symM_eq, symM_eq]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun pr => ?_
  rw [permS_permS]; rfl

/-! ## The weighted inner product -/

/-- `⟨g, h⟩_μ = Σ_s μ(s) conj(g s) h s`. -/
noncomputable def ipμ (g h : P.MState → ℂ) : ℂ :=
  ∑ s ∈ P.stSet, (P.stWeight s : ℂ) * (conj (g s) * h s)

lemma ipμ_self (h : P.MState → ℂ) :
    ipμ P h h = ((∑ s ∈ P.stSet, P.stWeight s * ‖h s‖ ^ 2 : ℝ) : ℂ) := by
  unfold ipμ
  push_cast
  refine sum_congr rfl fun s _ => ?_
  rw [mul_comm (conj (h s)), Complex.mul_conj']

/-- A bilinear bound gives the operator bound. -/
theorem opBound_of_bilin (O : (P.MState → ℂ) → (P.MState → ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s)
    (h : ∀ g f, ‖ipμ P g (O f)‖ ≤ C * P.wNorm g * P.wNorm f) : P.OpBound (O) C := by
  intro f
  have hsq : ∀ u : P.MState → ℂ, P.wNorm u ^ 2 = ∑ s ∈ P.stSet, P.stWeight s * ‖u s‖ ^ 2 :=
    fun u => Real.sq_sqrt (sum_nonneg fun s hs => mul_nonneg (hμ s hs) (sq_nonneg _))
  have h1 := h (O f) f
  rw [ipμ_self, Complex.norm_real, Real.norm_of_nonneg
    (sum_nonneg fun s hs => mul_nonneg (hμ s hs) (sq_nonneg _)), ← hsq] at h1
  have hn : 0 ≤ P.wNorm (O f) := Real.sqrt_nonneg _
  rcases hn.eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg hC (Real.sqrt_nonneg _)
  · have : P.wNorm (O f) * P.wNorm (O f) ≤ (C * P.wNorm f) * P.wNorm (O f) := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos

/-! ## The slot symmetrization -/

lemma ipμ_symM (g h : P.MState → ℂ) : ipμ P g (P.symM h) = ipμ P (P.symM g) h := by
  unfold ipμ
  simp only [symM_eq, map_mul, map_inv₀, map_natCast, map_sum]
  set N : ℂ := (((Fintype.card (SlotPerm P) : ℕ) : ℂ))⁻¹
  have hL : ∀ s ∈ P.stSet, (P.stWeight s : ℂ) * (conj (g s) * (N * ∑ pr : SlotPerm P,
      h (permS P pr s))) = N * ∑ pr : SlotPerm P,
        (P.stWeight s : ℂ) * (conj (g s) * h (permS P pr s)) := by
    intro s _; rw [mul_sum, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun pr _ => by ring
  rw [sum_congr rfl hL, ← mul_sum, sum_comm]
  have hR : ∀ pr : SlotPerm P, ∑ s ∈ P.stSet, (P.stWeight s : ℂ) *
      (conj (g s) * h (permS P pr s)) = ∑ s ∈ P.stSet, (P.stWeight s : ℂ) *
        (conj (g (permS P pr⁻¹ s)) * h s) := by
    intro pr
    rw [← sum_permS P pr⁻¹ (fun s => (P.stWeight s : ℂ) * (conj (g s) * h (permS P pr s)))]
    refine sum_congr rfl fun s _ => ?_
    simp only [stWeight_permS, permS_inv_cancel]
  rw [Fintype.sum_congr _ _ hR, sum_comm, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  have hinv : ∑ pr : SlotPerm P, conj (g (permS P pr⁻¹ s)) =
      ∑ pr : SlotPerm P, conj (g (permS P pr s)) :=
    Fintype.sum_equiv (Equiv.inv _) _ _ fun pr => rfl
  rw [← hinv, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma norm_sq_symM_le (f : P.MState → ℂ) (s : P.MState) :
    ‖P.symM f s‖ ^ 2 ≤ ((Fintype.card (SlotPerm P) : ℕ) : ℝ)⁻¹ *
      ∑ pr : SlotPerm P, ‖f (permS P pr s)‖ ^ 2 := by
  rw [symM_eq]
  set N := ((Fintype.card (SlotPerm P) : ℕ) : ℝ)
  have hN : 0 < N := by
    simp only [N]; exact_mod_cast Fintype.card_pos
  have h1 : ‖(((Fintype.card (SlotPerm P) : ℕ) : ℂ))⁻¹ * ∑ pr : SlotPerm P, f (permS P pr s)‖ ≤
      N⁻¹ * ∑ pr : SlotPerm P, ‖f (permS P pr s)‖ := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  have h2 : (∑ pr : SlotPerm P, ‖f (permS P pr s)‖) ^ 2 ≤
      N * ∑ pr : SlotPerm P, ‖f (permS P pr s)‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (SlotPerm P)))
      (f := fun pr => ‖f (permS P pr s)‖)
    simpa [N] using this
  calc _ ≤ (N⁻¹ * ∑ pr : SlotPerm P, ‖f (permS P pr s)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = N⁻¹ ^ 2 * (∑ pr : SlotPerm P, ‖f (permS P pr s)‖) ^ 2 := by ring
    _ ≤ N⁻¹ ^ 2 * (N * ∑ pr : SlotPerm P, ‖f (permS P pr s)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by field_simp

lemma wNorm_symM_le (hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s) (f : P.MState → ℂ) :
    P.wNorm (P.symM f) ≤ P.wNorm f := by
  unfold MemParams.wNorm
  apply Real.sqrt_le_sqrt
  set N := ((Fintype.card (SlotPerm P) : ℕ) : ℝ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  calc ∑ s ∈ P.stSet, P.stWeight s * ‖P.symM f s‖ ^ 2 ≤
      ∑ s ∈ P.stSet, P.stWeight s * (N⁻¹ * ∑ pr : SlotPerm P, ‖f (permS P pr s)‖ ^ 2) :=
        sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (norm_sq_symM_le P f s) (hμ s hs)
    _ = N⁻¹ * ∑ pr : SlotPerm P, ∑ s ∈ P.stSet, P.stWeight s * ‖f (permS P pr s)‖ ^ 2 := by
        rw [mul_sum]
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun pr _ => sum_congr rfl fun s _ => by ring
    _ = N⁻¹ * ∑ _pr : SlotPerm P, ∑ s ∈ P.stSet, P.stWeight s * ‖f s‖ ^ 2 := by
        congr 1; refine Fintype.sum_congr _ _ fun pr => ?_
        rw [← sum_permS P pr (fun s => P.stWeight s * ‖f s‖ ^ 2)]
        simp only [stWeight_permS]
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul]; field_simp; rfl

/-- The edge in bilinear form: `⟨g, E f⟩ = ⟨Sg, E^ord Sf⟩`. -/
lemma ipμ_edgeOp (ω : ℝ × ℝ × ℝ) (j : ℕ) (g f : P.MState → ℂ) :
    ipμ P g (P.edgeOp ω j f) = ipμ P (P.symM g) (P.edgeOrd ω j (P.symM f)) := by
  unfold MemParams.edgeOp; rw [ipμ_symM]

/-- Rows against a symmetric weight may be averaged over slot permutations. -/
lemma sum_sym_avg (φ R : P.MState → ℝ) (hφ : ∀ σ s, φ (permS P σ s) = φ s) :
    ∑ s ∈ P.stSet, φ s * R s = ∑ s ∈ P.stSet, φ s *
      (((Fintype.card (SlotPerm P) : ℕ) : ℝ)⁻¹ * ∑ pr : SlotPerm P, R (permS P pr s)) := by
  set N := ((Fintype.card (SlotPerm P) : ℕ) : ℝ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  have : ∀ pr : SlotPerm P, ∑ s ∈ P.stSet, φ s * R (permS P pr s) =
      ∑ s ∈ P.stSet, φ s * R s := by
    intro pr
    rw [← sum_permS P pr (fun s => φ s * R s)]
    simp only [hφ]
  calc ∑ s ∈ P.stSet, φ s * R s = N⁻¹ * ∑ _pr : SlotPerm P, ∑ s ∈ P.stSet, φ s * R s := by
        rw [sum_const, card_univ, nsmul_eq_mul]; field_simp; rfl
    _ = N⁻¹ * ∑ pr : SlotPerm P, ∑ s ∈ P.stSet, φ s * R (permS P pr s) := by
        congr 1; exact Fintype.sum_congr _ _ fun pr => (this pr).symm
    _ = _ := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun s _ => ?_
        rw [← mul_sum, mul_left_comm]

/-! ## One piece of a choice-indexed operator -/

variable {γ : Type*}

/-- Cauchy–Schwarz for a piece: rows against `G`, columns against `F`. -/
theorem piece_bound (Ch : Finset γ) (coeffP : P.MState → γ → ℂ) (out : P.MState → γ → P.MState)
    (G F : P.MState → ℂ) (R C : ℝ) (hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s)
    (hrow : ∑ s ∈ P.stSet, ∑ c ∈ Ch, P.stWeight s * ‖coeffP s c‖ *
      (if out s c ∈ P.stSet then 1 else 0) * ‖G s‖ ^ 2 ≤
        R * ∑ s ∈ P.stSet, P.stWeight s * ‖G s‖ ^ 2)
    (hcol : ∑ s ∈ P.stSet, ∑ c ∈ Ch, P.stWeight s * ‖coeffP s c‖ *
      (if out s c ∈ P.stSet then ‖F (out s c)‖ ^ 2 else 0) ≤
        C * ∑ s ∈ P.stSet, P.stWeight s * ‖F s‖ ^ 2) :
    ‖∑ s ∈ P.stSet, (P.stWeight s : ℂ) * (conj (G s) * ∑ c ∈ Ch, coeffP s c *
      (if out s c ∈ P.stSet then F (out s c) else 0))‖ ≤ √R * √C * P.wNorm G * P.wNorm F := by
  set W : P.MState × γ → ℝ := fun q => P.stWeight q.1 * ‖coeffP q.1 q.2‖ *
    (if out q.1 q.2 ∈ P.stSet then 1 else 0)
  have hW : ∀ q ∈ P.stSet ×ˢ Ch, 0 ≤ W q := by
    intro q hq
    simp only [W]
    have := hμ q.1 (mem_product.1 hq).1
    split_ifs <;> positivity
  have h1 : ‖∑ s ∈ P.stSet, (P.stWeight s : ℂ) * (conj (G s) * ∑ c ∈ Ch, coeffP s c *
      (if out s c ∈ P.stSet then F (out s c) else 0))‖ ≤
      ∑ q ∈ P.stSet ×ˢ Ch, (√(W q) * ‖G q.1‖) * (√(W q) *
        (if out q.1 q.2 ∈ P.stSet then ‖F (out q.1 q.2)‖ else 0)) := by
    rw [sum_product]
    refine (norm_sum_le _ _).trans (sum_le_sum fun s hs => ?_)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ s hs), Complex.norm_conj]
    calc P.stWeight s * (‖G s‖ * ‖∑ c ∈ Ch, coeffP s c *
          (if out s c ∈ P.stSet then F (out s c) else 0)‖) ≤
        P.stWeight s * (‖G s‖ * ∑ c ∈ Ch, ‖coeffP s c *
          (if out s c ∈ P.stSet then F (out s c) else 0)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sum_le _ _)
            (norm_nonneg _)) (hμ s hs)
      _ = _ := by
          rw [mul_sum, mul_sum]
          refine sum_congr rfl fun c hc => ?_
          have hWq := hW (s, c) (mem_product.2 ⟨hs, hc⟩)
          rw [show √(W (s, c)) * ‖G (s, c).1‖ * (√(W (s, c)) *
              (if out (s, c).1 (s, c).2 ∈ P.stSet then ‖F (out (s, c).1 (s, c).2)‖ else 0)) =
              (√(W (s, c)) * √(W (s, c))) * ‖G s‖ *
                (if out s c ∈ P.stSet then ‖F (out s c)‖ else 0) by ring,
            Real.mul_self_sqrt hWq]
          simp only [W]
          by_cases ho : out s c ∈ P.stSet
          · simp only [if_pos ho, norm_mul]; ring
          · simp only [if_neg ho, norm_mul, norm_zero]; ring
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (P.stSet ×ˢ Ch) (fun q => √(W q) * ‖G q.1‖)
    (fun q => √(W q) * (if out q.1 q.2 ∈ P.stSet then ‖F (out q.1 q.2)‖ else 0))
  have h3 : ∑ q ∈ P.stSet ×ˢ Ch, (√(W q) * ‖G q.1‖) ^ 2 ≤
      R * ∑ s ∈ P.stSet, P.stWeight s * ‖G s‖ ^ 2 := by
    refine le_trans (le_of_eq ?_) hrow
    rw [sum_product]
    refine sum_congr rfl fun s hs => sum_congr rfl fun c hc => ?_
    rw [mul_pow, Real.sq_sqrt (hW (s, c) (mem_product.2 ⟨hs, hc⟩))]
  have h4 : ∑ q ∈ P.stSet ×ˢ Ch, (√(W q) *
      (if out q.1 q.2 ∈ P.stSet then ‖F (out q.1 q.2)‖ else 0)) ^ 2 ≤
      C * ∑ s ∈ P.stSet, P.stWeight s * ‖F s‖ ^ 2 := by
    refine le_trans (le_of_eq ?_) hcol
    rw [sum_product]
    refine sum_congr rfl fun s hs => sum_congr rfl fun c hc => ?_
    rw [mul_pow, Real.sq_sqrt (hW (s, c) (mem_product.2 ⟨hs, hc⟩))]
    simp only [W]
    split_ifs <;> simp
  have hG := sum_nonneg fun s hs => mul_nonneg (hμ s hs) (sq_nonneg ‖G s‖)
  have hF := sum_nonneg fun s hs => mul_nonneg (hμ s hs) (sq_nonneg ‖F s‖)
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ √(R * ∑ s ∈ P.stSet, P.stWeight s * ‖G s‖ ^ 2) *
        √(C * ∑ s ∈ P.stSet, P.stWeight s * ‖F s‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt h3) (Real.sqrt_le_sqrt h4) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = √R * √C * P.wNorm G * P.wNorm F := by
        unfold MemParams.wNorm
        rw [Real.sqrt_mul' _ hG, Real.sqrt_mul' _ hF]; ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: reversing an edge (columns are rows of the reversed edge)

For a choice `c = (St, z', tg)` at a state `s = (z, ℓ, m)` with output `s' = (z', ℓ', m')`, the
reversed choice at `s'` is `(I, z, (ℓᵢ(last), i ∈ St))`, `I` the promoted groups: promotions become
stores and stores become promotions. `rev_rev`: reversing twice is the identity;
`edgeOut_rev`: the reversed edge returns to `s`; `econd_rev`: it satisfies the edge conditions;
`weight_rev`: `μ(s) rfac(s,c) ∏_{I} Vᵢ = μ(s') rfac(s',c') ∏_{St} Vᵢ` (the Fock measure identity
`memW(m₀ + δ_y) (m₀(y) + 1) = memW(m₀) λ(y)`, [21] (4.18)). -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- Edge choices. -/
abbrev EC := Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)

/-! ## Lists -/

lemma newList_last (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K) :
    P.newList ℓ nw i (Fin.last P.J) = nw i := by
  simp [MemParams.newList]

lemma newList_castSucc (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K) (k : Fin P.J) :
    P.newList ℓ nw i k.castSucc = ℓ i k.castSucc := by
  simp [MemParams.newList]

lemma newList_newList (ℓ : P.Lst) (nw lab : Fin P.K → ℕ) :
    P.newList (P.newList ℓ nw) lab = P.newList ℓ lab := by
  funext i k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp [newList_last]
  · simp [newList_castSucc]

lemma newList_self (ℓ : P.Lst) : P.newList ℓ (fun i => ℓ i (Fin.last P.J)) = ℓ := by
  funext i k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp [newList_last]
  · simp [newList_castSucc]

lemma padProd_newList (ℓ : P.Lst) (nw : Fin P.K → ℕ) : padProd (P.newList ℓ nw) = padProd ℓ := by
  unfold padProd; simp only [newList_castSucc]

lemma lastProd_newList (ℓ : P.Lst) (nw : Fin P.K → ℕ) :
    lastProd (P.newList ℓ nw) = ∏ i, nw i := by
  unfold lastProd; simp only [newList_last]

lemma detZ_swap (z z' : ℤ × ℤ) : detZ z' z = -detZ z z' := by unfold detZ; ring

lemma newList_injective (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K)
    (hinj : Function.Injective (ℓ i)) (hban : nw i ∉ Set.range (ℓ i)) :
    Function.Injective (P.newList ℓ nw i) := by
  intro k k' h
  induction k using Fin.lastCases with
  | last =>
    induction k' using Fin.lastCases with
    | last => rfl
    | cast k' =>
      rw [newList_last, newList_castSucc] at h
      exact absurd ⟨_, h.symm⟩ hban
  | cast k =>
    induction k' using Fin.lastCases with
    | last =>
      rw [newList_last, newList_castSucc] at h
      exact absurd ⟨_, h⟩ hban
    | cast k' =>
      rw [newList_castSucc, newList_castSucc] at h
      exact congrArg _ (Fin.castSucc_injective _ (hinj h))

/-- The listed weight splits into pads and last labels. -/
lemma listWeight_newList_mul (ℓ : P.Lst) (nw : Fin P.K → ℕ) :
    P.listWeight ℓ * ∏ i, P.nu i (nw i) =
      P.listWeight (P.newList ℓ nw) * ∏ i, P.nu i (ℓ i (Fin.last P.J)) := by
  unfold MemParams.listWeight
  rw [← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [newList_castSucc, newList_last]
  ring

/-! ## The edge condition and the real factor -/

/-- The condition of `edgeCoeff`. -/
def ECond (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) : Prop :=
  P.EdgeOK ω s.1 c.2.1 s.2.1 (fun i => (c.2.2 i).1) ∧
    (∀ i, (c.2.2 i).2 → P.promPart c.2.1 c.2.2 i ∈ P.partSet) ∧
    (∀ i ∈ c.1, P.storedPart s.1 s.2.1 i ∈ P.partSet) ∧
    (∀ y, P.promCount c.2.1 c.2.2 y ≤ s.2.2 y)

/-- The real factor of `edgeCoeff` (pending hits, promotions or fresh labels). -/
noncomputable def rfac (s : P.MState) (c : EC P) : ℝ :=
  memRho ^ P.hitCount s.1 s.2.2 *
    (∏ i, if (c.2.2 i).2 then (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i
      else P.nu i (c.2.2 i).1) *
    memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c)

open Classical in
/-- The edge coefficient with the geometric multiplier replaced by `κ t a b D`. -/
noncomputable def coeffK (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) : ℂ :=
  if ECond P ω s c then (rfac P s c : ℂ) *
    κ (detZ s.1 c.2.1 / padProd s.2.1) (∏ i, (c.2.2 i).1) (lastProd s.2.1) (padProd s.2.1) else 0

lemma edgeCoeff_eq (ω : ℝ × ℝ × ℝ) (j : ℕ) (s : P.MState) (c : EC P) :
    P.edgeCoeff ω j s c = coeffK P (P.edgeMult j) ω s c := by
  unfold MemParams.edgeCoeff coeffK ECond rfac
  congr 1

/-! ## The reversal -/

/-- The promoted groups. -/
def promSet (c : EC P) : Finset (Fin P.K) := univ.filter fun i => (c.2.2 i).2 = true

/-- The reversed choice. -/
def revC (s : P.MState) (c : EC P) : EC P :=
  (promSet P c, s.1, fun i => (s.2.1 i (Fin.last P.J), decide (i ∈ c.1)))

lemma storedPart_out (s : P.MState) (c : EC P) (i : Fin P.K) :
    P.storedPart (P.edgeOut s c).1 (P.edgeOut s c).2.1 i = P.promPart c.2.1 c.2.2 i := by
  simp only [MemParams.storedPart, MemParams.edgeOut, MemParams.promPart, newList_last]

lemma promCount_revC (s : P.MState) (c : EC P) (y : P.PT) :
    P.promCount s.1 (revC P s c).2.2 y = P.storeCount s.1 s.2.1 c.1 y := by
  unfold MemParams.promCount MemParams.storeCount
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, revC, decide_eq_true_eq]
  exact Iff.rfl

lemma storeCount_out (s : P.MState) (c : EC P) (y : P.PT) :
    P.storeCount (P.edgeOut s c).1 (P.edgeOut s c).2.1 (promSet P c) y =
      P.promCount c.2.1 c.2.2 y := by
  unfold MemParams.promCount MemParams.storeCount
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, promSet, storedPart_out]

lemma edgeOutMem_rev (s : P.MState) (c : EC P) (hc : ∀ y, P.promCount c.2.1 c.2.2 y ≤ s.2.2 y) :
    P.edgeOutMem (P.edgeOut s c) (revC P s c) = s.2.2 := by
  funext y
  unfold MemParams.edgeOutMem
  have h1 : (P.edgeOut s c).1 = c.2.1 := rfl
  have h2 := storeCount_out P s c y
  have h3 : (revC P s c).1 = promSet P c := rfl
  have h4 := promCount_revC P s c y
  have h5 : (P.edgeOut s c).2.2 y =
      s.2.2 y - P.promCount c.2.1 c.2.2 y + P.storeCount s.1 s.2.1 c.1 y := rfl
  have h6 : (revC P s c).2.1 = s.1 := rfl
  rw [h3, h2, h6, h4, h5]
  have := hc y
  omega

lemma edgeOut_rev (s : P.MState) (c : EC P) (hc : ∀ y, P.promCount c.2.1 c.2.2 y ≤ s.2.2 y) :
    P.edgeOut (P.edgeOut s c) (revC P s c) = s := by
  rcases s with ⟨z, ℓ, m⟩
  have hm := edgeOutMem_rev P (z, ℓ, m) c hc
  simp only [MemParams.edgeOut] at hm ⊢
  rw [hm]
  simp only [revC, newList_newList, newList_self]

lemma revC_rev (s : P.MState) (c : EC P) (hc : ∀ y, P.promCount c.2.1 c.2.2 y ≤ s.2.2 y) :
    revC P (P.edgeOut s c) (revC P s c) = c := by
  rcases c with ⟨St, z', tg⟩
  simp only [revC, promSet, MemParams.edgeOut, newList_last, mem_filter, mem_univ, true_and,
    decide_eq_true_eq]
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · ext i; simp
  · funext i; simp

lemma ecLabels_rev (s : P.MState) (c : EC P) :
    (fun i => ((revC P s c).2.2 i).1) = fun i => s.2.1 i (Fin.last P.J) := rfl

lemma prod_labels_rev (s : P.MState) (c : EC P) :
    ∏ i, ((revC P s c).2.2 i).1 = lastProd s.2.1 := rfl

lemma lastProd_out (s : P.MState) (c : EC P) :
    lastProd (P.edgeOut s c).2.1 = ∏ i, (c.2.2 i).1 := by
  simp only [MemParams.edgeOut, lastProd_newList]

lemma padProd_out (s : P.MState) (c : EC P) :
    padProd (P.edgeOut s c).2.1 = padProd s.2.1 := by
  simp only [MemParams.edgeOut, padProd_newList]

lemma det_rev (s : P.MState) (c : EC P) (hD : (padProd s.2.1 : ℤ) ∣ detZ s.1 c.2.1) :
    detZ (P.edgeOut s c).1 (revC P s c).2.1 / padProd (P.edgeOut s c).2.1 =
      -(detZ s.1 c.2.1 / padProd s.2.1) := by
  rw [padProd_out]
  show detZ c.2.1 s.1 / _ = _
  rw [detZ_swap, Int.neg_ediv_of_dvd hD]

lemma econd_rev (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) (h : ECond P ω s c) :
    ECond P ω (P.edgeOut s c) (revC P s c) := by
  obtain ⟨⟨hinj, hban, hd1, hd2, hdvd, hb1, hb2, hg1, hg2⟩, hpp, hsp, hpc⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hb2, hb1, hg2, ?_⟩, ?_, ?_, ?_⟩
  · intro i; exact newList_injective P _ (fun i => (c.2.2 i).1) i (hinj i) (hban i)
  · intro i hi
    obtain ⟨k, hk⟩ := hi
    simp only [revC] at hk
    induction k using Fin.lastCases with
    | last =>
      simp only [MemParams.edgeOut, newList_last] at hk
      exact hban i ⟨_, hk.symm⟩
    | cast k =>
      simp only [MemParams.edgeOut, newList_castSucc] at hk
      exact absurd (hinj i hk) (Fin.castSucc_ne_last k)
  · rw [padProd_out]; exact hd1
  · rw [padProd_out]; exact hd2
  · rw [padProd_out]; show _ ∣ detZ c.2.1 s.1
    rw [detZ_swap]; exact (dvd_neg).2 hdvd
  · show P.GoodAt ω s.1 (P.newList (P.newList s.2.1 _) _)
    rw [newList_newList, ecLabels_rev, newList_self]; exact hg1
  · intro i hi
    simp only [revC, decide_eq_true_eq] at hi
    exact hsp i hi
  · intro i hi
    simp only [revC, promSet, mem_filter, mem_univ, true_and] at hi
    rw [storedPart_out]; exact hpp i hi
  · intro y
    show P.promCount s.1 (revC P s c).2.2 y ≤ _
    rw [promCount_revC]
    show P.storeCount s.1 s.2.1 c.1 y ≤
      s.2.2 y - P.promCount c.2.1 c.2.2 y + P.storeCount s.1 s.2.1 c.1 y
    omega

/-! ## The Fock measure identity -/

lemma memWeight_update (m : P.Mem) (y : P.PT) :
    P.memWeight (Function.update m y (m y + 1)) * ((m y : ℝ) + 1) = P.memWeight m * P.lam y := by
  unfold MemParams.memWeight
  rw [← mul_prod_erase univ _ (mem_univ y), ← mul_prod_erase univ _ (mem_univ y)]
  have h : ∏ x ∈ univ.erase y, P.lam x ^ Function.update m y (m y + 1) x /
      ((Function.update m y (m y + 1) x).factorial : ℝ) =
      ∏ x ∈ univ.erase y, P.lam x ^ m x / ((m x).factorial : ℝ) := by
    refine prod_congr rfl fun x hx => ?_
    rw [Function.update_of_ne (ne_of_mem_erase hx)]
  rw [h, Function.update_self, Nat.factorial_succ]
  have hf : ((m y).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

/-- The count of a family of particles indexed by `T`. -/
def cntF (T : Finset (Fin P.K)) (yf : Fin P.K → Fin P.K × ℕ × ℕ) : P.Mem :=
  fun y => (T.filter fun i => yf i = y.1).card

lemma memAt_of_mem (m : P.Mem) (y : Fin P.K × ℕ × ℕ) (h : y ∈ P.partSet) :
    P.memAt m y = m ⟨y, h⟩ := by
  unfold MemParams.memAt; rw [dif_pos h]

/-- **The Fock identity**: inserting the particles `yf i`, `i ∈ T` (one per group), and paying
their indexed counts is the same as paying their measures. -/
lemma fock_prod (T : Finset (Fin P.K)) (yf : Fin P.K → Fin P.K × ℕ × ℕ)
    (hyf1 : ∀ i, (yf i).1 = i) (hyp : ∀ i ∈ T, yf i ∈ P.partSet) (m₀ : P.Mem) :
    P.memWeight (m₀ + cntF P T yf) * ∏ i ∈ T, (P.memAt (m₀ + cntF P T yf) (yf i) : ℝ) =
      P.memWeight m₀ * ∏ i ∈ T, P.nu i (yf i).2.1 := by
  induction T using Finset.induction_on with
  | empty =>
    have : m₀ + cntF P ∅ yf = m₀ := by funext y; simp [cntF]
    rw [this]; simp
  | insert i T hi ih =>
    have hyi : yf i ∈ P.partSet := hyp i (mem_insert_self i T)
    have hyT : ∀ i' ∈ T, yf i' ∈ P.partSet := fun i' h => hyp i' (mem_insert_of_mem h)
    set y : P.PT := ⟨yf i, hyi⟩
    set mT := m₀ + cntF P T yf
    have hupd : m₀ + cntF P (insert i T) yf = Function.update mT y (mT y + 1) := by
      funext y'
      by_cases hy : y' = y
      · subst hy
        rw [Function.update_self]
        simp only [mT, Pi.add_apply, cntF, filter_insert]
        rw [if_pos (rfl : yf i = (y : Fin P.K × ℕ × ℕ)),
          card_insert_of_notMem (fun h => hi (mem_filter.1 h).1)]
        ring
      · rw [Function.update_of_ne hy]
        simp only [mT, Pi.add_apply, cntF, filter_insert]
        have : ¬ yf i = y'.1 := fun h => hy (Subtype.ext h.symm)
        rw [if_neg this]
    have hT : ∀ i' ∈ T, P.memAt (m₀ + cntF P (insert i T) yf) (yf i') = P.memAt mT (yf i') := by
      intro i' hi'
      rw [memAt_of_mem P _ _ (hyT i' hi'), memAt_of_mem P _ _ (hyT i' hi'), hupd]
      have : (⟨yf i', hyT i' hi'⟩ : P.PT) ≠ y := by
        intro h
        have := congrArg (fun q : P.PT => q.1.1) h
        simp only [y, hyf1] at this
        exact hi (this ▸ hi')
      rw [Function.update_of_ne this]
    rw [prod_insert hi, prod_insert hi, prod_congr rfl fun i' hi' => by rw [hT i' hi']]
    rw [memAt_of_mem P _ _ hyi, hupd, Function.update_self]
    have hw := memWeight_update P mT y
    have hlam : P.lam y = P.nu i (yf i).2.1 := by
      simp only [MemParams.lam, y, hyf1]
    push_cast
    calc P.memWeight (Function.update mT y (mT y + 1)) * (((mT y : ℝ) + 1) *
          ∏ i' ∈ T, (P.memAt mT (yf i') : ℝ)) =
        (P.memWeight (Function.update mT y (mT y + 1)) * ((mT y : ℝ) + 1)) *
          ∏ i' ∈ T, (P.memAt mT (yf i') : ℝ) := by ring
      _ = P.lam y * (P.memWeight mT * ∏ i' ∈ T, (P.memAt mT (yf i') : ℝ)) := by
          rw [hw]; ring
      _ = _ := by rw [ih hyT, hlam]; ring

lemma promCount_eq_cntF (z' : ℤ × ℤ) (tg : Fin P.K → ℕ × Bool) (c : EC P) (hc : c.2.2 = tg)
    (y : P.PT) : P.promCount z' tg y = cntF P (promSet P c) (P.promPart z' tg) y := by
  unfold MemParams.promCount cntF promSet
  rw [filter_filter, hc]

/-- **The reversal weight identity**: `μ(s) rfac(s,c) ∏_I Vᵢ = μ(s') rfac(s',c') ∏_{St} Vᵢ`. -/
lemma weight_rev (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) (h : ECond P ω s c)
    (hV : ∀ i, P.Vg i ≠ 0) :
    P.stWeight s * rfac P s c * ∏ i ∈ promSet P c, P.Vg i =
      P.stWeight (P.edgeOut s c) * rfac P (P.edgeOut s c) (revC P s c) *
        ∏ i ∈ c.1, P.Vg i := by
  obtain ⟨_, hpp, hsp, hpc⟩ := h
  rcases s with ⟨z, ℓ, m⟩
  rcases c with ⟨St, z', tg⟩
  have hI : promSet P (St, z', tg) = univ.filter fun i => (tg i).2 = true := rfl
  set I := univ.filter fun i => (tg i).2 = true with hIdef
  set Pc := cntF P I (P.promPart z' tg)
  set Sc := cntF P St (P.storedPart z ℓ)
  set m₀ := m - Pc
  have hPc : ∀ y, P.promCount z' tg y = Pc y := fun y =>
    promCount_eq_cntF P z' tg (St, z', tg) rfl y
  have hpc' : ∀ y, Pc y ≤ m y := fun y => (hPc y) ▸ hpc y
  have hm : m = m₀ + Pc := by
    funext y; simp only [m₀, Pi.add_apply, Pi.sub_apply]
    have := hpc' y; omega
  have hm' : P.edgeOutMem (z, ℓ, m) (St, z', tg) = m₀ + Sc := by
    funext y
    show m y - P.promCount z' tg y + P.storeCount z ℓ St y = (m - Pc) y + Sc y
    rw [hPc]; rfl
  have hout : P.edgeOut (z, ℓ, m) (St, z', tg) =
      (z', P.newList ℓ (fun i => (tg i).1), m₀ + Sc) := by
    simp only [MemParams.edgeOut]; rw [hm']
  have hmem_rev : P.edgeOutMem (P.edgeOut (z, ℓ, m) (St, z', tg)) (revC P (z, ℓ, m) (St, z', tg))
      = m := edgeOutMem_rev P (z, ℓ, m) (St, z', tg) hpc
  have hF1 := fock_prod P I (P.promPart z' tg) (fun i => rfl)
    (fun i hi => hpp i (by simpa [I] using hi)) m₀
  have hF2 := fock_prod P St (P.storedPart z ℓ) (fun i => rfl) (fun i hi => hsp i hi) m₀
  rw [← hm] at hF1
  set A := ∏ i ∈ I, (P.memAt m (P.promPart z' tg i) : ℝ)
  set Bn := ∏ i ∈ univ.filter (fun i => ¬ (tg i).2 = true), P.nu i (tg i).1
  set A' := ∏ i ∈ St, (P.memAt (m₀ + Sc) (P.storedPart z ℓ i) : ℝ)
  set Bl := ∏ i ∈ univ.filter (fun i => ¬ i ∈ St), P.nu i (ℓ i (Fin.last P.J))
  have hVI : ∏ i ∈ I, P.Vg i ≠ 0 := prod_ne_zero_iff.2 fun i _ => hV i
  have hVS : ∏ i ∈ St, P.Vg i ≠ 0 := prod_ne_zero_iff.2 fun i _ => hV i
  have c1 : rfac P (z, ℓ, m) (St, z', tg) * ∏ i ∈ I, P.Vg i =
      memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * (A * Bn) := by
    unfold rfac
    rw [hm']
    simp only []
    rw [prod_ite, prod_div_distrib]
    simp only [A, Bn, I]
    have hVI' : (∏ x ∈ univ.filter (fun x => (tg x).2 = true), P.Vg x) ≠ 0 := hVI
    field_simp
  have c2 : rfac P (P.edgeOut (z, ℓ, m) (St, z', tg)) (revC P (z, ℓ, m) (St, z', tg)) *
      ∏ i ∈ St, P.Vg i =
      memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * (A' * Bl) := by
    unfold rfac
    rw [hmem_rev, hout]
    simp only [revC, decide_eq_true_eq]
    rw [prod_ite, prod_div_distrib]
    have hfil : univ.filter (fun i => i ∈ St) = St := by ext i; simp
    rw [hfil]
    simp only [A', Bl]
    have e : ∀ x, P.promPart z (fun i => (ℓ i (Fin.last P.J), decide (i ∈ St))) x =
        P.storedPart z ℓ x := fun x => rfl
    simp only [e]
    field_simp
  have c5a : (∏ i ∈ I, P.nu i (P.promPart z' tg i).2.1) * Bn = ∏ i, P.nu i (tg i).1 :=
    prod_filter_mul_prod_filter_not univ (fun i => (tg i).2 = true) _
  have c5b : (∏ i ∈ St, P.nu i (P.storedPart z ℓ i).2.1) * Bl =
      ∏ i, P.nu i (ℓ i (Fin.last P.J)) := by
    rw [← prod_filter_mul_prod_filter_not univ (fun i => i ∈ St)]
    have hfil : univ.filter (fun i => i ∈ St) = St := by ext i; simp
    rw [hfil]; rfl
  have hLW := listWeight_newList_mul P ℓ (fun i => (tg i).1)
  rw [hI]
  unfold MemParams.stWeight
  rw [hout] at c2
  rw [hout, mul_assoc, c1, mul_assoc (P.listWeight _ * P.memWeight _)]
  simp only []
  rw [c2]
  calc P.listWeight ℓ * P.memWeight m *
        (memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * (A * Bn)) =
      memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * P.listWeight ℓ *
        ((P.memWeight m * A) * Bn) := by ring
    _ = memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * P.memWeight m₀ *
        (P.listWeight ℓ * ∏ i, P.nu i (tg i).1) := by rw [hF1, ← c5a]; ring
    _ = memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) * P.memWeight m₀ *
        (P.listWeight (P.newList ℓ fun i => (tg i).1) * ∏ i, P.nu i (ℓ i (Fin.last P.J))) := by
        rw [hLW]
    _ = memRho ^ P.hitCount z m * memRho ^ P.hitCount z' (m₀ + Sc) *
        P.listWeight (P.newList ℓ fun i => (tg i).1) * ((P.memWeight (m₀ + Sc) * A') * Bl) := by
        rw [hF2, ← c5b]; ring
    _ = _ := by ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: column sums of edge pieces are row sums of the reversed pieces

`coeffP Qc κ` is the edge coefficient restricted to the classes `Qc St I` (stored groups `St`,
promoted groups `I`) with the geometric multiplier replaced by `κ`. `col_via_rev`: the weighted
column sum of `coeffP Qc κ` against `Φ ≥ 0` is at most `3^K` times the row sum of
`coeffP Qc' κ'` against `Φ`, when `Qc St I → Qc' I St` and `‖κ t a b D‖ ≤ ‖κ' (−t) b a D‖`
(`1/2 ≤ Vᵢ ≤ 3/2`, nonnegative `ν`). -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

open Classical in
/-- The edge coefficient restricted to a class of (stores, promotions), multiplier `κ`. -/
noncomputable def coeffP (Qc : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) : ℂ :=
  if Qc c.1 (promSet P c) then coeffK P κ ω s c else 0

lemma lam_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (y : P.PT) : 0 ≤ P.lam y := by
  have h := y.2
  simp only [MemParams.partSet, mem_biUnion, mem_univ, true_and, mem_image, mem_range] at h
  obtain ⟨i, p, hp, l, _, he⟩ := h
  unfold MemParams.lam; rw [← he]; exact hnu i p hp

lemma stWeight_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (s : P.MState) (hs : s ∈ P.stSet) :
    0 ≤ P.stWeight s := by
  simp only [MemParams.stSet, mem_product] at hs
  unfold MemParams.stWeight MemParams.memWeight MemParams.listWeight
  refine mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun k _ => ?_)
    (prod_nonneg fun y _ => by have := lam_nonneg P hnu y; positivity)
  apply hnu
  have := hs.2.1
  simp only [listCands, Fintype.mem_piFinset] at this
  exact this i k

lemma memRho_nonneg : (0 : ℝ) ≤ memRho := by unfold memRho; norm_num

lemma rfac_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV : ∀ i, 0 ≤ P.Vg i)
    (s : P.MState) (c : EC P) (hc : c ∈ P.edgeChoices) : 0 ≤ rfac P s c := by
  unfold rfac
  have hρ := memRho_nonneg
  refine mul_nonneg (mul_nonneg (pow_nonneg hρ _) (prod_nonneg fun i _ => ?_)) (pow_nonneg hρ _)
  split_ifs
  · exact div_nonneg (Nat.cast_nonneg _) (hV i)
  · apply hnu
    simp only [MemParams.edgeChoices, mem_product, mem_univ, true_and,
      Fintype.mem_piFinset] at hc
    exact (hc.2 i).1

lemma revC_mem (s : P.MState) (hs : s ∈ P.stSet) (c : EC P) :
    revC P s c ∈ P.edgeChoices := by
  simp only [MemParams.stSet, mem_product] at hs
  simp only [MemParams.edgeChoices, mem_product, mem_univ, true_and, Fintype.mem_piFinset, revC]
  refine ⟨hs.1, fun i => ⟨?_, trivial⟩⟩
  have := hs.2.1
  simp only [listCands, Fintype.mem_piFinset] at this
  exact this i _

lemma promSet_revC (s : P.MState) (c : EC P) : promSet P (revC P s c) = c.1 := by
  ext i; simp [promSet, revC]

/-- `∏_{St} Vᵢ / ∏_I Vᵢ ≤ 3^K` when `1/2 ≤ Vᵢ ≤ 3/2`. -/
lemma prod_ratio_le (St I : Finset (Fin P.K)) (hV1 : ∀ i, 1 / 2 ≤ P.Vg i)
    (hV2 : ∀ i, P.Vg i ≤ 3 / 2) :
    (∏ i ∈ St, P.Vg i) ≤ 3 ^ P.K * ∏ i ∈ I, P.Vg i := by
  have h1 : ∏ i ∈ St, P.Vg i ≤ (3 / 2) ^ P.K := by
    calc ∏ i ∈ St, P.Vg i ≤ ∏ i ∈ St, (3 / 2 : ℝ) :=
          prod_le_prod (fun i _ => by linarith [hV1 i]) fun i _ => hV2 i
      _ = (3 / 2) ^ St.card := by rw [prod_const]
      _ ≤ (3 / 2) ^ P.K := by
          apply pow_le_pow_right₀ (by norm_num)
          exact (card_le_univ St).trans (by simp)
  have h2 : (1 / 2 : ℝ) ^ P.K ≤ ∏ i ∈ I, P.Vg i := by
    calc (1 / 2 : ℝ) ^ P.K ≤ (1 / 2) ^ I.card := by
          apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
          exact (card_le_univ I).trans (by simp)
      _ = ∏ i ∈ I, (1 / 2 : ℝ) := by rw [prod_const]
      _ ≤ ∏ i ∈ I, P.Vg i := prod_le_prod (fun _ _ => by norm_num) fun i _ => hV1 i
  calc ∏ i ∈ St, P.Vg i ≤ (3 / 2) ^ P.K := h1
    _ = 3 ^ P.K * (1 / 2) ^ P.K := by rw [← mul_pow]; norm_num
    _ ≤ 3 ^ P.K * ∏ i ∈ I, P.Vg i := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Columns via reversal.** -/
theorem col_via_rev (Qc Qc' : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (hQc : ∀ St I, Qc St I → Qc' I St) (κ κ' : ℤ → ℕ → ℕ → ℕ → ℂ)
    (hκ : ∀ t a b D, ‖κ t a b D‖ ≤ ‖κ' (-t) b a D‖) (ω : ℝ × ℝ × ℝ)
    (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV1 : ∀ i, 1 / 2 ≤ P.Vg i)
    (hV2 : ∀ i, P.Vg i ≤ 3 / 2) (Φ : P.MState → ℝ) (hΦ : ∀ s, 0 ≤ Φ s) :
    ∑ s ∈ P.stSet, ∑ c ∈ P.edgeChoices, P.stWeight s * ‖coeffP P Qc κ ω s c‖ *
      (if P.edgeOut s c ∈ P.stSet then Φ (P.edgeOut s c) else 0) ≤
    3 ^ P.K * ∑ s' ∈ P.stSet, Φ s' * ∑ c' ∈ P.edgeChoices,
      P.stWeight s' * ‖coeffP P Qc' κ' ω s' c'‖ := by
  classical
  have hVnn : ∀ i, 0 ≤ P.Vg i := fun i => by linarith [hV1 i]
  have hV0 : ∀ i, P.Vg i ≠ 0 := fun i => by linarith [hV1 i]
  set S := P.stSet ×ˢ P.edgeChoices
  set A := S.filter fun q => ECond P ω q.1 q.2 ∧ Qc q.2.1 (promSet P q.2) ∧
    P.edgeOut q.1 q.2 ∈ P.stSet
  set F : P.MState × EC P → ℝ := fun q => P.stWeight q.1 * ‖coeffP P Qc' κ' ω q.1 q.2‖ * Φ q.1
  set rv : P.MState × EC P → P.MState × EC P := fun q => (P.edgeOut q.1 q.2, revC P q.1 q.2)
  -- the left side as a sum over `A`
  have hL : ∑ s ∈ P.stSet, ∑ c ∈ P.edgeChoices, P.stWeight s * ‖coeffP P Qc κ ω s c‖ *
      (if P.edgeOut s c ∈ P.stSet then Φ (P.edgeOut s c) else 0) =
      ∑ q ∈ A, P.stWeight q.1 * ‖coeffP P Qc κ ω q.1 q.2‖ * Φ (P.edgeOut q.1 q.2) := by
    rw [← sum_product (s := P.stSet) (t := P.edgeChoices)
      (f := fun q => P.stWeight q.1 * ‖coeffP P Qc κ ω q.1 q.2‖ *
        (if P.edgeOut q.1 q.2 ∈ P.stSet then Φ (P.edgeOut q.1 q.2) else 0)), sum_filter]
    refine sum_congr rfl fun q _ => ?_
    by_cases h1 : ECond P ω q.1 q.2 ∧ Qc q.2.1 (promSet P q.2) ∧ P.edgeOut q.1 q.2 ∈ P.stSet
    · rw [if_pos h1, if_pos h1.2.2]
    · rw [if_neg h1]
      by_cases h2 : P.edgeOut q.1 q.2 ∈ P.stSet
      · have : coeffP P Qc κ ω q.1 q.2 = 0 := by
          unfold coeffP coeffK
          by_cases h3 : Qc q.2.1 (promSet P q.2)
          · rw [if_pos h3, if_neg (fun h4 => h1 ⟨h4, h3, h2⟩)]
          · rw [if_neg h3]
        rw [this]; simp
      · rw [if_neg h2]; simp
  -- each term is dominated by `3^K F (rv q)`
  have hterm : ∀ q ∈ A, P.stWeight q.1 * ‖coeffP P Qc κ ω q.1 q.2‖ * Φ (P.edgeOut q.1 q.2) ≤
      3 ^ P.K * F (rv q) := by
    intro q hq
    simp only [A, mem_filter, S, mem_product] at hq
    obtain ⟨⟨hs, hc⟩, hE, hQq, hout⟩ := hq
    have hE' := econd_rev P ω q.1 q.2 hE
    have hD : (padProd q.1.2.1 : ℤ) ∣ detZ q.1.1 q.2.2.1 := hE.1.2.2.2.2.1
    have hw := weight_rev P ω q.1 q.2 hE hV0
    have hrf := rfac_nonneg P hnu hVnn q.1 q.2 hc
    have hrf' := rfac_nonneg P hnu hVnn (P.edgeOut q.1 q.2) _ (revC_mem P q.1 hs q.2)
    have hμ := stWeight_nonneg P hnu q.1 hs
    have hμ' := stWeight_nonneg P hnu _ hout
    have hc1 : ‖coeffP P Qc κ ω q.1 q.2‖ = rfac P q.1 q.2 * ‖κ (detZ q.1.1 q.2.2.1 /
        padProd q.1.2.1) (∏ i, (q.2.2.2 i).1) (lastProd q.1.2.1) (padProd q.1.2.1)‖ := by
      unfold coeffP coeffK
      rw [if_pos hQq, if_pos hE, norm_mul, Complex.norm_real, Real.norm_of_nonneg hrf]
    have hc2 : ‖coeffP P Qc' κ' ω (rv q).1 (rv q).2‖ = rfac P (rv q).1 (rv q).2 *
        ‖κ' (-(detZ q.1.1 q.2.2.1 / padProd q.1.2.1)) (lastProd q.1.2.1)
          (∏ i, (q.2.2.2 i).1) (padProd q.1.2.1)‖ := by
      unfold coeffP coeffK
      simp only [rv]
      have hr1 : (revC P q.1 q.2).1 = promSet P q.2 := rfl
      rw [promSet_revC, hr1, if_pos (hQc _ _ hQq), if_pos hE', norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hrf', det_rev P q.1 q.2 hD, prod_labels_rev, lastProd_out,
        padProd_out]
    have hratio := prod_ratio_le P q.2.1 (promSet P q.2) hV1 hV2
    have hpos : 0 < ∏ i ∈ promSet P q.2, P.Vg i := prod_pos fun i _ => by linarith [hV1 i]
    -- μ rfac ≤ 3^K μ' rfac'
    have hμr : P.stWeight q.1 * rfac P q.1 q.2 ≤
        3 ^ P.K * (P.stWeight (rv q).1 * rfac P (rv q).1 (rv q).2) := by
      have h1 : P.stWeight q.1 * rfac P q.1 q.2 * ∏ i ∈ promSet P q.2, P.Vg i ≤
          3 ^ P.K * (P.stWeight (rv q).1 * rfac P (rv q).1 (rv q).2) *
            ∏ i ∈ promSet P q.2, P.Vg i := by
        rw [hw]
        calc P.stWeight (P.edgeOut q.1 q.2) * rfac P (P.edgeOut q.1 q.2) (revC P q.1 q.2) *
              ∏ i ∈ q.2.1, P.Vg i ≤
            P.stWeight (P.edgeOut q.1 q.2) * rfac P (P.edgeOut q.1 q.2) (revC P q.1 q.2) *
              (3 ^ P.K * ∏ i ∈ promSet P q.2, P.Vg i) :=
              mul_le_mul_of_nonneg_left hratio (mul_nonneg hμ' hrf')
          _ = _ := by simp only [rv]; ring
      exact le_of_mul_le_mul_right h1 hpos
    have hκq := hκ (detZ q.1.1 q.2.2.1 / padProd q.1.2.1) (∏ i, (q.2.2.2 i).1)
      (lastProd q.1.2.1) (padProd q.1.2.1)
    have hΦq := hΦ (P.edgeOut q.1 q.2)
    simp only [F]
    rw [hc1, hc2]
    calc P.stWeight q.1 * (rfac P q.1 q.2 * ‖κ (detZ q.1.1 q.2.2.1 / ↑(padProd q.1.2.1))
          (∏ i, (q.2.2.2 i).1) (lastProd q.1.2.1) (padProd q.1.2.1)‖) *
          Φ (P.edgeOut q.1 q.2) =
        (P.stWeight q.1 * rfac P q.1 q.2) * ‖κ (detZ q.1.1 q.2.2.1 / ↑(padProd q.1.2.1))
          (∏ i, (q.2.2.2 i).1) (lastProd q.1.2.1) (padProd q.1.2.1)‖ *
          Φ (P.edgeOut q.1 q.2) := by ring
      _ ≤ (3 ^ P.K * (P.stWeight (rv q).1 * rfac P (rv q).1 (rv q).2)) *
          ‖κ' (-(detZ q.1.1 q.2.2.1 / ↑(padProd q.1.2.1))) (lastProd q.1.2.1)
            (∏ i, (q.2.2.2 i).1) (padProd q.1.2.1)‖ * Φ (P.edgeOut q.1 q.2) := by
          gcongr
      _ = _ := by simp only [rv]; ring
  -- `rv` is injective on `A` and maps into `S`
  have hinj : Set.InjOn rv A := by
    intro q hq q' hq' heq
    simp only [A, coe_filter, Set.mem_ofPred_eq] at hq hq'
    have e1 : rv (rv q) = q := by
      simp only [rv]
      rw [edgeOut_rev P q.1 q.2 hq.2.1.2.2.2, revC_rev P q.1 q.2 hq.2.1.2.2.2]
    have e2 : rv (rv q') = q' := by
      simp only [rv]
      rw [edgeOut_rev P q'.1 q'.2 hq'.2.1.2.2.2, revC_rev P q'.1 q'.2 hq'.2.1.2.2.2]
    rw [← e1, ← e2, heq]
  have hmaps : ∀ q ∈ A, rv q ∈ S := by
    intro q hq
    simp only [A, mem_filter, S, mem_product] at hq
    simp only [S, mem_product, rv]
    exact ⟨hq.2.2.2, revC_mem P q.1 hq.1.1 q.2⟩
  have hFnn : ∀ q ∈ S, 0 ≤ F q := by
    intro q hq
    simp only [S, mem_product] at hq
    exact mul_nonneg (mul_nonneg (stWeight_nonneg P hnu q.1 hq.1) (norm_nonneg _)) (hΦ _)
  rw [hL]
  calc ∑ q ∈ A, P.stWeight q.1 * ‖coeffP P Qc κ ω q.1 q.2‖ * Φ (P.edgeOut q.1 q.2) ≤
      ∑ q ∈ A, 3 ^ P.K * F (rv q) := sum_le_sum hterm
    _ = 3 ^ P.K * ∑ q ∈ A.image rv, F q := by rw [mul_sum, sum_image hinj]
    _ ≤ 3 ^ P.K * ∑ q ∈ S, F q := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨q₀, hq₀, rfl⟩ := mem_image.1 hq
          exact hmaps q₀ hq₀
        · intro q hq _; exact hFnn q hq
    _ = _ := by
        congr 1
        rw [sum_product]
        refine sum_congr rfl fun s' _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun c' _ => ?_
        simp only [F]; ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102D: the exact outer reduction of (10.9) ([21] §3.1, (3.10)–(3.11))

`Q_Y − Q_Y^maj = Q^sh − Q^{maj,sh} + Q^min`, where `Q^sh`, `Q^{maj,sh}` are the parts of the two
squares over label pairs whose products `a, b` are not coprime, and `Q^min` is the coprime part
of the minor-arc square, with kernel `ψ(t/Y) ∫_{[0,1) ∖ 𝔐} e(θ(t − b + a)) dθ`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary inputs -/

/-- `∫_{[0,1)} e(θ n) dθ = 1_{n = 0}`. -/
lemma integral_Ico_exp_int (n : ℤ) :
    ∫ θ in Set.Ico (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * ((θ * n : ℝ) : ℂ)) =
      if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn; simp
  · rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    have := integral_exp_mul_complex (a := 0) (b := 1) hc
    simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [show (fun θ : ℝ => Complex.exp (2 * π * Complex.I * ((θ : ℂ) * n))) =
        fun θ : ℝ => Complex.exp (2 * π * Complex.I * n * θ) by
      funext θ; ring_nf]
    rw [this]
    have h1 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show (2 * π * Complex.I * n : ℂ) = n * (2 * π * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1]; simp

lemma majorArcs_subset (x A₀ Y : ℝ) : majorArcs x A₀ Y ⊆ Set.Ico 0 1 :=
  fun _ h => ⟨h.1, h.2.1⟩

lemma measurableSet_majorArcs (x A₀ Y : ℝ) : MeasurableSet (majorArcs x A₀ Y) := by
  have : majorArcs x A₀ Y = Set.Ico 0 1 ∩ ⋃ k : ℕ, ⋃ c : ℤ,
      {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} := by
    ext θ
    simp only [majorArcs, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ico, Set.mem_iUnion]
    constructor
    · rintro ⟨h0, h1, k, hk1, hk2, c, hc, hd⟩; exact ⟨⟨h0, h1⟩, k, c, hk1, hk2, hc, hd⟩
    · rintro ⟨⟨h0, h1⟩, k, c, hk1, hk2, hc, hd⟩; exact ⟨h0, h1, k, hk1, hk2, c, hc, hd⟩
  rw [this]
  refine measurableSet_Ico.inter (MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun c => ?_)
  by_cases hP : 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1
  · have : {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} = {θ : ℝ | |θ - c / k| ≤ 2 * log x ^ A₀ / Y} := by
      ext θ; simp only [Set.mem_ofPred_eq]; tauto
    rw [this]
    exact measurableSet_le (by fun_prop) measurable_const
  · have : {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} = ∅ := by
      ext θ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; tauto
    rw [this]; exact MeasurableSet.empty

/-- `H_𝔪 = ψ(t/Y) 1_{t = b − a} − H_𝔐`. -/
lemma minorKernel_eq (x A₀ Y : ℝ) (t a b : ℤ) :
    minorKernel x A₀ Y t a b =
      (arcCutoff (t / Y) : ℂ) * (if t - b + a = 0 then 1 else 0) - majorKernel x A₀ Y t a b := by
  unfold minorKernel majorKernel
  have hint : IntegrableOn (fun θ : ℝ =>
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))) (Set.Ico 0 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ico_subset_Icc_self
  rw [setIntegral_sdiff (measurableSet_majorArcs x A₀ Y) hint (majorArcs_subset x A₀ Y), mul_sub]
  congr 2
  have := integral_Ico_exp_int (t - b + a)
  push_cast at this ⊢
  rw [this]

lemma dyadicBump_ne_zero {u : ℝ} (h : dyadicBump u ≠ 0) : 1 < u ∧ u < 4 := by
  unfold dyadicBump at h
  constructor
  · by_contra hu
    push Not at hu
    apply h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · by_contra hu
    push Not at hu
    apply h
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith)]
    simp

/-! ## The identity -/

/-! ## The reduction of (10.9) to the shared-label bound (D1b) and the minor-arc bound (D1c) -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102G: elementary facts copied from `L102D_Shared`

Copies (renamed with a prime) of the bounds on `dyadicBump`, `arcCutoff`, the measure of the major
arcs, the size of group primes and two facts from `L102D_Good`, so that the edge bound needs
neither `L102D_Shared` nor `L102D_Good`. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset MeasureTheory

lemma circNorm_eq_norm' (t : ℝ) : circNorm t = ‖(t : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]; rfl

/-- For a nonzero integer `n`, `{r ∈ (0,1] : ‖n r‖ ≤ ε}` has measure at most `2ε`
(multiplication by `n` preserves Haar measure on `ℝ/ℤ`). -/
lemma volume_circNorm_le' (n : ℤ) (hn : n ≠ 0) (ε : ℝ) :
    volume ({r : ℝ | circNorm (n * r) ≤ ε} ∩ Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * ε) := by
  set f : ℝ → UnitAddCircle := fun r => n • (r : UnitAddCircle)
  have hf : MeasurePreserving f (volume.restrict (Set.Ioc (0 : ℝ) 1)) volume := by
    have := (Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) hn).comp
      (AddCircle.measurePreserving_mk (1 : ℝ) 0)
    simpa [f, Function.comp_def] using this
  have hset : {r : ℝ | circNorm (n * r) ≤ ε} = f ⁻¹' Metric.closedBall 0 ε := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, f]
    rw [circNorm_eq_norm', ← AddCircle.coe_zsmul]
    simp
  have hmeas : MeasurableSet (f ⁻¹' Metric.closedBall 0 ε) :=
    hf.measurable measurableSet_closedBall
  rw [hset, ← Measure.restrict_apply hmeas, hf.measure_preimage
    measurableSet_closedBall.nullMeasurableSet, AddCircle.volume_closedBall]
  exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-- `L^b ≤ ε L^c` eventually, for `b < c` and `ε > 0`. -/
lemma eventually_rpow_le_rpow' {b c : ℝ} (hbc : b < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, L ^ b ≤ ε * L ^ c := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.2 hbc)).eventually (ge_mem_nhds hε)
  filter_upwards [h, Filter.eventually_gt_atTop 0] with L hL hL0
  have : L ^ b = L ^ (-(c - b)) * L ^ c := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hL (by positivity)

lemma dyadicBump_nonneg' (u : ℝ) : 0 ≤ dyadicBump u := by
  unfold dyadicBump
  rcases le_or_gt u 0 with hu | hu
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]; simp
  · exact sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

lemma dyadicBump_le_one' (u : ℝ) : dyadicBump u ≤ 1 := by
  unfold dyadicBump
  linarith [Real.smoothTransition.le_one (u - 1), Real.smoothTransition.nonneg (u / 2 - 1)]

lemma abs_dyadicBump_le_one' (u : ℝ) : |dyadicBump u| ≤ 1 := by
  rw [abs_of_nonneg (dyadicBump_nonneg' u)]; exact dyadicBump_le_one' u

lemma abs_arcCutoff_le' (u : ℝ) : |arcCutoff u| ≤ if |u| < 5 then 1 else 0 := by
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

/-- `vol 𝔐 ≤ 4 L^{3A₀}/Y` (`L = log x ≥ 1`, `A₀ ≥ 0`, `Y > 0`). -/
lemma volume_majorArcs_le' (x A₀ Y : ℝ) (hL : 1 ≤ log x) (hA₀ : 0 ≤ A₀) (hY : 0 < Y) :
    volume (majorArcs x A₀ Y) ≤ ENNReal.ofReal (4 * log x ^ (3 * A₀) / Y) := by
  set Q := log x ^ A₀
  set K₀ := ⌊Q⌋₊
  set ρ := 2 * Q / Y
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hL hA₀
  have hsub : majorArcs x A₀ Y ⊆ {0} ∪ ⋃ k ∈ Icc 1 K₀,
      ({θ : ℝ | circNorm (((k : ℤ) : ℝ) * θ) ≤ k * ρ} ∩ Set.Ioc 0 1) := by
    rintro θ ⟨h0, h1, k, hk1, hkQ, c, -, hc⟩
    rcases h0.lt_or_eq with h0 | h0
    · right
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_Icc]
      refine ⟨k, ⟨hk1, Nat.le_floor hkQ⟩, ?_, h0, h1.le⟩
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      calc circNorm (((k : ℤ) : ℝ) * θ) ≤ |((k : ℤ) : ℝ) * θ - c| := round_le _ c
        _ = k * |θ - c / k| := by
            have e : ((k : ℤ) : ℝ) * θ - c = k * (θ - c / k) := by
              push_cast; field_simp
            rw [e, abs_mul, abs_of_pos hk0]
        _ ≤ k * ρ := by gcongr
    · left; exact h0.symm
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_singleton, zero_add]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ k ∈ Icc 1 K₀, volume ({θ : ℝ | circNorm (((k : ℤ) : ℝ) * θ) ≤ k * ρ} ∩
      Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * (k * ρ)) := fun k hk =>
    volume_circNorm_le' k (by have := (mem_Icc.1 hk).1; omega) _
  refine (sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hK₀ : (K₀ : ℝ) ≤ Q := Nat.floor_le (by positivity)
  have hsum : ∑ k ∈ Icc 1 K₀, 2 * ((k : ℝ) * ρ) ≤ ∑ _k ∈ Icc 1 K₀, 2 * (Q * ρ) := by
    refine sum_le_sum fun k hk => ?_
    have : (k : ℝ) ≤ Q := (Nat.cast_le.2 (mem_Icc.1 hk).2).trans hK₀
    gcongr
  refine hsum.trans ?_
  rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  have h3 : log x ^ (3 * A₀) = Q * Q * Q := by
    rw [show 3 * A₀ = A₀ + A₀ + A₀ by ring, Real.rpow_add (by linarith),
      Real.rpow_add (by linarith)]
  rw [h3]
  have hρ : 0 ≤ ρ := by positivity
  calc (K₀ : ℝ) * (2 * (Q * ρ)) ≤ Q * (2 * (Q * ρ)) := by gcongr
    _ = 4 * (Q * Q * Q) / Y := by simp only [ρ]; ring

lemma le_of_mem_primeGroup' {x b : ℝ} {q : ℕ} (h : q ∈ primeGroup x b) :
    exp (log x ^ b) ≤ q ∧ (q : ℝ) ≤ exp (2 * log x ^ b) := by
  unfold primeGroup at h
  simp only [mem_filter, mem_range] at h
  refine ⟨h.2.2, ?_⟩
  have := Nat.lt_succ_iff.1 h.1
  exact (Nat.cast_le.2 this).trans (Nat.floor_le (exp_pos _).le)

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: the pieces of the edge

`edgeMult j = rawK − majK j` (`minorKernel = ψ·1[t = b − a] − majorKernel`, both parities), the
kernels are symmetric under `(t, a, b) ↦ (−t, b, a)` in norm, and the edge coefficient splits into
the clean class (no stores, no promotions; full minor kernel) and the dirty classes `D1`
(some promotion) and `D2` (stores only), each with a raw and a comparison part
(`edgeCoeff_split`, `ipμ_edgeOp_split`). `piece_sym_bound`: a dirty piece with averaged row
bound `R` whose reversed class has averaged row bound `R'` has bilinear norm `≤ √R √(3^K R')`. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset MeasureTheory
open scoped ComplexConjugate

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

lemma arcCutoff_neg (u : ℝ) : arcCutoff (-u) = arcCutoff u := by
  unfold arcCutoff; rw [sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

lemma majorKernel_neg (x A₀ Y : ℝ) (t a b : ℤ) :
    majorKernel x A₀ Y (-t) b a = conj (majorKernel x A₀ Y t a b) := by
  unfold majorKernel
  rw [map_mul, Complex.conj_ofReal, ← integral_conj]
  congr 1
  · push_cast; rw [neg_div, arcCutoff_neg]
  · congr 1; funext θ
    rw [← Complex.exp_conj]; congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast; ring

lemma norm_majorKernel_neg (x A₀ Y : ℝ) (t a b : ℤ) :
    ‖majorKernel x A₀ Y (-t) b a‖ = ‖majorKernel x A₀ Y t a b‖ := by
  rw [majorKernel_neg, Complex.norm_conj]

/-- The raw kernel `(d₀/D) η(b/Y) η(a/Y) ψ(t/Y) 1[t − b + a = 0]`. -/
noncomputable def rawK (t : ℤ) (a b D : ℕ) : ℂ :=
  ((((P.d₀ : ℝ) / D) * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y) : ℝ) : ℂ) *
    ((arcCutoff (t / P.Y) : ℝ) : ℂ) * (if t - b + a = 0 then 1 else 0)

/-- The comparison kernel `(d₀/D) η η H_𝔐` (conjugated and reversed on odd edges). -/
noncomputable def majK (j : ℕ) (t : ℤ) (a b D : ℕ) : ℂ :=
  ((((P.d₀ : ℝ) / D) * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y) : ℝ) : ℂ) *
    (if Even j then majorKernel P.x P.A₀ P.Y t a b
      else conj (majorKernel P.x P.A₀ P.Y (-t) b a))

lemma edgeMult_eq_sub (j : ℕ) (t : ℤ) (a b D : ℕ) :
    P.edgeMult j t a b D = rawK P t a b D - majK P j t a b D := by
  unfold MemParams.edgeMult rawK majK
  split_ifs with hj h1
  · rw [L102D.minorKernel_eq]; rw [if_pos h1]; ring
  · rw [L102D.minorKernel_eq]; rw [if_neg h1]; ring
  · rw [L102D.minorKernel_eq, map_sub, map_mul, Complex.conj_ofReal]
    have : (-t - (a : ℤ) + (b : ℤ) = 0) := by omega
    rw [if_pos this, map_one, mul_one]
    push_cast; rw [neg_div, arcCutoff_neg]; ring
  · rw [L102D.minorKernel_eq, map_sub, map_mul, Complex.conj_ofReal]
    have : ¬ (-t - (a : ℤ) + (b : ℤ) = 0) := by omega
    rw [if_neg this, map_zero, mul_zero]
    ring

lemma norm_rawK_swap (t : ℤ) (a b D : ℕ) : ‖rawK P (-t) b a D‖ = ‖rawK P t a b D‖ := by
  unfold rawK
  have h : ((-t : ℤ) : ℝ) / P.Y = -((t : ℝ) / P.Y) := by push_cast; ring
  rw [h, arcCutoff_neg]
  have hc : (-t - (a : ℤ) + (b : ℤ) = 0) ↔ (t - (b : ℤ) + (a : ℤ) = 0) := by omega
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases h' : t - (b : ℤ) + (a : ℤ) = 0
  · rw [if_pos (hc.2 h'), if_pos h']; ring
  · rw [if_neg (fun h'' => h' (hc.1 h'')), if_neg h']; ring

lemma norm_majK_eq (j : ℕ) (t : ℤ) (a b D : ℕ) :
    ‖majK P j t a b D‖ = |(P.d₀ : ℝ) / D * dyadicBump ((b : ℝ) / P.Y) *
      dyadicBump ((a : ℝ) / P.Y)| * ‖majorKernel P.x P.A₀ P.Y t a b‖ := by
  unfold majK
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  split_ifs
  · rfl
  · rw [Complex.norm_conj, norm_majorKernel_neg]

lemma norm_majK_swap (j : ℕ) (t : ℤ) (a b D : ℕ) :
    ‖majK P j (-t) b a D‖ = ‖majK P j t a b D‖ := by
  rw [norm_majK_eq, norm_majK_eq, norm_majorKernel_neg, mul_right_comm ((P.d₀ : ℝ) / D)]

/-! ## The classes and the split of the edge coefficient -/

/-- Clean: no stores and no promotions. -/
def clsClean (St I : Finset (Fin P.K)) : Prop := St = ∅ ∧ I = ∅

/-- `D1`: at least one promotion. -/
def clsD1 (_St I : Finset (Fin P.K)) : Prop := I.Nonempty

/-- `D2`: stores but no promotion. -/
def clsD2 (St I : Finset (Fin P.K)) : Prop := I = ∅ ∧ St.Nonempty

/-- At least one store. -/
def clsS (St _I : Finset (Fin P.K)) : Prop := St.Nonempty

/-- No promotion. -/
def clsNoProm (_St I : Finset (Fin P.K)) : Prop := I = ∅

/-- All classes. -/
def clsAll (_St _I : Finset (Fin P.K)) : Prop := True

lemma coeffK_sub (κ₁ κ₂ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) :
    coeffK P (fun t a b D => κ₁ t a b D - κ₂ t a b D) ω s c = coeffK P κ₁ ω s c - coeffK P κ₂ ω s c := by
  unfold coeffK; split_ifs <;> ring

lemma edgeCoeff_split (ω : ℝ × ℝ × ℝ) (j : ℕ) (s : P.MState) (c : EC P) :
    P.edgeCoeff ω j s c = coeffP P (clsClean P) (P.edgeMult j) ω s c +
      (coeffP P (clsD1 P) (rawK P) ω s c - coeffP P (clsD1 P) (majK P j) ω s c) +
      (coeffP P (clsD2 P) (rawK P) ω s c - coeffP P (clsD2 P) (majK P j) ω s c) := by
  classical
  rw [edgeCoeff_eq]
  have hsplit : P.edgeMult j = fun t a b D => rawK P t a b D - majK P j t a b D := by
    funext t a b D; exact edgeMult_eq_sub P j t a b D
  unfold coeffP clsClean clsD1 clsD2
  by_cases hI : promSet P c = ∅
  · have h2 : ¬ (promSet P c).Nonempty := by rw [hI]; exact not_nonempty_empty
    by_cases hS : c.1 = ∅
    · have h1 : c.1 = ∅ ∧ promSet P c = ∅ := ⟨hS, hI⟩
      have h3 : ¬ (promSet P c = ∅ ∧ c.1.Nonempty) := fun h => by
        rw [hS] at h; exact not_nonempty_empty h.2
      simp only [if_pos h1, if_neg h2, if_neg h3]
      ring
    · have h1 : ¬ (c.1 = ∅ ∧ promSet P c = ∅) := fun h => hS h.1
      have h3 : promSet P c = ∅ ∧ c.1.Nonempty := ⟨hI, nonempty_iff_ne_empty.2 hS⟩
      simp only [if_neg h1, if_neg h2, if_pos h3, hsplit, coeffK_sub]
      ring
  · have h1 : ¬ (c.1 = ∅ ∧ promSet P c = ∅) := fun h => hI h.2
    have h2 : (promSet P c).Nonempty := nonempty_iff_ne_empty.2 hI
    have h3 : ¬ (promSet P c = ∅ ∧ c.1.Nonempty) := fun h => hI h.1
    simp only [if_neg h1, if_pos h2, if_neg h3, hsplit, coeffK_sub]
    ring

/-- The bilinear form of one piece. -/
noncomputable def pieceB (Qc : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (G F : P.MState → ℂ) : ℂ :=
  ∑ s ∈ P.stSet, (P.stWeight s : ℂ) * (conj (G s) * ∑ c ∈ P.edgeChoices, coeffP P Qc κ ω s c *
    (if P.edgeOut s c ∈ P.stSet then F (P.edgeOut s c) else 0))

lemma ipμ_edgeOp_split (ω : ℝ × ℝ × ℝ) (j : ℕ) (g f : P.MState → ℂ) :
    ipμ P g (P.edgeOp ω j f) =
      pieceB P (clsClean P) (P.edgeMult j) ω (P.symM g) (P.symM f) +
      (pieceB P (clsD1 P) (rawK P) ω (P.symM g) (P.symM f) -
        pieceB P (clsD1 P) (majK P j) ω (P.symM g) (P.symM f)) +
      (pieceB P (clsD2 P) (rawK P) ω (P.symM g) (P.symM f) -
        pieceB P (clsD2 P) (majK P j) ω (P.symM g) (P.symM f)) := by
  rw [ipμ_edgeOp]
  unfold ipμ pieceB MemParams.edgeOrd
  simp only [← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun s _ => ?_
  simp only [edgeCoeff_split, add_mul, sub_mul, sum_add_distrib, sum_sub_distrib]
  ring

/-! ## The bound for one dirty piece -/

/-- The row sum of a piece at a state. -/
noncomputable def rowSum (Qc : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState) : ℝ :=
  ∑ c ∈ P.edgeChoices, ‖coeffP P Qc κ ω s c‖

/-- The row sum averaged over source slot permutations. -/
noncomputable def avgRow (Qc : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState) : ℝ :=
  ((Fintype.card (SlotPerm P) : ℕ) : ℝ)⁻¹ * ∑ pr : SlotPerm P, rowSum P Qc κ ω (permS P pr s)

lemma avgRow_le_of_rowSum (Qc : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (R : ℝ)
    (h : ∀ s ∈ P.stSet, rowSum P Qc κ ω s ≤ R) (s : P.MState) (hs : s ∈ P.stSet) :
    avgRow P Qc κ ω s ≤ R := by
  unfold avgRow
  set N := ((Fintype.card (SlotPerm P) : ℕ) : ℝ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  calc N⁻¹ * ∑ pr : SlotPerm P, rowSum P Qc κ ω (permS P pr s) ≤ N⁻¹ * ∑ _pr : SlotPerm P, R :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun pr _ =>
          h _ ((mem_stSet_permS P pr s).2 hs)) (by positivity)
    _ = R := by rw [sum_const, card_univ, nsmul_eq_mul]; field_simp; rfl

lemma norm_coeffP_mono (Qc₁ Qc₂ : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (h : ∀ St I, Qc₁ St I → Qc₂ St I) (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState)
    (c : EC P) : ‖coeffP P Qc₁ κ ω s c‖ ≤ ‖coeffP P Qc₂ κ ω s c‖ := by
  classical
  unfold coeffP
  by_cases h1 : Qc₁ c.1 (promSet P c)
  · rw [if_pos h1, if_pos (h _ _ h1)]
  · rw [if_neg h1]; simp

lemma norm_coeffP_or (Qc₁ Qc₂ Qc : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (h : ∀ St I, Qc St I → Qc₁ St I ∨ Qc₂ St I) (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ)
    (s : P.MState) (c : EC P) :
    ‖coeffP P Qc κ ω s c‖ ≤ ‖coeffP P Qc₁ κ ω s c‖ + ‖coeffP P Qc₂ κ ω s c‖ := by
  classical
  unfold coeffP
  by_cases h0 : Qc c.1 (promSet P c)
  · rw [if_pos h0]
    rcases h _ _ h0 with h1 | h2
    · rw [if_pos h1]; exact le_add_of_nonneg_right (norm_nonneg _)
    · rw [if_pos h2]; exact le_add_of_nonneg_left (norm_nonneg _)
  · rw [if_neg h0, norm_zero]; positivity

/-- **One dirty piece.** If the class `Qc` has averaged rows `≤ R` and the reversed class `Qc'`
has averaged rows `≤ R'`, the piece has bilinear norm `≤ √R √(3^K R')` on symmetric
functions. -/
theorem piece_sym_bound (Qc Qc' : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (hQc : ∀ St I, Qc St I → Qc' I St) (κ : ℤ → ℕ → ℕ → ℕ → ℂ)
    (hκ : ∀ t a b D, ‖κ t a b D‖ ≤ ‖κ (-t) b a D‖) (ω : ℝ × ℝ × ℝ)
    (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV1 : ∀ i, 1 / 2 ≤ P.Vg i)
    (hV2 : ∀ i, P.Vg i ≤ 3 / 2) (R R' : ℝ) (hR : 0 ≤ R) (hR' : 0 ≤ R')
    (hrow : ∀ s ∈ P.stSet, avgRow P Qc κ ω s ≤ R)
    (hrow' : ∀ s ∈ P.stSet, avgRow P Qc' κ ω s ≤ R') (g f : P.MState → ℂ) :
    ‖pieceB P Qc κ ω (P.symM g) (P.symM f)‖ ≤
      √R * √(3 ^ P.K * R') * P.wNorm g * P.wNorm f := by
  have hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s := fun s hs => stWeight_nonneg P hnu s hs
  have hsymμ : ∀ (G : P.MState → ℂ), (∀ σ s, G (permS P σ s) = G s) →
      ∀ σ s, P.stWeight (permS P σ s) * ‖G (permS P σ s)‖ ^ 2 = P.stWeight s * ‖G s‖ ^ 2 := by
    intro G hG σ s; rw [stWeight_permS, hG]
  have hGs : ∀ σ s, P.symM g (permS P σ s) = P.symM g s := fun σ s => symM_permS P g σ s
  have hFs : ∀ σ s, P.symM f (permS P σ s) = P.symM f s := fun σ s => symM_permS P f σ s
  have key := piece_bound P P.edgeChoices (coeffP P Qc κ ω) P.edgeOut (P.symM g) (P.symM f) R
    (3 ^ P.K * R') hμ ?_ ?_
  · refine key.trans ?_
    have h1 := wNorm_symM_le P hμ g
    have h2 := wNorm_symM_le P hμ f
    have h3 : 0 ≤ P.wNorm (P.symM g) := Real.sqrt_nonneg _
    have h4 : 0 ≤ P.wNorm (P.symM f) := Real.sqrt_nonneg _
    have h5 : 0 ≤ √R * √(3 ^ P.K * R') := by positivity
    have h6 : 0 ≤ P.wNorm g := Real.sqrt_nonneg _
    calc √R * √(3 ^ P.K * R') * P.wNorm (P.symM g) * P.wNorm (P.symM f) ≤
        √R * √(3 ^ P.K * R') * P.wNorm g * P.wNorm (P.symM f) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h5) h4
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (mul_nonneg h5 h6)
  · -- rows
    calc ∑ s ∈ P.stSet, ∑ c ∈ P.edgeChoices, P.stWeight s * ‖coeffP P Qc κ ω s c‖ *
          (if P.edgeOut s c ∈ P.stSet then 1 else 0) * ‖P.symM g s‖ ^ 2 ≤
        ∑ s ∈ P.stSet, (P.stWeight s * ‖P.symM g s‖ ^ 2) * rowSum P Qc κ ω s := by
          refine sum_le_sum fun s hs => ?_
          rw [rowSum, mul_sum]
          refine sum_le_sum fun c _ => ?_
          have h0 := mul_nonneg (mul_nonneg (hμ s hs) (sq_nonneg ‖P.symM g s‖))
            (norm_nonneg (coeffP P Qc κ ω s c))
          split_ifs
          · exact le_of_eq (by ring)
          · simp only [mul_zero, zero_mul]; exact h0
      _ = ∑ s ∈ P.stSet, (P.stWeight s * ‖P.symM g s‖ ^ 2) * avgRow P Qc κ ω s :=
          sum_sym_avg P _ _ (hsymμ _ hGs)
      _ ≤ ∑ s ∈ P.stSet, (P.stWeight s * ‖P.symM g s‖ ^ 2) * R :=
          sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hrow s hs)
            (mul_nonneg (hμ s hs) (sq_nonneg _))
      _ = R * ∑ s ∈ P.stSet, P.stWeight s * ‖P.symM g s‖ ^ 2 := by
          rw [mul_sum]; exact sum_congr rfl fun s _ => by ring
  · -- columns
    have hc := col_via_rev P Qc Qc' hQc κ κ hκ ω hnu hV1 hV2 (fun s => ‖P.symM f s‖ ^ 2)
      (fun s => sq_nonneg _)
    refine hc.trans ?_
    calc 3 ^ P.K * ∑ s' ∈ P.stSet, ‖P.symM f s'‖ ^ 2 * ∑ c' ∈ P.edgeChoices,
          P.stWeight s' * ‖coeffP P Qc' κ ω s' c'‖ =
        3 ^ P.K * ∑ s' ∈ P.stSet, (P.stWeight s' * ‖P.symM f s'‖ ^ 2) * rowSum P Qc' κ ω s' := by
          congr 1; refine sum_congr rfl fun s' _ => ?_
          rw [rowSum, mul_sum, mul_sum]; refine sum_congr rfl fun c' _ => by ring
      _ = 3 ^ P.K * ∑ s' ∈ P.stSet, (P.stWeight s' * ‖P.symM f s'‖ ^ 2) *
          avgRow P Qc' κ ω s' := by rw [sum_sym_avg P _ _ (hsymμ _ hFs)]; rfl
      _ ≤ 3 ^ P.K * ∑ s' ∈ P.stSet, (P.stWeight s' * ‖P.symM f s'‖ ^ 2) * R' := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (hrow' s hs)
            (mul_nonneg (hμ s hs) (sq_nonneg _))
      _ = 3 ^ P.K * R' * ∑ s ∈ P.stSet, P.stWeight s * ‖P.symM f s‖ ^ 2 := by
          rw [mul_sum, mul_sum]; refine sum_congr rfl fun s _ => by ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: bilinear forms on finite sets

`bil S T K g f = Σ_{x∈S} Σ_{y∈T} conj(g x) K(x,y) f(y)`, `l2 S g = (Σ_{x∈S} ‖g x‖²)^{1/2}`,
`BilBound S T K C`: `‖bil S T K g f‖ ≤ C ‖g‖ ‖f‖` for all `g, f`. Closure under sums, diagonal
multipliers, restriction to subsets, compression along injections, direct sums of blocks, and the
Schur test. -/

namespace ArtinPrimitiveRoots.L102G

open Finset
open scoped ComplexConjugate

variable {α β α' β' ι : Type*}

/-- The bilinear form. -/
def bil (S : Finset α) (T : Finset β) (K : α → β → ℂ) (g : α → ℂ) (f : β → ℂ) : ℂ :=
  ∑ x ∈ S, ∑ y ∈ T, conj (g x) * K x y * f y

/-- The `ℓ²` norm on a finite set. -/
noncomputable def l2 (S : Finset α) (g : α → ℂ) : ℝ := √(∑ x ∈ S, ‖g x‖ ^ 2)

/-- The bilinear bound. -/
def BilBound (S : Finset α) (T : Finset β) (K : α → β → ℂ) (C : ℝ) : Prop :=
  ∀ g f, ‖bil S T K g f‖ ≤ C * l2 S g * l2 T f

lemma l2_nonneg (S : Finset α) (g : α → ℂ) : 0 ≤ l2 S g := Real.sqrt_nonneg _

lemma l2_sq (S : Finset α) (g : α → ℂ) : l2 S g ^ 2 = ∑ x ∈ S, ‖g x‖ ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)

lemma l2_mul_le (S : Finset α) (g : α → ℂ) (w : α → ℂ) (a : ℝ) (hw : ∀ x ∈ S, ‖w x‖ ≤ a) :
    l2 S (fun x => w x * g x) ≤ a * l2 S g := by
  have ha : 0 ≤ a ∨ S = ∅ := by
    by_cases hS : S = ∅
    · exact Or.inr hS
    · obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hS
      exact Or.inl ((norm_nonneg _).trans (hw x hx))
  rcases ha with ha | hS
  · unfold l2
    rw [← Real.sqrt_sq ha, ← Real.sqrt_mul (sq_nonneg _)]
    apply Real.sqrt_le_sqrt
    rw [mul_sum]
    refine sum_le_sum fun x hx => ?_
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hw x hx) 2) (sq_nonneg _)
  · subst hS; simp [l2]

lemma bilBound_mono (S : Finset α) (T : Finset β) (K : α → β → ℂ) (C C' : ℝ) (h : C ≤ C')
    (hK : BilBound S T K C) : BilBound S T K C' := by
  intro g f
  refine (hK g f).trans ?_
  have := l2_nonneg S g; have := l2_nonneg T f
  gcongr

lemma bil_add (S : Finset α) (T : Finset β) (K₁ K₂ : α → β → ℂ) (g : α → ℂ) (f : β → ℂ) :
    bil S T (fun x y => K₁ x y + K₂ x y) g f = bil S T K₁ g f + bil S T K₂ g f := by
  unfold bil; rw [← sum_add_distrib]
  exact sum_congr rfl fun x _ => by rw [← sum_add_distrib]; exact sum_congr rfl fun y _ => by ring

lemma bil_sub (S : Finset α) (T : Finset β) (K₁ K₂ : α → β → ℂ) (g : α → ℂ) (f : β → ℂ) :
    bil S T (fun x y => K₁ x y - K₂ x y) g f = bil S T K₁ g f - bil S T K₂ g f := by
  unfold bil; rw [← sum_sub_distrib]
  exact sum_congr rfl fun x _ => by rw [← sum_sub_distrib]; exact sum_congr rfl fun y _ => by ring

lemma bilBound_add (S : Finset α) (T : Finset β) (K₁ K₂ : α → β → ℂ) (C₁ C₂ : ℝ)
    (h₁ : BilBound S T K₁ C₁) (h₂ : BilBound S T K₂ C₂) :
    BilBound S T (fun x y => K₁ x y + K₂ x y) (C₁ + C₂) := by
  intro g f
  rw [bil_add]
  refine (norm_add_le _ _).trans ?_
  have := h₁ g f; have := h₂ g f
  linarith

lemma bilBound_sub (S : Finset α) (T : Finset β) (K₁ K₂ : α → β → ℂ) (C₁ C₂ : ℝ)
    (h₁ : BilBound S T K₁ C₁) (h₂ : BilBound S T K₂ C₂) :
    BilBound S T (fun x y => K₁ x y - K₂ x y) (C₁ + C₂) := by
  intro g f
  rw [bil_sub]
  refine (norm_sub_le _ _).trans ?_
  have := h₁ g f; have := h₂ g f
  linarith

lemma bilBound_finsum (S : Finset α) (T : Finset β) (I : Finset ι) (K : ι → α → β → ℂ)
    (C : ℝ) (h : ∀ k ∈ I, BilBound S T (K k) C) :
    BilBound S T (fun x y => ∑ k ∈ I, K k x y) (I.card * C) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    intro g f; simp [bil]
  | insert k I hk ih =>
    have h1 := h k (mem_insert_self k I)
    have h2 := ih fun k' hk' => h k' (mem_insert_of_mem hk')
    have e : (fun x y => ∑ k' ∈ insert k I, K k' x y) = fun x y => K k x y + ∑ k' ∈ I, K k' x y := by
      funext x y; rw [sum_insert hk]
    rw [e, card_insert_of_notMem hk]
    refine bilBound_mono S T _ _ _ (le_of_eq (by push_cast; ring)) (bilBound_add S T _ _ C
      (I.card * C) h1 h2)

/-- Diagonal multipliers. -/
lemma bilBound_diag (S : Finset α) (T : Finset β) (K : α → β → ℂ) (C : ℝ) (u : α → ℂ)
    (v : β → ℂ) (a b : ℝ) (ha0 : 0 ≤ a) (_hb0 : 0 ≤ b) (ha : ∀ x ∈ S, ‖u x‖ ≤ a)
    (hb : ∀ y ∈ T, ‖v y‖ ≤ b) (hC : 0 ≤ C)
    (hK : BilBound S T K C) : BilBound S T (fun x y => u x * K x y * v y) (a * b * C) := by
  intro g f
  have e : bil S T (fun x y => u x * K x y * v y) g f =
      bil S T K (fun x => conj (u x) * g x) (fun y => v y * f y) := by
    unfold bil
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    simp only [map_mul, Complex.conj_conj]; ring
  rw [e]
  refine (hK _ _).trans ?_
  have h1 := l2_mul_le S g (fun x => conj (u x)) a (fun x hx => by rw [Complex.norm_conj]; exact ha x hx)
  have h2 := l2_mul_le T f v b hb
  have hg := l2_nonneg S g
  have hf := l2_nonneg T f
  have hg' := l2_nonneg S (fun x => conj (u x) * g x)
  have hf' := l2_nonneg T (fun y => v y * f y)
  calc C * l2 S (fun x => conj (u x) * g x) * l2 T (fun y => v y * f y) ≤
      C * (a * l2 S g) * (b * l2 T f) := by gcongr
    _ = a * b * C * l2 S g * l2 T f := by ring

/-- Kernels that agree on `S × T`. -/
lemma bilBound_congr (S : Finset α) (T : Finset β) (K K' : α → β → ℂ) (C : ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ T, K x y = K' x y) (hK : BilBound S T K C) : BilBound S T K' C := by
  intro g f
  have : bil S T K' g f = bil S T K g f := by
    unfold bil
    exact sum_congr rfl fun x hx => sum_congr rfl fun y hy => by rw [h x hx y hy]
  rw [this]; exact hK g f

/-- Restriction to subsets. -/
lemma bilBound_subset (S S' : Finset α) (T T' : Finset β) (hS : S ⊆ S') (hT : T ⊆ T')
    (K : α → β → ℂ) (C : ℝ) (hK : BilBound S' T' K C) : BilBound S T K C := by
  classical
  intro g f
  set g' : α → ℂ := fun x => if x ∈ S then g x else 0
  set f' : β → ℂ := fun y => if y ∈ T then f y else 0
  have e : bil S T K g f = bil S' T' K g' f' := by
    unfold bil
    rw [← sum_subset hS (f := fun x => ∑ y ∈ T', conj (g' x) * K x y * f' y)]
    · refine sum_congr rfl fun x hx => ?_
      rw [← sum_subset hT (f := fun y => conj (g' x) * K x y * f' y)]
      · refine sum_congr rfl fun y hy => ?_
        simp [g', f', hx, hy]
      · intro y _ hy; simp [f', hy]
    · intro x _ hx; simp [g', hx]
  have e1 : l2 S' g' = l2 S g := by
    unfold l2; congr 1
    rw [← sum_subset hS (f := fun x => ‖g' x‖ ^ 2)]
    · exact sum_congr rfl fun x hx => by simp [g', hx]
    · intro x _ hx; simp [g', hx]
  have e2 : l2 T' f' = l2 T f := by
    unfold l2; congr 1
    rw [← sum_subset hT (f := fun y => ‖f' y‖ ^ 2)]
    · exact sum_congr rfl fun y hy => by simp [f', hy]
    · intro y _ hy; simp [f', hy]
  rw [e, ← e1, ← e2]; exact hK g' f'

/-- Compression along injections. -/
lemma bilBound_comp [DecidableEq α'] [DecidableEq β'] (S : Finset α) (T : Finset β)
    (φ : α → α') (ψ : β → β')
    (hφ : Set.InjOn φ S) (hψ : Set.InjOn ψ T) (K' : α' → β' → ℂ) (C : ℝ)
    (hK : BilBound (S.image φ) (T.image ψ) K' C) :
    BilBound S T (fun x y => K' (φ x) (ψ y)) C := by
  classical
  intro g f
  set g' : α' → ℂ := fun x' => ∑ x ∈ S, if φ x = x' then g x else 0
  set f' : β' → ℂ := fun y' => ∑ y ∈ T, if ψ y = y' then f y else 0
  have hg' : ∀ x ∈ S, g' (φ x) = g x := by
    intro x hx
    simp only [g']
    rw [sum_eq_single x]
    · simp
    · intro x₀ hx₀ hne; rw [if_neg]; exact fun h => hne (hφ hx₀ hx h)
    · intro h; exact absurd hx h
  have hf' : ∀ y ∈ T, f' (ψ y) = f y := by
    intro y hy
    simp only [f']
    rw [sum_eq_single y]
    · simp
    · intro y₀ hy₀ hne; rw [if_neg]; exact fun h => hne (hψ hy₀ hy h)
    · intro h; exact absurd hy h
  have e : bil S T (fun x y => K' (φ x) (ψ y)) g f = bil (S.image φ) (T.image ψ) K' g' f' := by
    unfold bil
    rw [sum_image hφ]
    refine sum_congr rfl fun x hx => ?_
    rw [sum_image hψ]
    refine sum_congr rfl fun y hy => ?_
    rw [hg' x hx, hf' y hy]
  have e1 : l2 (S.image φ) g' = l2 S g := by
    unfold l2; rw [sum_image hφ]; congr 1
    exact sum_congr rfl fun x hx => by rw [hg' x hx]
  have e2 : l2 (T.image ψ) f' = l2 T f := by
    unfold l2; rw [sum_image hψ]; congr 1
    exact sum_congr rfl fun y hy => by rw [hf' y hy]
  rw [e, ← e1, ← e2]; exact hK g' f'

/-- **Direct sums of blocks.** If the kernel vanishes off `⋃ₖ Sₖ × Tₖ` with disjoint `Sₖ` and
disjoint `Tₖ`, and each block is bounded by `C`, so is the whole form. -/
lemma bilBound_blocks [DecidableEq ι] (S : Finset α) (T : Finset β) (I : Finset ι)
    (bs : α → ι) (bt : β → ι)
    (K : α → β → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsupp : ∀ x ∈ S, ∀ y ∈ T, K x y ≠ 0 → bs x = bt y)
    (hmaps : ∀ x ∈ S, bs x ∈ I)
    (hblock : ∀ k ∈ I, BilBound (S.filter fun x => bs x = k) (T.filter fun y => bt y = k) K C) :
    BilBound S T K C := by
  classical
  intro g f
  have e : bil S T K g f = ∑ k ∈ I, bil (S.filter fun x => bs x = k)
      (T.filter fun y => bt y = k) K g f := by
    unfold bil
    rw [← sum_fiberwise_of_maps_to (g := bs) hmaps]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_filter, sum_filter]
    refine sum_congr rfl fun x hx => ?_
    split_ifs with hk
    · rw [sum_filter]
      refine sum_congr rfl fun y hy => ?_
      split_ifs with hk'
      · rfl
      · by_cases hK : K x y = 0
        · simp [hK]
        · exact absurd (hk ▸ (hsupp x hx y hy hK).symm) hk'
    · rfl
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ I, ‖bil (S.filter fun x => bs x = k) (T.filter fun y => bt y = k) K g f‖ ≤
      ∑ k ∈ I, C * l2 (S.filter fun x => bs x = k) g * l2 (T.filter fun y => bt y = k) f :=
        sum_le_sum fun k hk => hblock k hk g f
    _ = C * ∑ k ∈ I, l2 (S.filter fun x => bs x = k) g * l2 (T.filter fun y => bt y = k) f := by
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    _ ≤ C * (√(∑ k ∈ I, l2 (S.filter fun x => bs x = k) g ^ 2) *
          √(∑ k ∈ I, l2 (T.filter fun y => bt y = k) f ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hC
    _ ≤ C * (l2 S g * l2 T f) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply mul_le_mul _ _ (Real.sqrt_nonneg _) (l2_nonneg _ _)
        · rw [show l2 S g = √(∑ x ∈ S, ‖g x‖ ^ 2) from rfl]; apply Real.sqrt_le_sqrt
          simp only [l2_sq]
          exact (sum_fiberwise_of_maps_to hmaps (fun x => ‖g x‖ ^ 2)).le
        · rw [show l2 T f = √(∑ y ∈ T, ‖f y‖ ^ 2) from rfl]; apply Real.sqrt_le_sqrt
          simp only [l2_sq]
          calc ∑ k ∈ I, ∑ y ∈ T.filter (fun y => bt y = k), ‖f y‖ ^ 2 =
              ∑ y ∈ T.filter (fun y => bt y ∈ I), ‖f y‖ ^ 2 := by
                rw [← sum_fiberwise_of_maps_to (s := T.filter (fun y => bt y ∈ I)) (t := I)
                  (g := bt) (fun y hy => (mem_filter.1 hy).2)]
                refine sum_congr rfl fun k hk => ?_
                rw [filter_filter]
                congr 1; ext y; simp only [mem_filter]
                constructor
                · rintro ⟨h1, h2⟩; exact ⟨h1, h2 ▸ hk, h2⟩
                · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
            _ ≤ ∑ y ∈ T, ‖f y‖ ^ 2 :=
                sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _
    _ = C * l2 S g * l2 T f := by ring

/-- **Schur's test.** -/
lemma bilBound_schur (S : Finset α) (T : Finset β) (K : α → β → ℂ) (R Cc : ℝ)
    (hR : 0 ≤ R) (hCc : 0 ≤ Cc)
    (hrow : ∀ x ∈ S, ∑ y ∈ T, ‖K x y‖ ≤ R) (hcol : ∀ y ∈ T, ∑ x ∈ S, ‖K x y‖ ≤ Cc) :
    BilBound S T K (√R * √Cc) := by
  intro g f
  have h1 : ‖bil S T K g f‖ ≤ ∑ q ∈ S ×ˢ T, (√‖K q.1 q.2‖ * ‖g q.1‖) * (√‖K q.1 q.2‖ * ‖f q.2‖) := by
    unfold bil
    rw [sum_product]
    refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => (norm_sum_le _ _).trans
      (le_of_eq (sum_congr rfl fun y _ => ?_)))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have := Real.mul_self_sqrt (norm_nonneg (K x y))
    calc ‖g x‖ * ‖K x y‖ * ‖f y‖ = (√‖K x y‖ * √‖K x y‖) * ‖g x‖ * ‖f y‖ := by rw [this]; ring
      _ = _ := by ring
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (S ×ˢ T) (fun q => √‖K q.1 q.2‖ * ‖g q.1‖)
    (fun q => √‖K q.1 q.2‖ * ‖f q.2‖)
  have h3 : ∑ q ∈ S ×ˢ T, (√‖K q.1 q.2‖ * ‖g q.1‖) ^ 2 ≤ R * ∑ x ∈ S, ‖g x‖ ^ 2 := by
    rw [sum_product, mul_sum]
    refine sum_le_sum fun x hx => ?_
    calc ∑ y ∈ T, (√‖K (x, y).1 (x, y).2‖ * ‖g (x, y).1‖) ^ 2 =
        (∑ y ∈ T, ‖K x y‖) * ‖g x‖ ^ 2 := by
          rw [sum_mul]; refine sum_congr rfl fun y _ => ?_
          rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
      _ ≤ R * ‖g x‖ ^ 2 := mul_le_mul_of_nonneg_right (hrow x hx) (sq_nonneg _)
  have h4 : ∑ q ∈ S ×ˢ T, (√‖K q.1 q.2‖ * ‖f q.2‖) ^ 2 ≤ Cc * ∑ y ∈ T, ‖f y‖ ^ 2 := by
    rw [sum_product, sum_comm, mul_sum]
    refine sum_le_sum fun y hy => ?_
    calc ∑ x ∈ S, (√‖K (x, y).1 (x, y).2‖ * ‖f (x, y).2‖) ^ 2 =
        (∑ x ∈ S, ‖K x y‖) * ‖f y‖ ^ 2 := by
          rw [sum_mul]; refine sum_congr rfl fun x _ => ?_
          rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
      _ ≤ Cc * ‖f y‖ ^ 2 := mul_le_mul_of_nonneg_right (hcol y hy) (sq_nonneg _)
  calc ‖bil S T K g f‖ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ √(R * ∑ x ∈ S, ‖g x‖ ^ 2) * √(Cc * ∑ y ∈ T, ‖f y‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt h3) (Real.sqrt_le_sqrt h4) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = √R * √Cc * l2 S g * l2 T f := by
        unfold l2
        rw [Real.sqrt_mul hR, Real.sqrt_mul hCc]; ring

/-- **Weighted Schur test** for kernels `√(a x · b y) X(x, y)`. -/
lemma bilBound_wschur (S : Finset α) (T : Finset β) (K : α → β → ℂ) (a : α → ℝ) (b : β → ℝ)
    (ha : ∀ x ∈ S, 0 ≤ a x) (hb : ∀ y ∈ T, 0 ≤ b y) (X : α → β → ℂ)
    (hK : ∀ x ∈ S, ∀ y ∈ T, ‖K x y‖ ≤ √(a x * b y) * ‖X x y‖) (R Cc : ℝ) (hR : 0 ≤ R)
    (hCc : 0 ≤ Cc) (hrow : ∀ x ∈ S, ∑ y ∈ T, ‖X x y‖ * b y ≤ R)
    (hcol : ∀ y ∈ T, ∑ x ∈ S, ‖X x y‖ * a x ≤ Cc) :
    BilBound S T K (√R * √Cc) := by
  intro g f
  have h1 : ‖bil S T K g f‖ ≤ ∑ q ∈ S ×ˢ T, (√(‖X q.1 q.2‖ * b q.2) * ‖g q.1‖) *
      (√(‖X q.1 q.2‖ * a q.1) * ‖f q.2‖) := by
    unfold bil
    rw [sum_product]
    refine (norm_sum_le _ _).trans (sum_le_sum fun x hx => (norm_sum_le _ _).trans
      (sum_le_sum fun y hy => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hax := ha x hx
    have hby := hb y hy
    have e : √(‖X x y‖ * b y) * ‖g x‖ * (√(‖X x y‖ * a x) * ‖f y‖) =
        (√(a x * b y) * ‖X x y‖) * ‖g x‖ * ‖f y‖ := by
      rw [show √(‖X x y‖ * b y) * ‖g x‖ * (√(‖X x y‖ * a x) * ‖f y‖) =
          (√(‖X x y‖ * b y) * √(‖X x y‖ * a x)) * ‖g x‖ * ‖f y‖ by ring,
        ← Real.sqrt_mul (by positivity),
        show ‖X x y‖ * b y * (‖X x y‖ * a x) = (a x * b y) * ‖X x y‖ ^ 2 by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
    rw [e]
    have := hK x hx y hy
    have hg := norm_nonneg (g x)
    have hf := norm_nonneg (f y)
    calc ‖g x‖ * ‖K x y‖ * ‖f y‖ ≤ ‖g x‖ * (√(a x * b y) * ‖X x y‖) * ‖f y‖ := by gcongr
      _ = _ := by ring
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (S ×ˢ T) (fun q => √(‖X q.1 q.2‖ * b q.2) * ‖g q.1‖)
    (fun q => √(‖X q.1 q.2‖ * a q.1) * ‖f q.2‖)
  have h3 : ∑ q ∈ S ×ˢ T, (√(‖X q.1 q.2‖ * b q.2) * ‖g q.1‖) ^ 2 ≤ R * ∑ x ∈ S, ‖g x‖ ^ 2 := by
    rw [sum_product, mul_sum]
    refine sum_le_sum fun x hx => ?_
    calc ∑ y ∈ T, (√(‖X (x, y).1 (x, y).2‖ * b (x, y).2) * ‖g (x, y).1‖) ^ 2 =
        (∑ y ∈ T, ‖X x y‖ * b y) * ‖g x‖ ^ 2 := by
          rw [sum_mul]; refine sum_congr rfl fun y hy => ?_
          rw [mul_pow, Real.sq_sqrt (mul_nonneg (norm_nonneg _) (hb y hy))]
      _ ≤ R * ‖g x‖ ^ 2 := mul_le_mul_of_nonneg_right (hrow x hx) (sq_nonneg _)
  have h4 : ∑ q ∈ S ×ˢ T, (√(‖X q.1 q.2‖ * a q.1) * ‖f q.2‖) ^ 2 ≤ Cc * ∑ y ∈ T, ‖f y‖ ^ 2 := by
    rw [sum_product, sum_comm, mul_sum]
    refine sum_le_sum fun y hy => ?_
    calc ∑ x ∈ S, (√(‖X (x, y).1 (x, y).2‖ * a (x, y).1) * ‖f (x, y).2‖) ^ 2 =
        (∑ x ∈ S, ‖X x y‖ * a x) * ‖f y‖ ^ 2 := by
          rw [sum_mul]; refine sum_congr rfl fun x hx => ?_
          rw [mul_pow, Real.sq_sqrt (mul_nonneg (norm_nonneg _) (ha x hx))]
      _ ≤ Cc * ‖f y‖ ^ 2 := mul_le_mul_of_nonneg_right (hcol y hy) (sq_nonneg _)
  calc ‖bil S T K g f‖ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ √(R * ∑ x ∈ S, ‖g x‖ ^ 2) * √(Cc * ∑ y ∈ T, ‖f y‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt h3) (Real.sqrt_le_sqrt h4) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = √R * √Cc * l2 S g * l2 T f := by
        unfold l2
        rw [Real.sqrt_mul hR, Real.sqrt_mul hCc]; ring

/-- A kernel vanishing on `S × T` has every bound `C ≥ 0`. -/
lemma bilBound_zero (S : Finset α) (T : Finset β) (K : α → β → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x ∈ S, ∀ y ∈ T, K x y = 0) : BilBound S T K C := by
  intro g f
  have : bil S T K g f = 0 := by
    unfold bil
    exact sum_eq_zero fun x hx => sum_eq_zero fun y hy => by rw [h x hx y hy]; ring
  rw [this, norm_zero]
  have := l2_nonneg S g; have := l2_nonneg T f
  positivity

/-- A kernel supported on `S' × T'` (subsets) has the bound of its restriction. -/
lemma bilBound_of_support [DecidableEq α] [DecidableEq β] (S S' : Finset α) (T T' : Finset β)
    (hS : S' ⊆ S) (hT : T' ⊆ T) (K : α → β → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hsupp : ∀ x ∈ S, ∀ y ∈ T, K x y ≠ 0 → x ∈ S' ∧ y ∈ T')
    (hK : BilBound S' T' K C) : BilBound S T K C := by
  intro g f
  have e : bil S T K g f = bil S' T' K g f := by
    unfold bil
    rw [← sum_subset hS (f := fun x => ∑ y ∈ T, conj (g x) * K x y * f y)]
    · refine sum_congr rfl fun x hx => ?_
      rw [← sum_subset hT (f := fun y => conj (g x) * K x y * f y)]
      intro y hy hy'
      by_cases hK0 : K x y = 0
      · rw [hK0]; ring
      · exact absurd (hsupp x (hS hx) y hy hK0).2 hy'
    · intro x hx hx'
      refine sum_eq_zero fun y hy => ?_
      by_cases hK0 : K x y = 0
      · rw [hK0]; ring
      · exact absurd (hsupp x hx y hy hK0).1 hx'
  rw [e]
  refine (hK g f).trans ?_
  have h1 : l2 S' g ≤ l2 S g := Real.sqrt_le_sqrt (sum_le_sum_of_subset_of_nonneg hS
    fun _ _ _ => sq_nonneg _)
  have h2 : l2 T' f ≤ l2 T f := Real.sqrt_le_sqrt (sum_le_sum_of_subset_of_nonneg hT
    fun _ _ _ => sq_nonneg _)
  have := l2_nonneg S' g
  have := l2_nonneg T' f
  calc C * l2 S' g * l2 T' f ≤ C * l2 S g * l2 T' f := by gcongr
    _ ≤ C * l2 S g * l2 T f := by gcongr; exact mul_nonneg hC (l2_nonneg S g)

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: the clean edge, reduction to blocks of fixed pads and memory

A clean choice (no stores, no promotions) keeps the memory and the pads, and draws the target's
last labels freshly. `clean_reduce`: if for every pad tuple `pd` and memory `m` the block kernel
`kblock pd m` on `(positions × last-label tuples)²` (the clean coefficient conjugated to counting
measure: `√(ν(lab) ν(nw)) ρ^{hits} edgeMult [EdgeOK]`) has bilinear bound `ε`, then the clean piece
has bilinear bound `ε` on `H_B`. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset
open scoped ComplexConjugate

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- Pad tuples: `J` primes of `𝒫ᵢ` in each group. -/
noncomputable def padCands : Finset (Fin P.K → Fin P.J → ℕ) :=
  Fintype.piFinset fun i => Fintype.piFinset fun _ => P.grp i

/-- Last-label tuples: one prime of `𝒫ᵢ` in each group. -/
noncomputable def labCands : Finset (Fin P.K → ℕ) := Fintype.piFinset P.grp

/-- The list with pads `pd` and last labels `lab`. -/
def mkList (pd : Fin P.K → Fin P.J → ℕ) (lab : Fin P.K → ℕ) : P.Lst :=
  fun i => Fin.lastCases (lab i) (pd i)

lemma mkList_last (pd : Fin P.K → Fin P.J → ℕ) (lab : Fin P.K → ℕ) (i : Fin P.K) :
    mkList P pd lab i (Fin.last P.J) = lab i := by simp [mkList]

lemma mkList_castSucc (pd : Fin P.K → Fin P.J → ℕ) (lab : Fin P.K → ℕ) (i : Fin P.K)
    (k : Fin P.J) : mkList P pd lab i k.castSucc = pd i k := by simp [mkList]

lemma newList_mkList (pd : Fin P.K → Fin P.J → ℕ) (lab nw : Fin P.K → ℕ) :
    P.newList (mkList P pd lab) nw = mkList P pd nw := by
  funext i k
  induction k using Fin.lastCases with
  | last => rw [newList_last, mkList_last]
  | cast k => rw [newList_castSucc, mkList_castSucc, mkList_castSucc]

lemma lastProd_mkList (pd : Fin P.K → Fin P.J → ℕ) (lab : Fin P.K → ℕ) :
    lastProd (mkList P pd lab) = ∏ i, lab i := by
  unfold lastProd; simp only [mkList_last]

lemma padProd_mkList (pd : Fin P.K → Fin P.J → ℕ) (lab lab' : Fin P.K → ℕ) :
    padProd (mkList P pd lab) = padProd (mkList P pd lab') := by
  unfold padProd; simp only [mkList_castSucc]

/-- The pad weight. -/
noncomputable def padW (pd : Fin P.K → Fin P.J → ℕ) : ℝ := ∏ i, ∏ k, P.nu i (pd i k)

lemma listWeight_mkList (pd : Fin P.K → Fin P.J → ℕ) (lab : Fin P.K → ℕ) :
    P.listWeight (mkList P pd lab) = padW P pd * ∏ i, P.nu i (lab i) := by
  unfold MemParams.listWeight padW
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp only [mkList_castSucc, mkList_last]

lemma mem_listCands_mkList (pd : Fin P.K → Fin P.J → ℕ) (lab : Fin P.K → ℕ)
    (hpd : pd ∈ padCands P) (hlab : lab ∈ labCands P) :
    mkList P pd lab ∈ listCands P.x P.a P.J := by
  simp only [padCands, labCands, Fintype.mem_piFinset] at hpd hlab
  simp only [listCands, Fintype.mem_piFinset]
  intro i k
  induction k using Fin.lastCases with
  | last => rw [mkList_last]; exact hlab i
  | cast k => rw [mkList_castSucc]; exact hpd i k

lemma sum_listCands {M : Type*} [AddCommMonoid M] (f : P.Lst → M) :
    ∑ ℓ ∈ listCands P.x P.a P.J, f ℓ =
      ∑ pd ∈ padCands P, ∑ lab ∈ labCands P, f (mkList P pd lab) := by
  rw [← sum_product (s := padCands P) (t := labCands P) (f := fun q => f (mkList P q.1 q.2))]
  symm
  refine sum_nbij' (fun q => mkList P q.1 q.2)
    (fun ℓ => (fun i k => ℓ i k.castSucc, fun i => ℓ i (Fin.last P.J))) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [mem_product] at hq
    exact mem_listCands_mkList P q.1 q.2 hq.1 hq.2
  · intro ℓ hℓ
    simp only [listCands, Fintype.mem_piFinset] at hℓ
    simp only [mem_product, padCands, labCands, Fintype.mem_piFinset]
    exact ⟨fun i k => hℓ i _, fun i => hℓ i _⟩
  · intro q _
    simp only [mkList_castSucc, mkList_last]
  · intro ℓ _
    funext i k
    induction k using Fin.lastCases with
    | last => rw [mkList_last]
    | cast k => rw [mkList_castSucc]
  · intro q _; rfl

/-! ## Clean choices -/

/-- The clean choice with target `z'` and fresh labels `nw`. -/
def cleanC (z' : ℤ × ℤ) (nw : Fin P.K → ℕ) : EC P := (∅, z', fun i => (nw i, false))

lemma promSet_cleanC (z' : ℤ × ℤ) (nw : Fin P.K → ℕ) : promSet P (cleanC P z' nw) = ∅ := by
  ext i; simp [promSet, cleanC]

lemma edgeOutMem_cleanC (s : P.MState) (z' : ℤ × ℤ) (nw : Fin P.K → ℕ) :
    P.edgeOutMem s (cleanC P z' nw) = s.2.2 := by
  funext y
  simp [MemParams.edgeOutMem, MemParams.promCount, MemParams.storeCount, cleanC]

lemma edgeOut_cleanC (s : P.MState) (z' : ℤ × ℤ) (nw : Fin P.K → ℕ) :
    P.edgeOut s (cleanC P z' nw) = (z', P.newList s.2.1 nw, s.2.2) := by
  simp only [MemParams.edgeOut, edgeOutMem_cleanC]; rfl

lemma econd_cleanC (ω : ℝ × ℝ × ℝ) (s : P.MState) (z' : ℤ × ℤ) (nw : Fin P.K → ℕ) :
    ECond P ω s (cleanC P z' nw) ↔ P.EdgeOK ω s.1 z' s.2.1 nw := by
  unfold ECond
  constructor
  · rintro ⟨h, -, -, -⟩; exact h
  · intro h
    refine ⟨h, fun i hi => by simp [cleanC] at hi, fun i hi => by simp [cleanC] at hi, fun y => ?_⟩
    simp [MemParams.promCount, cleanC]

lemma rfac_cleanC (s : P.MState) (z' : ℤ × ℤ) (nw : Fin P.K → ℕ) :
    rfac P s (cleanC P z' nw) =
      memRho ^ P.hitCount s.1 s.2.2 * (∏ i, P.nu i (nw i)) * memRho ^ P.hitCount z' s.2.2 := by
  unfold rfac
  rw [edgeOutMem_cleanC]
  simp [cleanC]

/-- The clean class sums only over clean choices. -/
lemma sum_clean (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState) (Φ : EC P → ℂ) :
    ∑ c ∈ P.edgeChoices, coeffP P (clsClean P) κ ω s c * Φ c =
      ∑ z' ∈ P.zSet, ∑ nw ∈ labCands P, coeffK P κ ω s (cleanC P z' nw) * Φ (cleanC P z' nw) := by
  classical
  rw [← sum_product (s := P.zSet) (t := labCands P)
    (f := fun q => coeffK P κ ω s (cleanC P q.1 q.2) * Φ (cleanC P q.1 q.2))]
  have hinj : Set.InjOn (fun q : (ℤ × ℤ) × (Fin P.K → ℕ) => cleanC P q.1 q.2)
      ↑(P.zSet ×ˢ labCands P) := by
    intro q _ q' _ h
    simp only [cleanC, Prod.mk.injEq] at h
    obtain ⟨-, h1, h2⟩ := h
    refine Prod.ext h1 (funext fun i => ?_)
    have := congrFun h2 i
    simp only [Prod.mk.injEq] at this
    exact this.1
  rw [← sum_image (f := fun c => coeffK P κ ω s c * Φ c) hinj]
  symm
  apply sum_subset_zero_on_sdiff
  · intro c hc
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hc
    rw [mem_product] at hq
    simp only [MemParams.edgeChoices, mem_product, mem_univ, true_and, cleanC,
      Fintype.mem_piFinset]
    have h2 := hq.2
    simp only [labCands, Fintype.mem_piFinset] at h2
    exact ⟨hq.1, fun i => ⟨h2 i, trivial⟩⟩
  · intro c hc
    rw [mem_sdiff] at hc
    unfold coeffP clsClean
    rw [if_neg]
    · ring
    · rintro ⟨h1, h2⟩
      apply hc.2
      rw [mem_image]
      refine ⟨(c.2.1, fun i => (c.2.2 i).1), ?_, ?_⟩
      · have := hc.1
        simp only [MemParams.edgeChoices, mem_product, mem_univ, true_and,
          Fintype.mem_piFinset] at this
        simp only [mem_product, labCands, Fintype.mem_piFinset]
        exact ⟨this.1, fun i => (this.2 i).1⟩
      · rcases c with ⟨St, z', tg⟩
        simp only at h1
        simp only [cleanC, h1, Prod.mk.injEq, true_and]
        funext i
        have : (tg i).2 = false := by
          by_contra hne
          have : i ∈ promSet P (St, z', tg) := by simp [promSet, Bool.not_eq_false] at hne ⊢; exact hne
          rw [h2] at this; exact absurd this (notMem_empty i)
        exact Prod.ext rfl this.symm
  · intro c hc
    obtain ⟨q, _, rfl⟩ := mem_image.1 hc
    unfold coeffP clsClean
    rw [if_pos ⟨rfl, promSet_cleanC P _ _⟩]

/-! ## The block kernel and the reduction -/

open Classical in
/-- The clean block kernel at pads `pd` and memory `m`, on `(position, last labels)` pairs,
conjugated to counting measure. -/
noncomputable def kblock (ω : ℝ × ℝ × ℝ) (j : ℕ) (pd : Fin P.K → Fin P.J → ℕ) (m : P.Mem)
    (p q : (ℤ × ℤ) × (Fin P.K → ℕ)) : ℂ :=
  ((√((∏ i, P.nu i (p.2 i)) * ∏ i, P.nu i (q.2 i)) * memRho ^ P.hitCount p.1 m *
      memRho ^ P.hitCount q.1 m : ℝ) : ℂ) *
    P.edgeMult j (detZ p.1 q.1 / padProd (mkList P pd p.2)) (∏ i, q.2 i) (∏ i, p.2 i)
      (padProd (mkList P pd p.2)) *
    (if P.EdgeOK ω p.1 q.1 (mkList P pd p.2) q.2 then 1 else 0)

lemma sqrt_trip (W L N : ℝ) (hW : 0 ≤ W) (hL : 0 ≤ L) (hN : 0 ≤ N) :
    √(W * L) * √(L * N) * √(W * N) = W * L * N := by
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  rw [show W * L * (L * N) * (W * N) = (W * L * N) ^ 2 by ring, Real.sqrt_sq (by positivity)]

lemma memWeight_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (m : P.Mem) :
    0 ≤ P.memWeight m := by
  unfold MemParams.memWeight
  exact prod_nonneg fun y _ => by have := lam_nonneg P hnu y; positivity

lemma padW_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (pd : Fin P.K → Fin P.J → ℕ)
    (hpd : pd ∈ padCands P) : 0 ≤ padW P pd := by
  simp only [padCands, Fintype.mem_piFinset] at hpd
  exact prod_nonneg fun i _ => prod_nonneg fun k _ => hnu i _ (hpd i k)

lemma prod_nu_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (lab : Fin P.K → ℕ)
    (hlab : lab ∈ labCands P) : 0 ≤ ∏ i, P.nu i (lab i) := by
  simp only [labCands, Fintype.mem_piFinset] at hlab
  exact prod_nonneg fun i _ => hnu i _ (hlab i)

/-- Sums over states by blocks of (memory, pads). -/
lemma sum_stSet_blocks {M : Type*} [AddCommMonoid M] (Φ : P.MState → M) :
    ∑ s ∈ P.stSet, Φ s = ∑ m ∈ P.memSet, ∑ pd ∈ padCands P,
      ∑ q ∈ P.zSet ×ˢ labCands P, Φ (q.1, mkList P pd q.2, m) := by
  unfold MemParams.stSet
  calc ∑ s ∈ P.zSet ×ˢ (listCands P.x P.a P.J ×ˢ P.memSet), Φ s =
      ∑ z ∈ P.zSet, ∑ ℓ ∈ listCands P.x P.a P.J, ∑ m ∈ P.memSet, Φ (z, ℓ, m) := by
        rw [sum_product]
        exact sum_congr rfl fun z _ => sum_product _ _ _
    _ = ∑ z ∈ P.zSet, ∑ m ∈ P.memSet, ∑ ℓ ∈ listCands P.x P.a P.J, Φ (z, ℓ, m) :=
        sum_congr rfl fun z _ => sum_comm
    _ = ∑ m ∈ P.memSet, ∑ z ∈ P.zSet, ∑ ℓ ∈ listCands P.x P.a P.J, Φ (z, ℓ, m) := sum_comm
    _ = ∑ m ∈ P.memSet, ∑ z ∈ P.zSet, ∑ pd ∈ padCands P, ∑ lab ∈ labCands P,
        Φ (z, mkList P pd lab, m) :=
        sum_congr rfl fun m _ => sum_congr rfl fun z _ =>
          sum_listCands P (fun ℓ => Φ (z, ℓ, m))
    _ = ∑ m ∈ P.memSet, ∑ pd ∈ padCands P, ∑ z ∈ P.zSet, ∑ lab ∈ labCands P,
        Φ (z, mkList P pd lab, m) := sum_congr rfl fun m _ => sum_comm
    _ = _ := by
        refine sum_congr rfl fun m _ => sum_congr rfl fun pd _ => ?_
        rw [sum_product]

/-- **Reduction of the clean piece to blocks.** -/
theorem clean_reduce (ω : ℝ × ℝ × ℝ) (j : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p)
    (hblock : ∀ pd ∈ padCands P, ∀ m ∈ P.memSet,
      BilBound (P.zSet ×ˢ labCands P) (P.zSet ×ˢ labCands P) (kblock P ω j pd m) ε)
    (G F : P.MState → ℂ) :
    ‖pieceB P (clsClean P) (P.edgeMult j) ω G F‖ ≤ ε * P.wNorm G * P.wNorm F := by
  classical
  set S := P.zSet ×ˢ labCands P
  set Gb : (Fin P.K → Fin P.J → ℕ) → P.Mem → (ℤ × ℤ) × (Fin P.K → ℕ) → ℂ :=
    fun pd m q => ((√(P.stWeight (q.1, mkList P pd q.2, m)) : ℝ) : ℂ) * G (q.1, mkList P pd q.2, m)
  set Fb : (Fin P.K → Fin P.J → ℕ) → P.Mem → (ℤ × ℤ) × (Fin P.K → ℕ) → ℂ :=
    fun pd m q => ((√(P.stWeight (q.1, mkList P pd q.2, m)) : ℝ) : ℂ) * F (q.1, mkList P pd q.2, m)
  -- the term identity
  have hterm : ∀ pd ∈ padCands P, ∀ m ∈ P.memSet, ∀ q ∈ S, ∀ q' ∈ S,
      (P.stWeight (q.1, mkList P pd q.2, m) : ℂ) * (conj (G (q.1, mkList P pd q.2, m)) *
        (coeffK P (P.edgeMult j) ω (q.1, mkList P pd q.2, m) (cleanC P q'.1 q'.2) *
          (if P.edgeOut (q.1, mkList P pd q.2, m) (cleanC P q'.1 q'.2) ∈ P.stSet then
            F (P.edgeOut (q.1, mkList P pd q.2, m) (cleanC P q'.1 q'.2)) else 0))) =
      conj (Gb pd m q) * kblock P ω j pd m q q' * Fb pd m q' := by
    intro pd hpd m hm q hq q' hq'
    rw [mem_product] at hq hq'
    have hout : P.edgeOut (q.1, mkList P pd q.2, m) (cleanC P q'.1 q'.2) =
        (q'.1, mkList P pd q'.2, m) := by
      rw [edgeOut_cleanC]; simp only [newList_mkList]
    have hin : (q'.1, mkList P pd q'.2, m) ∈ P.stSet := by
      unfold MemParams.stSet
      rw [mem_product, mem_product]
      exact ⟨hq'.1, mem_listCands_mkList P pd q'.2 hpd hq'.2, hm⟩
    rw [hout, if_pos hin]
    unfold coeffK kblock
    simp only [Gb, Fb, map_mul, Complex.conj_ofReal]
    rw [econd_cleanC]
    by_cases hE : P.EdgeOK ω q.1 q'.1 (mkList P pd q.2) q'.2
    · rw [if_pos hE, if_pos hE, rfac_cleanC]
      simp only [lastProd_mkList, padProd_mkList P pd q.2 q'.2]
      have hW := mul_nonneg (padW_nonneg P hnu pd hpd) (memWeight_nonneg P hnu m)
      have hL := prod_nu_nonneg P hnu q.2 hq.2
      have hN := prod_nu_nonneg P hnu q'.2 hq'.2
      have e1 : P.stWeight (q.1, mkList P pd q.2, m) =
          (padW P pd * P.memWeight m) * ∏ i, P.nu i (q.2 i) := by
        unfold MemParams.stWeight; rw [listWeight_mkList]; ring
      have e2 : P.stWeight (q'.1, mkList P pd q'.2, m) =
          (padW P pd * P.memWeight m) * ∏ i, P.nu i (q'.2 i) := by
        unfold MemParams.stWeight; rw [listWeight_mkList]; ring
      have key := sqrt_trip _ _ _ hW hL hN
      rw [e1, e2]
      have key' : ((√((padW P pd * P.memWeight m) * ∏ i, P.nu i (q.2 i)) : ℝ) : ℂ) *
          ((√((∏ i, P.nu i (q.2 i)) * ∏ i, P.nu i (q'.2 i)) : ℝ) : ℂ) *
          ((√((padW P pd * P.memWeight m) * ∏ i, P.nu i (q'.2 i)) : ℝ) : ℂ) =
          (((padW P pd * P.memWeight m) * ∏ i, P.nu i (q.2 i) : ℝ) : ℂ) *
            ((∏ i, P.nu i (q'.2 i) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, key]; push_cast; ring
      simp only [cleanC]
      push_cast at key' ⊢
      linear_combination (-(conj (G (q.1, mkList P pd q.2, m)) *
        (memRho : ℂ) ^ P.hitCount q.1 m * (memRho : ℂ) ^ P.hitCount q'.1 m *
        P.edgeMult j (detZ q.1 q'.1 / padProd (mkList P pd q'.2)) (∏ i, q'.2 i) (∏ i, q.2 i)
          (padProd (mkList P pd q'.2)) * F (q'.1, mkList P pd q'.2, m))) * key'
    · rw [if_neg hE, if_neg hE]; ring
  -- the bilinear identity
  set T : P.MState → (ℤ × ℤ) × (Fin P.K → ℕ) → ℂ := fun s q' =>
    (P.stWeight s : ℂ) * (conj (G s) * (coeffK P (P.edgeMult j) ω s (cleanC P q'.1 q'.2) *
      (if P.edgeOut s (cleanC P q'.1 q'.2) ∈ P.stSet then
        F (P.edgeOut s (cleanC P q'.1 q'.2)) else 0)))
  have hA : pieceB P (clsClean P) (P.edgeMult j) ω G F = ∑ s ∈ P.stSet, ∑ q' ∈ S, T s q' := by
    unfold pieceB
    refine sum_congr rfl fun s _ => ?_
    rw [sum_clean P (P.edgeMult j) ω s
      (fun c => if P.edgeOut s c ∈ P.stSet then F (P.edgeOut s c) else 0)]
    rw [← sum_product (s := P.zSet) (t := labCands P)
      (f := fun q' => coeffK P (P.edgeMult j) ω s (cleanC P q'.1 q'.2) *
        (if P.edgeOut s (cleanC P q'.1 q'.2) ∈ P.stSet then
          F (P.edgeOut s (cleanC P q'.1 q'.2)) else 0)), mul_sum, mul_sum]
  set Φ : P.MState → ℂ := fun s => ∑ q' ∈ S, T s q'
  have hB := sum_stSet_blocks P Φ
  have hid : pieceB P (clsClean P) (P.edgeMult j) ω G F = ∑ m ∈ P.memSet, ∑ pd ∈ padCands P,
      bil S S (kblock P ω j pd m) (Gb pd m) (Fb pd m) := by
    rw [hA, hB]
    refine sum_congr rfl fun m hm => sum_congr rfl fun pd hpd => ?_
    unfold bil
    refine sum_congr rfl fun q hq => sum_congr rfl fun q' hq' => ?_
    exact hterm pd hpd m hm q hq q' hq'
  -- the final Cauchy–Schwarz over `(m, pd)`
  have hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s := fun s hs => stWeight_nonneg P hnu s hs
  have hl2 : ∀ (H : P.MState → ℂ), ∑ m ∈ P.memSet, ∑ pd ∈ padCands P,
      l2 S (fun q => ((√(P.stWeight (q.1, mkList P pd q.2, m)) : ℝ) : ℂ) *
        H (q.1, mkList P pd q.2, m)) ^ 2 = ∑ s ∈ P.stSet, P.stWeight s * ‖H s‖ ^ 2 := by
    intro H
    rw [sum_stSet_blocks P (fun s => P.stWeight s * ‖H s‖ ^ 2)]
    refine sum_congr rfl fun m hm => sum_congr rfl fun pd hpd => ?_
    rw [l2_sq]
    refine sum_congr rfl fun q hq => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt]
    rw [mem_product] at hq
    apply hμ
    unfold MemParams.stSet
    rw [mem_product, mem_product]
    exact ⟨hq.1, mem_listCands_mkList P pd q.2 hpd hq.2, hm⟩
  rw [hid]
  have hG2 := hl2 G
  have hF2 := hl2 F
  set I := P.memSet ×ˢ padCands P
  have hsum : ∀ (X : P.Mem → (Fin P.K → Fin P.J → ℕ) → ℝ),
      ∑ m ∈ P.memSet, ∑ pd ∈ padCands P, X m pd = ∑ q ∈ I, X q.1 q.2 := fun X =>
    (sum_product (s := P.memSet) (t := padCands P) (f := fun q => X q.1 q.2)).symm
  calc ‖∑ m ∈ P.memSet, ∑ pd ∈ padCands P, bil S S (kblock P ω j pd m) (Gb pd m) (Fb pd m)‖ ≤
      ∑ m ∈ P.memSet, ∑ pd ∈ padCands P, ε * l2 S (Gb pd m) * l2 S (Fb pd m) :=
        (norm_sum_le _ _).trans (sum_le_sum fun m hm => (norm_sum_le _ _).trans
          (sum_le_sum fun pd hpd => hblock pd hpd m hm _ _))
    _ = ε * ∑ q ∈ I, l2 S (Gb q.2 q.1) * l2 S (Fb q.2 q.1) := by
        rw [hsum (fun m pd => ε * l2 S (Gb pd m) * l2 S (Fb pd m)), mul_sum]
        exact sum_congr rfl fun q _ => by ring
    _ ≤ ε * (√(∑ q ∈ I, l2 S (Gb q.2 q.1) ^ 2) * √(∑ q ∈ I, l2 S (Fb q.2 q.1) ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hε
    _ = ε * P.wNorm G * P.wNorm F := by
        rw [← hsum (fun m pd => l2 S (Gb pd m) ^ 2), ← hsum (fun m pd => l2 S (Fb pd m) ^ 2)]
        simp only [Gb, Fb]
        rw [hG2, hF2]
        unfold MemParams.wNorm; ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: the parameter facts used by the edge bound

`EP P`: `1/2 ≤ Vᵢ ≤ 3/2`, `b'_p ≥ 1/2` on group primes, disjoint groups. Consequences:
`0 ≤ νᵢ(p) ≤ 4/p`, `Σ_{p ∈ 𝒫ᵢ} νᵢ(p) ≤ 2`, `∏ νᵢ(labᵢ) ≤ 4^K/∏ labᵢ`, and the label product is
injective on last-label tuples. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- The parameter facts. -/
structure EP : Prop where
  hV1 : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i
  hV2 : ∀ i, P.Vg i ≤ 3 / 2
  hb : ∀ p ∈ P.gPrimes, (1 : ℝ) / 2 ≤ P.bprime p
  hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')

variable {P}

lemma grp_prime {i : Fin P.K} {p : ℕ} (hp : p ∈ P.grp i) : p.Prime := by
  simp only [MemParams.grp, primeGroup, mem_filter] at hp; exact hp.2.1

lemma grp_gPrimes {i : Fin P.K} {p : ℕ} (hp : p ∈ P.grp i) : p ∈ P.gPrimes := by
  simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]; exact ⟨i, hp⟩

lemma EP.Vpos (h : EP P) (i : Fin P.K) : 0 < P.Vg i := by linarith [h.hV1 i]

lemma EP.nu_nonneg (h : EP P) (i : Fin P.K) (p : ℕ) (hp : p ∈ P.grp i) : 0 ≤ P.nu i p := by
  have := h.hb p (grp_gPrimes hp)
  have := h.Vpos i
  unfold MemParams.nu; positivity

lemma EP.nu_le (h : EP P) (i : Fin P.K) (p : ℕ) (hp : p ∈ P.grp i) :
    P.nu i p ≤ 4 / p := by
  have hb := h.hb p (grp_gPrimes hp)
  have hV := h.hV1 i
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (grp_prime hp).pos
  unfold MemParams.nu
  rw [div_le_div_iff₀ (by have := h.Vpos i; positivity) hp0]
  have h1 : 1 / 4 ≤ P.Vg i * P.bprime p := by nlinarith
  have h2 : 0 ≤ (p : ℝ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

lemma EP.sum_nu_le (h : EP P) (i : Fin P.K) : ∑ p ∈ P.grp i, P.nu i p ≤ 2 := by
  have hVi := h.Vpos i
  calc ∑ p ∈ P.grp i, P.nu i p ≤ ∑ p ∈ P.grp i, 2 / P.Vg i * (1 / (p : ℝ)) := by
        refine sum_le_sum fun p hp => ?_
        have hbp := h.hb p (grp_gPrimes hp)
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (grp_prime hp).pos
        unfold MemParams.nu
        rw [div_le_iff₀ (by positivity)]
        rw [show 2 / P.Vg i * (1 / (p : ℝ)) * (P.Vg i * ((p : ℝ) + 1) * P.bprime p) =
          2 * P.bprime p * (((p : ℝ) + 1) / p) by field_simp]
        have : (1 : ℝ) ≤ ((p : ℝ) + 1) / p := by rw [le_div_iff₀ hp0]; linarith
        nlinarith
    _ = 2 / P.Vg i * P.Vg i := by rw [← mul_sum]; rfl
    _ = 2 := by field_simp

lemma EP.prod_nu_nonneg (h : EP P) (lab : Fin P.K → ℕ) (hlab : lab ∈ labCands P) :
    0 ≤ ∏ i, P.nu i (lab i) := by
  simp only [labCands, Fintype.mem_piFinset] at hlab
  exact prod_nonneg fun i _ => h.nu_nonneg i _ (hlab i)

lemma EP.prod_nu_le (h : EP P) (lab : Fin P.K → ℕ) (hlab : lab ∈ labCands P) :
    ∏ i, P.nu i (lab i) ≤ 4 ^ P.K / ((∏ i, lab i : ℕ) : ℝ) := by
  simp only [labCands, Fintype.mem_piFinset] at hlab
  have hpos : ∀ i, (0 : ℝ) < lab i := fun i => by exact_mod_cast (grp_prime (hlab i)).pos
  calc ∏ i, P.nu i (lab i) ≤ ∏ i, (4 / (lab i : ℝ)) :=
        prod_le_prod (fun i _ => h.nu_nonneg i _ (hlab i)) fun i _ => h.nu_le i _ (hlab i)
    _ = 4 ^ P.K / ((∏ i, lab i : ℕ) : ℝ) := by
        rw [prod_div_distrib, prod_const, card_univ, Fintype.card_fin]; push_cast; rfl

/-- The label product is injective on last-label tuples (disjoint groups of primes). -/
lemma EP.prod_injOn (h : EP P) : Set.InjOn (fun lab : Fin P.K → ℕ => ∏ i, lab i) (labCands P) := by
  intro lab hlab lab' hlab' heq
  simp only [labCands, mem_coe, Fintype.mem_piFinset] at hlab hlab'
  simp only at heq
  funext i
  have hp := grp_prime (hlab i)
  have hdvd : lab i ∣ ∏ k, lab' k := heq ▸ dvd_prod_of_mem _ (mem_univ i)
  obtain ⟨k, -, hk⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hdvd
  have hpk := grp_prime (hlab' k)
  have he : lab i = lab' k := (Nat.prime_dvd_prime_iff_eq hp hpk).1 hk
  by_cases hik : i = k
  · subst hik; exact he
  · exact absurd (h.hdisj i k hik) (Finset.not_disjoint_iff.2 ⟨lab i, hlab i, he ▸ hlab' k⟩)

/-- Positions are primitive (outside any `classical` context: the instance matches `zSet`). -/
lemma zSet_gcd {z : ℤ × ℤ} (hz : z ∈ P.zSet) : Int.gcd z.1 z.2 = 1 := by
  rw [MemParams.zSet, Finset.mem_filter] at hz; exact hz.2

end ArtinPrimitiveRoots.L102G
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

/-- **D7d** ([21] (4.23)–(4.42), the edge bound). For every `G` one can choose `A₀`, then `K₀`,
so that `‖E_j‖_{H_B → H_B} ≤ L^{-G}` (clean edges by the minor-arc cancellation (4.34), dirty raw
edges by test (ii) (4.39), dirty comparison edges by (4.41)). -/
def EdgeBoundStmt (δ c₁ c₂ : ℝ) : Prop :=
  ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
        let P := dyadParams x a A₀ Y Hm Hn k
        ∀ ω, P.RootIn ω → ∀ j < P.N, P.OpBound (P.edgeOp ω j) (log x ^ (-G))

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102G: positions at a root

* `z' = det(z', w) z + det(z, z') w` when `det(z, w) = 1` (`decomp`), and `τ` is linear;
* at a root of the box, positions have `τ(z) ∈ [U/u, 16U/u] ⊆ [1/16, 16]` and
  `τ(z')/τ(z) ∈ [1/16, 16]` (`tau_ratio_mem`);
* `z'₂/τ(z') − z₂/τ(z) = det(z, z')/(τ(z) τ(z'))` (`slope_diff`);
* lines: for primitive `z, z'` and a prime `p`, `p ∣ det(z, z') ↔ [z]_p = [z']_p`;
* at most 16 positions at a fixed determinant from a box position (`card_fixed_det_le`). -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

lemma detZ_complVec (z : ℤ × ℤ) (h : Int.gcd z.1 z.2 = 1) : detZ z (complVec z) = 1 := by
  unfold detZ complVec
  have := Int.gcd_eq_gcd_ab z.1 z.2
  rw [h] at this
  simp only [Nat.cast_one] at this
  linarith

lemma decomp (z w z' : ℤ × ℤ) (h : detZ z w = 1) :
    z' = (detZ z' w * z.1 + detZ z z' * w.1, detZ z' w * z.2 + detZ z z' * w.2) := by
  unfold detZ at *
  ext
  · simp only
    linear_combination (-z'.1) * h
  · simp only
    linear_combination (-z'.2) * h

lemma tauR_decomp (ω : ℝ × ℝ × ℝ) (z w z' : ℤ × ℤ) (h : detZ z w = 1) :
    tauR ω z' = detZ z' w * tauR ω z + detZ z z' * tauR ω w := by
  have hz := decomp z w z' h
  unfold tauR
  conv_lhs => rw [hz]
  push_cast; ring

lemma tauR_decomp' (ω : ℝ × ℝ × ℝ) (z z' : ℤ × ℤ) (h : Int.gcd z.1 z.2 = 1)
    (hτ : tauR ω z ≠ 0) :
    tauR ω z' / tauR ω z = detZ z' (complVec z) + detZ z z' * ratioAt ω z := by
  rw [tauR_decomp ω z (complVec z) z' (detZ_complVec z h)]
  unfold ratioAt
  field_simp

/-- At a root of the box, a position in the box has `τ ∈ [U/u, 16U/u]`. -/
lemma tau_mem (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z : ℤ × ℤ) (hz : P.InBox ω z) :
    P.U / ω.1 ≤ tauR ω z ∧ tauR ω z ≤ 16 * P.U / ω.1 := by
  have hu : 0 < ω.1 := lt_of_lt_of_le hU hω.1
  obtain ⟨h1, h2, -, -⟩ := hz
  constructor
  · rw [div_le_iff₀ hu]; linarith
  · rw [le_div_iff₀ hu]; linarith

lemma tau_pos (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z : ℤ × ℤ) (hz : P.InBox ω z) :
    0 < tauR ω z := by
  have hu : 0 < ω.1 := lt_of_lt_of_le hU hω.1
  exact lt_of_lt_of_le (div_pos hU hu) (tau_mem P ω hω hU z hz).1

lemma tau_le (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z : ℤ × ℤ) (hz : P.InBox ω z) :
    1 / 16 ≤ tauR ω z ∧ tauR ω z ≤ 16 := by
  have hu : 0 < ω.1 := lt_of_lt_of_le hU hω.1
  obtain ⟨h1, h2⟩ := tau_mem P ω hω hU z hz
  obtain ⟨hu1, hu2, -⟩ := hω
  constructor
  · refine le_trans ?_ h1
    rw [le_div_iff₀ hu]; linarith
  · refine h2.trans ?_
    rw [div_le_iff₀ hu]; nlinarith

/-- The ratio window `τ(z')/τ(z) ∈ [1/16, 16]` ([21] (4.23)). -/
lemma tau_ratio_mem (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z z' : ℤ × ℤ)
    (hz : P.InBox ω z) (hz' : P.InBox ω z') :
    1 / 16 ≤ tauR ω z' / tauR ω z ∧ tauR ω z' / tauR ω z ≤ 16 := by
  have hu : 0 < ω.1 := lt_of_lt_of_le hU hω.1
  obtain ⟨a1, a2⟩ := tau_mem P ω hω hU z hz
  obtain ⟨b1, b2⟩ := tau_mem P ω hω hU z' hz'
  have hτ := tau_pos P ω hω hU z hz
  have hq : 0 < P.U / ω.1 := div_pos hU hu
  constructor
  · rw [le_div_iff₀ hτ]
    calc 1 / 16 * tauR ω z ≤ 1 / 16 * (16 * P.U / ω.1) := by gcongr
      _ = P.U / ω.1 := by ring
      _ ≤ _ := b1
  · rw [div_le_iff₀ hτ]
    calc tauR ω z' ≤ 16 * P.U / ω.1 := b2
      _ = 16 * (P.U / ω.1) := by ring
      _ ≤ 16 * tauR ω z := by gcongr

lemma slope_diff (ω : ℝ × ℝ × ℝ) (z z' : ℤ × ℤ) (hτ : tauR ω z ≠ 0) (hτ' : tauR ω z' ≠ 0) :
    (z'.2 : ℝ) / tauR ω z' - z.2 / tauR ω z = detZ z z' / (tauR ω z * tauR ω z') := by
  rw [div_sub_div _ _ hτ' hτ]
  have : (z'.2 : ℝ) * tauR ω z - tauR ω z' * z.2 = detZ z z' := by
    unfold detZ tauR; push_cast; ring
  rw [this, mul_comm (tauR ω z')]

/-! ## Lines modulo a prime -/

lemma not_both_zero (p : ℕ) (hp : p.Prime) (w : ℤ × ℤ) (hw : Int.gcd w.1 w.2 = 1) :
    ¬ ((w.1 : ZMod p) = 0 ∧ (w.2 : ZMod p) = 0) := by
  rintro ⟨h1, h2⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
  have h := Int.dvd_gcd h1 h2
  rw [hw] at h
  have h' : p ∣ 1 := by exact_mod_cast h
  exact hp.one_lt.ne' (Nat.dvd_one.1 h')

lemma lineOf_eq_iff (p : ℕ) (hp : p.Prime) (z z' : ℤ × ℤ) (hz : Int.gcd z.1 z.2 = 1)
    (hz' : Int.gcd z'.1 z'.2 = 1) : lineOf p z = lineOf p z' ↔ (p : ℤ) ∣ detZ z z' := by
  have := Fact.mk hp
  have hdet : ((p : ℤ) ∣ detZ z z') ↔ ((z.1 : ZMod p) * z'.2 - z.2 * z'.1 = 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; unfold detZ; push_cast; rfl
  have hn := not_both_zero p hp z hz
  have hn' := not_both_zero p hp z' hz'
  unfold lineOf
  rw [hdet]
  have hpv : ∀ x : ZMod p, x.val < p := fun x => ZMod.val_lt x
  by_cases h1 : (p : ℤ) ∣ z.1 <;> by_cases h2 : (p : ℤ) ∣ z'.1
  · rw [if_pos h1, if_pos h2]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
    simp [h1, h2]
  · rw [if_pos h1, if_neg h2]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
    have hb : (z.2 : ZMod p) ≠ 0 := fun h => hn ⟨h1, h⟩
    constructor
    · intro h; exact absurd h.symm (ne_of_lt (hpv _))
    · intro h; rw [h1, zero_mul, zero_sub, neg_eq_zero] at h
      exact absurd (mul_eq_zero.1 h) (by tauto)
  · rw [if_neg h1, if_pos h2]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
    have hb : (z'.2 : ZMod p) ≠ 0 := fun h => hn' ⟨h2, h⟩
    constructor
    · intro h; exact absurd h (ne_of_lt (hpv _))
    · intro h; rw [h2, mul_zero, sub_zero] at h
      exact absurd (mul_eq_zero.1 h) (by tauto)
  · rw [if_neg h1, if_neg h2]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
    rw [(ZMod.val_injective p).eq_iff]
    constructor
    · intro h
      have := congrArg (· * ((z.1 : ZMod p) * (z'.1 : ZMod p))) h
      field_simp at this
      linear_combination -this
    · intro h
      field_simp
      linear_combination -h

/-- `D ∣ det` from equal lines at all primes of a set (squarefree product). -/
lemma prod_dvd_det_of_lines (ps : Finset ℕ) (hps : ∀ p ∈ ps, p.Prime) (z z' : ℤ × ℤ)
    (hz : Int.gcd z.1 z.2 = 1) (hz' : Int.gcd z'.1 z'.2 = 1)
    (h : ∀ p ∈ ps, lineOf p z = lineOf p z') : ((∏ p ∈ ps, p : ℕ) : ℤ) ∣ detZ z z' := by
  push_cast
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    rw [Function.onFun, Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.coprime_primes (hps p hp) (hps q hq)).2 hpq
  · intro p hp; exact (lineOf_eq_iff p (hps p hp) z z' hz hz').1 (h p hp)

/-! ## Counting positions at a fixed determinant -/

open Classical in
/-- At most 16 box positions at a fixed determinant from a box position ([21] (4.23)). -/
lemma card_fixed_det_le (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z : ℤ × ℤ)
    (hz : P.InBox ω z) (hzp : Int.gcd z.1 z.2 = 1) (J : ℤ) :
    ((P.zSet.filter fun z' => P.InBox ω z' ∧ detZ z z' = J).card : ℝ) ≤ 16 := by
  classical
  set w := complVec z
  have hw : detZ z w = 1 := detZ_complVec z hzp
  have hτ := tau_pos P ω hω hU z hz
  set r := ratioAt ω z
  set Sf := P.zSet.filter fun z' => P.InBox ω z' ∧ detZ z z' = J
  set hmap : ℤ × ℤ → ℤ := fun z' => detZ z' w
  have hinj : Set.InjOn hmap Sf := by
    intro a ha b hb hab
    simp only [Sf, coe_filter, Set.mem_ofPred_eq] at ha hb
    rw [decomp z w a hw, decomp z w b hw]
    simp only [hmap] at hab
    rw [hab, ha.2.2, hb.2.2]
  set lo : ℤ := ⌈(1 / 16 : ℝ) - J * r⌉
  set hi : ℤ := ⌊(16 : ℝ) - J * r⌋
  have himg : Sf.image hmap ⊆ Icc lo hi := by
    intro h hh
    obtain ⟨z', hz', rfl⟩ := mem_image.1 hh
    simp only [Sf, mem_filter] at hz'
    have hm := tau_ratio_mem P ω hω hU z z' hz hz'.2.1
    rw [tauR_decomp' ω z z' hzp hτ.ne', hz'.2.2] at hm
    simp only [mem_Icc, hmap, lo, hi]
    constructor
    · exact Int.ceil_le.2 (by linarith [hm.1])
    · exact Int.le_floor.2 (by linarith [hm.2])
  have hcard : Sf.card = (Sf.image hmap).card := (card_image_of_injOn hinj).symm
  have h1 : ((Icc lo hi).card : ℝ) ≤ 16 := by
    rw [Int.card_Icc]
    have hlo : (1 / 16 : ℝ) - J * r ≤ lo := Int.le_ceil _
    have hhi : (hi : ℝ) ≤ 16 - J * r := Int.floor_le _
    have : (hi : ℝ) - lo < 16 := by linarith
    have : hi - lo < 16 := by exact_mod_cast this
    have : (hi + 1 - lo).toNat ≤ 16 := by omega
    exact_mod_cast this
  rw [hcard]
  exact le_trans (by exact_mod_cast card_le_card himg) h1

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: crude sums of the edge kernels over targets ([21] (4.23)–(4.25))

From a box position `z`, over the box targets `z'` with `D ∣ det(z, z')`:
* `sum_rawK_le`: `Σ_{z'} ‖rawK‖ ≤ 16` (the raw determinant `D(b − a)` is fixed);
* `sum_majK_le`: `Σ_{z'} ‖majK‖ ≤ 16 (10Y + 1) · 4L^{3A₀}/Y` (`|t| < 5Y`, `|H_𝔐| ≤ |𝔐|`);
* `norm_majorKernel_le`: `‖H_𝔐(t;a,b)‖ ≤ 4 L^{3A₀}/Y`. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset MeasureTheory

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

lemma norm_rawK_le (t : ℤ) (a b D : ℕ) (hD : P.d₀ ≤ D) (hD1 : 1 ≤ D) :
    ‖rawK P t a b D‖ ≤ if t - b + a = 0 then 1 else 0 := by
  unfold rawK
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD1
  have hd : (P.d₀ : ℝ) / D ≤ 1 := by
    rw [div_le_one hDp]; exact_mod_cast hD
  have hd0 : (0 : ℝ) ≤ (P.d₀ : ℝ) / D := by positivity
  have h1 := abs_dyadicBump_le_one' ((b : ℝ) / P.Y)
  have h2 := abs_dyadicBump_le_one' ((a : ℝ) / P.Y)
  have h3 : |arcCutoff ((t : ℝ) / P.Y)| ≤ 1 := by
    have := abs_arcCutoff_le' ((t : ℝ) / P.Y); split_ifs at this <;> linarith
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hd0]
  split_ifs with h
  · rw [norm_one, mul_one]
    calc (P.d₀ : ℝ) / D * |dyadicBump ((b : ℝ) / P.Y)| * |dyadicBump ((a : ℝ) / P.Y)| *
        |arcCutoff ((t : ℝ) / P.Y)| ≤ 1 * 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  · simp

lemma norm_majorKernel_le (t a b : ℤ) (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀) (hY : 0 < P.Y) :
    ‖majorKernel P.x P.A₀ P.Y t a b‖ ≤
      (if |(t : ℝ) / P.Y| < 5 then 1 else 0) * (4 * log P.x ^ (3 * P.A₀) / P.Y) := by
  unfold majorKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hvol := volume_majorArcs_le' P.x P.A₀ P.Y hL hA₀ hY
  have hfin : volume (majorArcs P.x P.A₀ P.Y) < ⊤ := lt_of_le_of_lt hvol ENNReal.ofReal_lt_top
  have hint : ‖∫ θ in majorArcs P.x P.A₀ P.Y,
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))‖ ≤
      1 * volume.real (majorArcs P.x P.A₀ P.Y) := by
    apply norm_setIntegral_le_of_norm_le_const hfin
    intro θ _
    rw [show 2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ) =
      ((2 * π * (θ * (t - b + a)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.norm_exp_ofReal_mul_I]
  have hreal : volume.real (majorArcs P.x P.A₀ P.Y) ≤ 4 * log P.x ^ (3 * P.A₀) / P.Y :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hvol
  have hψ := abs_arcCutoff_le' ((t : ℝ) / P.Y)
  have h0 : 0 ≤ ‖∫ θ in majorArcs P.x P.A₀ P.Y,
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))‖ := norm_nonneg _
  split_ifs at hψ ⊢ with h
  · calc |arcCutoff ((t : ℝ) / P.Y)| * _ ≤ 1 * (4 * log P.x ^ (3 * P.A₀) / P.Y) :=
        mul_le_mul hψ (by linarith) h0 (by norm_num)
      _ = _ := by ring
  · have : |arcCutoff ((t : ℝ) / P.Y)| = 0 := le_antisymm hψ (abs_nonneg _)
    rw [this, zero_mul, zero_mul]

lemma norm_majK_le (j : ℕ) (t : ℤ) (a b D : ℕ) (hD : P.d₀ ≤ D) (hD1 : 1 ≤ D)
    (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀) (hY : 0 < P.Y) :
    ‖majK P j t a b D‖ ≤
      (if |(t : ℝ) / P.Y| < 5 then 1 else 0) * (4 * log P.x ^ (3 * P.A₀) / P.Y) := by
  rw [norm_majK_eq]
  have hDp : (0 : ℝ) < D := by exact_mod_cast hD1
  have hd : (P.d₀ : ℝ) / D ≤ 1 := by rw [div_le_one hDp]; exact_mod_cast hD
  have hd0 : (0 : ℝ) ≤ (P.d₀ : ℝ) / D := by positivity
  have h1 := abs_dyadicBump_le_one' ((b : ℝ) / P.Y)
  have h2 := abs_dyadicBump_le_one' ((a : ℝ) / P.Y)
  have hc : |(P.d₀ : ℝ) / D * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hd0]
    calc (P.d₀ : ℝ) / D * |dyadicBump ((b : ℝ) / P.Y)| * |dyadicBump ((a : ℝ) / P.Y)| ≤
        1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hm := norm_majorKernel_le P t a b hL hA₀ hY
  calc _ ≤ 1 * ‖majorKernel P.x P.A₀ P.Y t a b‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hm

open Classical in
/-- Raw kernels summed over targets. -/
lemma sum_rawK_le (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z : ℤ × ℤ)
    (hz : P.InBox ω z) (hzp : Int.gcd z.1 z.2 = 1) (D : ℕ) (hD : P.d₀ ≤ D) (hD1 : 1 ≤ D)
    (a b : ℕ) :
    ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then
      ‖rawK P (detZ z z' / D) a b D‖ else 0) ≤ 16 := by
  set J : ℤ := D * ((b : ℤ) - a)
  calc ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then
        ‖rawK P (detZ z z' / D) a b D‖ else 0) ≤
      ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ detZ z z' = J then (1 : ℝ) else 0) := by
        refine sum_le_sum fun z' _ => ?_
        split_ifs with h1 h2 h2
        · exact (norm_rawK_le P _ a b D hD hD1).trans (by split_ifs <;> norm_num)
        · have hr := norm_rawK_le P (detZ z z' / D) a b D hD hD1
          rw [if_neg] at hr
          · exact hr
          · intro h0
            apply h2
            refine ⟨h1.1, ?_⟩
            obtain ⟨k, hk⟩ := h1.2
            have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
            rw [hk, Int.mul_ediv_cancel_left _ hD0] at h0
            rw [hk]
            simp only [J]
            have : k = b - a := by linarith
            rw [this]
        · exact zero_le_one
        · exact le_refl _
    _ = ((P.zSet.filter fun z' => P.InBox ω z' ∧ detZ z z' = J).card : ℝ) := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 16 := card_fixed_det_le P ω hω hU z hz hzp J

open Classical in
/-- Comparison kernels summed over targets. -/
lemma sum_majK_le (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z : ℤ × ℤ)
    (hz : P.InBox ω z) (hzp : Int.gcd z.1 z.2 = 1) (D : ℕ) (hD : P.d₀ ≤ D) (hD1 : 1 ≤ D)
    (j : ℕ) (a b : ℕ) (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀) (hY : 0 < P.Y) :
    ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then
      ‖majK P j (detZ z z' / D) a b D‖ else 0) ≤
        16 * (10 * P.Y + 1) * (4 * log P.x ^ (3 * P.A₀) / P.Y) := by
  set M := 4 * log P.x ^ (3 * P.A₀) / P.Y
  have hM : 0 ≤ M := by positivity
  set T : Finset ℤ := Icc (-⌊5 * P.Y⌋) ⌊5 * P.Y⌋
  have hstep : ∀ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then
      ‖majK P j (detZ z z' / D) a b D‖ else 0) ≤
      ∑ t ∈ T, (if P.InBox ω z' ∧ detZ z z' = D * t then M else 0) := by
    intro z' _
    split_ifs with h1
    · have hk := norm_majK_le P j (detZ z z' / D) a b D hD hD1 hL hA₀ hY
      split_ifs at hk with h5
      · rw [one_mul] at hk
        obtain ⟨k, hkk⟩ := h1.2
        have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
        have hq : detZ z z' / D = k := by rw [hkk, Int.mul_ediv_cancel_left _ hD0]
        rw [hq] at h5
        have hkT : k ∈ T := by
          rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY, abs_lt] at h5
          simp only [T, mem_Icc]
          constructor
          · have : (-⌊5 * P.Y⌋ : ℤ) ≤ k := by
              have h6 : -(5 * P.Y) < k := by linarith
              have : -(k : ℝ) < 5 * P.Y := by linarith
              have : -k ≤ ⌊5 * P.Y⌋ := Int.le_floor.2 (by push_cast; linarith)
              linarith
            exact this
          · exact Int.le_floor.2 (by linarith)
        refine hk.trans ?_
        rw [sum_eq_single k]
        · rw [if_pos ⟨h1.1, hkk⟩]
        · intro t _ ht
          rw [if_neg]
          intro h7
          apply ht
          have := h7.2
          rw [hkk] at this
          exact (mul_left_cancel₀ hD0 this).symm
        · intro h7; exact absurd hkT h7
      · rw [zero_mul] at hk
        exact hk.trans (sum_nonneg fun t _ => by split_ifs <;> linarith)
    · exact sum_nonneg fun t _ => by split_ifs <;> linarith
  calc ∑ z' ∈ P.zSet, _ ≤ ∑ z' ∈ P.zSet, ∑ t ∈ T,
        (if P.InBox ω z' ∧ detZ z z' = D * t then M else 0) := sum_le_sum hstep
    _ = ∑ t ∈ T, ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ detZ z z' = D * t then M else 0) := sum_comm
    _ ≤ ∑ _t ∈ T, 16 * M := by
        refine sum_le_sum fun t _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (card_fixed_det_le P ω hω hU z hz hzp _) hM
    _ = T.card * (16 * M) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (10 * P.Y + 1) * (16 * M) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simp only [T]
        rw [Int.card_Icc]
        have h1 : (⌊5 * P.Y⌋ : ℝ) ≤ 5 * P.Y := Int.floor_le _
        have h2 : (0 : ℤ) ≤ ⌊5 * P.Y⌋ := Int.floor_nonneg.2 (by positivity)
        have : ((⌊5 * P.Y⌋ + 1 - -⌊5 * P.Y⌋).toNat : ℝ) = 2 * ⌊5 * P.Y⌋ + 1 := by
          rw [show ⌊5 * P.Y⌋ + 1 - -⌊5 * P.Y⌋ = 2 * ⌊5 * P.Y⌋ + 1 by ring]
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
        rw [this]; linarith
    _ = _ := by ring

/-- The crude constant `16 + 16(10Y + 1)·4L^{3A₀}/Y`. -/
noncomputable def Ccr : ℝ := 16 + 16 * (10 * P.Y + 1) * (4 * log P.x ^ (3 * P.A₀) / P.Y)

open Classical in
lemma crude_tgt (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z : ℤ × ℤ)
    (hz : P.InBox ω z) (hzp : Int.gcd z.1 z.2 = 1) (D : ℕ) (hD : P.d₀ ≤ D) (hD1 : 1 ≤ D)
    (j : ℕ) (a b : ℕ) (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀) (hY : 0 < P.Y) :
    ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then
      ‖rawK P (detZ z z' / D) a b D‖ + ‖majK P j (detZ z z' / D) a b D‖ else 0) ≤ Ccr P := by
  have h1 := sum_rawK_le P ω hω hU z hz hzp D hD hD1 a b
  have h2 := sum_majK_le P ω hω hU z hz hzp D hD hD1 j a b hL hA₀ hY
  unfold Ccr
  calc _ = ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then
        ‖rawK P (detZ z z' / D) a b D‖ else 0) + ∑ z' ∈ P.zSet,
          (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then ‖majK P j (detZ z z' / D) a b D‖ else 0) := by
        rw [← sum_add_distrib]; exact sum_congr rfl fun z' _ => by split_ifs <;> simp
    _ ≤ _ := add_le_add h1 h2

open Classical in
lemma crude_src (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z' : ℤ × ℤ)
    (hz' : P.InBox ω z') (hzp : Int.gcd z'.1 z'.2 = 1) (D : ℕ) (hD : P.d₀ ≤ D) (hD1 : 1 ≤ D)
    (j : ℕ) (a b : ℕ) (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀) (hY : 0 < P.Y) :
    ∑ z ∈ P.zSet, (if P.InBox ω z ∧ (D : ℤ) ∣ detZ z z' then
      ‖rawK P (detZ z z' / D) a b D‖ + ‖majK P j (detZ z z' / D) a b D‖ else 0) ≤ Ccr P := by
  refine le_trans (le_of_eq (sum_congr rfl fun z _ => ?_))
    (crude_tgt P ω hω hU z' hz' hzp D hD hD1 j b a hL hA₀ hY)
  have hsw : (D : ℤ) ∣ detZ z z' ↔ (D : ℤ) ∣ detZ z' z := by
    rw [detZ_swap z z', dvd_neg]
  by_cases h : P.InBox ω z ∧ (D : ℤ) ∣ detZ z z'
  · rw [if_pos h, if_pos ⟨h.1, hsw.1 h.2⟩]
    have hneg : detZ z z' / D = -(detZ z' z / D) := by
      rw [show detZ z z' = -detZ z' z from (detZ_swap z' z), Int.neg_ediv_of_dvd (hsw.1 h.2)]
    rw [hneg, norm_rawK_swap, norm_majK_swap]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, hsw.2 h'.2⟩)]

open Classical in
/-- Targets in the `ψ`-window `|det/D| < 5Y`, counted with a constant weight. -/
lemma sum_window_le (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z : ℤ × ℤ)
    (hz : P.InBox ω z) (hzp : Int.gcd z.1 z.2 = 1) (D : ℕ) (hD1 : 1 ≤ D) (Mv : ℝ) (hM : 0 ≤ Mv)
    (hY : 0 < P.Y) :
    ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' ∧
      |((detZ z z' / D : ℤ) : ℝ) / P.Y| < 5 then Mv else 0) ≤ 16 * (10 * P.Y + 1) * Mv := by
  set T : Finset ℤ := Icc (-⌊5 * P.Y⌋) ⌊5 * P.Y⌋
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hstep : ∀ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' ∧
      |((detZ z z' / D : ℤ) : ℝ) / P.Y| < 5 then Mv else 0) ≤
      ∑ t ∈ T, (if P.InBox ω z' ∧ detZ z z' = D * t then Mv else 0) := by
    intro z' _
    split_ifs with h1
    · obtain ⟨k, hkk⟩ := h1.2.1
      have h5 := h1.2.2
      have hq : detZ z z' / D = k := by rw [hkk, Int.mul_ediv_cancel_left _ hD0]
      rw [hq] at h5
      have hkT : k ∈ T := by
        rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY, abs_lt] at h5
        simp only [T, mem_Icc]
        constructor
        · have : -k ≤ ⌊5 * P.Y⌋ := Int.le_floor.2 (by push_cast; linarith)
          linarith
        · exact Int.le_floor.2 (by linarith)
      rw [sum_eq_single k]
      · rw [if_pos ⟨h1.1, hkk⟩]
      · intro t _ ht
        rw [if_neg]
        intro h7
        apply ht
        have := h7.2
        rw [hkk] at this
        exact (mul_left_cancel₀ hD0 this).symm
      · intro h7; exact absurd hkT h7
    · exact sum_nonneg fun t _ => by split_ifs <;> linarith
  calc _ ≤ ∑ z' ∈ P.zSet, ∑ t ∈ T,
        (if P.InBox ω z' ∧ detZ z z' = D * t then Mv else 0) := sum_le_sum hstep
    _ = ∑ t ∈ T, ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ detZ z z' = D * t then Mv else 0) := sum_comm
    _ ≤ ∑ _t ∈ T, 16 * Mv := by
        refine sum_le_sum fun t _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (card_fixed_det_le P ω hω hU z hz hzp _) hM
    _ = T.card * (16 * Mv) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (10 * P.Y + 1) * (16 * Mv) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simp only [T]
        rw [Int.card_Icc]
        have h1 : (⌊5 * P.Y⌋ : ℝ) ≤ 5 * P.Y := Int.floor_le _
        have h2 : (0 : ℤ) ≤ ⌊5 * P.Y⌋ := Int.floor_nonneg.2 (by positivity)
        have : ((⌊5 * P.Y⌋ + 1 - -⌊5 * P.Y⌋).toNat : ℝ) = 2 * ⌊5 * P.Y⌋ + 1 := by
          rw [show ⌊5 * P.Y⌋ + 1 - -⌊5 * P.Y⌋ = 2 * ⌊5 * P.Y⌋ + 1 by ring]
          rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
        rw [this]; linarith
    _ = _ := by ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: crude row bounds of the dirty pieces ([21] (4.24)–(4.25))

* `norm_coeffK_le`: the edge coefficient is at most `∏ᵢ g(tgᵢ) ‖κ‖` with `g = ν` on fresh labels and
  `2·count` on promotions (`ρ ≤ 1`, `Vᵢ ≥ 1/2`);
* `sum_tg_gfac_le`: summing the label/flag choices costs `(2 + 2B)^K`;
* `rowSum_noProm_raw_le` (R2): raw rows without promotions are `≤ 2^K · 16 · 2^K`;
* `rowSum_all_maj_le` (R4): comparison rows are `≤ 2^K (2+2B)^K · 16(10Y+1) · 4L^{3A₀}/Y`. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- The per-group factor of the edge coefficient. -/
noncomputable def gfac (m : P.Mem) (z' : ℤ × ℤ) (i : Fin P.K) (q : ℕ × Bool) : ℝ :=
  if q.2 then 2 * (P.memAt m (i, q.1, lineOf q.1 z') : ℝ) else P.nu i q.1

lemma gfac_nonneg (hEP : EP P) (m : P.Mem) (z' : ℤ × ℤ) (i : Fin P.K) (q : ℕ × Bool)
    (hq : q.1 ∈ P.grp i) : 0 ≤ gfac P m z' i q := by
  unfold gfac; split_ifs
  · positivity
  · exact hEP.nu_nonneg i _ hq

lemma mem_choices (c : EC P) (hc : c ∈ P.edgeChoices) :
    c.2.1 ∈ P.zSet ∧ ∀ i, (c.2.2 i).1 ∈ P.grp i := by
  simp only [MemParams.edgeChoices, mem_product, mem_univ, true_and, Fintype.mem_piFinset] at hc
  exact ⟨hc.1, fun i => (hc.2 i).1⟩

lemma memRho_pow_le1 (n : ℕ) : memRho ^ n ≤ 1 := by
  unfold memRho; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma rfac_le_gfac (hEP : EP P) (s : P.MState) (c : EC P) (hc : c ∈ P.edgeChoices) :
    rfac P s c ≤ ∏ i, gfac P s.2.2 c.2.1 i (c.2.2 i) := by
  have hρ := memRho_nonneg
  have hg := (mem_choices P c hc).2
  unfold rfac
  have hprod : (∏ i, if (c.2.2 i).2 then (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i
      else P.nu i (c.2.2 i).1) ≤ ∏ i, gfac P s.2.2 c.2.1 i (c.2.2 i) := by
    refine prod_le_prod (fun i _ => ?_) fun i _ => ?_
    · split_ifs
      · exact div_nonneg (Nat.cast_nonneg _) (hEP.Vpos i).le
      · exact hEP.nu_nonneg i _ (hg i)
    · unfold gfac
      split_ifs with h
      · rw [div_le_iff₀ (hEP.Vpos i)]
        have := hEP.hV1 i
        have h0 : (0 : ℝ) ≤ P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) := Nat.cast_nonneg _
        unfold MemParams.promPart
        nlinarith
      · exact le_refl _
  have h0 : 0 ≤ ∏ i, (if (c.2.2 i).2 then (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i
      else P.nu i (c.2.2 i).1) := by
    refine prod_nonneg fun i _ => ?_
    split_ifs
    · exact div_nonneg (Nat.cast_nonneg _) (hEP.Vpos i).le
    · exact hEP.nu_nonneg i _ (hg i)
  calc memRho ^ P.hitCount s.1 s.2.2 * (∏ i, if (c.2.2 i).2 then
        (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) *
        memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c) ≤ 1 * (∏ i, gfac P s.2.2 c.2.1 i (c.2.2 i)) * 1 :=
        mul_le_mul (mul_le_mul (memRho_pow_le1 _) hprod h0 zero_le_one)
          (memRho_pow_le1 _) (pow_nonneg hρ _)
          (mul_nonneg zero_le_one (prod_nonneg fun i _ => gfac_nonneg P hEP _ _ i _ (hg i)))
    _ = _ := by ring

open Classical in
lemma norm_coeffK_le (hEP : EP P) (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState)
    (c : EC P) (hc : c ∈ P.edgeChoices) :
    ‖coeffK P κ ω s c‖ ≤ if ECond P ω s c then (∏ i, gfac P s.2.2 c.2.1 i (c.2.2 i)) *
      ‖κ (detZ s.1 c.2.1 / padProd s.2.1) (∏ i, (c.2.2 i).1) (lastProd s.2.1) (padProd s.2.1)‖
      else 0 := by
  unfold coeffK
  split_ifs with h
  · rw [norm_mul, Complex.norm_real]
    have hr : 0 ≤ rfac P s c := rfac_nonneg P (fun i p hp => hEP.nu_nonneg i p hp)
      (fun i => (hEP.Vpos i).le) s c hc
    rw [Real.norm_of_nonneg hr]
    exact mul_le_mul_of_nonneg_right (rfac_le_gfac P hEP s c hc) (norm_nonneg _)
  · simp

lemma lineOf_le (p : ℕ) (hp : 0 < p) (z' : ℤ × ℤ) : lineOf p z' ≤ p := by
  unfold lineOf
  split_ifs
  · exact le_refl _
  · have : NeZero p := ⟨hp.ne'⟩
    exact (ZMod.val_lt _).le

lemma part_mem (i : Fin P.K) (p : ℕ) (hp : p ∈ P.grp i) (z' : ℤ × ℤ) :
    (i, p, lineOf p z') ∈ P.partSet := by
  unfold MemParams.partSet
  simp only [mem_biUnion, mem_univ, true_and, mem_image, mem_range]
  exact ⟨i, p, hp, lineOf p z', Nat.lt_succ_of_le (lineOf_le p (grp_prime hp).pos z'), rfl⟩

lemma sum_memAt_le (m : P.Mem) (z' : ℤ × ℤ) (i : Fin P.K) :
    ∑ p ∈ P.grp i, (P.memAt m (i, p, lineOf p z') : ℝ) ≤ P.memSize m := by
  classical
  set g : {p // p ∈ P.grp i} → P.PT := fun x => ⟨(i, x.1, lineOf x.1 z'), part_mem P i x.1 x.2 z'⟩
  have hinj : Set.InjOn g ((P.grp i).attach : Set {p // p ∈ P.grp i}) := by
    intro x _ x' _ h
    have := congrArg (fun y : P.PT => y.1.2.1) h
    exact Subtype.ext this
  calc ∑ p ∈ P.grp i, (P.memAt m (i, p, lineOf p z') : ℝ) =
      ∑ x ∈ (P.grp i).attach, ((m (g x) : ℕ) : ℝ) := by
        rw [← sum_attach]
        refine sum_congr rfl fun x _ => ?_
        rw [memAt_of_mem P m _ (part_mem P i x.1 x.2 z')]
    _ = ∑ y ∈ (P.grp i).attach.image g, ((m y : ℕ) : ℝ) :=
        (sum_image (f := fun y => ((m y : ℕ) : ℝ)) hinj).symm
    _ ≤ ∑ y : P.PT, ((m y : ℕ) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.cast_nonneg _
    _ = P.memSize m := by unfold MemParams.memSize; push_cast; rfl

lemma sum_tg_gfac_le (hEP : EP P) (m : P.Mem) (z' : ℤ × ℤ) :
    ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
      ∏ i, gfac P m z' i (tg i) ≤ (2 + 2 * P.memSize m) ^ P.K := by
  rw [← prod_univ_sum]
  calc ∏ i, ∑ q ∈ P.grp i ×ˢ (univ : Finset Bool), gfac P m z' i q ≤
      ∏ _i : Fin P.K, (2 + 2 * (P.memSize m : ℝ)) := by
        refine prod_le_prod (fun i _ => sum_nonneg fun q hq =>
          gfac_nonneg P hEP m z' i q (mem_product.1 hq).1) fun i _ => ?_
        rw [sum_product]
        calc ∑ p ∈ P.grp i, ∑ fl : Bool, gfac P m z' i (p, fl) =
            ∑ p ∈ P.grp i, (P.nu i p + 2 * (P.memAt m (i, p, lineOf p z') : ℝ)) := by
              refine sum_congr rfl fun p _ => ?_
              rw [Fintype.sum_bool]; unfold gfac; simp; ring
          _ = ∑ p ∈ P.grp i, P.nu i p + 2 * ∑ p ∈ P.grp i, (P.memAt m (i, p, lineOf p z') : ℝ) := by
              rw [sum_add_distrib, mul_sum]
          _ ≤ 2 + 2 * P.memSize m := by
              have := hEP.sum_nu_le i
              have := sum_memAt_le P m z' i
              linarith
    _ = _ := by simp

lemma rowSum_eq (Qc : Finset (Fin P.K) → Finset (Fin P.K) → Prop) (κ : ℤ → ℕ → ℕ → ℕ → ℂ)
    (ω : ℝ × ℝ × ℝ) (s : P.MState) :
    rowSum P Qc κ ω s = ∑ St : Finset (Fin P.K), ∑ z' ∈ P.zSet,
      ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
        ‖coeffP P Qc κ ω s (St, z', tg)‖ := by
  unfold rowSum MemParams.edgeChoices
  rw [sum_product]
  refine sum_congr rfl fun St _ => ?_
  rw [sum_product]

lemma ecChoice_mem (St : Finset (Fin P.K)) (z' : ℤ × ℤ) (hz' : z' ∈ P.zSet)
    (tg : Fin P.K → ℕ × Bool) (htg : tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool))) :
    ((St, z', tg) : EC P) ∈ P.edgeChoices := by
  simp only [MemParams.edgeChoices, mem_product, mem_univ, true_and]
  exact ⟨hz', htg⟩

lemma padProd_pos (s : P.MState) (hs : s ∈ P.stSet) : 1 ≤ padProd s.2.1 := by
  unfold MemParams.stSet at hs
  rw [mem_product, mem_product] at hs
  have h := hs.2.1
  simp only [listCands, Fintype.mem_piFinset] at h
  unfold padProd
  exact Nat.one_le_iff_ne_zero.2 (prod_ne_zero_iff.2 fun i _ => prod_ne_zero_iff.2 fun k _ =>
    (grp_prime (h i k.castSucc)).pos.ne')

lemma memSize_le (m : P.Mem) (hm : m ∈ P.memSet) : (P.memSize m : ℝ) ≤ P.B := by
  unfold MemParams.memSet at hm
  exact_mod_cast (mem_filter.1 hm).2

lemma stSet_parts (s : P.MState) (hs : s ∈ P.stSet) :
    s.1 ∈ P.zSet ∧ s.2.1 ∈ listCands P.x P.a P.J ∧ s.2.2 ∈ P.memSet := by
  unfold MemParams.stSet at hs
  rw [mem_product, mem_product] at hs
  exact hs

lemma zSet_prim (z : ℤ × ℤ) (hz : z ∈ P.zSet) : Int.gcd z.1 z.2 = 1 := by
  rw [MemParams.zSet, Finset.mem_filter] at hz; exact hz.2

/-- **R4**: crude comparison rows. -/
theorem rowSum_all_maj_le (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    (j : ℕ) (s : P.MState) (hs : s ∈ P.stSet) (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀)
    (hY : 0 < P.Y) :
    rowSum P (clsAll P) (majK P j) ω s ≤
      2 ^ P.K * (16 * (10 * P.Y + 1) * (4 * log P.x ^ (3 * P.A₀) / P.Y)) *
        (2 + 2 * P.B) ^ P.K := by
  classical
  obtain ⟨hz, _, hm⟩ := stSet_parts P s hs
  set MA := 4 * log P.x ^ (3 * P.A₀) / P.Y
  have hMA : 0 ≤ MA := by positivity
  have hD1 := padProd_pos P s hs
  set Tg := Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool))
  rw [rowSum_eq]
  by_cases hsrc : P.InBox ω s.1 ∧ P.d₀ ≤ padProd s.2.1
  swap
  · refine le_trans (le_of_eq (sum_eq_zero fun St _ => sum_eq_zero fun z' _ =>
      sum_eq_zero fun tg _ => ?_)) (by positivity)
    unfold coeffP coeffK
    split_ifs with h1 h2
    · exact absurd ⟨h2.1.2.2.2.2.2.1, h2.1.2.2.1⟩ hsrc
    · simp
    · simp
  have hstep : ∀ St, ∀ z' ∈ P.zSet, ∀ tg ∈ Tg, ‖coeffP P (clsAll P) (majK P j) ω s (St, z', tg)‖ ≤
      (∏ i, gfac P s.2.2 z' i (tg i)) * (if P.InBox ω z' ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 z' ∧
        |((detZ s.1 z' / padProd s.2.1 : ℤ) : ℝ) / P.Y| < 5 then MA else 0) := by
    intro St z' hz' tg htg
    have hc := ecChoice_mem P St z' hz' tg htg
    unfold coeffP clsAll
    rw [if_pos trivial]
    refine (norm_coeffK_le P hEP _ ω s _ hc).trans ?_
    have hg : 0 ≤ ∏ i, gfac P s.2.2 z' i (tg i) :=
      prod_nonneg fun i _ => gfac_nonneg P hEP _ _ i _ ((mem_choices P _ hc).2 i)
    have hRHS : 0 ≤ (∏ i, gfac P s.2.2 z' i (tg i)) * (if P.InBox ω z' ∧
        (padProd s.2.1 : ℤ) ∣ detZ s.1 z' ∧
        |((detZ s.1 z' / padProd s.2.1 : ℤ) : ℝ) / P.Y| < 5 then MA else 0) :=
      mul_nonneg hg (by split_ifs <;> linarith)
    by_cases hE : ECond P ω s (St, z', tg)
    · rw [if_pos hE]
      have hk := norm_majK_le P j (detZ s.1 z' / padProd s.2.1) (∏ i, (tg i).1) (lastProd s.2.1)
        (padProd s.2.1) hsrc.2 hD1 hL hA₀ hY
      by_cases hw : |((detZ s.1 z' / padProd s.2.1 : ℤ) : ℝ) / P.Y| < 5
      · rw [if_pos hw, one_mul] at hk
        rw [if_pos ⟨hE.1.2.2.2.2.2.2.1, hE.1.2.2.2.2.1, hw⟩]
        exact mul_le_mul_of_nonneg_left hk hg
      · rw [if_neg hw, zero_mul] at hk
        have : ‖majK P j (detZ s.1 z' / padProd s.2.1) (∏ i, (tg i).1) (lastProd s.2.1)
            (padProd s.2.1)‖ = 0 := le_antisymm hk (norm_nonneg _)
        rw [this, mul_zero]; exact hRHS
    · rw [if_neg hE]; exact hRHS
  calc ∑ St : Finset (Fin P.K), ∑ z' ∈ P.zSet, ∑ tg ∈ Tg,
        ‖coeffP P (clsAll P) (majK P j) ω s (St, z', tg)‖ ≤
      ∑ _St : Finset (Fin P.K), ∑ z' ∈ P.zSet, ∑ tg ∈ Tg, (∏ i, gfac P s.2.2 z' i (tg i)) *
        (if P.InBox ω z' ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 z' ∧
          |((detZ s.1 z' / padProd s.2.1 : ℤ) : ℝ) / P.Y| < 5 then MA else 0) :=
        sum_le_sum fun St _ => sum_le_sum fun z' hz' => sum_le_sum fun tg htg =>
          hstep St z' hz' tg htg
    _ ≤ ∑ _St : Finset (Fin P.K), ∑ z' ∈ P.zSet, (2 + 2 * P.B) ^ P.K *
        (if P.InBox ω z' ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 z' ∧
          |((detZ s.1 z' / padProd s.2.1 : ℤ) : ℝ) / P.Y| < 5 then MA else 0) := by
        refine sum_le_sum fun St _ => sum_le_sum fun z' _ => ?_
        rw [← sum_mul]
        refine mul_le_mul_of_nonneg_right ?_ (by split_ifs <;> linarith)
        refine (sum_tg_gfac_le P hEP s.2.2 z').trans ?_
        have := memSize_le P s.2.2 hm
        have h0 : (0 : ℝ) ≤ 2 + 2 * P.memSize s.2.2 := by positivity
        exact pow_le_pow_left₀ h0 (by linarith) _
    _ = ∑ _St : Finset (Fin P.K), (2 + 2 * P.B) ^ P.K * ∑ z' ∈ P.zSet,
        (if P.InBox ω z' ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 z' ∧
          |((detZ s.1 z' / padProd s.2.1 : ℤ) : ℝ) / P.Y| < 5 then MA else 0) := by
        simp only [mul_sum]
    _ ≤ ∑ _St : Finset (Fin P.K), (2 + 2 * P.B) ^ P.K * (16 * (10 * P.Y + 1) * MA) := by
        refine sum_le_sum fun St _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact sum_window_le P ω hω hU s.1 hsrc.1 (zSet_prim P s.1 hz) _ hD1 MA hMA hY
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- **R2**: raw rows without promotions. -/
theorem rowSum_noProm_raw_le (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    (s : P.MState) (hs : s ∈ P.stSet) :
    rowSum P (clsNoProm P) (rawK P) ω s ≤ 2 ^ P.K * 16 * 2 ^ P.K := by
  classical
  obtain ⟨hz, _, _⟩ := stSet_parts P s hs
  have hD1 := padProd_pos P s hs
  set Tg := Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool))
  set g0 : Fin P.K → ℕ × Bool → ℝ := fun i q => if q.2 then 0 else P.nu i q.1
  have hg0 : ∀ tg ∈ Tg, 0 ≤ ∏ i, g0 i (tg i) := by
    intro tg htg
    simp only [Tg, Fintype.mem_piFinset, mem_product] at htg
    refine prod_nonneg fun i _ => ?_
    simp only [g0]; split_ifs
    · exact le_refl 0
    · exact hEP.nu_nonneg i _ (htg i).1
  rw [rowSum_eq]
  by_cases hsrc : P.InBox ω s.1 ∧ P.d₀ ≤ padProd s.2.1
  swap
  · refine le_trans (le_of_eq (sum_eq_zero fun St _ => sum_eq_zero fun z' _ =>
      sum_eq_zero fun tg _ => ?_)) (by positivity)
    unfold coeffP coeffK
    split_ifs with h1 h2
    · exact absurd ⟨h2.1.2.2.2.2.2.1, h2.1.2.2.1⟩ hsrc
    · simp
    · simp
  have hstep : ∀ St, ∀ z' ∈ P.zSet, ∀ tg ∈ Tg,
      ‖coeffP P (clsNoProm P) (rawK P) ω s (St, z', tg)‖ ≤
      (∏ i, g0 i (tg i)) * (if P.InBox ω z' ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 z' then
        ‖rawK P (detZ s.1 z' / padProd s.2.1) (∏ i, (tg i).1) (lastProd s.2.1)
          (padProd s.2.1)‖ else 0) := by
    intro St z' hz' tg htg
    have hc := ecChoice_mem P St z' hz' tg htg
    have hRHS : 0 ≤ (∏ i, g0 i (tg i)) * (if P.InBox ω z' ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 z' then
        ‖rawK P (detZ s.1 z' / padProd s.2.1) (∏ i, (tg i).1) (lastProd s.2.1)
          (padProd s.2.1)‖ else 0) :=
      mul_nonneg (hg0 tg htg) (by split_ifs <;> simp)
    unfold coeffP clsNoProm
    by_cases hI : promSet P (St, z', tg) = ∅
    · rw [if_pos hI]
      refine (norm_coeffK_le P hEP _ ω s _ hc).trans ?_
      have hfl : ∀ i, (tg i).2 = false := by
        intro i
        by_contra h
        have : i ∈ promSet P (St, z', tg) := by simp [promSet]; simpa using h
        rw [hI] at this; exact absurd this (notMem_empty i)
      have heq : ∏ i, gfac P s.2.2 z' i (tg i) = ∏ i, g0 i (tg i) := by
        refine prod_congr rfl fun i _ => ?_
        simp only [gfac, g0, hfl i]; rfl
      by_cases hE : ECond P ω s (St, z', tg)
      · rw [if_pos hE, heq, if_pos ⟨hE.1.2.2.2.2.2.2.1, hE.1.2.2.2.2.1⟩]
      · rw [if_neg hE]; exact hRHS
    · rw [if_neg hI, norm_zero]; exact hRHS
  calc ∑ St : Finset (Fin P.K), ∑ z' ∈ P.zSet, ∑ tg ∈ Tg,
        ‖coeffP P (clsNoProm P) (rawK P) ω s (St, z', tg)‖ ≤
      ∑ _St : Finset (Fin P.K), ∑ tg ∈ Tg, ∑ z' ∈ P.zSet, (∏ i, g0 i (tg i)) *
        (if P.InBox ω z' ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 z' then
          ‖rawK P (detZ s.1 z' / padProd s.2.1) (∏ i, (tg i).1) (lastProd s.2.1)
            (padProd s.2.1)‖ else 0) := by
        refine sum_le_sum fun St _ => ?_
        rw [sum_comm]
        exact sum_le_sum fun tg htg => sum_le_sum fun z' hz' => hstep St z' hz' tg htg
    _ ≤ ∑ _St : Finset (Fin P.K), ∑ tg ∈ Tg, (∏ i, g0 i (tg i)) * 16 := by
        refine sum_le_sum fun St _ => sum_le_sum fun tg htg => ?_
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_rawK_le P ω hω hU s.1 hsrc.1 (zSet_prim P s.1 hz)
          _ hsrc.2 hD1 _ _) (hg0 tg htg)
    _ = ∑ _St : Finset (Fin P.K), 16 * ∏ i, ∑ q ∈ P.grp i ×ˢ (univ : Finset Bool), g0 i q := by
        refine sum_congr rfl fun St _ => ?_
        rw [← sum_mul, prod_univ_sum, mul_comm]
    _ ≤ ∑ _St : Finset (Fin P.K), 16 * 2 ^ P.K := by
        refine sum_le_sum fun St _ => mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc ∏ i, ∑ q ∈ P.grp i ×ˢ (univ : Finset Bool), g0 i q ≤ ∏ _i : Fin P.K, (2 : ℝ) := by
              refine prod_le_prod (fun i _ => sum_nonneg fun q hq => ?_) fun i _ => ?_
              · simp only [g0]; split_ifs
                · exact le_refl 0
                · exact hEP.nu_nonneg i _ (mem_product.1 hq).1
              · rw [sum_product]
                calc ∑ p ∈ P.grp i, ∑ fl : Bool, g0 i (p, fl) = ∑ p ∈ P.grp i, P.nu i p := by
                      refine sum_congr rfl fun p _ => ?_
                      rw [Fintype.sum_bool]; simp [g0]
                  _ ≤ 2 := hEP.sum_nu_le i
          _ = 2 ^ P.K := by simp
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: the clean block kernel, factored

At fixed pads `pd` (product `D`) and memory `m`, the clean block kernel is
`α(z,lab) κ(z,∏lab; z',∏nw) β(z',nw) − kviol`, where
* `κ = kappaC` is `[T1(z)] [z, z' in the box] [D ∣ det] H(det/D, a, b)` with the minor kernel `H`
  (test (i) `T1` at the source with the pad product, [21] (4.26));
* `α, β` are diagonal with `|α|, |β| ≤ √(4^K/Y)` (`∏ ν(lab) ≤ 4^K/∏ lab`, `∏ lab > Y`);
* `kviol` is the part where a fresh label repeats the source's last label in its group (the
  cross-edge ban), bounded by the weighted Schur test with `sup ν ≤ 4/p_min`.
-/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- Test (i) at `z` for the omission product `D` ([21] §3.2 (i) with the last label omitted). -/
def T1 (D : ℕ) (ω : ℝ × ℝ × ℝ) (z : ℤ × ℤ) : Prop :=
  ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ P.Y ^ (0.2 : ℝ) →
    P.Y ^ (-0.7 : ℝ) < |l * (D * ratioAt ω z) - round (l * (D * ratioAt ω z))|

lemma omitProd_last (ℓ : P.Lst) : omitProd ℓ (fun _ => Fin.last P.J) = padProd ℓ := by
  unfold omitProd padProd
  refine prod_congr rfl fun i _ => ?_
  have : Finset.univ.erase (Fin.last P.J) = Finset.univ.map Fin.castSuccEmb := by
    ext j; simp [Fin.exists_castSucc_eq]
  rw [this, Finset.prod_map]; rfl

lemma T1_of_good (ω : ℝ × ℝ × ℝ) (z : ℤ × ℤ) (ℓ : P.Lst) (h : P.GoodAt ω z ℓ) :
    T1 P (padProd ℓ) ω z := by
  intro l hl1 hl2
  have := h.1 (fun _ => Fin.last P.J) l hl1 hl2
  rw [omitProd_last] at this
  unfold circNorm at this
  convert this using 2 <;> push_cast <;> ring_nf

/-- The pad product of a pad tuple. -/
def padD (pd : Fin P.K → Fin P.J → ℕ) : ℕ := ∏ i, ∏ k, pd i k

lemma padProd_mkList_eq (pd : Fin P.K → Fin P.J → ℕ) (lab : Fin P.K → ℕ) :
    padProd (mkList P pd lab) = padD P pd := by
  unfold padProd padD; simp only [mkList_castSucc]

open Classical in
/-- The core clean kernel on `(position, product)` pairs. -/
noncomputable def kappaC (ω : ℝ × ℝ × ℝ) (pd : Fin P.K → Fin P.J → ℕ) (p q : (ℤ × ℤ) × ℤ) : ℂ :=
  if (∀ i, Function.Injective (pd i)) ∧ P.d₀ ≤ padD P pd ∧ padD P pd < 2 * P.d₀ ∧
      T1 P (padD P pd) ω p.1 ∧ P.InBox ω p.1 ∧ P.InBox ω q.1 ∧
      ((padD P pd : ℕ) : ℤ) ∣ detZ p.1 q.1 then
    minorKernel P.x P.A₀ P.Y (detZ p.1 q.1 / padD P pd) q.2 p.2 else 0

lemma edgeMult_eq_minor (j : ℕ) (t : ℤ) (a b D : ℕ) :
    P.edgeMult j t a b D = ((((P.d₀ : ℝ) / D) * dyadicBump ((b : ℝ) / P.Y) *
      dyadicBump ((a : ℝ) / P.Y) : ℝ) : ℂ) * minorKernel P.x P.A₀ P.Y t a b := by
  unfold MemParams.edgeMult
  split_ifs
  · rfl
  · congr 1
    rw [L102D.minorKernel_eq, L102D.minorKernel_eq, map_sub, map_mul, Complex.conj_ofReal,
      majorKernel_neg, Complex.conj_conj]
    have h : ((-t : ℤ) : ℝ) / P.Y = -((t : ℝ) / P.Y) := by push_cast; ring
    rw [h, arcCutoff_neg]
    congr 1
    by_cases h' : t - (b : ℤ) + (a : ℤ) = 0
    · rw [if_pos h', if_pos (by omega), map_one]
    · rw [if_neg h', if_neg (by omega), map_zero]

/-! ## The factorization -/

open Classical in
/-- The source multiplier `α`. -/
noncomputable def alphaC (ω : ℝ × ℝ × ℝ) (pd : Fin P.K → Fin P.J → ℕ) (m : P.Mem)
    (p : (ℤ × ℤ) × (Fin P.K → ℕ)) : ℂ :=
  if (∀ i, Function.Injective (mkList P pd p.2 i)) ∧ P.d₀ ≤ padD P pd ∧ padD P pd < 2 * P.d₀ ∧
      P.InBox ω p.1 ∧ P.GoodAt ω p.1 (mkList P pd p.2) then
    ((√(∏ i, P.nu i (p.2 i)) * memRho ^ P.hitCount p.1 m * ((P.d₀ : ℝ) / padD P pd) *
      dyadicBump (((∏ i, p.2 i : ℕ) : ℝ) / P.Y) : ℝ) : ℂ) else 0

open Classical in
/-- The target multiplier `β`. -/
noncomputable def betaC (ω : ℝ × ℝ × ℝ) (pd : Fin P.K → Fin P.J → ℕ) (m : P.Mem)
    (q : (ℤ × ℤ) × (Fin P.K → ℕ)) : ℂ :=
  if (∀ i, q.2 i ∉ Set.range (pd i)) ∧ P.InBox ω q.1 ∧ P.GoodAt ω q.1 (mkList P pd q.2) then
    ((√(∏ i, P.nu i (q.2 i)) * memRho ^ P.hitCount q.1 m *
      dyadicBump (((∏ i, q.2 i : ℕ) : ℝ) / P.Y) : ℝ) : ℂ) else 0

/-- The product map `(z, lab) ↦ (z, ∏ lab)`. -/
def prodMap (p : (ℤ × ℤ) × (Fin P.K → ℕ)) : (ℤ × ℤ) × ℤ := (p.1, ((∏ i, p.2 i : ℕ) : ℤ))

open Classical in
/-- The ban-violating part. -/
noncomputable def kviol (ω : ℝ × ℝ × ℝ) (j : ℕ) (pd : Fin P.K → Fin P.J → ℕ) (m : P.Mem)
    (p q : (ℤ × ℤ) × (Fin P.K → ℕ)) : ℂ :=
  if ((∀ i, Function.Injective (mkList P pd p.2 i)) ∧ (∀ i, q.2 i ∉ Set.range (pd i)) ∧
      P.d₀ ≤ padD P pd ∧ padD P pd < 2 * P.d₀ ∧ ((padD P pd : ℕ) : ℤ) ∣ detZ p.1 q.1 ∧
      P.InBox ω p.1 ∧ P.InBox ω q.1 ∧ P.GoodAt ω p.1 (mkList P pd p.2) ∧
      P.GoodAt ω q.1 (mkList P pd q.2)) ∧ ¬ ∀ i, q.2 i ≠ p.2 i then
    ((√((∏ i, P.nu i (p.2 i)) * ∏ i, P.nu i (q.2 i)) * memRho ^ P.hitCount p.1 m *
      memRho ^ P.hitCount q.1 m : ℝ) : ℂ) *
      P.edgeMult j (detZ p.1 q.1 / padD P pd) (∏ i, q.2 i) (∏ i, p.2 i) (padD P pd) else 0

lemma ban_iff (pd : Fin P.K → Fin P.J → ℕ) (lab nw : Fin P.K → ℕ) :
    (∀ i, nw i ∉ Set.range (mkList P pd lab i)) ↔
      (∀ i, nw i ∉ Set.range (pd i)) ∧ ∀ i, nw i ≠ lab i := by
  constructor
  · intro h
    refine ⟨fun i ⟨k, hk⟩ => h i ⟨k.castSucc, by rw [mkList_castSucc]; exact hk⟩,
      fun i hi => h i ⟨Fin.last P.J, by rw [mkList_last]; exact hi.symm⟩⟩
  · rintro ⟨h1, h2⟩ i ⟨k, hk⟩
    induction k using Fin.lastCases with
    | last => rw [mkList_last] at hk; exact h2 i hk.symm
    | cast k => rw [mkList_castSucc] at hk; exact h1 i ⟨k, hk⟩

lemma ite_factor {cα cβ cκ cA W cE cV : Prop} [Decidable cα] [Decidable cβ] [Decidable cκ]
    [Decidable cE] [Decidable cV] (a k b Z : ℂ) (hZ : Z = a * k * b) (h1 : cE ↔ cA ∧ W)
    (h2 : cV ↔ cA ∧ ¬ W) (h3 : cA ↔ cα ∧ cβ ∧ cκ) :
    Z * (if cE then 1 else 0) =
      (if cα then a else 0) * (if cκ then k else 0) * (if cβ then b else 0) -
        (if cV then Z else 0) := by
  by_cases hα : cα <;> by_cases hβ : cβ <;> by_cases hκ : cκ <;> by_cases hW : W <;>
    simp_all

lemma kblock_eq (ω : ℝ × ℝ × ℝ) (j : ℕ) (pd : Fin P.K → Fin P.J → ℕ) (m : P.Mem)
    (p q : (ℤ × ℤ) × (Fin P.K → ℕ)) (hnu : 0 ≤ ∏ i, P.nu i (p.2 i)) :
    kblock P ω j pd m p q = alphaC P ω pd m p * kappaC P ω pd (prodMap P p)
      (prodMap P q) * betaC P ω pd m q - kviol P ω j pd m p q := by
  classical
  have hT : P.GoodAt ω p.1 (mkList P pd p.2) → T1 P (padD P pd) ω p.1 := fun h => by
    have := T1_of_good P ω p.1 _ h
    rwa [padProd_mkList_eq] at this
  unfold kblock alphaC betaC kappaC kviol prodMap MemParams.EdgeOK
  simp only [padProd_mkList_eq, newList_mkList, ban_iff]
  rw [edgeMult_eq_minor, Real.sqrt_mul hnu]
  refine ite_factor _ _ _ _ ?_ ?_ Iff.rfl ?_
  · push_cast; ring
  · tauto
  · constructor
    · intro h
      have hpinj : ∀ i, Function.Injective (pd i) := fun i k k' hk => by
        have := h.1 i (a₁ := k.castSucc) (a₂ := k'.castSucc)
          (by rw [mkList_castSucc, mkList_castSucc]; exact hk)
        exact Fin.castSucc_injective _ this
      exact ⟨⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩,
        ⟨h.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩,
        ⟨hpinj, h.2.2.1, h.2.2.2.1, hT h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
          h.2.2.2.2.1⟩⟩
    · rintro ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8⟩, ⟨_, _, _, _, _, _, h9⟩⟩
      exact ⟨h1, h6, h2, h3, h9, h4, h7, h5, h8⟩

/-! ## Bounds for the multipliers and the violation part -/

lemma memRho_pow_le (n : ℕ) : memRho ^ n ≤ 1 := by
  unfold memRho; exact pow_le_one₀ (by norm_num) (by norm_num)

lemma sqrt_nu_eta_le (hEP : EP P) (lab : Fin P.K → ℕ) (hlab : lab ∈ labCands P)
    (hY : 0 < P.Y) :
    √(∏ i, P.nu i (lab i)) * |dyadicBump (((∏ i, lab i : ℕ) : ℝ) / P.Y)| ≤ √(4 ^ P.K / P.Y) := by
  by_cases hη : dyadicBump (((∏ i, lab i : ℕ) : ℝ) / P.Y) = 0
  · rw [hη, abs_zero, mul_zero]; positivity
  · have h1 := (L102D.dyadicBump_ne_zero hη).1
    rw [lt_div_iff₀ hY, one_mul] at h1
    have hb : (0 : ℝ) < ((∏ i, lab i : ℕ) : ℝ) := lt_trans hY h1
    have h2 := hEP.prod_nu_le lab hlab
    have h3 : 4 ^ P.K / ((∏ i, lab i : ℕ) : ℝ) ≤ 4 ^ P.K / P.Y :=
      div_le_div_of_nonneg_left (by positivity) hY h1.le
    have h4 := abs_dyadicBump_le_one' (((∏ i, lab i : ℕ) : ℝ) / P.Y)
    calc √(∏ i, P.nu i (lab i)) * |dyadicBump (((∏ i, lab i : ℕ) : ℝ) / P.Y)| ≤
        √(4 ^ P.K / P.Y) * 1 := mul_le_mul (Real.sqrt_le_sqrt (h2.trans h3)) h4 (abs_nonneg _)
          (Real.sqrt_nonneg _)
      _ = _ := mul_one _

lemma padD_pos (pd : Fin P.K → Fin P.J → ℕ) (hpd : pd ∈ padCands P) : 0 < padD P pd := by
  simp only [padCands, Fintype.mem_piFinset] at hpd
  unfold padD
  exact prod_pos fun i _ => prod_pos fun k _ => (grp_prime (hpd i k)).pos

lemma norm_alphaC_le (hEP : EP P) (ω : ℝ × ℝ × ℝ) (pd : Fin P.K → Fin P.J → ℕ)
    (hpd : pd ∈ padCands P) (m : P.Mem)
    (p : (ℤ × ℤ) × (Fin P.K → ℕ)) (hp : p ∈ P.zSet ×ˢ labCands P) (hY : 0 < P.Y) :
    ‖alphaC P ω pd m p‖ ≤ √(4 ^ P.K / P.Y) := by
  rw [mem_product] at hp
  have hD0 : (0 : ℝ) < padD P pd := by exact_mod_cast padD_pos P pd hpd
  unfold alphaC
  split_ifs with h
  · have hD : (P.d₀ : ℝ) / padD P pd ≤ 1 := by
      rw [div_le_one hD0]; exact_mod_cast h.2.1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (pow_nonneg memRho_nonneg _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (P.d₀ : ℝ) / padD P pd)]
    have h1 := sqrt_nu_eta_le P hEP p.2 hp.2 hY
    have h2 := memRho_pow_le (P.hitCount p.1 m)
    have h5 : 0 ≤ memRho ^ P.hitCount p.1 m := pow_nonneg memRho_nonneg _
    have h6 : (0 : ℝ) ≤ (P.d₀ : ℝ) / padD P pd := by positivity
    calc √(∏ i, P.nu i (p.2 i)) * memRho ^ P.hitCount p.1 m * ((P.d₀ : ℝ) / padD P pd) *
          |dyadicBump (((∏ i, p.2 i : ℕ) : ℝ) / P.Y)| =
        (√(∏ i, P.nu i (p.2 i)) * |dyadicBump (((∏ i, p.2 i : ℕ) : ℝ) / P.Y)|) *
          (memRho ^ P.hitCount p.1 m * ((P.d₀ : ℝ) / padD P pd)) := by ring
      _ ≤ √(4 ^ P.K / P.Y) * (1 * 1) := mul_le_mul h1 (mul_le_mul h2 hD h6 zero_le_one)
          (mul_nonneg h5 h6) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · rw [norm_zero]; positivity

lemma norm_betaC_le (hEP : EP P) (ω : ℝ × ℝ × ℝ) (pd : Fin P.K → Fin P.J → ℕ) (m : P.Mem)
    (q : (ℤ × ℤ) × (Fin P.K → ℕ)) (hq : q ∈ P.zSet ×ˢ labCands P) (hY : 0 < P.Y) :
    ‖betaC P ω pd m q‖ ≤ √(4 ^ P.K / P.Y) := by
  rw [mem_product] at hq
  unfold betaC
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (pow_nonneg memRho_nonneg _)]
    have h1 := sqrt_nu_eta_le P hEP q.2 hq.2 hY
    have h2 := memRho_pow_le (P.hitCount q.1 m)
    have h5 : 0 ≤ memRho ^ P.hitCount q.1 m := pow_nonneg memRho_nonneg _
    calc √(∏ i, P.nu i (q.2 i)) * memRho ^ P.hitCount q.1 m *
          |dyadicBump (((∏ i, q.2 i : ℕ) : ℝ) / P.Y)| =
        (√(∏ i, P.nu i (q.2 i)) * |dyadicBump (((∏ i, q.2 i : ℕ) : ℝ) / P.Y)|) *
          memRho ^ P.hitCount q.1 m := by ring
      _ ≤ √(4 ^ P.K / P.Y) * 1 := mul_le_mul h1 h2 h5 (Real.sqrt_nonneg _)
      _ = _ := by ring
  · rw [norm_zero]; positivity

/-! ## The violation part -/

lemma norm_edgeMult_le (j : ℕ) (t : ℤ) (a b D : ℕ) :
    ‖P.edgeMult j t a b D‖ ≤ ‖rawK P t a b D‖ + ‖majK P j t a b D‖ := by
  rw [edgeMult_eq_sub]; exact norm_sub_le _ _

/-- The `ν`-mass of last-label tuples with a prescribed label in group `i`. -/
lemma sum_nu_fix_le (hEP : EP P) (pmin : ℝ) (hpmin0 : 0 < pmin)
    (hpmin : ∀ i, ∀ p ∈ P.grp i, pmin ≤ p) (i : Fin P.K) (c : ℕ) :
    ∑ lab ∈ labCands P, (if lab i = c then ∏ k, P.nu k (lab k) else 0) ≤ 4 / pmin * 2 ^ P.K := by
  classical
  set f : Fin P.K → ℕ → ℝ := fun k p => if k = i then (if p = c then P.nu k p else 0) else P.nu k p
  have h1 : ∀ lab : Fin P.K → ℕ, (if lab i = c then ∏ k, P.nu k (lab k) else 0) =
      ∏ k, f k (lab k) := by
    intro lab
    by_cases hc : lab i = c
    · rw [if_pos hc]; refine prod_congr rfl fun k _ => ?_
      simp only [f]; split_ifs with hk <;> simp_all
    · rw [if_neg hc]; symm
      exact prod_eq_zero (mem_univ i) (by simp [f, hc])
  rw [sum_congr rfl fun lab _ => h1 lab]
  unfold labCands
  rw [← prod_univ_sum]
  set g : Fin P.K → ℝ := fun k => if k = i then 4 / pmin else 2
  have h2 : ∀ k ∈ univ, ∑ p ∈ P.grp k, f k p ≤ g k := by
    intro k _
    simp only [f, g]
    split_ifs with hk
    · subst hk
      rw [sum_ite_eq']
      split_ifs with hcm
      · exact (hEP.nu_le k c hcm).trans (div_le_div_of_nonneg_left (by norm_num) hpmin0
          (hpmin k c hcm))
      · positivity
    · exact hEP.sum_nu_le k
  have h3 : ∀ k ∈ univ, 0 ≤ ∑ p ∈ P.grp k, f k p := by
    intro k _
    refine sum_nonneg fun p hp => ?_
    simp only [f]; split_ifs <;> first | exact hEP.nu_nonneg k p hp | exact le_refl 0
  calc ∏ k, ∑ p ∈ P.grp k, f k p ≤ ∏ k, g k := prod_le_prod h3 h2
    _ = g i * ∏ k ∈ univ.erase i, g k := (mul_prod_erase univ g (mem_univ i)).symm
    _ = 4 / pmin * 2 ^ (P.K - 1) := by
        simp only [g, if_pos rfl]
        congr 1
        rw [prod_congr rfl fun k hk => if_neg (ne_of_mem_erase hk), prod_const, card_erase_of_mem
          (mem_univ i), card_univ, Fintype.card_fin]
    _ ≤ 4 / pmin * 2 ^ P.K := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)

lemma sum_nu_exists_le (hEP : EP P) (pmin : ℝ) (hpmin0 : 0 < pmin)
    (hpmin : ∀ i, ∀ p ∈ P.grp i, pmin ≤ p) (c : Fin P.K → ℕ) :
    ∑ lab ∈ labCands P, (if ¬ ∀ i, lab i ≠ c i then ∏ k, P.nu k (lab k) else 0) ≤
      P.K * (4 / pmin * 2 ^ P.K) := by
  classical
  calc ∑ lab ∈ labCands P, (if ¬ ∀ i, lab i ≠ c i then ∏ k, P.nu k (lab k) else 0) ≤
      ∑ lab ∈ labCands P, ∑ i, (if lab i = c i then ∏ k, P.nu k (lab k) else 0) := by
        refine sum_le_sum fun lab hlab => ?_
        have hn := hEP.prod_nu_nonneg lab hlab
        by_cases h : ∀ i, lab i ≠ c i
        · rw [if_neg (not_not.2 h)]
          exact sum_nonneg fun i _ => by split_ifs <;> linarith
        · rw [if_pos h]
          obtain ⟨i, hi⟩ := not_forall.1 h
          rw [not_not] at hi
          calc ∏ k, P.nu k (lab k) = (if lab i = c i then ∏ k, P.nu k (lab k) else 0) := by
                rw [if_pos hi]
            _ ≤ _ := single_le_sum (f := fun i => if lab i = c i then ∏ k, P.nu k (lab k) else 0)
                (fun i _ => by split_ifs <;> linarith) (mem_univ i)
    _ = ∑ i, ∑ lab ∈ labCands P, (if lab i = c i then ∏ k, P.nu k (lab k) else 0) := sum_comm
    _ ≤ ∑ _i : Fin P.K, 4 / pmin * 2 ^ P.K :=
        sum_le_sum fun i _ => sum_nu_fix_le P hEP pmin hpmin0 hpmin i (c i)
    _ = _ := by simp

/-- **The ban-violating part is negligible** (weighted Schur, `sup ν ≤ 4/p_min`). -/
lemma kviol_bilBound (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (j : ℕ)
    (pd : Fin P.K → Fin P.J → ℕ) (hpd : pd ∈ padCands P) (m : P.Mem) (pmin : ℝ)
    (hpmin0 : 0 < pmin) (hpmin : ∀ i, ∀ p ∈ P.grp i, pmin ≤ p) (hL : 1 ≤ log P.x)
    (hA₀ : 0 ≤ P.A₀) (hY : 0 < P.Y) :
    BilBound (P.zSet ×ˢ labCands P) (P.zSet ×ˢ labCands P) (kviol P ω j pd m)
      (√(P.K * (4 / pmin * 2 ^ P.K) * Ccr P) * √(P.K * (4 / pmin * 2 ^ P.K) * Ccr P)) := by
  classical
  set S := P.zSet ×ˢ labCands P
  set D := padD P pd
  have hD1 : 1 ≤ D := padD_pos P pd hpd
  have hCcr : 0 ≤ Ccr P := by unfold Ccr; positivity
  set Rv := P.K * (4 / pmin * 2 ^ P.K) * Ccr P
  have hRv : 0 ≤ Rv := by positivity
  set X : (ℤ × ℤ) × (Fin P.K → ℕ) → (ℤ × ℤ) × (Fin P.K → ℕ) → ℂ := fun p q =>
    if ((∀ i, Function.Injective (mkList P pd p.2 i)) ∧ (∀ i, q.2 i ∉ Set.range (pd i)) ∧
      P.d₀ ≤ D ∧ D < 2 * P.d₀ ∧ ((D : ℕ) : ℤ) ∣ detZ p.1 q.1 ∧
      P.InBox ω p.1 ∧ P.InBox ω q.1 ∧ P.GoodAt ω p.1 (mkList P pd p.2) ∧
      P.GoodAt ω q.1 (mkList P pd q.2)) ∧ ¬ ∀ i, q.2 i ≠ p.2 i then
    ((memRho ^ P.hitCount p.1 m * memRho ^ P.hitCount q.1 m : ℝ) : ℂ) *
      P.edgeMult j (detZ p.1 q.1 / D) (∏ i, q.2 i) (∏ i, p.2 i) D else 0
  -- the pointwise bound on `X`
  have hXle : ∀ p q, ‖X p q‖ ≤ (if ¬ ∀ i, q.2 i ≠ p.2 i then 1 else 0) *
      (if P.d₀ ≤ D ∧ P.InBox ω p.1 ∧ P.InBox ω q.1 ∧ (D : ℤ) ∣ detZ p.1 q.1 then
        ‖rawK P (detZ p.1 q.1 / D) (∏ i, q.2 i) (∏ i, p.2 i) D‖ +
          ‖majK P j (detZ p.1 q.1 / D) (∏ i, q.2 i) (∏ i, p.2 i) D‖ else 0) := by
    intro p q
    simp only [X]
    by_cases hc : ((∀ i, Function.Injective (mkList P pd p.2 i)) ∧
        (∀ i, q.2 i ∉ Set.range (pd i)) ∧
        P.d₀ ≤ D ∧ D < 2 * P.d₀ ∧ ((D : ℕ) : ℤ) ∣ detZ p.1 q.1 ∧
        P.InBox ω p.1 ∧ P.InBox ω q.1 ∧ P.GoodAt ω p.1 (mkList P pd p.2) ∧
        P.GoodAt ω q.1 (mkList P pd q.2)) ∧ ¬ ∀ i, q.2 i ≠ p.2 i
    · rw [if_pos hc, if_pos hc.2, if_pos ⟨hc.1.2.2.1, hc.1.2.2.2.2.2.1, hc.1.2.2.2.2.2.2.1,
        hc.1.2.2.2.2.1⟩, one_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg (pow_nonneg memRho_nonneg _) (pow_nonneg memRho_nonneg _))]
      calc memRho ^ P.hitCount p.1 m * memRho ^ P.hitCount q.1 m *
            ‖P.edgeMult j (detZ p.1 q.1 / D) (∏ i, q.2 i) (∏ i, p.2 i) D‖ ≤
          1 * 1 * (‖rawK P (detZ p.1 q.1 / D) (∏ i, q.2 i) (∏ i, p.2 i) D‖ +
            ‖majK P j (detZ p.1 q.1 / D) (∏ i, q.2 i) (∏ i, p.2 i) D‖) := by
            gcongr
            · exact pow_nonneg memRho_nonneg _
            · exact memRho_pow_le _
            · exact memRho_pow_le _
            · exact norm_edgeMult_le P j _ _ _ _
        _ = _ := by ring
    · rw [if_neg hc, norm_zero]
      refine mul_nonneg (by split_ifs <;> norm_num) ?_
      split_ifs
      · positivity
      · exact le_refl 0
  have hzp : ∀ z ∈ P.zSet, Int.gcd z.1 z.2 = 1 := by
    intro z hz; exact zSet_gcd hz
  refine bilBound_wschur S S (kviol P ω j pd m) (fun p => ∏ i, P.nu i (p.2 i))
    (fun q => ∏ i, P.nu i (q.2 i)) (fun p hp => hEP.prod_nu_nonneg p.2 (mem_product.1 hp).2)
    (fun q hq => hEP.prod_nu_nonneg q.2 (mem_product.1 hq).2) X ?_ Rv Rv hRv hRv ?_ ?_
  · intro p hp q hq
    unfold kviol
    simp only [X]
    split_ifs with hc
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by have := memRho_nonneg; positivity), Real.norm_of_nonneg
          (mul_nonneg (pow_nonneg memRho_nonneg _) (pow_nonneg memRho_nonneg _))]
      apply le_of_eq; ring
    · simp
  · -- rows
    intro p hp
    rw [mem_product] at hp
    by_cases hz : P.d₀ ≤ D ∧ P.InBox ω p.1
    · calc ∑ q ∈ S, ‖X p q‖ * ∏ i, P.nu i (q.2 i) ≤
          ∑ q ∈ S, (if ¬ ∀ i, q.2 i ≠ p.2 i then ∏ i, P.nu i (q.2 i) else 0) *
            (if P.InBox ω q.1 ∧ (D : ℤ) ∣ detZ p.1 q.1 then
              ‖rawK P (detZ p.1 q.1 / D) (∏ i, q.2 i) (∏ i, p.2 i) D‖ +
                ‖majK P j (detZ p.1 q.1 / D) (∏ i, q.2 i) (∏ i, p.2 i) D‖ else 0) := by
            refine sum_le_sum fun q hq => ?_
            have hn := hEP.prod_nu_nonneg q.2 (mem_product.1 hq).2
            refine (mul_le_mul_of_nonneg_right (hXle p q) hn).trans (le_of_eq ?_)
            by_cases h1 : ¬ ∀ i, q.2 i ≠ p.2 i
            · rw [if_pos h1, if_pos h1]
              by_cases h2 : P.InBox ω q.1 ∧ (D : ℤ) ∣ detZ p.1 q.1
              · rw [if_pos ⟨hz.1, hz.2, h2.1, h2.2⟩, if_pos h2]; ring
              · rw [if_neg (fun h => h2 ⟨h.2.2.1, h.2.2.2⟩), if_neg h2]; ring
            · rw [if_neg h1, if_neg h1]; ring
        _ = ∑ nw ∈ labCands P, (if ¬ ∀ i, nw i ≠ p.2 i then ∏ i, P.nu i (nw i) else 0) *
            ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ p.1 z' then
              ‖rawK P (detZ p.1 z' / D) (∏ i, nw i) (∏ i, p.2 i) D‖ +
                ‖majK P j (detZ p.1 z' / D) (∏ i, nw i) (∏ i, p.2 i) D‖ else 0) := by
            rw [sum_product, sum_comm]
            exact sum_congr rfl fun nw _ => by rw [mul_sum]
        _ ≤ ∑ nw ∈ labCands P, (if ¬ ∀ i, nw i ≠ p.2 i then ∏ i, P.nu i (nw i) else 0) *
            Ccr P := by
            refine sum_le_sum fun nw hnw => mul_le_mul_of_nonneg_left
              (crude_tgt P ω hω hU p.1 hz.2 (hzp p.1 hp.1) D hz.1 hD1 j _ _ hL hA₀ hY) ?_
            split_ifs
            · exact le_refl _
            · exact hEP.prod_nu_nonneg nw hnw
        _ = (∑ nw ∈ labCands P, (if ¬ ∀ i, nw i ≠ p.2 i then ∏ i, P.nu i (nw i) else 0)) *
            Ccr P := (sum_mul _ _ _).symm
        _ ≤ (P.K * (4 / pmin * 2 ^ P.K)) * Ccr P :=
            mul_le_mul_of_nonneg_right (sum_nu_exists_le P hEP pmin hpmin0 hpmin p.2) hCcr
    · refine le_trans (le_of_eq ?_) hRv
      refine sum_eq_zero fun q _ => ?_
      have : X p q = 0 := by
        simp only [X]
        rw [if_neg]
        intro h
        exact hz ⟨h.1.2.2.1, h.1.2.2.2.2.2.1⟩
      rw [this, norm_zero, zero_mul]
  · -- columns
    intro q hq
    rw [mem_product] at hq
    by_cases hz : P.d₀ ≤ D ∧ P.InBox ω q.1
    · calc ∑ p ∈ S, ‖X p q‖ * ∏ i, P.nu i (p.2 i) ≤
          ∑ p ∈ S, (if ¬ ∀ i, p.2 i ≠ q.2 i then ∏ i, P.nu i (p.2 i) else 0) *
            (if P.InBox ω p.1 ∧ (D : ℤ) ∣ detZ p.1 q.1 then
              ‖rawK P (detZ p.1 q.1 / D) (∏ i, q.2 i) (∏ i, p.2 i) D‖ +
                ‖majK P j (detZ p.1 q.1 / D) (∏ i, q.2 i) (∏ i, p.2 i) D‖ else 0) := by
            refine sum_le_sum fun p hp => ?_
            have hn := hEP.prod_nu_nonneg p.2 (mem_product.1 hp).2
            refine (mul_le_mul_of_nonneg_right (hXle p q) hn).trans (le_of_eq ?_)
            have hiff : (¬ ∀ i, q.2 i ≠ p.2 i) ↔ (¬ ∀ i, p.2 i ≠ q.2 i) := by
              constructor <;> intro h h' <;> exact h fun i hi => h' i hi.symm
            by_cases h1 : ¬ ∀ i, q.2 i ≠ p.2 i
            · rw [if_pos h1, if_pos (hiff.1 h1)]
              by_cases h2 : P.InBox ω p.1 ∧ (D : ℤ) ∣ detZ p.1 q.1
              · rw [if_pos ⟨hz.1, h2.1, hz.2, h2.2⟩, if_pos h2]; ring
              · rw [if_neg (fun h => h2 ⟨h.2.1, h.2.2.2⟩), if_neg h2]; ring
            · rw [if_neg h1, if_neg (fun h => h1 (hiff.2 h))]; ring
        _ = ∑ lab ∈ labCands P, (if ¬ ∀ i, lab i ≠ q.2 i then ∏ i, P.nu i (lab i) else 0) *
            ∑ z ∈ P.zSet, (if P.InBox ω z ∧ (D : ℤ) ∣ detZ z q.1 then
              ‖rawK P (detZ z q.1 / D) (∏ i, q.2 i) (∏ i, lab i) D‖ +
                ‖majK P j (detZ z q.1 / D) (∏ i, q.2 i) (∏ i, lab i) D‖ else 0) := by
            rw [sum_product, sum_comm]
            exact sum_congr rfl fun lab _ => by rw [mul_sum]
        _ ≤ ∑ lab ∈ labCands P, (if ¬ ∀ i, lab i ≠ q.2 i then ∏ i, P.nu i (lab i) else 0) *
            Ccr P := by
            refine sum_le_sum fun lab hlab => mul_le_mul_of_nonneg_left
              (crude_src P ω hω hU q.1 hz.2 (hzp q.1 hq.1) D hz.1 hD1 j _ _ hL hA₀ hY) ?_
            split_ifs
            · exact le_refl _
            · exact hEP.prod_nu_nonneg lab hlab
        _ = (∑ lab ∈ labCands P, (if ¬ ∀ i, lab i ≠ q.2 i then ∏ i, P.nu i (lab i) else 0)) *
            Ccr P := (sum_mul _ _ _).symm
        _ ≤ (P.K * (4 / pmin * 2 ^ P.K)) * Ccr P :=
            mul_le_mul_of_nonneg_right (sum_nu_exists_le P hEP pmin hpmin0 hpmin q.2) hCcr
    · refine le_trans (le_of_eq ?_) hRv
      refine sum_eq_zero fun p _ => ?_
      have : X p q = 0 := by
        simp only [X]
        rw [if_neg]
        intro h
        exact hz ⟨h.1.2.2.1, h.1.2.2.2.2.2.2.1⟩
      rw [this, norm_zero, zero_mul]

/-- The products of last-label tuples. -/
noncomputable def prodSet : Finset ℤ := (labCands P).image fun lab => ((∏ i, lab i : ℕ) : ℤ)

/-- **The clean block bound** from the core kernel bound. -/
theorem kblock_bilBound (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (j : ℕ)
    (pd : Fin P.K → Fin P.J → ℕ) (hpd : pd ∈ padCands P) (m : P.Mem) (pmin : ℝ)
    (hpmin0 : 0 < pmin) (hpmin : ∀ i, ∀ p ∈ P.grp i, pmin ≤ p) (hL : 1 ≤ log P.x)
    (hA₀ : 0 ≤ P.A₀) (hY : 0 < P.Y) (Mκ : ℝ) (hMκ : 0 ≤ Mκ)
    (hκ : BilBound (P.zSet ×ˢ prodSet P) (P.zSet ×ˢ prodSet P) (kappaC P ω pd) Mκ) :
    BilBound (P.zSet ×ˢ labCands P) (P.zSet ×ˢ labCands P) (kblock P ω j pd m)
      (4 ^ P.K / P.Y * Mκ + P.K * (4 / pmin * 2 ^ P.K) * Ccr P) := by
  set S := P.zSet ×ˢ labCands P
  have hinj : Set.InjOn (prodMap P) S := by
    intro p hp q hq h
    simp only [prodMap, Prod.mk.injEq] at h
    have hp' := (mem_product.1 hp).2
    have hq' := (mem_product.1 hq).2
    have h2 : (∏ i, p.2 i : ℕ) = ∏ i, q.2 i := by exact_mod_cast h.2
    exact Prod.ext h.1 (hEP.prod_injOn hp' hq' h2)
  have himg : S.image (prodMap P) ⊆ P.zSet ×ˢ prodSet P := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
    rw [mem_product] at hp ⊢
    exact ⟨hp.1, mem_image.2 ⟨p.2, hp.2, rfl⟩⟩
  have hK1 : BilBound S S (fun p q => kappaC P ω pd (prodMap P p) (prodMap P q)) Mκ :=
    bilBound_comp S S (prodMap P) (prodMap P) hinj hinj (kappaC P ω pd) Mκ
      (bilBound_subset _ _ _ _ himg himg _ _ hκ)
  have hK2 := bilBound_diag S S _ Mκ (alphaC P ω pd m) (betaC P ω pd m) _ _ (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (fun p hp => norm_alphaC_le P hEP ω pd hpd m p hp hY)
    (fun q hq => norm_betaC_le P hEP ω pd m q hq hY) hMκ hK1
  have hK3 := kviol_bilBound P hEP ω hω hU j pd hpd m pmin hpmin0 hpmin hL hA₀ hY
  have hK4 := bilBound_sub S S _ _ _ _ hK2 hK3
  refine bilBound_congr S S _ _ _ (fun p hp q _ => ?_) (bilBound_mono S S _ _ _ ?_ hK4)
  · rw [kblock_eq P ω j pd m p q (hEP.prod_nu_nonneg p.2 (mem_product.1 hp).2)]
  · have h1 : √(4 ^ P.K / P.Y) * √(4 ^ P.K / P.Y) = 4 ^ P.K / P.Y :=
      Real.mul_self_sqrt (by positivity)
    have h2 : √(P.K * (4 / pmin * 2 ^ P.K) * Ccr P) * √(P.K * (4 / pmin * 2 ^ P.K) * Ccr P) =
        P.K * (4 / pmin * 2 ^ P.K) * Ccr P :=
      Real.mul_self_sqrt (by unfold Ccr; positivity)
    rw [h1, h2]

end ArtinPrimitiveRoots.L102G
end

section
/-!
# L102M: shared basic definitions and lemmas

`arcCutoff` facts, `ψ_λ = psiL`, `n^{iτ}` helpers, and the Cauchy weight `ω_a`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory
open scoped ContDiff

noncomputable section

lemma arcCutoff_eq_fun : arcCutoff = fun t => Real.smoothTransition (5 - t) *
    Real.smoothTransition (5 + t) := rfl

lemma arcCutoff_eq_zero {y : ℝ} (h : 5 ≤ |y|) : arcCutoff y = 0 := by
  unfold arcCutoff
  rcases le_abs'.mp h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 + y ≤ 0), mul_zero]
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 - y ≤ 0), zero_mul]

lemma arcCutoff_ne_zero {y : ℝ} (h : arcCutoff y ≠ 0) : |y| < 5 := by
  by_contra h'
  exact h (arcCutoff_eq_zero (not_lt.mp h'))

/-- The complexified cutoff. -/
def arcC (y : ℝ) : ℂ := (arcCutoff y : ℂ)

end

end ArtinPrimitiveRoots.L102M
end

section
/-!
# L102M: one-variable smooth bounds for the Mellin separation

`arcCutoff` is smooth with compact support; `ψ_λ(y) = ψ(y) e(λ y)` has `n`-th derivatives
bounded by `M (1 + 2π|λ|)^n`.
-/

namespace ArtinPrimitiveRoots.L102M

open Real Complex MeasureTheory
open scoped ContDiff

noncomputable section

lemma arcCutoff_contDiff : ContDiff ℝ ∞ arcCutoff := by
  rw [arcCutoff_eq_fun]
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id))

lemma arcC_contDiff : ContDiff ℝ ∞ arcC :=
  Complex.ofRealCLM.contDiff.comp arcCutoff_contDiff

lemma arcC_hasCompactSupport : HasCompactSupport arcC := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-5) 5) isCompact_Icc
  intro y hy
  have h : arcCutoff y ≠ 0 := by
    intro h0; apply hy; simp [arcC, h0]
  have := arcCutoff_ne_zero h
  rw [abs_lt] at this
  exact ⟨this.1.le, this.2.le⟩

end

end ArtinPrimitiveRoots.L102M
end

section
/-! # L102G: geometric sums and the Vinogradov block bound ([21] (4.31)–(4.32))

`ee t = e(t) = exp(2πit)`.

* `norm_sum_ee_le_card`, `norm_sum_ee_le_inv`: `‖Σ_{|k|≤B} e(xk)‖ ≤ min(2B+1, 1/(2‖x‖))`,
  `‖x‖ = |x − round x|`;
* `abs_mul_sub_ge` (separation): if `(c,d) = 1`, `d ≤ Q`, `|ϑ − c/d| ≤ 1/(dQ)`, `0 < 2|k| ≤ d`,
  then `|kϑ − n| ≥ 1/(2d)` for every integer `n`;
* `vinogradov_sum`: `Σ_{|j|≤2A} ‖Σ_{|k|≤B} e(ϑjk)‖ ≤ 2(8A/d + 1)(2B + 1 + d(1 + log d))`;
* `dirichlet_reduced`: a reduced `c/d` with `1 ≤ d ≤ Q`, `|ϑ − c/d| ≤ 1/(dQ)` ((4.31)).
-/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

/-- `e(t) = exp(2πit)`. -/
noncomputable def ee (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (t : ℂ))

lemma norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  rw [ee, show 2 * π * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  rw [ee, ee, ee, ← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_int (n : ℤ) : ee n = 1 := by
  rw [ee, show 2 * π * Complex.I * ((n : ℝ) : ℂ) = (n : ℂ) * (2 * π * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

lemma conj_ee (t : ℝ) : (starRingEnd ℂ) (ee t) = ee (-t) := by
  rw [ee, ee, ← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

lemma ee_pow (x : ℝ) (i : ℕ) : ee x ^ i = ee (i * x) := by
  rw [ee, ee, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma ee_sub_round (x : ℝ) : ee (x - round x) = ee x := by
  have h := ee_add (x - round x) ((round x : ℤ) : ℝ)
  rw [ee_int, mul_one, sub_add_cancel] at h
  exact h.symm

/-- Jordan's inequality on the circle: `|e(x) − 1| ≥ 4‖x‖`. -/
lemma four_mul_abs_le_norm_ee_sub_one (x : ℝ) : 4 * |x - round x| ≤ ‖ee x - 1‖ := by
  have hu2 : |x - round x| ≤ 1 / 2 := abs_sub_round x
  rw [← ee_sub_round]
  set u := x - round x
  have : ee u = Complex.exp (Complex.I * ((2 * π * u : ℝ) : ℂ)) := by
    rw [ee]; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h1 : |π * u| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos pi_pos]; nlinarith [pi_pos]
  have h2 := Real.mul_abs_le_abs_sin h1
  rw [show 2 * π * u / 2 = π * u by ring, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  rw [abs_mul, abs_of_pos pi_pos] at h2
  have : 2 / π * (π * |u|) = 2 * |u| := by field_simp
  linarith

lemma Icc_neg_eq_image (B : ℕ) :
    Icc (-(B : ℤ)) B = (range (2 * B + 1)).image (fun i : ℕ => (i : ℤ) - B) := by
  ext k
  simp only [mem_Icc, mem_image, mem_range]
  constructor
  · intro h; exact ⟨(k + B).toNat, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩; omega

lemma sum_Icc_neg_eq {M : Type*} [AddCommMonoid M] (B : ℕ) (F : ℤ → M) :
    ∑ k ∈ Icc (-(B : ℤ)) B, F k = ∑ i ∈ range (2 * B + 1), F ((i : ℤ) - B) := by
  rw [Icc_neg_eq_image, sum_image]
  intro i _ j _ h
  have := sub_left_inj.mp h
  exact_mod_cast this

lemma card_Icc_neg (B : ℕ) : ((Icc (-(B : ℤ)) B).card : ℝ) = 2 * B + 1 := by
  rw [Int.card_Icc]
  have : ((B : ℤ) + 1 - -(B : ℤ)).toNat = 2 * B + 1 := by omega
  rw [this]; push_cast; ring

/-- The geometric sum: `‖Σ_{|k|≤B} e(xk)‖ · |e(x) − 1| ≤ 2`. -/
lemma norm_sum_ee_mul (x : ℝ) (B : ℕ) :
    ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (x * k)‖ * ‖ee x - 1‖ ≤ 2 := by
  rw [sum_Icc_neg_eq]
  have hsum : ∑ i ∈ range (2 * B + 1), ee (x * (((i : ℤ) - B : ℤ) : ℝ)) =
      ee (-(x * B)) * ∑ i ∈ range (2 * B + 1), ee x ^ i := by
    rw [mul_sum]; refine sum_congr rfl fun i _ => ?_
    rw [ee_pow, ← ee_add]; congr 1; push_cast; ring
  rw [hsum, norm_mul, norm_ee, one_mul, ← norm_mul, geom_sum_mul]
  calc ‖ee x ^ (2 * B + 1) - 1‖ ≤ ‖ee x ^ (2 * B + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, norm_ee, one_pow, norm_one]; norm_num

lemma norm_sum_ee_le_card (x : ℝ) (B : ℕ) :
    ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (x * k)‖ ≤ 2 * B + 1 := by
  calc _ ≤ ∑ k ∈ Icc (-(B : ℤ)) B, ‖ee (x * k)‖ := norm_sum_le _ _
    _ = 2 * B + 1 := by
      rw [sum_congr rfl (fun k _ => norm_ee _), sum_const, nsmul_eq_mul, mul_one, card_Icc_neg]

lemma norm_sum_ee_le_inv (x : ℝ) (B : ℕ) (hu : x - round x ≠ 0) :
    ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (x * k)‖ ≤ 1 / (2 * |x - round x|) := by
  have h1 := norm_sum_ee_mul x B
  have h2 := four_mul_abs_le_norm_ee_sub_one x
  have hpos : 0 < |x - round x| := abs_pos.mpr hu
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (∑ k ∈ Icc (-(B : ℤ)) B, ee (x * k))]

/-- Separation of the multiples of `ϑ` ([21], after (4.32)). -/
lemma abs_mul_sub_ge (ϑ Q : ℝ) (c : ℤ) (d : ℕ) (hd : 1 ≤ d) (hc : IsCoprime c (d : ℤ))
    (hQ : (d : ℝ) ≤ Q) (hϑ : |ϑ - c / d| ≤ 1 / (d * Q)) (k n : ℤ) (hk0 : k ≠ 0)
    (hk : 2 * |k| ≤ (d : ℤ)) : 1 / (2 * d) ≤ |k * ϑ - n| := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hQpos : (0 : ℝ) < Q := lt_of_lt_of_le hdpos hQ
  have hne : k * c - n * d ≠ 0 := by
    intro h
    have hdvd : (d : ℤ) ∣ k * c := ⟨n, by linarith⟩
    have h1 : (d : ℤ) ∣ k := hc.symm.dvd_of_dvd_mul_right hdvd
    have h2 := Int.le_of_dvd (abs_pos.mpr hk0) ((dvd_abs _ _).mpr h1)
    have h3 := abs_pos.mpr hk0
    linarith
  have h1 : (1 : ℝ) ≤ |((k * c - n * d : ℤ) : ℝ)| := by
    have := Int.one_le_abs hne; exact_mod_cast this
  have hid : (k : ℝ) * ϑ - n = ((k * c - n * d : ℤ) : ℝ) / d + k * (ϑ - c / d) := by
    push_cast; field_simp; ring
  have hk' : (2 : ℝ) * |(k : ℝ)| ≤ d := by exact_mod_cast hk
  have h2 : |(k : ℝ) * (ϑ - c / d)| ≤ 1 / (2 * d) := by
    rw [abs_mul]
    calc |(k : ℝ)| * |ϑ - c / d| ≤ (d / 2) * (1 / (d * Q)) :=
          mul_le_mul (by linarith) hϑ (abs_nonneg _) (by positivity)
      _ = 1 / (2 * Q) := by field_simp
      _ ≤ 1 / (2 * d) := by
          apply one_div_le_one_div_of_le (by positivity); linarith
  have h3 : 1 / d ≤ |((k * c - n * d : ℤ) : ℝ) / d| := by
    rw [abs_div, abs_of_pos hdpos]; exact div_le_div_of_nonneg_right h1 hdpos.le
  rw [hid]
  have key : |((k * c - n * d : ℤ) : ℝ) / d| - |(k : ℝ) * (ϑ - c / d)| ≤
      |((k * c - n * d : ℤ) : ℝ) / d + k * (ϑ - c / d)| := by
    have := abs_sub_abs_le_abs_sub (((k * c - n * d : ℤ) : ℝ) / d) (-((k : ℝ) * (ϑ - c / d)))
    rwa [abs_neg, sub_neg_eq_add] at this
  have : 1 / (d : ℝ) - 1 / (2 * d) = 1 / (2 * d) := by field_simp; ring
  linarith

/-- The per-point bound in terms of the bin `r = ⌊2d‖x‖⌋₊`. -/
lemma norm_sum_ee_le_bin (x : ℝ) (B d : ℕ) (hd : 1 ≤ d) :
    ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (x * k)‖ ≤
      if ⌊2 * d * |x - round x|⌋₊ = 0 then (2 * B + 1 : ℝ)
      else d / (⌊2 * d * |x - round x|⌋₊ : ℝ) := by
  split_ifs with h
  · exact norm_sum_ee_le_card x B
  · have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    set r := ⌊2 * d * |x - round x|⌋₊
    have hr : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    have hrle : (r : ℝ) ≤ 2 * d * |x - round x| := Nat.floor_le (by positivity)
    have hu : 0 < |x - round x| := by
      by_contra hc; push Not at hc
      have : 2 * (d : ℝ) * |x - round x| ≤ 0 := by
        have := abs_nonneg (x - round x)
        nlinarith
      linarith
    refine (norm_sum_ee_le_inv x B (abs_pos.mp hu)).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith

/-- **Vinogradov's block bound** ([21] (4.32)): if `(c, d) = 1`, `d ≤ Q` and
`|ϑ − c/d| ≤ 1/(dQ)`, then `Σ_{|j|≤2A} ‖Σ_{|k|≤B} e(ϑjk)‖ ≤ 2(8A/d + 1)(2B + 1 + d(1 + log d))`. -/
theorem vinogradov_sum (A B d : ℕ) (hd : 1 ≤ d) (c : ℤ) (hc : IsCoprime c (d : ℤ)) (Q ϑ : ℝ)
    (hQ : (d : ℝ) ≤ Q) (hϑ : |ϑ - c / d| ≤ 1 / (d * Q)) :
    ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (ϑ * j * k)‖ ≤
      2 * (8 * A / d + 1) * (2 * B + 1 + d * (1 + Real.log d)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set m : ℕ := d / 2 + 1 with hm
  have hm0 : 0 < m := by omega
  let u : ℤ → ℝ := fun j => ϑ * j - round (ϑ * j)
  let G : ℕ → ℝ := fun r => if r = 0 then (2 * B + 1 : ℝ) else d / (r : ℝ)
  let key : ℤ → ℕ × Bool × ℕ := fun j =>
    ((j + 2 * A).toNat / m, decide (0 ≤ u j), ⌊2 * d * |u j|⌋₊)
  have hG0 : ∀ r, 0 ≤ G r := by
    intro r; simp only [G]; split_ifs <;> positivity
  -- Step 1: pointwise bound
  have h1 : ∀ j : ℤ, ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (ϑ * j * k)‖ ≤ G (key j).2.2 :=
    fun j => norm_sum_ee_le_bin (ϑ * j) B d hd
  -- Step 2: injectivity
  have hinj : ∀ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ∀ j' ∈ Icc (-(2 * A : ℤ)) (2 * A),
      key j = key j' → j = j' := by
    intro j hj j' hj' hkey
    rw [mem_Icc] at hj hj'
    simp only [key, Prod.mk.injEq] at hkey
    obtain ⟨hb, hs, hr⟩ := hkey
    by_contra hne
    -- the block condition
    have hblock : 2 * |j - j'| ≤ (d : ℤ) := by
      have e1 := Nat.div_add_mod (j + 2 * A).toNat m
      have e2 := Nat.div_add_mod (j' + 2 * A).toNat m
      have l1 := Nat.mod_lt (j + 2 * A).toNat hm0
      have l2 := Nat.mod_lt (j' + 2 * A).toNat hm0
      rw [hb] at e1
      generalize m * ((j' + 2 * A).toNat / m) = P at e1 e2
      rcases abs_cases (j - j') with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega
    have hsep := abs_mul_sub_ge ϑ Q c d hd hc hQ hϑ (j - j') (round (ϑ * j) - round (ϑ * j'))
      (sub_ne_zero.mpr hne) hblock
    have hdiff : ((j - j' : ℤ) : ℝ) * ϑ - ((round (ϑ * j) - round (ϑ * j') : ℤ) : ℝ) =
        u j - u j' := by simp only [u]; push_cast; ring
    rw [hdiff] at hsep
    -- the same bin
    have ha := Nat.floor_le (show 0 ≤ 2 * (d : ℝ) * |u j| by positivity)
    have hb' := Nat.lt_floor_add_one (2 * (d : ℝ) * |u j|)
    have hc' := Nat.floor_le (show 0 ≤ 2 * (d : ℝ) * |u j'| by positivity)
    have hd' := Nat.lt_floor_add_one (2 * (d : ℝ) * |u j'|)
    rw [hr] at ha hb'
    have hclose : |u j - u j'| < 1 / (2 * d) := by
      have hsign : (0 ≤ u j ↔ 0 ≤ u j') := by simpa using hs
      have habs : |u j - u j'| = |(|u j| - |u j'|)| := by
        by_cases h0 : 0 ≤ u j
        · have h0' := hsign.mp h0
          rw [abs_of_nonneg h0, abs_of_nonneg h0']
        · have h0' : ¬ 0 ≤ u j' := fun h => h0 (hsign.mpr h)
          push Not at h0 h0'
          rw [abs_of_neg h0, abs_of_neg h0', ← abs_neg]; congr 1; ring
      have hd2 : (0 : ℝ) < 2 * d := by positivity
      have hlt : abs (2 * (d : ℝ) * |u j| - 2 * d * |u j'|) < 1 := by
        rw [abs_lt]; constructor <;> linarith
      have : |(|u j| - |u j'|)| = abs (2 * (d : ℝ) * |u j| - 2 * d * |u j'|) / (2 * d) := by
        rw [← mul_sub, abs_mul, abs_of_pos hd2]; field_simp
      rw [habs, this, div_lt_div_iff_of_pos_right hd2]
      exact hlt
    linarith
  -- Step 3: the image lies in a product
  set nb : ℕ := 4 * A / m + 1
  have hmaps : ∀ j ∈ Icc (-(2 * A : ℤ)) (2 * A),
      key j ∈ range nb ×ˢ (univ : Finset Bool) ×ˢ range (d + 1) := by
    intro j hj
    rw [mem_Icc] at hj
    simp only [key, mem_product, mem_range, mem_univ, true_and]
    constructor
    · have : (j + 2 * A).toNat ≤ 4 * A := by omega
      have := Nat.div_le_div_right (c := m) this
      omega
    · rw [Nat.floor_lt (by positivity)]
      have : |u j| ≤ 1 / 2 := abs_sub_round _
      push_cast
      nlinarith
  -- Step 4: sum
  have hsum : ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (ϑ * j * k)‖ ≤
      (nb : ℝ) * 2 * (2 * B + 1 + d * (harmonic d : ℝ)) := by
    calc _ ≤ ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), G (key j).2.2 := sum_le_sum fun j _ => h1 j
      _ = ∑ t ∈ (Icc (-(2 * A : ℤ)) (2 * A)).image key, G t.2.2 := (sum_image (f := fun t => G t.2.2) hinj).symm
      _ ≤ ∑ t ∈ range nb ×ˢ (univ : Finset Bool) ×ˢ range (d + 1), G t.2.2 := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro t ht
            obtain ⟨j, hj, rfl⟩ := mem_image.mp ht
            exact hmaps j hj
          · intro t _ _; exact hG0 _
      _ = (nb : ℝ) * 2 * ∑ r ∈ range (d + 1), G r := by
          rw [sum_product]
          simp only [sum_product, sum_const, card_range, card_univ, Fintype.card_bool,
            nsmul_eq_mul]
          push_cast; ring
      _ = (nb : ℝ) * 2 * (2 * B + 1 + d * (harmonic d : ℝ)) := by
          congr 1
          rw [sum_range_succ', harmonic, Rat.cast_sum, mul_sum]
          simp only [G, Nat.succ_ne_zero, if_false, if_true]
          rw [add_comm]; congr 1
          refine sum_congr rfl fun i _ => ?_
          push_cast; ring
  -- Step 5: constants
  have hnb : (nb : ℝ) ≤ 8 * A / d + 1 := by
    simp only [nb]; push_cast
    have h1 : ((4 * A / m : ℕ) : ℝ) ≤ (4 * A : ℝ) / m := by
      have := Nat.cast_div_le (α := ℝ) (m := 4 * A) (n := m); push_cast at this; exact this
    have h2 : (d : ℝ) / 2 ≤ m := by
      have : d ≤ 2 * m := by omega
      have : (d : ℝ) ≤ 2 * m := by exact_mod_cast this
      linarith
    have h3 : (4 * A : ℝ) / m ≤ 8 * A / d := by
      rw [div_le_div_iff₀ (by positivity) hdpos]
      have : (0 : ℝ) ≤ A := by positivity
      nlinarith
    linarith
  have hH : (harmonic d : ℝ) ≤ 1 + Real.log d := harmonic_le_one_add_log d
  calc _ ≤ (nb : ℝ) * 2 * (2 * B + 1 + d * (harmonic d : ℝ)) := hsum
    _ ≤ (8 * A / d + 1) * 2 * (2 * B + 1 + d * (1 + Real.log d)) := by
        have hh : (0 : ℝ) ≤ harmonic d := by
          have : (0 : ℚ) ≤ harmonic d := by
            unfold harmonic; exact sum_nonneg fun i _ => by positivity
          exact_mod_cast this
        apply mul_le_mul (by nlinarith) (by nlinarith) (by positivity) (by positivity)
    _ = _ := by ring

/-- Dirichlet's approximation in reduced form ([21] (4.31)): for `Q ≥ 1` there is a reduced
fraction `c/d` with `1 ≤ d ≤ Q` and `|ϑ − c/d| ≤ 1/(dQ)`. -/
theorem dirichlet_reduced (ϑ : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ (c : ℤ) (d : ℕ), IsCoprime c (d : ℤ) ∧ 1 ≤ d ∧ d ≤ Q ∧ |ϑ - c / d| ≤ 1 / (d * Q) := by
  obtain ⟨j, k, hk0, hkQ, hjk⟩ := Real.exists_int_int_abs_mul_sub_le ϑ (n := Q) hQ
  set g : ℕ := Int.gcd j k
  have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_right j hk0.ne'
  set c : ℤ := j / g
  set d' : ℤ := k / g
  have hj : j = (g : ℤ) * c := (Int.mul_ediv_cancel' (Int.gcd_dvd_left j k)).symm
  have hk : k = (g : ℤ) * d' := (Int.mul_ediv_cancel' (Int.gcd_dvd_right j k)).symm
  have hcop : IsCoprime c d' := Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_ediv_gcd_ediv_gcd hgpos)
  have hg1 : (1 : ℤ) ≤ g := by exact_mod_cast hgpos
  have hd'pos : 0 < d' := by
    rcases lt_or_ge 0 d' with h | h
    · exact h
    · exfalso; have : (g : ℤ) * d' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      omega
  have hd'k : d' ≤ k := by
    rw [hk]; nlinarith
  refine ⟨c, d'.toNat, ?_, by omega, by omega, ?_⟩
  · rwa [Int.toNat_of_nonneg hd'pos.le]
  · have hcast : ((d'.toNat : ℕ) : ℝ) = (d' : ℝ) := by
      rw [show ((d'.toNat : ℕ) : ℝ) = ((d'.toNat : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg hd'pos.le]
    rw [hcast]
    have hd'R : (0 : ℝ) < d' := by exact_mod_cast hd'pos
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have e : ϑ - c / d' = ((k : ℝ) * ϑ - j) / k := by
      rw [hj, hk]; push_cast; field_simp
    rw [e, abs_div, abs_of_pos hkR, div_le_div_iff₀ hkR (by positivity)]
    have hdk : (d' : ℝ) ≤ k := by exact_mod_cast hd'k
    have h1 : |(k : ℝ) * ϑ - j| * (Q + 1) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at hjk
    have h2 : |(k : ℝ) * ϑ - j| * (d' * Q) ≤ |(k : ℝ) * ϑ - j| * (k * (Q + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact mul_le_mul hdk (by linarith) (by positivity) hkR.le
    have h3 : |(k : ℝ) * ϑ - j| * (k * (Q + 1)) ≤ 1 * k := by
      rw [show |(k : ℝ) * ϑ - j| * (k * (Q + 1)) = (|(k : ℝ) * ϑ - j| * (Q + 1)) * k by ring]
      exact mul_le_mul_of_nonneg_right h1 hkR.le
    linarith

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: the determinant exponential matrix on a box ([21] (4.32)–(4.33))

Box `[−A, A] × [−B, B] ⊆ ℤ²`, `det(v, w) = v₁w₂ − v₂w₁`. With
`N(ϑ) = Σ_{|j|≤2A} ‖Σ_{|k|≤B} e(ϑjk)‖`:

* `sum_norm_sq_transform_le`: `Σ_{|k|≤B} ‖Σ_{|h|≤A} w(h) e(ϑhk)‖² ≤ N(ϑ) Σ‖w‖²` (Schur on `TT*`);
* `norm_bilinear_det_le_aux`: `‖Σ_{v,w} f(v) e(ϑ det(v,w)) g(w)‖ ≤ √(N(ϑ)‖f‖²) √(N(−ϑ)‖g‖²)`,
  by writing the form as `Σ_{l₁,l₂} F(l₁,l₂) G(l₁,l₂)` with transforms in the first coordinate
  (no tensor products);
* `det_bilinear_bound` (**D6, matrix part**): if `(c,d) = 1`, `d ≤ Q`, `|ϑ − c/d| ≤ 1/(dQ)`, the
  matrix `(e(ϑ det(v, w)))_{v,w ∈ box}` has operator norm at most
  `2(8A/d + 1)(2B + 1 + d(1 + log d))`, as a bilinear form;
* `det_bilinear_bound'`: the same with the constant `64(A/d + 1)(B + d log 2d)` of (4.32);
* `det_matrix_l2_bound`: the same as an `ℓ² → ℓ²` bound;
* `det_bilinear_bound_div` ((4.33)): if moreover `AB ≤ C₁Y`, `A, B ≤ Y^{0.9}`, `P < d`,
  `Q ≤ Y/P + 1`, `1 ≤ P`, `1 ≤ Y`, the norm divided by `Y` is at most
  `(32C₁ + 40)(1/P + Y^{−0.1})(1 + log 2Y)`.
-/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj']; push_cast; rfl

/-- Shifted sums of a nonnegative kernel over `[−A, A]` are dominated by its sum over `[−2A, 2A]`. -/
lemma sum_sub_le (A : ℕ) (K : ℤ → ℝ) (hK : ∀ j, 0 ≤ K j) (h : ℤ) (hh : h ∈ Icc (-(A : ℤ)) A) :
    ∑ h' ∈ Icc (-(A : ℤ)) A, K (h - h') ≤ ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), K j := by
  rw [← sum_image (s := Icc (-(A : ℤ)) A) (g := fun h' => h - h') (f := K)
    (fun a _ b _ hab => by simpa using hab)]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨h', hh', rfl⟩ := mem_image.mp hj
    rw [mem_Icc] at hh hh' ⊢; omega
  · intro j _ _; exact hK j

lemma sum_sub_le' (A : ℕ) (K : ℤ → ℝ) (hK : ∀ j, 0 ≤ K j) (h' : ℤ)
    (hh : h' ∈ Icc (-(A : ℤ)) A) :
    ∑ h ∈ Icc (-(A : ℤ)) A, K (h - h') ≤ ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), K j := by
  rw [← sum_image (s := Icc (-(A : ℤ)) A) (g := fun h => h - h') (f := K)
    (fun a _ b _ hab => by simpa using hab)]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨h, hh', rfl⟩ := mem_image.mp hj
    rw [mem_Icc] at hh hh' ⊢; omega
  · intro j _ _; exact hK j

/-- The `T*` bound (Schur's test on `TT*`): for `T = (e(ϑhk))_{|h|≤A, |k|≤B}`,
`Σ_{|k|≤B} ‖Σ_{|h|≤A} w(h) e(ϑhk)‖² ≤ N(ϑ) Σ_{|h|≤A} ‖w(h)‖²`. -/
theorem sum_norm_sq_transform_le (A B : ℕ) (ϑ : ℝ) (w : ℤ → ℂ) :
    ∑ k ∈ Icc (-(B : ℤ)) B, ‖∑ h ∈ Icc (-(A : ℤ)) A, w h * ee (ϑ * h * k)‖ ^ 2 ≤
      (∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (ϑ * j * k)‖) *
        ∑ h ∈ Icc (-(A : ℤ)) A, ‖w h‖ ^ 2 := by
  set IA := Icc (-(A : ℤ)) A
  set IB := Icc (-(B : ℤ)) B
  set K : ℤ → ℝ := fun j => ‖∑ k ∈ IB, ee (ϑ * j * k)‖ with hKdef
  have hK : ∀ j, 0 ≤ K j := fun j => norm_nonneg _
  have hexp : ((∑ k ∈ IB, ‖∑ h ∈ IA, w h * ee (ϑ * h * k)‖ ^ 2 : ℝ) : ℂ) =
      ∑ h ∈ IA, ∑ h' ∈ IA, w h * (starRingEnd ℂ) (w h') *
        ∑ k ∈ IB, ee (ϑ * ((h - h' : ℤ) : ℝ) * k) := by
    rw [Complex.ofReal_sum]
    calc ∑ k ∈ IB, ((‖∑ h ∈ IA, w h * ee (ϑ * h * k)‖ ^ 2 : ℝ) : ℂ)
        = ∑ k ∈ IB, ∑ h ∈ IA, ∑ h' ∈ IA,
            w h * (starRingEnd ℂ) (w h') * ee (ϑ * ((h - h' : ℤ) : ℝ) * k) := by
          refine sum_congr rfl fun k _ => ?_
          rw [ofReal_norm_sq, map_sum, sum_mul_sum]
          refine sum_congr rfl fun h _ => sum_congr rfl fun h' _ => ?_
          rw [map_mul, conj_ee, show ϑ * ((h - h' : ℤ) : ℝ) * k = ϑ * h * k + -(ϑ * h' * k) by
            push_cast; ring, ee_add]
          ring
      _ = _ := by
          rw [sum_comm]; refine sum_congr rfl fun h _ => ?_
          rw [sum_comm]; refine sum_congr rfl fun h' _ => ?_
          rw [mul_sum]
  have hnn : 0 ≤ ∑ k ∈ IB, ‖∑ h ∈ IA, w h * ee (ϑ * h * k)‖ ^ 2 :=
    sum_nonneg fun _ _ => by positivity
  have step1 : ∑ k ∈ IB, ‖∑ h ∈ IA, w h * ee (ϑ * h * k)‖ ^ 2 ≤
      ∑ h ∈ IA, ∑ h' ∈ IA, ‖w h‖ * ‖w h'‖ * K (h - h') := by
    rw [← Real.norm_of_nonneg hnn, ← Complex.norm_real, hexp]
    refine (norm_sum_le _ _).trans (sum_le_sum fun h _ => (norm_sum_le _ _).trans
      (sum_le_sum fun h' _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj]
  have step2 : ∑ h ∈ IA, ∑ h' ∈ IA, ‖w h‖ * ‖w h'‖ * K (h - h') ≤
      (1 / 2) * ∑ h ∈ IA, ‖w h‖ ^ 2 * ∑ h' ∈ IA, K (h - h') +
        (1 / 2) * ∑ h' ∈ IA, ‖w h'‖ ^ 2 * ∑ h ∈ IA, K (h - h') := by
    have : ∀ h ∈ IA, ∀ h' ∈ IA, ‖w h‖ * ‖w h'‖ * K (h - h') ≤
        (1 / 2) * (‖w h‖ ^ 2 * K (h - h')) + (1 / 2) * (‖w h'‖ ^ 2 * K (h - h')) := by
      intro h _ h' _
      have := hK (h - h')
      nlinarith [sq_nonneg (‖w h‖ - ‖w h'‖), mul_nonneg this (sq_nonneg (‖w h‖ - ‖w h'‖))]
    calc _ ≤ ∑ h ∈ IA, ∑ h' ∈ IA,
          ((1 / 2) * (‖w h‖ ^ 2 * K (h - h')) + (1 / 2) * (‖w h'‖ ^ 2 * K (h - h'))) :=
          sum_le_sum fun h hh => sum_le_sum fun h' hh' => this h hh h' hh'
      _ = (1 / 2) * ∑ h ∈ IA, ∑ h' ∈ IA, ‖w h‖ ^ 2 * K (h - h') +
            (1 / 2) * ∑ h ∈ IA, ∑ h' ∈ IA, ‖w h'‖ ^ 2 * K (h - h') := by
          simp only [sum_add_distrib, mul_sum]
      _ = _ := by
          congr 2
          · exact sum_congr rfl fun h _ => (mul_sum _ _ _).symm
          · rw [sum_comm]; exact sum_congr rfl fun h' _ => (mul_sum _ _ _).symm
  have step3 : ∑ h ∈ IA, ‖w h‖ ^ 2 * ∑ h' ∈ IA, K (h - h') ≤
      ∑ h ∈ IA, ‖w h‖ ^ 2 * ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), K j :=
    sum_le_sum fun h hh => mul_le_mul_of_nonneg_left (sum_sub_le A K hK h hh) (by positivity)
  have step4 : ∑ h' ∈ IA, ‖w h'‖ ^ 2 * ∑ h ∈ IA, K (h - h') ≤
      ∑ h' ∈ IA, ‖w h'‖ ^ 2 * ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), K j :=
    sum_le_sum fun h' hh => mul_le_mul_of_nonneg_left (sum_sub_le' A K hK h' hh) (by positivity)
  rw [← sum_mul] at step3 step4
  have : ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), K j =
      ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ IB, ee (ϑ * j * k)‖ := rfl
  rw [← this]
  linarith

/-- The bilinear form of the determinant matrix, in terms of `N(ϑ)` and `N(−ϑ)`. -/
theorem norm_bilinear_det_le_aux (A B : ℕ) (ϑ : ℝ) (f g : ℤ × ℤ → ℂ) :
    ‖∑ v ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B, ∑ w ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B,
        f v * ee (ϑ * ((v.1 * w.2 - v.2 * w.1 : ℤ) : ℝ)) * g w‖ ≤
      √((∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (ϑ * j * k)‖) *
          ∑ v ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B, ‖f v‖ ^ 2) *
        √((∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (-ϑ * j * k)‖) *
          ∑ w ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B, ‖g w‖ ^ 2) := by
  set IA := Icc (-(A : ℤ)) A
  set IB := Icc (-(B : ℤ)) B
  -- the transforms in the first coordinate
  set F : ℤ × ℤ → ℂ := fun p => ∑ h ∈ IA, f (h, p.1) * ee (ϑ * h * p.2) with hF
  set G : ℤ × ℤ → ℂ := fun p => ∑ h ∈ IA, g (h, p.2) * ee (-ϑ * h * p.1) with hG
  have hid' : ∀ h₁ l₁ h₂ l₂ : ℤ, f (h₁, l₁) * ee (ϑ * ((h₁ * l₂ - l₁ * h₂ : ℤ) : ℝ)) * g (h₂, l₂) =
      f (h₁, l₁) * ee (ϑ * h₁ * l₂) * (g (h₂, l₂) * ee (-ϑ * h₂ * l₁)) := by
    intro h₁ l₁ h₂ l₂
    rw [show ϑ * ((h₁ * l₂ - l₁ * h₂ : ℤ) : ℝ) = ϑ * h₁ * l₂ + -ϑ * h₂ * l₁ by push_cast; ring,
      ee_add]
    ring
  have hid : ∑ v ∈ IA ×ˢ IB, ∑ w ∈ IA ×ˢ IB, f v * ee (ϑ * ((v.1 * w.2 - v.2 * w.1 : ℤ) : ℝ)) * g w
      = ∑ p ∈ IB ×ˢ IB, F p * G p := by
    rw [sum_product (s := IB) (t := IB)]
    simp only [hF, hG, sum_mul_sum, sum_product]
    -- LHS: Σ_{h₁} Σ_{l₁} Σ_{h₂} Σ_{l₂}; RHS: Σ_{l₁} Σ_{l₂} Σ_{h₁} Σ_{h₂}
    calc _ = ∑ l₁ ∈ IB, ∑ h₁ ∈ IA, ∑ l₂ ∈ IB, ∑ h₂ ∈ IA,
          f (h₁, l₁) * ee (ϑ * h₁ * l₂) * (g (h₂, l₂) * ee (-ϑ * h₂ * l₁)) := by
          rw [sum_comm]
          refine sum_congr rfl fun l₁ _ => sum_congr rfl fun h₁ _ => ?_
          rw [sum_comm]
          exact sum_congr rfl fun l₂ _ => sum_congr rfl fun h₂ _ => hid' _ _ _ _
      _ = _ := by
          refine sum_congr rfl fun l₁ _ => ?_
          rw [sum_comm]
  have hFs : ∑ p ∈ IB ×ˢ IB, ‖F p‖ ^ 2 ≤
      (∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ IB, ee (ϑ * j * k)‖) *
        ∑ v ∈ IA ×ˢ IB, ‖f v‖ ^ 2 := by
    rw [sum_product, sum_product, sum_comm (s := IA), mul_sum]
    exact sum_le_sum fun l₁ _ => sum_norm_sq_transform_le A B ϑ (fun h => f (h, l₁))
  have hGs : ∑ p ∈ IB ×ˢ IB, ‖G p‖ ^ 2 ≤
      (∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ IB, ee (-ϑ * j * k)‖) *
        ∑ w ∈ IA ×ˢ IB, ‖g w‖ ^ 2 := by
    rw [sum_product, sum_comm, sum_product, sum_comm (s := IA), mul_sum]
    exact sum_le_sum fun l₂ _ => sum_norm_sq_transform_le A B (-ϑ) (fun h => g (h, l₂))
  rw [hid]
  calc ‖∑ p ∈ IB ×ˢ IB, F p * G p‖ ≤ ∑ p ∈ IB ×ˢ IB, ‖F p‖ * ‖G p‖ :=
        (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun p _ => norm_mul _ _))
    _ ≤ √(∑ p ∈ IB ×ˢ IB, ‖F p‖ ^ 2) * √(∑ p ∈ IB ×ˢ IB, ‖G p‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt hFs) (Real.sqrt_le_sqrt hGs) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)

/-- **D6, matrix part** ([21] (4.32)): the determinant exponential matrix on the box
`[−A, A] × [−B, B]` has operator norm at most `2(8A/d + 1)(2B + 1 + d(1 + log d))` when
`(c, d) = 1`, `d ≤ Q` and `|ϑ − c/d| ≤ 1/(dQ)`; stated as a bound for the bilinear form. -/
theorem det_bilinear_bound (A B d : ℕ) (hd : 1 ≤ d) (c : ℤ) (hc : IsCoprime c (d : ℤ))
    (Q ϑ : ℝ) (hQ : (d : ℝ) ≤ Q) (hϑ : |ϑ - c / d| ≤ 1 / (d * Q)) (f g : ℤ × ℤ → ℂ) :
    ‖∑ v ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B, ∑ w ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B,
        f v * Complex.exp (2 * π * Complex.I * ((ϑ * ((v.1 * w.2 - v.2 * w.1 : ℤ) : ℝ) : ℝ) : ℂ)) *
          g w‖ ≤
      2 * (8 * A / d + 1) * (2 * B + 1 + d * (1 + Real.log d)) *
        √(∑ v ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B, ‖f v‖ ^ 2) *
          √(∑ w ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B, ‖g w‖ ^ 2) := by
  set V := 2 * (8 * A / d + 1) * (2 * B + 1 + d * (1 + Real.log d)) with hV
  have hN1 := vinogradov_sum A B d hd c hc Q ϑ hQ hϑ
  have hN2 := vinogradov_sum A B d hd (-c) hc.neg_left Q (-ϑ) hQ (by
    rw [show -ϑ - ((-c : ℤ) : ℝ) / d = -(ϑ - c / d) by push_cast; ring, abs_neg]; exact hϑ)
  have h := norm_bilinear_det_le_aux A B ϑ f g
  have hf := sum_nonneg (s := Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B)
    (fun v _ => sq_nonneg ‖f v‖)
  have hg := sum_nonneg (s := Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B)
    (fun v _ => sq_nonneg ‖g v‖)
  refine h.trans ?_
  rw [Real.sqrt_mul' _ hf, Real.sqrt_mul' _ hg]
  have hNn : 0 ≤ ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (ϑ * j * k)‖ :=
    sum_nonneg fun _ _ => norm_nonneg _
  have hNn' : 0 ≤ ∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (-ϑ * j * k)‖ :=
    sum_nonneg fun _ _ => norm_nonneg _
  have hs1 := Real.sqrt_le_sqrt hN1
  have hs2 := Real.sqrt_le_sqrt hN2
  have hVn : 0 ≤ V := le_trans hNn hN1
  have hVV : √V * √V = V := Real.mul_self_sqrt hVn
  calc _ = (√(∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (ϑ * j * k)‖) *
          √(∑ j ∈ Icc (-(2 * A : ℤ)) (2 * A), ‖∑ k ∈ Icc (-(B : ℤ)) B, ee (-ϑ * j * k)‖)) *
        (√(∑ v ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B, ‖f v‖ ^ 2) *
          √(∑ w ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B, ‖g w‖ ^ 2)) := by ring
    _ ≤ (√V * √V) * (√(∑ v ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B, ‖f v‖ ^ 2) *
          √(∑ w ∈ Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B, ‖g w‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [hVV]; ring

/-- **(4.33)**: under `AB ≤ C₁Y`, `A, B ≤ Y^{0.9}`, `1 ≤ P ≤ d ≤ Q ≤ Y/P + 1` and `Y ≥ 1`, the bound
of `det_bilinear_bound`, divided by `Y`, is at most `(32C₁ + 40)(1/P + Y^{−0.1})(1 + log 2Y)`.
(With `P = L^{A₀}` and `log Y ≪ L^{0.2}` this is `≪ L^{0.2−A₀} + Y^{−0.1} log 2Y`.) -/
theorem det_bound_div (A B d : ℕ) (hd : 1 ≤ d) (Y P Q C₁ : ℝ) (hY : 1 ≤ Y) (hP : 1 ≤ P)
    (hPd : P ≤ d) (hdQ : (d : ℝ) ≤ Q) (hQY : Q ≤ Y / P + 1) (hAB : (A : ℝ) * B ≤ C₁ * Y)
    (hA : (A : ℝ) ≤ Y ^ (0.9 : ℝ)) (hB : (B : ℝ) ≤ Y ^ (0.9 : ℝ)) :
    2 * (8 * A / d + 1) * (2 * B + 1 + d * (1 + Real.log d)) / Y ≤
      (32 * C₁ + 40) * (1 / P + Y ^ (-0.1 : ℝ)) * (1 + Real.log (2 * Y)) := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hPpos : (0 : ℝ) < P := by linarith
  set y := Y ^ (-0.1 : ℝ) with hy
  set iP := 1 / P with hiP
  set ℓ := 1 + Real.log (2 * Y) with hℓ
  set Ld := 1 + Real.log d with hLd
  have hy0 : 0 ≤ y := Real.rpow_nonneg hYpos.le _
  have hiP0 : 0 ≤ iP := by positivity
  have h09 : Y ^ (0.9 : ℝ) = Y * y := by
    rw [hy, ← Real.rpow_one_add' hYpos.le (by norm_num)]; norm_num
  have hYy : 1 ≤ Y * y := by rw [← h09]; exact Real.one_le_rpow hY (by norm_num)
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hC₁Y : 0 ≤ C₁ * Y := le_trans (mul_nonneg hA0 hB0) hAB
  have hC₁ : 0 ≤ C₁ := nonneg_of_mul_nonneg_left hC₁Y hYpos
  have hd2Y : (d : ℝ) ≤ 2 * Y := by
    have : Y / P ≤ Y := div_le_self hYpos.le hP
    linarith
  have hLd1 : 1 ≤ Ld := by have := Real.log_nonneg hd1; linarith
  have hLdℓ : Ld ≤ ℓ := by
    have := Real.log_le_log hdpos hd2Y; linarith
  have hℓ1 : 1 ≤ ℓ := le_trans hLd1 hLdℓ
  have hid : (1 : ℝ) / d ≤ iP := one_div_le_one_div_of_le hPpos hPd
  -- the five terms
  have F1 : 32 * (A * B / d) ≤ 32 * (C₁ * Y * iP) := by
    have : A * B / d ≤ C₁ * Y / d := div_le_div_of_nonneg_right hAB hdpos.le
    have : C₁ * Y / d ≤ C₁ * Y * iP := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hid hC₁Y
    linarith
  have F2 : 16 * (A / d) ≤ 16 * (Y * y) := by
    have : (A : ℝ) / d ≤ A := div_le_self hA0 hd1
    linarith
  have F3 : 16 * (A * Ld) ≤ 16 * (Y * y * ℓ) := by
    have := mul_le_mul (hA.trans_eq h09) hLdℓ (by linarith) (by positivity)
    linarith
  have F4 : 4 * (B : ℝ) + 2 ≤ 6 * (Y * y) := by
    have := hB.trans_eq h09; linarith
  have F5 : 2 * (d * Ld) ≤ 2 * ((Y * iP + Y * y) * ℓ) := by
    have h1 : (d : ℝ) ≤ Y * iP + Y * y := by
      have : Y / P = Y * iP := by rw [hiP]; ring
      linarith
    have := mul_le_mul h1 hLdℓ (by linarith) (by positivity)
    linarith
  have hV : 2 * (8 * A / d + 1) * (2 * B + 1 + d * Ld) =
      32 * (A * B / d) + 16 * (A / d) + 16 * (A * Ld) + (4 * B + 2) + 2 * (d * Ld) := by
    field_simp; ring
  rw [div_le_iff₀ hYpos, hV]
  have G1 : C₁ * Y * iP ≤ C₁ * Y * iP * ℓ := le_mul_of_one_le_right (by positivity) hℓ1
  have G2 : Y * y ≤ Y * y * ℓ := le_mul_of_one_le_right (by positivity) hℓ1
  have G3 : 0 ≤ Y * iP * ℓ := by positivity
  have G4 : 0 ≤ C₁ * Y * y * ℓ := by positivity
  have : (32 * C₁ + 40) * (iP + y) * ℓ * Y =
      32 * (C₁ * Y * iP * ℓ) + 32 * (C₁ * Y * y * ℓ) + 40 * (Y * iP * ℓ) + 40 * (Y * y * ℓ) := by
    ring
  rw [this]
  linarith

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: Fourier separation of the arc cutoff `ψ` ([21] (4.30))

`psiHat = 𝓕 ψ` is continuous, `(1 + ξ⁴) ‖ψ̂(ξ)‖ ≤ C`, so `ψ̂` and `(1 + |ξ|) ψ̂` are integrable, and
`ψ(x) = ∫ ψ̂(ξ) e(ξ x) dξ` for every real `x` (`arcCutoff_eq_integral`). -/

namespace ArtinPrimitiveRoots.L102G

open Real MeasureTheory
open scoped FourierTransform

/-- `ψ̂ = 𝓕 ψ`. -/
noncomputable def psiHat : ℝ → ℂ := 𝓕 L102M.arcC

lemma integrable_iteratedFDeriv_arcC (n : ℕ) :
    Integrable (iteratedFDeriv ℝ n L102M.arcC) :=
  (L102M.arcC_contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).integrable_of_hasCompactSupport
    (L102M.arcC_hasCompactSupport.iteratedFDeriv n)

lemma arcC_integrable : Integrable L102M.arcC :=
  L102M.arcC_contDiff.continuous.integrable_of_hasCompactSupport L102M.arcC_hasCompactSupport

lemma psiHat_continuous : Continuous psiHat :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simp only [innerₗ_apply_apply]; exact continuous_fst.inner continuous_snd) arcC_integrable

/-- Decay of `ψ̂`. -/
lemma psiHat_decay : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, (1 + ‖ξ‖ ^ 4) * ‖psiHat ξ‖ ≤ C := by
  have hcd : ContDiff ℝ (4 : ℕ∞) L102M.arcC :=
    L102M.arcC_contDiff.of_le (by exact_mod_cast le_top)
  have hint : ∀ (k n : ℕ), (k : ℕ∞) ≤ (0 : ℕ∞) → (n : ℕ∞) ≤ (4 : ℕ∞) →
      Integrable (fun v ↦ ‖v‖ ^ k * ‖iteratedFDeriv ℝ n L102M.arcC v‖) := by
    intro k n hk _
    have hk0 : k = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hk
    subst hk0
    simpa using (integrable_iteratedFDeriv_arcC n).norm
  set S4 := ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (4 + 1),
    ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 L102M.arcC v‖
  set S0 := ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (0 + 1),
    ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 L102M.arcC v‖
  have hS4 : 0 ≤ S4 := Finset.sum_nonneg fun p _ => integral_nonneg fun v => by positivity
  have hS0 : 0 ≤ S0 := Finset.sum_nonneg fun p _ => integral_nonneg fun v => by positivity
  refine ⟨16 * S4 + S0, by positivity, fun ξ => ?_⟩
  have h4 := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := 4) hcd hint
    (k := 0) (n := 4) le_rfl le_rfl ξ
  have h0 := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := 4) hcd hint
    (k := 0) (n := 0) le_rfl (by norm_num) ξ
  rw [norm_iteratedFDeriv_zero] at h4 h0
  have e4 : (2 * π) ^ (0 : ℕ) * (2 * ((0 : ℕ) : ℝ) + 2) ^ (4 : ℕ) = 16 := by norm_num
  have e0 : (2 * π) ^ (0 : ℕ) * (2 * ((0 : ℕ) : ℝ) + 2) ^ (0 : ℕ) = 1 := by norm_num
  rw [e4] at h4
  rw [e0, pow_zero, one_mul, one_mul] at h0
  have : (1 + ‖ξ‖ ^ 4) * ‖psiHat ξ‖ = ‖ξ‖ ^ 4 * ‖𝓕 L102M.arcC ξ‖ + ‖𝓕 L102M.arcC ξ‖ := by
    simp only [psiHat]; ring
  rw [this]
  linarith

lemma psiHat_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, (1 + |ξ|) * ‖psiHat ξ‖ ≤ C * (1 + ξ ^ 2)⁻¹ := by
  obtain ⟨C, hC, hdec⟩ := psiHat_decay
  refine ⟨4 * C, by positivity, fun ξ => ?_⟩
  have h1 : 0 < 1 + ξ ^ 2 := by positivity
  have ha := abs_nonneg ξ
  have hq : ‖ξ‖ ^ 4 = |ξ| ^ 4 := by rw [Real.norm_eq_abs]
  have h2 : (1 + |ξ|) * (1 + ξ ^ 2) ≤ 4 * (1 + ‖ξ‖ ^ 4) := by
    rw [hq, ← sq_abs ξ]
    nlinarith [sq_nonneg (|ξ| - 1), sq_nonneg (|ξ| ^ 2 - 1), mul_nonneg ha (sq_nonneg (|ξ| - 1)),
      pow_nonneg ha 3, pow_nonneg ha 4]
  have h3 := hdec ξ
  rw [← div_eq_mul_inv, le_div_iff₀ h1]
  calc (1 + |ξ|) * ‖psiHat ξ‖ * (1 + ξ ^ 2) = ‖psiHat ξ‖ * ((1 + |ξ|) * (1 + ξ ^ 2)) := by ring
    _ ≤ ‖psiHat ξ‖ * (4 * (1 + ‖ξ‖ ^ 4)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = 4 * ((1 + ‖ξ‖ ^ 4) * ‖psiHat ξ‖) := by ring
    _ ≤ 4 * C := by linarith

lemma integrable_weighted_psiHat : Integrable (fun ξ : ℝ => (1 + |ξ|) * ‖psiHat ξ‖) := by
  obtain ⟨C, _, hb⟩ := psiHat_bound
  refine (integrable_inv_one_add_sq.const_mul C).mono'
    ((continuous_const.add continuous_abs).mul psiHat_continuous.norm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact hb ξ

lemma psiHat_integrable : Integrable psiHat := by
  refine integrable_weighted_psiHat.mono' psiHat_continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  have := abs_nonneg ξ
  have := norm_nonneg (psiHat ξ)
  nlinarith

/-- **Fourier separation**: `ψ(x) = ∫ ψ̂(ξ) e(ξ x) dξ`. -/
lemma arcCutoff_eq_integral (x : ℝ) :
    ((arcCutoff x : ℝ) : ℂ) = ∫ ξ : ℝ, psiHat ξ * Complex.exp (2 * π * Complex.I * ((ξ * x : ℝ) : ℂ)) := by
  have hinv := L102M.arcC_contDiff.continuous.fourierInv_fourier_eq arcC_integrable psiHat_integrable
  have h := congrFun hinv x
  rw [fourierInv_eq'] at h
  rw [show ((arcCutoff x : ℝ) : ℂ) = L102M.arcC x from rfl, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, psiHat]
  rw [mul_comm]
  have hin : (inner ℝ ξ x : ℝ) = ξ * x := by simp [mul_comm]
  rw [hin]
  congr 2
  push_cast; ring

/-! ## The determinant form with the cutoff -/

open Finset

/-- The integer box `[−A, A] × [−B, B]`. -/
noncomputable def boxZ (A B : ℕ) : Finset (ℤ × ℤ) := Icc (-(A : ℤ)) A ×ˢ Icc (-(B : ℤ)) B

/-- `det(v, w)`. -/
def detI (v w : ℤ × ℤ) : ℤ := v.1 * w.2 - v.2 * w.1

/-- The determinant exponential kernel `e(ϑ det(v, w))`. -/
noncomputable def detKer (ϑ : ℝ) (v w : ℤ × ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ((ϑ * (detI v w : ℝ) : ℝ) : ℂ))

lemma norm_detKer (ϑ : ℝ) (v w : ℤ × ℤ) : ‖detKer ϑ v w‖ = 1 := by
  unfold detKer
  rw [show 2 * π * Complex.I * ((ϑ * (detI v w : ℝ) : ℝ) : ℂ) =
    ((2 * π * (ϑ * detI v w) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The trivial bound `#box`. -/
lemma det_bilBound_triv (A B : ℕ) (ϑ : ℝ) :
    BilBound (boxZ A B) (boxZ A B) (detKer ϑ) (boxZ A B).card := by
  have h := bilBound_schur (boxZ A B) (boxZ A B) (detKer ϑ) (boxZ A B).card (boxZ A B).card
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (fun x _ => by simp [norm_detKer])
    (fun y _ => by simp [norm_detKer])
  rwa [Real.mul_self_sqrt (Nat.cast_nonneg _)] at h

/-- `Iψ = ∫ ‖ψ̂‖`, `Jψ = ∫ (1 + |ξ|) ‖ψ̂‖`. -/
noncomputable def Ipsi : ℝ := ∫ ξ, ‖psiHat ξ‖
noncomputable def Jpsi : ℝ := ∫ ξ, (1 + |ξ|) * ‖psiHat ξ‖

lemma Ipsi_nonneg : 0 ≤ Ipsi := integral_nonneg fun _ => norm_nonneg _
lemma Jpsi_nonneg : 0 ≤ Jpsi := integral_nonneg fun _ => by positivity

/-- **The cutoff determinant form** ([21] (4.30)): if the determinant form is bounded by `N₁` at
every `ϑ` within `T/Y` of `θ`, then the form with kernel `ψ(det/Y) e(θ det)` is bounded by
`N₁ Iψ + #box Jψ / T`. -/
lemma box_psi_bound (A B : ℕ) (Y T θ N₁ : ℝ) (hY : 0 < Y) (hT : 0 < T) (hN₁ : 0 ≤ N₁)
    (hN : ∀ ϑ, |ϑ - θ| ≤ T / Y → BilBound (boxZ A B) (boxZ A B) (detKer ϑ) N₁) :
    BilBound (boxZ A B) (boxZ A B)
      (fun v w => ((arcCutoff ((detI v w : ℝ) / Y) : ℝ) : ℂ) * detKer θ v w)
      (N₁ * Ipsi + (boxZ A B).card * Jpsi / T) := by
  intro g f
  set S := boxZ A B
  have hrep : ∀ v w : ℤ × ℤ, ((arcCutoff ((detI v w : ℝ) / Y) : ℝ) : ℂ) * detKer θ v w =
      ∫ ξ : ℝ, psiHat ξ * detKer (θ + ξ / Y) v w := by
    intro v w
    rw [arcCutoff_eq_integral, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [detKer]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  have hint : ∀ v w : ℤ × ℤ, Integrable (fun ξ : ℝ => psiHat ξ * detKer (θ + ξ / Y) v w) := by
    intro v w
    have hc : Continuous fun ξ : ℝ => detKer (θ + ξ / Y) v w := by unfold detKer; fun_prop
    refine psiHat_integrable.norm.mono' (psiHat_continuous.mul hc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, norm_detKer, mul_one]
  have hbil : bil S S (fun v w => ((arcCutoff ((detI v w : ℝ) / Y) : ℝ) : ℂ) * detKer θ v w) g f =
      ∫ ξ : ℝ, psiHat ξ * bil S S (detKer (θ + ξ / Y)) g f := by
    unfold bil
    simp_rw [hrep, mul_sum]
    rw [integral_finsetSum]
    · refine sum_congr rfl fun v _ => ?_
      rw [integral_finsetSum]
      · refine sum_congr rfl fun w _ => ?_
        rw [← integral_const_mul, ← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp only; ring
      · intro w _
        exact ((hint v w).const_mul ((starRingEnd ℂ) (g v))).mul_const (f w) |>.congr
          (Filter.Eventually.of_forall fun ξ => by simp only; ring)
    · intro v _
      refine integrable_finsetSum _ fun w _ => ?_
      exact ((hint v w).const_mul ((starRingEnd ℂ) (g v))).mul_const (f w) |>.congr
        (Filter.Eventually.of_forall fun ξ => by simp only; ring)
  rw [hbil]
  have hg := l2_nonneg S g
  have hf := l2_nonneg S f
  have hpt : ∀ ξ : ℝ, ‖psiHat ξ * bil S S (detKer (θ + ξ / Y)) g f‖ ≤
      ‖psiHat ξ‖ * (N₁ + S.card * (1 + |ξ|) / T) * (l2 S g * l2 S f) := by
    intro ξ
    rw [norm_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    by_cases hξ : |ξ| ≤ T
    · have h1 : |θ + ξ / Y - θ| ≤ T / Y := by
        rw [add_sub_cancel_left, abs_div, abs_of_pos hY]
        exact div_le_div_of_nonneg_right hξ hY.le
      have h2 := hN _ h1 g f
      have h3 : 0 ≤ S.card * (1 + |ξ|) / T := by positivity
      nlinarith [mul_nonneg hg hf]
    · push Not at hξ
      have h2 := det_bilBound_triv A B (θ + ξ / Y) g f
      have h3 : (S.card : ℝ) ≤ S.card * (1 + |ξ|) / T := by
        rw [le_div_iff₀ hT]
        have : T ≤ 1 + |ξ| := by linarith
        nlinarith [(Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)]
      calc ‖bil S S (detKer (θ + ξ / Y)) g f‖ ≤ S.card * l2 S g * l2 S f := h2
        _ ≤ (S.card * (1 + |ξ|) / T) * (l2 S g * l2 S f) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right h3 (mul_nonneg hg hf)
        _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hg hf)
            linarith
  have hmaj : Integrable (fun ξ : ℝ => ‖psiHat ξ‖ * (N₁ + S.card * (1 + |ξ|) / T) *
      (l2 S g * l2 S f)) := by
    have e : (fun ξ : ℝ => ‖psiHat ξ‖ * (N₁ + S.card * (1 + |ξ|) / T) * (l2 S g * l2 S f)) =
        fun ξ => (N₁ * (l2 S g * l2 S f)) * ‖psiHat ξ‖ +
          (S.card / T * (l2 S g * l2 S f)) * ((1 + |ξ|) * ‖psiHat ξ‖) := by
      funext ξ; ring
    rw [e]
    exact (psiHat_integrable.norm.const_mul _).add (integrable_weighted_psiHat.const_mul _)
  refine (norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
  have e : (fun ξ : ℝ => ‖psiHat ξ‖ * (N₁ + S.card * (1 + |ξ|) / T) * (l2 S g * l2 S f)) =
      fun ξ => (N₁ * (l2 S g * l2 S f)) * ‖psiHat ξ‖ +
        (S.card / T * (l2 S g * l2 S f)) * ((1 + |ξ|) * ‖psiHat ξ‖) := by
    funext ξ; ring
  rw [e, integral_add (psiHat_integrable.norm.const_mul _) (integrable_weighted_psiHat.const_mul _),
    integral_const_mul, integral_const_mul]
  unfold Ipsi Jpsi
  ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: Parseval in the product variable ([21] (4.29)–(4.30))

`parseval`: `∫_{[0,1)} ‖Σ_b c_b e(θ b)‖² dθ = Σ_b ‖c_b‖²`. `minor_form_bound`: the form on
`(positions × products)` with kernel `ψ(det/Y) ∫_𝔪 e(θ(det − b + a)) dθ` is bounded by the
uniform bound `M` of the forms `ψ(det/Y) e(θ det)`, `θ ∈ 𝔪` (Fourier in the product variable
diagonalizes the convolution). -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset MeasureTheory
open scoped ComplexConjugate

/-- `e(t) = exp(2πit)` (complex form). -/
noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (t : ℂ))

lemma eC_add (s t : ℝ) : eC (s + t) = eC s * eC t := by
  unfold eC; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma conj_eC (t : ℝ) : conj (eC t) = eC (-t) := by
  unfold eC; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

lemma continuous_eC_mul (c : ℝ) : Continuous fun θ : ℝ => eC (θ * c) := by
  unfold eC; fun_prop

/-- The trigonometric polynomial `Σ_b c_b e(θ b)`. -/
noncomputable def trig (N : Finset ℤ) (c : ℤ → ℂ) (θ : ℝ) : ℂ := ∑ b ∈ N, c b * eC (θ * b)

lemma continuous_trig (N : Finset ℤ) (c : ℤ → ℂ) : Continuous (trig N c) := by
  unfold trig
  exact continuous_finsetSum _ fun b _ => continuous_const.mul (continuous_eC_mul _)

lemma integral_eC_int (n : ℤ) : ∫ θ in Set.Ico (0 : ℝ) 1, eC (θ * n) = if n = 0 then 1 else 0 := by
  have := L102D.integral_Ico_exp_int n
  unfold eC; exact this

lemma integrableOn_Ico_of_continuous {f : ℝ → ℂ} (hf : Continuous f) :
    IntegrableOn f (Set.Ico (0 : ℝ) 1) :=
  (hf.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self

lemma integrableOn_Ico_of_continuous_real {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f (Set.Ico (0 : ℝ) 1) :=
  (hf.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self

/-- **Parseval** for trigonometric polynomials. -/
lemma parseval (N : Finset ℤ) (c : ℤ → ℂ) :
    ∫ θ in Set.Ico (0 : ℝ) 1, ‖trig N c θ‖ ^ 2 = ∑ b ∈ N, ‖c b‖ ^ 2 := by
  have hC : ((∫ θ in Set.Ico (0 : ℝ) 1, ‖trig N c θ‖ ^ 2 : ℝ) : ℂ) =
      ((∑ b ∈ N, ‖c b‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    have hpt : ∀ θ : ℝ, ((‖trig N c θ‖ ^ 2 : ℝ) : ℂ) =
        ∑ b ∈ N, ∑ b' ∈ N, c b * conj (c b') * eC (θ * ((b - b' : ℤ) : ℝ)) := by
      intro θ
      rw [show ((‖trig N c θ‖ ^ 2 : ℝ) : ℂ) = trig N c θ * conj (trig N c θ) by
        rw [Complex.mul_conj']; push_cast; rfl]
      unfold trig
      rw [map_sum, sum_mul_sum]
      refine sum_congr rfl fun b _ => sum_congr rfl fun b' _ => ?_
      rw [map_mul, conj_eC, show θ * ((b - b' : ℤ) : ℝ) = θ * b + -(θ * b') by push_cast; ring,
        eC_add]
      ring
    simp_rw [hpt]
    rw [integral_finsetSum, Complex.ofReal_sum]
    · refine sum_congr rfl fun b hb => ?_
      rw [integral_finsetSum]
      · rw [sum_eq_single b]
        · rw [integral_const_mul, integral_eC_int (b - b), if_pos (sub_self b), mul_one,
            Complex.mul_conj']
          push_cast; ring
        · intro b' _ hne
          rw [integral_const_mul, integral_eC_int (b - b'), if_neg (sub_ne_zero.2 (Ne.symm hne)),
            mul_zero]
        · intro h; exact absurd hb h
      · intro b' _
        exact (integrableOn_Ico_of_continuous (continuous_eC_mul _)).const_mul _
    · intro b _
      exact integrable_finsetSum _ fun b' _ =>
        (integrableOn_Ico_of_continuous (continuous_eC_mul _)).const_mul _
  exact_mod_cast hC

/-- An elementary Cauchy–Schwarz: `X ≤ (t a + b/t)/2` for all `t > 0` gives `X ≤ √a √b`. -/
lemma le_sqrt_mul_of_forall (X a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → X ≤ (t * a + b / t) / 2) : X ≤ √a * √b := by
  rcases ha.eq_or_lt with ha0 | hapos
  · -- `a = 0`: `X ≤ b/(2t)` for all `t`
    rw [← ha0, Real.sqrt_zero, zero_mul]
    by_contra hX
    push Not at hX
    have := h ((b + 1) / X) (by positivity)
    rw [← ha0, mul_zero, zero_add] at this
    have e : b / ((b + 1) / X) / 2 = b * X / (2 * (b + 1)) := by field_simp
    rw [e, le_div_iff₀ (by positivity)] at this
    nlinarith
  · rcases hb.eq_or_lt with hb0 | hbpos
    · rw [← hb0, Real.sqrt_zero, mul_zero]
      by_contra hX
      push Not at hX
      have := h (X / (a + 1)) (by positivity)
      rw [← hb0, zero_div, add_zero] at this
      have e : X / (a + 1) * a / 2 = X * a / (2 * (a + 1)) := by field_simp
      rw [e, le_div_iff₀ (by positivity)] at this
      nlinarith
    · have hsa := Real.sqrt_pos.2 hapos
      have hsb := Real.sqrt_pos.2 hbpos
      have := h (√b / √a) (by positivity)
      have e1 : √b / √a * a = √a * √b := by
        rw [div_mul_eq_mul_div, mul_div_assoc, Real.div_sqrt]; ring
      have e2 : b / (√b / √a) = √a * √b := by
        rw [div_div_eq_mul_div, mul_div_right_comm, Real.div_sqrt]; ring
      rw [e1, e2] at this
      linarith

/-- Cauchy–Schwarz for set integrals of nonnegative continuous functions. -/
lemma setIntegral_mul_le (s : Set ℝ) (_hs : MeasurableSet s) (hsub : s ⊆ Set.Ico 0 1)
    (φ χ : ℝ → ℝ) (hφ : Continuous φ) (hχ : Continuous χ) (hφ0 : ∀ θ, 0 ≤ φ θ)
    (hχ0 : ∀ θ, 0 ≤ χ θ) :
    ∫ θ in s, φ θ * χ θ ≤ √(∫ θ in Set.Ico (0 : ℝ) 1, φ θ ^ 2) *
      √(∫ θ in Set.Ico (0 : ℝ) 1, χ θ ^ 2) := by
  have hI1 : IntegrableOn (fun θ => φ θ * χ θ) (Set.Ico (0 : ℝ) 1) :=
    integrableOn_Ico_of_continuous_real (hφ.mul hχ)
  have hI2 : IntegrableOn (fun θ => φ θ ^ 2) (Set.Ico (0 : ℝ) 1) :=
    integrableOn_Ico_of_continuous_real (hφ.pow 2)
  have hI3 : IntegrableOn (fun θ => χ θ ^ 2) (Set.Ico (0 : ℝ) 1) :=
    integrableOn_Ico_of_continuous_real (hχ.pow 2)
  have hmono : ∫ θ in s, φ θ * χ θ ≤ ∫ θ in Set.Ico (0 : ℝ) 1, φ θ * χ θ :=
    setIntegral_mono_set hI1 (Filter.Eventually.of_forall fun θ => mul_nonneg (hφ0 θ) (hχ0 θ))
      (Filter.Eventually.of_forall hsub)
  refine hmono.trans (le_sqrt_mul_of_forall _ _ _ (setIntegral_nonneg measurableSet_Ico
    fun θ _ => sq_nonneg _) (setIntegral_nonneg measurableSet_Ico fun θ _ => sq_nonneg _) ?_)
  intro t ht
  have hpt : ∀ θ, φ θ * χ θ ≤ (t * φ θ ^ 2 + χ θ ^ 2 / t) / 2 := by
    intro θ
    have : 0 ≤ (t * φ θ - χ θ) ^ 2 / t := by positivity
    have e : (t * φ θ ^ 2 + χ θ ^ 2 / t) / 2 - φ θ * χ θ = (t * φ θ - χ θ) ^ 2 / (2 * t) := by
      field_simp; ring
    nlinarith [div_nonneg (sq_nonneg (t * φ θ - χ θ)) (by positivity : (0 : ℝ) ≤ 2 * t)]
  calc ∫ θ in Set.Ico (0 : ℝ) 1, φ θ * χ θ ≤
      ∫ θ in Set.Ico (0 : ℝ) 1, (t * φ θ ^ 2 + χ θ ^ 2 / t) / 2 :=
        setIntegral_mono hI1 (integrableOn_Ico_of_continuous_real (by fun_prop)) hpt
    _ = _ := by
        rw [integral_div, integral_add (hI2.const_mul t) (hI3.div_const t), integral_const_mul,
          integral_div]

/-- The vector of trigonometric polynomials `v ↦ Σ_b G(v, b) e(θ b)`. -/
noncomputable def trigV (N : Finset ℤ) (G : (ℤ × ℤ) × ℤ → ℂ) (θ : ℝ) (v : ℤ × ℤ) : ℂ :=
  trig N (fun b => G (v, b)) θ

lemma l2_trigV_sq_integral (S : Finset (ℤ × ℤ)) (N : Finset ℤ) (G : (ℤ × ℤ) × ℤ → ℂ) :
    ∫ θ in Set.Ico (0 : ℝ) 1, l2 S (trigV N G θ) ^ 2 = l2 (S ×ˢ N) G ^ 2 := by
  simp only [l2_sq]
  rw [integral_finsetSum]
  · rw [sum_product]
    refine sum_congr rfl fun v _ => ?_
    exact parseval N (fun b => G (v, b))
  · intro v _
    exact integrableOn_Ico_of_continuous_real ((continuous_trig _ _).norm.pow 2)

lemma continuous_l2_trigV (S : Finset (ℤ × ℤ)) (N : Finset ℤ) (G : (ℤ × ℤ) × ℤ → ℂ) :
    Continuous fun θ => l2 S (trigV N G θ) := by
  unfold l2
  exact (continuous_finsetSum _ fun v _ => ((continuous_trig _ _).norm.pow 2)).sqrt

/-- **The minor-arc form**: Fourier in the product variable. -/
theorem minor_form_bound (S : Finset (ℤ × ℤ)) (N : Finset ℤ) (L : ℝ → (ℤ × ℤ) → (ℤ × ℤ) → ℂ)
    (Dt : (ℤ × ℤ) → (ℤ × ℤ) → ℤ) (hLc : ∀ v w, Continuous fun θ => L θ v w)
    (hLe : ∀ θ v w, L θ v w = L 0 v w * eC (θ * Dt v w))
    (𝔪 : Set ℝ) (h𝔪 : MeasurableSet 𝔪) (hsub : 𝔪 ⊆ Set.Ico 0 1) (M : ℝ) (hM : 0 ≤ M)
    (hθ : ∀ θ ∈ 𝔪, BilBound S S (L θ) M) :
    BilBound (S ×ˢ N) (S ×ˢ N)
      (fun p q => L 0 p.1 q.1 * ∫ θ in 𝔪, eC (θ * ((Dt p.1 q.1 - p.2 + q.2 : ℤ) : ℝ))) M := by
  intro G F
  -- rewrite the form as an integral over `𝔪`
  have hbil : bil (S ×ˢ N) (S ×ˢ N)
      (fun p q => L 0 p.1 q.1 * ∫ θ in 𝔪, eC (θ * ((Dt p.1 q.1 - p.2 + q.2 : ℤ) : ℝ))) G F =
      ∫ θ in 𝔪, bil S S (L θ) (trigV N G θ) (trigV N F θ) := by
    have hint : ∀ p q : (ℤ × ℤ) × ℤ, IntegrableOn
        (fun θ => conj (G p) * L 0 p.1 q.1 * eC (θ * ((Dt p.1 q.1 - p.2 + q.2 : ℤ) : ℝ)) * F q)
        𝔪 := by
      intro p q
      exact (integrableOn_Ico_of_continuous ((continuous_const.mul (continuous_eC_mul _)).mul
        continuous_const)).mono_set hsub
    have lhs : bil (S ×ˢ N) (S ×ˢ N)
        (fun p q => L 0 p.1 q.1 * ∫ θ in 𝔪, eC (θ * ((Dt p.1 q.1 - p.2 + q.2 : ℤ) : ℝ))) G F =
        ∫ θ in 𝔪, ∑ p ∈ S ×ˢ N, ∑ q ∈ S ×ˢ N,
          conj (G p) * L 0 p.1 q.1 * eC (θ * ((Dt p.1 q.1 - p.2 + q.2 : ℤ) : ℝ)) * F q := by
      unfold bil
      rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hint p q]
      refine sum_congr rfl fun p _ => ?_
      rw [integral_finsetSum _ fun q _ => hint p q]
      refine sum_congr rfl fun q _ => ?_
      beta_reduce
      rw [← mul_assoc, ← integral_const_mul, ← integral_mul_const]
    rw [lhs]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only
    unfold bil trigV trig
    rw [sum_product, sum_comm]
    simp only [sum_product]
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    simp only [map_sum, sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun w _ => sum_congr rfl fun a _ => ?_
    rw [hLe θ, map_mul, conj_eC,
      show ∀ (D x y : ℤ), θ * ((D - x + y : ℤ) : ℝ) = θ * D + (-(θ * x) + θ * y) from
        fun D x y => by push_cast; ring,
      eC_add, eC_add]
    ring
  rw [hbil]
  have hcont : Continuous fun θ => bil S S (L θ) (trigV N G θ) (trigV N F θ) := by
    unfold bil trigV
    refine continuous_finsetSum _ fun v _ => continuous_finsetSum _ fun w _ => ?_
    exact (((continuous_trig _ _).star).mul (hLc v w)).mul (continuous_trig _ _)
  have hpt : ∀ θ ∈ 𝔪, ‖bil S S (L θ) (trigV N G θ) (trigV N F θ)‖ ≤
      M * (l2 S (trigV N G θ) * l2 S (trigV N F θ)) := fun θ hθm => by
    rw [← mul_assoc]; exact hθ θ hθm _ _
  have hcR : Continuous fun θ => M * (l2 S (trigV N G θ) * l2 S (trigV N F θ)) :=
    continuous_const.mul ((continuous_l2_trigV S N G).mul (continuous_l2_trigV S N F))
  calc ‖∫ θ in 𝔪, bil S S (L θ) (trigV N G θ) (trigV N F θ)‖ ≤
      ∫ θ in 𝔪, ‖bil S S (L θ) (trigV N G θ) (trigV N F θ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ in 𝔪, M * (l2 S (trigV N G θ) * l2 S (trigV N F θ)) :=
        setIntegral_mono_on ((integrableOn_Ico_of_continuous_real hcont.norm).mono_set hsub)
          ((integrableOn_Ico_of_continuous_real hcR).mono_set hsub) h𝔪 hpt
    _ = M * ∫ θ in 𝔪, l2 S (trigV N G θ) * l2 S (trigV N F θ) := integral_const_mul _ _
    _ ≤ M * (√(∫ θ in Set.Ico (0 : ℝ) 1, l2 S (trigV N G θ) ^ 2) *
          √(∫ θ in Set.Ico (0 : ℝ) 1, l2 S (trigV N F θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (setIntegral_mul_le 𝔪 h𝔪 hsub _ _
          (continuous_l2_trigV S N G) (continuous_l2_trigV S N F) (fun θ => l2_nonneg _ _)
          (fun θ => l2_nonneg _ _)) hM
    _ = M * l2 (S ×ˢ N) G * l2 (S ×ˢ N) F := by
        rw [l2_trigV_sq_integral, l2_trigV_sq_integral, Real.sqrt_sq (l2_nonneg _ _),
          Real.sqrt_sq (l2_nonneg _ _)]; ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: the clean signed bound on the box ([21] (4.29)–(4.34))

* `minor_dirichlet`: for `θ ∈ [0,1) ∖ 𝔐` and `|ϑ − θ| ≤ L^{A₀}/(2Y)`, a reduced `c/d` with
  `L^{A₀} < d ≤ Q = ⌈Y/L^{A₀}⌉` and `|ϑ − c/d| ≤ 1/(dQ)` ((4.31));
* `box_minor_bound`: on `box × products`, the form with kernel
  `ψ(det/Y) ∫_𝔪 e(θ(det − b + a)) dθ` (= `minorKernel (det) a b`) is bounded by
  `Mbox = Y (32C₁+40)(L^{−A₀} + Y^{−0.1})(1 + log 2Y) Iψ + 2 #box Jψ / L^{A₀}`. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset MeasureTheory

/-- D6 with the constant of `det_bilinear_bound`. -/
lemma det_bilBound2 (A B d : ℕ) (hd : 1 ≤ d) (c : ℤ) (hc : IsCoprime c (d : ℤ)) (Q ϑ : ℝ)
    (hQ : (d : ℝ) ≤ Q) (hϑ : |ϑ - c / d| ≤ 1 / (d * Q)) :
    BilBound (boxZ A B) (boxZ A B) (detKer ϑ)
      (2 * (8 * A / d + 1) * (2 * B + 1 + d * (1 + Real.log d))) := by
  intro g f
  have h := det_bilinear_bound A B d hd c hc Q ϑ hQ hϑ (fun v => (starRingEnd ℂ) (g v)) f
  unfold bil l2 boxZ detKer detI
  simp only [Complex.norm_conj] at h
  push_cast at h ⊢
  exact h

/-- **Minor arcs give large denominators** ([21] (4.31)). -/
lemma minor_dirichlet (x A₀ Y θ ϑ : ℝ) (hY : 0 < Y) (hP : 1 ≤ log x ^ A₀)
    (hθ : θ ∈ Set.Ico (0 : ℝ) 1 \ majorArcs x A₀ Y) (hϑ : |ϑ - θ| ≤ log x ^ A₀ / (2 * Y)) :
    ∃ (c : ℤ) (d : ℕ), IsCoprime c (d : ℤ) ∧ log x ^ A₀ < d ∧ (d : ℝ) ≤ ⌈Y / log x ^ A₀⌉₊ ∧
      |ϑ - c / d| ≤ 1 / (d * ⌈Y / log x ^ A₀⌉₊) := by
  set P := log x ^ A₀
  set Q := ⌈Y / P⌉₊
  have hPpos : 0 < P := by linarith
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  obtain ⟨c, d, hc, hd1, hdQ, hcd⟩ := dirichlet_reduced ϑ Q hQ1
  refine ⟨c, d, hc, ?_, by exact_mod_cast hdQ, hcd⟩
  by_contra hdP
  push Not at hdP
  apply hθ.2
  refine ⟨hθ.1.1, hθ.1.2, d, hd1, hdP, c, ?_, ?_⟩
  · exact Int.isCoprime_iff_gcd_eq_one.1 hc
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hQR : Y / P ≤ (Q : ℝ) := Nat.le_ceil _
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
    have h1 : 1 / ((d : ℝ) * Q) ≤ P / Y := by
      rw [div_le_div_iff₀ (by positivity) hY, one_mul]
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      have h2 : Y ≤ P * Q := by rwa [div_le_iff₀ hPpos, mul_comm] at hQR
      nlinarith
    calc |θ - c / d| ≤ |θ - ϑ| + |ϑ - c / d| := abs_sub_le _ _ _
      _ ≤ P / (2 * Y) + P / Y := by rw [abs_sub_comm]; exact add_le_add hϑ (hcd.trans h1)
      _ ≤ 2 * P / Y := by
          have : P / (2 * Y) ≤ P / Y := div_le_div_of_nonneg_left hPpos.le hY (by linarith)
          rw [show 2 * P / Y = P / Y + P / Y by ring]; linarith

/-- The constant of the box bound. -/
noncomputable def Mbox (x A₀ Y C₁ : ℝ) (A B : ℕ) : ℝ :=
  Y * ((32 * C₁ + 40) * (1 / log x ^ A₀ + Y ^ (-0.1 : ℝ)) * (1 + Real.log (2 * Y))) * Ipsi +
    (boxZ A B).card * Jpsi / (log x ^ A₀ / 2)

/-- **The clean bound on the box.** -/
theorem box_minor_bound (x A₀ Y C₁ : ℝ) (A B : ℕ) (hY : 1 ≤ Y) (hP : 1 ≤ log x ^ A₀)
    (hAB : (A : ℝ) * B ≤ C₁ * Y) (hA : (A : ℝ) ≤ Y ^ (0.9 : ℝ)) (hB : (B : ℝ) ≤ Y ^ (0.9 : ℝ))
    (N : Finset ℤ) :
    BilBound (boxZ A B ×ˢ N) (boxZ A B ×ˢ N)
      (fun p q => minorKernel x A₀ Y (detI p.1 q.1) q.2 p.2) (Mbox x A₀ Y C₁ A B) := by
  have hY0 : (0 : ℝ) < Y := by linarith
  set P := log x ^ A₀
  have hPpos : 0 < P := by linarith
  set N₁ := Y * ((32 * C₁ + 40) * (1 / P + Y ^ (-0.1 : ℝ)) * (1 + Real.log (2 * Y)))
  have hC₁ : 0 ≤ C₁ := by
    have : (0 : ℝ) ≤ A * B := by positivity
    nlinarith
  have hN₁ : 0 ≤ N₁ := by
    have : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
    have : 0 ≤ Y ^ (-0.1 : ℝ) := Real.rpow_nonneg hY0.le _
    positivity
  set L : ℝ → (ℤ × ℤ) → (ℤ × ℤ) → ℂ := fun θ v w =>
    ((arcCutoff ((detI v w : ℝ) / Y) : ℝ) : ℂ) * detKer θ v w
  set 𝔪 := Set.Ico (0 : ℝ) 1 \ majorArcs x A₀ Y
  have hθ : ∀ θ ∈ 𝔪, BilBound (boxZ A B) (boxZ A B) (L θ)
      (N₁ * Ipsi + (boxZ A B).card * Jpsi / (P / 2)) := by
    intro θ hθm
    refine box_psi_bound A B Y (P / 2) θ N₁ hY0 (by positivity) hN₁ fun ϑ hϑ => ?_
    have hϑ' : |ϑ - θ| ≤ P / (2 * Y) := by
      rw [show P / (2 * Y) = P / 2 / Y by ring]; exact hϑ
    obtain ⟨c, d, hc, hPd, hdQ, hcd⟩ := minor_dirichlet x A₀ Y θ ϑ hY0 hP hθm hϑ'
    have hd1 : 1 ≤ d := by
      have : (1 : ℝ) < d := lt_of_le_of_lt hP hPd
      exact_mod_cast this.le
    refine bilBound_mono _ _ _ _ _ ?_ (det_bilBound2 A B d hd1 c hc _ ϑ hdQ hcd)
    have hQY : (⌈Y / P⌉₊ : ℝ) ≤ Y / P + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have := det_bound_div A B d hd1 Y P ⌈Y / P⌉₊ C₁ hY hP hPd.le hdQ hQY hAB hA hB
    rw [div_le_iff₀ hY0] at this
    simp only [N₁]
    linarith
  have hmain := minor_form_bound (boxZ A B) N L detI
    (fun v w => by simp only [L, detKer]; fun_prop)
    (fun θ v w => by
      simp only [L, detKer, eC]
      rw [show (0 : ℝ) * (detI v w : ℝ) = 0 by ring]
      simp)
    𝔪 ((measurableSet_Ico).diff (L102D.measurableSet_majorArcs x A₀ Y))
    Set.sdiff_subset _ (by have := Ipsi_nonneg; have := Jpsi_nonneg; positivity) hθ
  refine bilBound_congr _ _ _ _ _ (fun p _ q _ => ?_) hmain
  simp only [L, minorKernel, detKer, eC]
  rw [show (0 : ℝ) * (detI p.1 q.1 : ℝ) = 0 by ring]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  push_cast; ring_nf

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: the lattice box ([21] (4.26)–(4.27))

Let `q(h, l) = (h + lα)² + (l/Y)²`, the squared length of the image of `(h, l)` under
`(h, l) ↦ (h + lα, l/Y)` (a lattice of covolume `1/Y`). Under the Diophantine condition
`‖lα‖ > Y^{−0.7}` for `1 ≤ l ≤ Y^{0.2}` (test (i) of the good states; `‖·‖ = |· − round ·|`):

* `qf_ge`: every nonzero integer vector has `q ≥ Y^{−1.6}` (shortest vector `≥ Y^{−0.8}`);
* `lattice_box_core`: there is a basis `(p, r), (q, s)` of `ℤ²` with `ps − qr = 1` and reals `a, b`
  with `a² ≤ 4c₀²Y^{1.6}`, `b² ≤ 4c₀²Y`, `ab ≤ 3c₀²Y`, such that every `(h, l)` with
  `|l| ≤ c₀Y`, `|h + lα| ≤ c₀` is `x(p, r) + y(q, s)` with `|x| ≤ a`, `|y| ≤ b`.
  (Dirichlet gives a primitive vector with `q ≤ 2/Y`; Bezout and one size-reduction step give the
  second vector; Lagrange's identity bounds the coordinates.)
* `lattice_box` (**D6, lattice part**): for `Y ≥ (2c₀ + 2)^{10}`, natural `A', B'` with
  `A'B' ≤ (3c₀² + 8c₀ + 4)Y` and `Y^{0.1} ≤ A', B' ≤ Y^{0.9}`, and the same covering.
* `lattice_box_SL`: the same with `γ ∈ SL₂(ℤ)`, and `det_transform`: `det(γu, γu') = det(u, u')`.
-/

namespace ArtinPrimitiveRoots.L102G

open Real

/-- The quadratic form `q(h, l) = (h + lα)² + (l/Y)²`. -/
noncomputable def qf (Y α : ℝ) (h l : ℤ) : ℝ := (h + l * α) ^ 2 + (l / Y) ^ 2

/-- Its polar form. -/
noncomputable def ipf (Y α : ℝ) (h₁ l₁ h₂ l₂ : ℤ) : ℝ :=
  (h₁ + l₁ * α) * (h₂ + l₂ * α) + (l₁ / Y) * (l₂ / Y)

/-- Lagrange's identity: `q(v) q(w) = ⟨v, w⟩² + (det(v, w)/Y)²`. -/
lemma lagrange (Y α : ℝ) (hY : Y ≠ 0) (h₁ l₁ h₂ l₂ : ℤ) :
    qf Y α h₁ l₁ * qf Y α h₂ l₂ =
      ipf Y α h₁ l₁ h₂ l₂ ^ 2 + (((h₁ * l₂ - l₁ * h₂ : ℤ) : ℝ) / Y) ^ 2 := by
  unfold qf ipf; push_cast; field_simp; ring

lemma qf_nonneg (Y α : ℝ) (h l : ℤ) : 0 ≤ qf Y α h l := by unfold qf; positivity

lemma rpow_tenth (Y : ℝ) (hY : 0 ≤ Y) (n : ℕ) : Y ^ ((n : ℝ) / 10) = (Y ^ (0.1 : ℝ)) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hY]; congr 1; norm_num; ring

/-- The shortest vector is at least `Y^{−0.8}`: `q(h, l) ≥ Y^{−1.6}` for `(h, l) ≠ 0`. -/
lemma qf_ge (Y α : ℝ) (hY : 1 ≤ Y)
    (hdio : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (0.2 : ℝ) → Y ^ (-0.7 : ℝ) < |l * α - round (l * α)|)
    (h l : ℤ) (hne : ¬ (h = 0 ∧ l = 0)) : Y ^ (-1.6 : ℝ) ≤ qf Y α h l := by
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  set t := Y ^ (0.1 : ℝ) with ht
  have ht1 : 1 ≤ t := Real.one_le_rpow hY (by norm_num)
  have e2 : Y ^ (0.2 : ℝ) = t ^ 2 := by
    rw [show (0.2 : ℝ) = ((2 : ℕ) : ℝ) / 10 by norm_num, rpow_tenth Y hY0]
  have e7 : Y ^ (-0.7 : ℝ) = (t ^ 7)⁻¹ := by
    rw [Real.rpow_neg hY0, show (0.7 : ℝ) = ((7 : ℕ) : ℝ) / 10 by norm_num, rpow_tenth Y hY0]
  have e16 : Y ^ (-1.6 : ℝ) = (t ^ 16)⁻¹ := by
    rw [Real.rpow_neg hY0, show (1.6 : ℝ) = ((16 : ℕ) : ℝ) / 10 by norm_num, rpow_tenth Y hY0]
  have e10 : Y = t ^ 10 := by
    rw [← rpow_tenth Y hY0]; norm_num
  rw [e16]
  have ht16 : (t ^ 16)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ht1)
  unfold qf
  by_cases hl : l = 0
  · have hh : h ≠ 0 := fun hh => hne ⟨hh, hl⟩
    subst hl
    have : (1 : ℝ) ≤ (h : ℝ) ^ 2 := by
      have := Int.one_le_abs hh
      have h1 : (1 : ℝ) ≤ |(h : ℝ)| := by exact_mod_cast this
      nlinarith [abs_mul_abs_self (h : ℝ), abs_nonneg (h : ℝ)]
    simp only [Int.cast_zero, zero_mul, add_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    linarith
  · have hlabs : (1 : ℝ) ≤ |(l : ℝ)| := by
      have := Int.one_le_abs hl; exact_mod_cast this
    by_cases hsmall : |(l : ℝ)| ≤ t ^ 2
    · -- the Diophantine test applies to `|l|`
      have hn1 : 1 ≤ l.natAbs := by omega
      have hncast : ((l.natAbs : ℕ) : ℝ) = |(l : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have hd := hdio l.natAbs hn1 (by rw [hncast, e2]; exact hsmall)
      rw [hncast, e7] at hd
      have hge : |(|(l : ℝ)| * α - round (|(l : ℝ)| * α))| ≤ |(h : ℝ) + l * α| := by
        rcases le_or_gt 0 l with hl0 | hl0
        · have : |(l : ℝ)| = l := abs_of_nonneg (by exact_mod_cast hl0)
          rw [this]
          have := round_le ((l : ℝ) * α) (-h)
          rw [show (l : ℝ) * α - ((-h : ℤ) : ℝ) = h + l * α by push_cast; ring] at this
          exact this
        · have : |(l : ℝ)| = -l := abs_of_neg (by exact_mod_cast hl0)
          rw [this]
          have := round_le (-(l : ℝ) * α) h
          rw [show -(l : ℝ) * α - (h : ℝ) = -(h + l * α) by ring, abs_neg] at this
          exact this
      have h7 : (t ^ 7)⁻¹ < |(h : ℝ) + l * α| := lt_of_lt_of_le hd hge
      have h7pos : 0 < (t ^ 7)⁻¹ := by positivity
      have hsq : ((t ^ 7)⁻¹) ^ 2 < ((h : ℝ) + l * α) ^ 2 := by
        rw [← sq_abs ((h : ℝ) + l * α)]
        exact pow_lt_pow_left₀ h7 h7pos.le (by norm_num)
      have : (t ^ 16)⁻¹ ≤ ((t ^ 7)⁻¹) ^ 2 := by
        rw [inv_pow, ← pow_mul]
        apply inv_anti₀ (by positivity)
        exact pow_le_pow_right₀ ht1 (by norm_num)
      nlinarith [sq_nonneg ((l : ℝ) / Y)]
    · push Not at hsmall
      have htpos : 0 < t := by linarith
      have hl2 : (t ^ 2) ^ 2 < (l : ℝ) ^ 2 := by
        rw [← sq_abs (l : ℝ)]
        exact pow_lt_pow_left₀ hsmall (by positivity) (by norm_num)
      have : (t ^ 16)⁻¹ < ((l : ℝ) / Y) ^ 2 := by
        rw [div_pow, e10, ← pow_mul, lt_div_iff₀ (by positivity)]
        rw [show (t ^ 16)⁻¹ * t ^ (10 * 2) = t ^ 4 by
          rw [show 10 * 2 = 16 + 4 by norm_num, pow_add]; field_simp]
        calc t ^ 4 = (t ^ 2) ^ 2 := by ring
          _ < _ := hl2
      nlinarith [sq_nonneg ((h : ℝ) + l * α)]

/-- **The lattice box, explicit form** ([21] (4.26)–(4.27)). -/
theorem lattice_box_core (Y α c₀ : ℝ) (hY : 1 ≤ Y)
    (hdio : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (0.2 : ℝ) → Y ^ (-0.7 : ℝ) < |l * α - round (l * α)|) :
    ∃ p q r s : ℤ, p * s - q * r = 1 ∧ ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      a ^ 2 ≤ 4 * c₀ ^ 2 * Y ^ (1.6 : ℝ) ∧ b ^ 2 ≤ 4 * c₀ ^ 2 * Y ∧ a * b ≤ 3 * c₀ ^ 2 * Y ∧
      ∀ h l : ℤ, |(l : ℝ)| ≤ c₀ * Y → |h + l * α| ≤ c₀ →
        ∃ x y : ℤ, |(x : ℝ)| ≤ a ∧ |(y : ℝ)| ≤ b ∧ h = p * x + q * y ∧ l = r * x + s * y := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have hY0 : Y ≠ 0 := hYpos.ne'
  -- Step 1: Dirichlet, a vector with `q ≤ 2/Y`
  set n := ⌊√Y⌋₊ with hn
  have hsY : 1 ≤ √Y := by rw [Real.one_le_sqrt]; exact hY
  have hn1 : 0 < n := Nat.floor_pos.mpr hsY
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α hn1
  have hnle : (n : ℝ) ≤ √Y := Nat.floor_le (Real.sqrt_nonneg _)
  have hnlt : √Y < n + 1 := Nat.lt_floor_add_one _
  have hsq : √Y * √Y = Y := Real.mul_self_sqrt hYpos.le
  have hq0 : qf Y α (-j) k ≤ 2 / Y := by
    unfold qf
    have h1 : ((-j : ℤ) + k * α : ℝ) ^ 2 ≤ 1 / Y := by
      have e : ((-j : ℤ) + k * α : ℝ) = k * α - j := by push_cast; ring
      rw [e, ← sq_abs]
      have h2 : |(k : ℝ) * α - j| ≤ 1 / √Y := hjk.trans (by
        apply one_div_le_one_div_of_le (by positivity); linarith)
      calc |(k : ℝ) * α - j| ^ 2 ≤ (1 / √Y) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
        _ = 1 / Y := by rw [div_pow, Real.sq_sqrt hYpos.le]; ring
    have h3 : ((k : ℝ) / Y) ^ 2 ≤ 1 / Y := by
      have hk : (k : ℝ) ≤ √Y := le_trans (by exact_mod_cast hkn) hnle
      have hk0' : (0 : ℝ) ≤ k := by exact_mod_cast hk0.le
      rw [div_pow, div_le_div_iff₀ (by positivity) hYpos]
      nlinarith [mul_le_mul hk hk hk0' (Real.sqrt_nonneg Y)]
    have : (2 : ℝ) / Y = 1 / Y + 1 / Y := by ring
    linarith
  -- Step 2: make it primitive
  set g : ℕ := Int.gcd j k with hg
  have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_right j hk0.ne'
  set h₁ : ℤ := -(j / g)
  set l₁ : ℤ := k / g
  have hj : j = -((g : ℤ) * h₁) := by
    simp only [h₁, mul_neg, neg_neg]; exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left j k)).symm
  have hk : k = (g : ℤ) * l₁ := (Int.mul_ediv_cancel' (Int.gcd_dvd_right j k)).symm
  have hprim : Int.gcd h₁ l₁ = 1 := by
    simp only [h₁, l₁, Int.neg_gcd]; exact Int.gcd_ediv_gcd_ediv_gcd hgpos
  have hl₁ : l₁ ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hk; exact hk0.ne' hk
  have hq1 : qf Y α h₁ l₁ ≤ 2 / Y := by
    refine le_trans ?_ hq0
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hgpos
    have e : qf Y α (-j) k = (g : ℝ) ^ 2 * qf Y α h₁ l₁ := by
      unfold qf
      have ej : ((-j : ℤ) : ℝ) = g * h₁ := by
        rw [hj]; push_cast; ring
      have ek : ((k : ℤ) : ℝ) = g * l₁ := by
        rw [hk]; push_cast; ring
      rw [ej, ek]; ring
    rw [e]
    calc qf Y α h₁ l₁ = 1 * qf Y α h₁ l₁ := (one_mul _).symm
      _ ≤ (g : ℝ) ^ 2 * qf Y α h₁ l₁ :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hg1) (qf_nonneg Y α h₁ l₁)
  -- Step 3: Bezout
  set A₁ := Int.gcdA h₁ l₁
  set B₁ := Int.gcdB h₁ l₁
  have hbez : h₁ * A₁ + l₁ * B₁ = 1 := by
    have := Int.gcd_eq_gcd_ab h₁ l₁
    rw [hprim] at this; simp only [Nat.cast_one] at this; linarith
  -- Step 4: size reduction
  set Q1 := qf Y α h₁ l₁ with hQ1
  have hQ1pos : 0 < Q1 := by
    have : 0 < ((l₁ : ℝ) / Y) ^ 2 := by
      have : (l₁ : ℝ) ≠ 0 := by exact_mod_cast hl₁
      positivity
    simp only [hQ1, qf]; linarith [sq_nonneg ((h₁ : ℝ) + l₁ * α)]
  set κ : ℤ := round (ipf Y α h₁ l₁ (-B₁) A₁ / Q1)
  set h₂ : ℤ := -B₁ - κ * h₁
  set l₂ : ℤ := A₁ - κ * l₁
  have hdet : h₁ * l₂ - l₁ * h₂ = 1 := by simp only [h₂, l₂]; linear_combination hbez
  have hip : ipf Y α h₁ l₁ h₂ l₂ =
      Q1 * (ipf Y α h₁ l₁ (-B₁) A₁ / Q1 - κ) := by
    rw [mul_sub, mul_div_cancel₀ _ hQ1pos.ne']
    simp only [hQ1, qf, ipf, h₂, l₂]; push_cast; ring
  have hip2 : ipf Y α h₁ l₁ h₂ l₂ ^ 2 ≤ Q1 ^ 2 / 4 := by
    rw [hip, mul_pow]
    have := abs_sub_round (ipf Y α h₁ l₁ (-B₁) A₁ / Q1)
    have h2 : (ipf Y α h₁ l₁ (-B₁) A₁ / Q1 - κ) ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]
      calc |ipf Y α h₁ l₁ (-B₁) A₁ / Q1 - κ| ^ 2 ≤ (1 / 2) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = 1 / 4 := by norm_num
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg Q1)
    linarith
  set Q2 := qf Y α h₂ l₂ with hQ2
  have hQ2n : 0 ≤ Q2 := qf_nonneg _ _ _ _
  have hQ12 : Q1 * Q2 ≤ 2 / Y ^ 2 := by
    rw [hQ1, hQ2, lagrange Y α hY0, hdet]
    have : Q1 ^ 2 / 4 ≤ 1 / Y ^ 2 := by
      have := hq1
      have h0 := hQ1pos.le
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      have : Q1 * Y ≤ 2 := by rwa [le_div_iff₀ hYpos] at this
      have hQY0 : 0 ≤ Q1 * Y := by positivity
      have := mul_le_mul this this hQY0 (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    push_cast
    rw [div_pow, one_pow]
    have : (2 : ℝ) / Y ^ 2 = 1 / Y ^ 2 + 1 / Y ^ 2 := by ring
    linarith
  -- Step 5: the lower bound
  have hQ1ge : Y ^ (-1.6 : ℝ) ≤ Q1 := qf_ge Y α hY hdio h₁ l₁ (fun h => hl₁ h.2)
  -- the box
  set a := √(2 * c₀ ^ 2 * Y ^ 2 * Q2) with ha
  set b := √(2 * c₀ ^ 2 * Y ^ 2 * Q1) with hb
  have ha2 : a ^ 2 = 2 * c₀ ^ 2 * Y ^ 2 * Q2 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = 2 * c₀ ^ 2 * Y ^ 2 * Q1 := Real.sq_sqrt (by positivity)
  refine ⟨h₁, h₂, l₁, l₂, by linear_combination hdet, a, b, Real.sqrt_nonneg _,
    Real.sqrt_nonneg _, ?_, ?_, ?_, ?_⟩
  · -- a² ≤ 4c₀²Y^{1.6}
    rw [ha2]
    have hprod : 2 * c₀ ^ 2 * Y ^ 2 * Q2 * Q1 ≤ 4 * c₀ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hQ12 (show 0 ≤ 2 * c₀ ^ 2 * Y ^ 2 by positivity)
      have e : 2 * c₀ ^ 2 * Y ^ 2 * (2 / Y ^ 2) = 4 * c₀ ^ 2 := by field_simp; ring
      linarith
    have hY16 : Y ^ (1.6 : ℝ) * Y ^ (-1.6 : ℝ) = 1 := by
      rw [← Real.rpow_add hYpos]; norm_num
    have hpos16 : 0 < Y ^ (1.6 : ℝ) := Real.rpow_pos_of_pos hYpos _
    -- X * Q1 ≤ 4c₀² and Q1 ≥ Y^{-1.6} ⇒ X ≤ 4c₀² Y^{1.6}
    have hX : 0 ≤ 2 * c₀ ^ 2 * Y ^ 2 * Q2 := by positivity
    have : 2 * c₀ ^ 2 * Y ^ 2 * Q2 * Y ^ (-1.6 : ℝ) ≤ 4 * c₀ ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_left hQ1ge hX) hprod
    calc 2 * c₀ ^ 2 * Y ^ 2 * Q2 = 2 * c₀ ^ 2 * Y ^ 2 * Q2 * Y ^ (-1.6 : ℝ) * Y ^ (1.6 : ℝ) := by
          rw [mul_assoc _ (Y ^ (-1.6 : ℝ)), mul_comm (Y ^ (-1.6 : ℝ)), hY16, mul_one]
      _ ≤ 4 * c₀ ^ 2 * Y ^ (1.6 : ℝ) := mul_le_mul_of_nonneg_right this hpos16.le
  · -- b² ≤ 4c₀²Y
    rw [hb2]
    have := mul_le_mul_of_nonneg_left hq1 (show 0 ≤ 2 * c₀ ^ 2 * Y ^ 2 by positivity)
    have e : 2 * c₀ ^ 2 * Y ^ 2 * (2 / Y) = 4 * c₀ ^ 2 * Y := by field_simp; ring
    linarith
  · -- ab ≤ 3c₀²Y
    have hab2 : (a * b) ^ 2 ≤ (3 * c₀ ^ 2 * Y) ^ 2 := by
      rw [mul_pow, ha2, hb2]
      have h1 : 2 * c₀ ^ 2 * Y ^ 2 * Q2 * (2 * c₀ ^ 2 * Y ^ 2 * Q1) =
          4 * c₀ ^ 4 * Y ^ 4 * (Q1 * Q2) := by ring
      rw [h1]
      have := mul_le_mul_of_nonneg_left hQ12 (show 0 ≤ 4 * c₀ ^ 4 * Y ^ 4 by positivity)
      have e : 4 * c₀ ^ 4 * Y ^ 4 * (2 / Y ^ 2) = 8 * c₀ ^ 4 * Y ^ 2 := by field_simp; ring
      linarith [sq_nonneg (c₀ ^ 2 * Y)]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hab2
  · -- the covering
    intro h l hl hh
    have hQw : qf Y α h l ≤ 2 * c₀ ^ 2 := by
      unfold qf
      have h1 : ((h : ℝ) + l * α) ^ 2 ≤ c₀ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hh 2
      have h2 : ((l : ℝ) / Y) ^ 2 ≤ c₀ ^ 2 := by
        rw [← sq_abs, abs_div, abs_of_pos hYpos]
        have : |(l : ℝ)| / Y ≤ c₀ := by rw [div_le_iff₀ hYpos]; exact hl
        exact pow_le_pow_left₀ (by positivity) this 2
      linarith
    have hQwn := qf_nonneg Y α h l
    refine ⟨h * l₂ - l * h₂, h₁ * l - l₁ * h, ?_, ?_, ?_, ?_⟩
    · apply Real.abs_le_sqrt
      have hL := lagrange Y α hY0 h l h₂ l₂
      have hx : (((h * l₂ - l * h₂ : ℤ) : ℝ) / Y) ^ 2 ≤ qf Y α h l * Q2 := by
        rw [hL]; exact le_add_of_nonneg_left (sq_nonneg _)
      rw [div_pow, div_le_iff₀ (by positivity)] at hx
      have := mul_le_mul_of_nonneg_right hQw (mul_nonneg hQ2n (sq_nonneg Y))
      linarith
    · apply Real.abs_le_sqrt
      have hL := lagrange Y α hY0 h₁ l₁ h l
      have hy : (((h₁ * l - l₁ * h : ℤ) : ℝ) / Y) ^ 2 ≤ Q1 * qf Y α h l := by
        rw [hL]; exact le_add_of_nonneg_left (sq_nonneg _)
      rw [div_pow, div_le_iff₀ (by positivity)] at hy
      have := mul_le_mul_of_nonneg_left hQw (mul_nonneg hQ1pos.le (sq_nonneg Y))
      linarith
    · linear_combination (-h) * hdet
    · linear_combination (-l) * hdet

/-- **D6, lattice part** ([21] (4.27)): for `Y ≥ (2c₀ + 2)^{10}`, the region
`{(h, l) : |l| ≤ c₀Y, |h + lα| ≤ c₀}` lies in the image of the box `[−A', A'] × [−B', B']` under
the integer matrix `(p q; r s)` of determinant one, with `A'B' ≤ (3c₀² + 8c₀ + 4)Y` and
`Y^{0.1} ≤ A', B' ≤ Y^{0.9}`. -/
theorem lattice_box (c₀ : ℝ) (hc₀ : 0 ≤ c₀) (Y α : ℝ) (hY : (2 * c₀ + 2) ^ 10 ≤ Y)
    (hdio : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Y ^ (0.2 : ℝ) → Y ^ (-0.7 : ℝ) < |l * α - round (l * α)|) :
    ∃ p q r s : ℤ, p * s - q * r = 1 ∧ ∃ A' B' : ℕ,
      (A' : ℝ) * B' ≤ (3 * c₀ ^ 2 + 8 * c₀ + 4) * Y ∧
      Y ^ (0.1 : ℝ) ≤ A' ∧ Y ^ (0.1 : ℝ) ≤ B' ∧ (A' : ℝ) ≤ Y ^ (0.9 : ℝ) ∧
      (B' : ℝ) ≤ Y ^ (0.9 : ℝ) ∧
      ∀ h l : ℤ, |(l : ℝ)| ≤ c₀ * Y → |h + l * α| ≤ c₀ →
        ∃ x y : ℤ, |x| ≤ A' ∧ |y| ≤ B' ∧ h = p * x + q * y ∧ l = r * x + s * y := by
  have h2c : (2 : ℝ) ≤ 2 * c₀ + 2 := by linarith
  have hY1 : (1 : ℝ) ≤ Y := le_trans (one_le_pow₀ (by linarith)) hY
  have hY0 : (0 : ℝ) ≤ Y := by linarith
  obtain ⟨p, q, r, s, hdet, a, b, ha0, hb0, ha2, hb2, hab, hcov⟩ :=
    lattice_box_core Y α c₀ hY1 hdio
  set t := Y ^ (0.1 : ℝ) with ht
  have et : ∀ n : ℕ, Y ^ ((n : ℝ) / 10) = t ^ n := rpow_tenth Y hY0
  have e10 : Y = t ^ 10 := by rw [← et]; norm_num
  have e9 : Y ^ (0.9 : ℝ) = t ^ 9 := by rw [← et]; norm_num
  have e16 : Y ^ (1.6 : ℝ) = t ^ 16 := by rw [← et]; norm_num
  have htc : 2 * c₀ + 2 ≤ t := by
    have := Real.rpow_le_rpow (by positivity) hY (show (0 : ℝ) ≤ 0.1 by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show ((10 : ℕ) : ℝ) * 0.1 = 1 by norm_num, Real.rpow_one] at this
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 ≤ t := by linarith
  -- a ≤ 2c₀t⁸, b ≤ 2c₀t⁵
  have ha : a ≤ 2 * c₀ * t ^ 8 := by
    rw [e16] at ha2
    have e : (2 * c₀ * t ^ 8) ^ 2 = 4 * c₀ ^ 2 * t ^ 16 := by ring
    exact (sq_le_sq₀ ha0 (by positivity)).mp (by linarith)
  have hb : b ≤ 2 * c₀ * t ^ 5 := by
    rw [e10] at hb2
    have e : (2 * c₀ * t ^ 5) ^ 2 = 4 * c₀ ^ 2 * t ^ 10 := by ring
    exact (sq_le_sq₀ hb0 (by positivity)).mp (by linarith)
  have hab' : a * b ≤ 3 * c₀ ^ 2 * t ^ 10 := by rw [← e10]; exact hab
  set A' := ⌈max a t⌉₊
  set B' := ⌈max b t⌉₊
  have hA1 : max a t ≤ A' := Nat.le_ceil _
  have hB1 : max b t ≤ B' := Nat.le_ceil _
  have hA2 : (A' : ℝ) < max a t + 1 := Nat.ceil_lt_add_one (le_max_of_le_right ht0)
  have hB2 : (B' : ℝ) < max b t + 1 := Nat.ceil_lt_add_one (le_max_of_le_right ht0)
  have hmaxa : max a t ≤ a + t := max_le (by linarith) (by linarith)
  have hmaxb : max b t ≤ b + t := max_le (by linarith) (by linarith)
  have p1 : t ≤ t ^ 2 := by nlinarith
  have p5 : t ^ 5 ≤ t ^ 8 := pow_le_pow_right₀ ht1 (by norm_num)
  have p18 : t ≤ t ^ 8 := by simpa using pow_le_pow_right₀ ht1 (show 1 ≤ 8 by norm_num)
  have p9 : (2 * c₀ + 2) * t ^ 8 ≤ t ^ 9 := by
    have := mul_le_mul_of_nonneg_right htc (show 0 ≤ t ^ 8 by positivity)
    calc _ ≤ t * t ^ 8 := this
      _ = t ^ 9 := by ring
  have hc8 : 0 ≤ c₀ * t ^ 8 := by positivity
  have hc5 : c₀ * t ^ 5 ≤ c₀ * t ^ 8 := mul_le_mul_of_nonneg_left p5 hc₀
  have hAle : (A' : ℝ) ≤ a + t + 1 := by linarith
  have hBle : (B' : ℝ) ≤ b + t + 1 := by linarith
  refine ⟨p, q, r, s, hdet, A', B', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- A'B' ≤ (3c₀² + 8c₀ + 4)Y
    rw [e10]
    have h1 : (A' : ℝ) * B' ≤ (a + t + 1) * (b + t + 1) :=
      mul_le_mul hAle hBle (Nat.cast_nonneg _) (by positivity)
    have q1 : a * (t + 1) ≤ 4 * c₀ * t ^ 10 := by
      have h1 : a * (t + 1) ≤ (2 * c₀ * t ^ 8) * (2 * t) :=
        mul_le_mul ha (by linarith) (by positivity) (by positivity)
      have h9 : t ^ 9 ≤ t ^ 10 := pow_le_pow_right₀ ht1 (by norm_num)
      have h2 : (2 * c₀ * t ^ 8) * (2 * t) = 4 * c₀ * t ^ 9 := by ring
      have h3 := mul_le_mul_of_nonneg_left h9 hc₀
      linarith
    have q2 : b * (t + 1) ≤ 4 * c₀ * t ^ 10 := by
      have h1 : b * (t + 1) ≤ (2 * c₀ * t ^ 5) * (2 * t) :=
        mul_le_mul hb (by linarith) (by positivity) (by positivity)
      have h6 : t ^ 6 ≤ t ^ 10 := pow_le_pow_right₀ ht1 (by norm_num)
      have h2 : (2 * c₀ * t ^ 5) * (2 * t) = 4 * c₀ * t ^ 6 := by ring
      have h3 := mul_le_mul_of_nonneg_left h6 hc₀
      linarith
    have q3 : (t + 1) ^ 2 ≤ 4 * t ^ 10 := by
      have h2 : t ^ 2 ≤ t ^ 10 := pow_le_pow_right₀ ht1 (by norm_num)
      have h3 : (t + 1) ^ 2 ≤ (2 * t) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      have h4 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
      linarith
    calc (A' : ℝ) * B' ≤ (a + t + 1) * (b + t + 1) := h1
      _ = a * b + a * (t + 1) + b * (t + 1) + (t + 1) ^ 2 := by ring
      _ ≤ 3 * c₀ ^ 2 * t ^ 10 + 4 * c₀ * t ^ 10 + 4 * c₀ * t ^ 10 + 4 * t ^ 10 :=
          add_le_add (add_le_add (add_le_add hab' q1) q2) q3
      _ = (3 * c₀ ^ 2 + 8 * c₀ + 4) * t ^ 10 := by ring
  · exact le_trans (le_max_right _ _) hA1
  · exact le_trans (le_max_right _ _) hB1
  · rw [e9]
    have := one_le_pow₀ (n := 8) ht1
    linarith
  · rw [e9]
    have := one_le_pow₀ (n := 8) ht1
    linarith
  · intro h l hl hh
    obtain ⟨x, y, hx, hy, hxe, hye⟩ := hcov h l hl hh
    refine ⟨x, y, ?_, ?_, hxe, hye⟩
    · have : ((|x| : ℤ) : ℝ) ≤ ((A' : ℤ) : ℝ) := by
        push_cast; exact le_trans hx (le_trans (le_max_left _ _) hA1)
      exact_mod_cast this
    · have : ((|y| : ℤ) : ℝ) ≤ ((B' : ℤ) : ℝ) := by
        push_cast; exact le_trans hy (le_trans (le_max_left _ _) hB1)
      exact_mod_cast this

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: the core clean kernel via cells, line tuples and the lattice box ([21] §4.5)

`kappaC_bilBound`: the core clean kernel on `(positions × products)²` is bounded by
`5121 · Mbox'`. Positions are cut into cells of length `H = d₀Y` in `z₂/τ(z)` (an edge moves
at most 2560 cells) and by their line tuple at the pad primes (an edge preserves it, because
`D ∣ det`); every block lies in the lattice `ℤz₀ + ℤDw₀` of a good base point `z₀`, which
`lattice_box` (test (i) at `z₀`) maps into a box with `A'B' ≪ Y`, where `box_minor_bound`
applies. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- The lattice constant `c₀ = 256 · 2562`. -/
def cLat : ℝ := 256 * 2562

/-- The box constant `C₁ = 3c₀² + 8c₀ + 4`. -/
def C1 : ℝ := 3 * cLat ^ 2 + 8 * cLat + 4

/-- The uniform block bound. -/
noncomputable def Mbox' : ℝ :=
  P.Y * ((32 * C1 + 40) * (1 / log P.x ^ P.A₀ + P.Y ^ (-0.1 : ℝ)) * (1 + Real.log (2 * P.Y))) *
    Ipsi + 9 * C1 * P.Y * Jpsi / (log P.x ^ P.A₀ / 2)

/-- The cell of a position. -/
noncomputable def cellOf (ω : ℝ × ℝ × ℝ) (z : ℤ × ℤ) : ℤ :=
  ⌊((z.2 : ℝ) / tauR ω z) / (P.d₀ * P.Y)⌋

/-- The line tuple at the pad primes. -/
def linesOf (pd : Fin P.K → Fin P.J → ℕ) (z : ℤ × ℤ) : Fin P.K → Fin P.J → ℕ :=
  fun i k => lineOf (pd i k) z

lemma minorKernel_support (x A₀ Y : ℝ) (t a b : ℤ) (h : minorKernel x A₀ Y t a b ≠ 0) :
    |(t : ℝ) / Y| < 5 := by
  by_contra h5
  push Not at h5
  apply h
  unfold minorKernel
  rw [L102M.arcCutoff_eq_zero h5]; simp

lemma floor_diff_le (a b H : ℝ) (hH : 0 < H) (n : ℕ) (h : |a - b| < n * H) :
    |⌊a / H⌋ - ⌊b / H⌋| ≤ (n : ℤ) := by
  have h1 : |a / H - b / H| < n := by
    rw [← sub_div, abs_div, abs_of_pos hH, div_lt_iff₀ hH]; exact h
  rw [abs_lt] at h1
  have e1 := Int.floor_le (a / H)
  have e2 := Int.lt_floor_add_one (a / H)
  have e3 := Int.floor_le (b / H)
  have e4 := Int.lt_floor_add_one (b / H)
  have h2 : ((⌊a / H⌋ - ⌊b / H⌋ : ℤ) : ℝ) < n + 1 := by push_cast; linarith
  have h3 : -((n : ℝ) + 1) < ((⌊a / H⌋ - ⌊b / H⌋ : ℤ) : ℝ) := by push_cast; linarith
  rw [abs_le]
  constructor
  · have : -((n : ℤ) + 1) < ⌊a / H⌋ - ⌊b / H⌋ := by exact_mod_cast h3
    omega
  · have : ⌊a / H⌋ - ⌊b / H⌋ < (n : ℤ) + 1 := by exact_mod_cast h2
    omega

lemma slope_lt_of_floor (a b H : ℝ) (hH : 0 < H) (n : ℤ) (h : |⌊a / H⌋ - ⌊b / H⌋| ≤ n) :
    |a - b| < (n + 1) * H := by
  have e1 := Int.floor_le (a / H)
  have e2 := Int.lt_floor_add_one (a / H)
  have e3 := Int.floor_le (b / H)
  have e4 := Int.lt_floor_add_one (b / H)
  rw [abs_le] at h
  have h1 : ((⌊a / H⌋ - ⌊b / H⌋ : ℤ) : ℝ) ≤ n := by exact_mod_cast h.2
  have h2 : (-n : ℝ) ≤ ((⌊a / H⌋ - ⌊b / H⌋ : ℤ) : ℝ) := by exact_mod_cast h.1
  push_cast at h1 h2
  have : |a / H - b / H| < n + 1 := by rw [abs_lt]; constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hH, div_lt_iff₀ hH] at this
  exact this

/-- An edge moves at most 2560 cells. -/
lemma cell_shift (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hd : 0 < (P.d₀ : ℝ))
    (hY : 0 < P.Y) (z z' : ℤ × ℤ) (hz : P.InBox ω z) (hz' : P.InBox ω z')
    (hdet : |(detZ z z' : ℝ)| < 10 * P.d₀ * P.Y) :
    |cellOf P ω z' - cellOf P ω z| ≤ 2560 := by
  have hτ := tau_pos P ω hω hU z hz
  have hτ' := tau_pos P ω hω hU z' hz'
  have hb := tau_le P ω hω hU z hz
  have hb' := tau_le P ω hω hU z' hz'
  have hs := slope_diff ω z z' hτ.ne' hτ'.ne'
  have hlt : |(z'.2 : ℝ) / tauR ω z' - z.2 / tauR ω z| < (2560 : ℕ) * (P.d₀ * P.Y) := by
    rw [hs, abs_div, abs_of_pos (mul_pos hτ hτ')]
    rw [div_lt_iff₀ (mul_pos hτ hτ')]
    have h1 : 1 / 256 ≤ tauR ω z * tauR ω z' := by nlinarith [hb.1, hb'.1]
    have h2 : 0 ≤ (P.d₀ : ℝ) * P.Y := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    push_cast
    nlinarith
  exact_mod_cast floor_diff_le _ _ _ (by positivity) 2560 hlt

/-! ## Pads and lines -/

lemma pad_injective (hEP : EP P) (pd : Fin P.K → Fin P.J → ℕ) (hpd : pd ∈ padCands P)
    (hinj : ∀ i, Function.Injective (pd i)) :
    Function.Injective (fun q : Fin P.K × Fin P.J => pd q.1 q.2) := by
  simp only [padCands, Fintype.mem_piFinset] at hpd
  intro q q' h
  simp only at h
  by_cases hi : q.1 = q'.1
  · have : q.2 = q'.2 := by
      have := hinj q.1 (a₁ := q.2) (a₂ := q'.2) (by rw [h, hi])
      exact this
    exact Prod.ext hi this
  · exact absurd (hEP.hdisj q.1 q'.1 hi) (Finset.not_disjoint_iff.2
      ⟨pd q.1 q.2, hpd q.1 q.2, h ▸ hpd q'.1 q'.2⟩)

lemma padD_eq_prod_image (hEP : EP P) (pd : Fin P.K → Fin P.J → ℕ) (hpd : pd ∈ padCands P)
    (hinj : ∀ i, Function.Injective (pd i)) :
    padD P pd = ∏ p ∈ (univ : Finset (Fin P.K × Fin P.J)).image (fun q => pd q.1 q.2), p := by
  rw [prod_image fun a _ b _ h => pad_injective P hEP pd hpd hinj h]
  unfold padD
  rw [← Finset.univ_product_univ, prod_product]

lemma lines_eq_iff_dvd (hEP : EP P) (pd : Fin P.K → Fin P.J → ℕ) (hpd : pd ∈ padCands P)
    (hinj : ∀ i, Function.Injective (pd i)) (z z' : ℤ × ℤ) (hz : Int.gcd z.1 z.2 = 1)
    (hz' : Int.gcd z'.1 z'.2 = 1) :
    linesOf P pd z = linesOf P pd z' ↔ ((padD P pd : ℕ) : ℤ) ∣ detZ z z' := by
  have hpd' := hpd
  simp only [padCands, Fintype.mem_piFinset] at hpd'
  constructor
  · intro h
    rw [padD_eq_prod_image P hEP pd hpd hinj]
    refine prod_dvd_det_of_lines _ (fun p hp => ?_) z z' hz hz' (fun p hp => ?_)
    · obtain ⟨q, _, rfl⟩ := mem_image.1 hp
      exact grp_prime (hpd' q.1 q.2)
    · obtain ⟨q, _, rfl⟩ := mem_image.1 hp
      exact congrFun (congrFun h q.1) q.2
  · intro h
    funext i k
    apply (lineOf_eq_iff (pd i k) (grp_prime (hpd' i k)) z z' hz hz').2
    refine dvd_trans ?_ h
    have : pd i k ∣ padD P pd := by
      unfold padD
      exact dvd_trans (dvd_prod_of_mem _ (mem_univ k)) (dvd_prod_of_mem _ (mem_univ i))
    exact_mod_cast this

/-! ## Lattice coordinates of a block -/

lemma int_cast_div_of_dvd (a : ℤ) (D : ℕ) (hD : 1 ≤ D) (h : (D : ℤ) ∣ a) :
    ((a / D : ℤ) : ℝ) = (a : ℝ) / D := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  rw [Int.cast_div h (by exact_mod_cast hD0)]
  push_cast; rfl

/-- Block positions lie in the lattice region of [21] (4.26). -/
lemma block_region (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hd : 0 < (P.d₀ : ℝ))
    (hY : 0 < P.Y) (z₀ z : ℤ × ℤ) (hz₀ : P.InBox ω z₀) (hz : P.InBox ω z)
    (hz₀p : Int.gcd z₀.1 z₀.2 = 1) (D : ℕ) (hD : P.d₀ ≤ D) (hdvd : (D : ℤ) ∣ detZ z₀ z)
    (hcell : |cellOf P ω z - cellOf P ω z₀| ≤ 2561) :
    |((detZ z₀ z / D : ℤ) : ℝ)| ≤ cLat * P.Y ∧
      |((detZ z (complVec z₀) : ℤ) : ℝ) + ((detZ z₀ z / D : ℤ) : ℝ) * (D * ratioAt ω z₀)| ≤
        cLat := by
  have hd1 : 0 < P.d₀ := Nat.cast_pos.1 hd
  have hD1 : 1 ≤ D := by omega
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD1
  rw [int_cast_div_of_dvd _ D hD1 hdvd]
  have hτ₀ := tau_pos P ω hω hU z₀ hz₀
  have hτ := tau_pos P ω hω hU z hz
  constructor
  · have hs := slope_diff ω z₀ z hτ₀.ne' hτ.ne'
    have hlt := slope_lt_of_floor ((z.2 : ℝ) / tauR ω z) ((z₀.2 : ℝ) / tauR ω z₀)
      (P.d₀ * P.Y) (by positivity) 2561 hcell
    rw [hs, abs_div, abs_of_pos (mul_pos hτ₀ hτ), div_lt_iff₀ (mul_pos hτ₀ hτ)] at hlt
    have hb := tau_le P ω hω hU z₀ hz₀
    have hb' := tau_le P ω hω hU z hz
    have h1 : tauR ω z₀ * tauR ω z ≤ 256 := by nlinarith [hb.2, hb'.2]
    have h2 : |(detZ z₀ z : ℝ)| ≤ 2562 * (P.d₀ * P.Y) * 256 := by
      have h3 : (0 : ℝ) ≤ 2562 * (P.d₀ * P.Y) := by positivity
      push_cast at hlt
      nlinarith [mul_le_mul_of_nonneg_left h1 h3]
    rw [abs_div, abs_of_pos hDr, div_le_iff₀ hDr]
    have : (P.d₀ : ℝ) ≤ D := by exact_mod_cast hD
    unfold cLat
    nlinarith
  · have e : (detZ z (complVec z₀) : ℝ) + (detZ z₀ z : ℝ) / D * (D * ratioAt ω z₀) =
        tauR ω z / tauR ω z₀ := by
      rw [tauR_decomp' ω z₀ z hz₀p hτ₀.ne']
      field_simp
    rw [e]
    have hr := tau_ratio_mem P ω hω hU z₀ z hz₀ hz
    rw [abs_of_pos (div_pos hτ hτ₀)]
    unfold cLat; linarith [hr.2]

/-- The lattice coordinates `(x, y) = γ⁻¹ (h, l)`, `h = det(z, w₀)`, `l = det(z₀, z)/D`. -/
def latCoord (p q r s : ℤ) (z₀ : ℤ × ℤ) (D : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (s * detZ z (complVec z₀) - q * (detZ z₀ z / D), -r * detZ z (complVec z₀) + p * (detZ z₀ z / D))

lemma det_plucker (z₀ w₀ z z' : ℤ × ℤ) (h : detZ z₀ w₀ = 1) :
    detZ z z' = detZ z w₀ * detZ z₀ z' - detZ z₀ z * detZ z' w₀ := by
  unfold detZ at *
  linear_combination (-(z.1 * z'.2 - z.2 * z'.1)) * h

lemma det_latCoord (p q r s : ℤ) (hdet : p * s - q * r = 1) (z₀ : ℤ × ℤ)
    (hz₀p : Int.gcd z₀.1 z₀.2 = 1) (D : ℕ) (hD1 : 1 ≤ D) (z z' : ℤ × ℤ)
    (h1 : (D : ℤ) ∣ detZ z₀ z) (h2 : (D : ℤ) ∣ detZ z₀ z') :
    detZ z z' / D = detI (latCoord p q r s z₀ D z) (latCoord p q r s z₀ D z') := by
  have hw := detZ_complVec z₀ hz₀p
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  obtain ⟨l, hl⟩ := h1
  obtain ⟨l', hl'⟩ := h2
  rw [det_plucker z₀ (complVec z₀) z z' hw, hl, hl']
  unfold latCoord detI
  rw [hl, hl', Int.mul_ediv_cancel_left _ hD0, Int.mul_ediv_cancel_left _ hD0]
  rw [show detZ z (complVec z₀) * (D * l') - D * l * detZ z' (complVec z₀) =
    D * (detZ z (complVec z₀) * l' - l * detZ z' (complVec z₀)) by ring,
    Int.mul_ediv_cancel_left _ hD0]
  linear_combination (-(detZ z (complVec z₀) * l' - l * detZ z' (complVec z₀))) * hdet

lemma latCoord_injOn (p q r s : ℤ) (hdet : p * s - q * r = 1) (z₀ : ℤ × ℤ)
    (hz₀p : Int.gcd z₀.1 z₀.2 = 1) (D : ℕ) (hD1 : 1 ≤ D) (z z' : ℤ × ℤ)
    (h1 : (D : ℤ) ∣ detZ z₀ z) (h2 : (D : ℤ) ∣ detZ z₀ z')
    (h : latCoord p q r s z₀ D z = latCoord p q r s z₀ D z') : z = z' := by
  have hw := detZ_complVec z₀ hz₀p
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  unfold latCoord at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨ha, hb⟩ := h
  set h₀ := detZ z (complVec z₀)
  set h₀' := detZ z' (complVec z₀)
  set l := detZ z₀ z / D
  set l' := detZ z₀ z' / D
  have e1 : h₀ = h₀' := by linear_combination p * ha + q * hb - (h₀ - h₀') * hdet
  have e2 : l = l' := by linear_combination r * ha + s * hb - (l - l') * hdet
  have e3 : detZ z₀ z = detZ z₀ z' := by
    rw [← Int.mul_ediv_cancel' h1, ← Int.mul_ediv_cancel' h2]
    show (D : ℤ) * l = D * l'
    rw [e2]
  have e1' : detZ z (complVec z₀) = detZ z' (complVec z₀) := e1
  rw [decomp z₀ (complVec z₀) z hw, decomp z₀ (complVec z₀) z' hw, e1', e3]

lemma latCoord_mem_box (p q r s : ℤ) (hdet : p * s - q * r = 1) (z₀ : ℤ × ℤ) (D : ℕ)
    (z : ℤ × ℤ) (A' B' : ℕ)
    (hcov : ∃ x y : ℤ, |x| ≤ A' ∧ |y| ≤ B' ∧ detZ z (complVec z₀) = p * x + q * y ∧
      detZ z₀ z / D = r * x + s * y) :
    latCoord p q r s z₀ D z ∈ boxZ A' B' := by
  obtain ⟨x, y, hx, hy, e1, e2⟩ := hcov
  have hc : latCoord p q r s z₀ D z = (x, y) := by
    unfold latCoord
    rw [e1, e2]
    ext
    · simp only; linear_combination x * hdet
    · simp only; linear_combination y * hdet
  rw [hc]
  unfold boxZ
  rw [mem_product, mem_Icc, mem_Icc]
  rw [abs_le] at hx hy
  exact ⟨hx, hy⟩

/-! ## The block bound and the assembly -/

lemma card_boxZ (A B : ℕ) : ((boxZ A B).card : ℝ) = (2 * A + 1) * (2 * B + 1) := by
  unfold boxZ
  rw [card_product, Int.card_Icc, Int.card_Icc]
  have h1 : ((A : ℤ) + 1 - -(A : ℤ)).toNat = 2 * A + 1 := by omega
  have h2 : ((B : ℤ) + 1 - -(B : ℤ)).toNat = 2 * B + 1 := by omega
  rw [h1, h2]; push_cast; ring

lemma C1_nonneg : 0 ≤ C1 := by unfold C1 cLat; norm_num

lemma Mbox'_nonneg (hY1 : 1 ≤ P.Y) (hP : 1 ≤ log P.x ^ P.A₀) : 0 ≤ Mbox' P := by
  unfold Mbox'
  have := Ipsi_nonneg; have := Jpsi_nonneg; have := C1_nonneg
  have : 0 ≤ Real.log (2 * P.Y) := Real.log_nonneg (by linarith)
  have : 0 ≤ P.Y ^ (-0.1 : ℝ) := Real.rpow_nonneg (by linarith) _
  have : 0 < log P.x ^ P.A₀ := by linarith
  positivity

lemma Mbox_le (A B : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hAB : (A : ℝ) * B ≤ C1 * P.Y)
    (hP : 1 ≤ log P.x ^ P.A₀) :
    Mbox P.x P.A₀ P.Y C1 A B ≤ Mbox' P := by
  unfold Mbox Mbox'
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hc : ((boxZ A B).card : ℝ) ≤ 9 * C1 * P.Y := by
    rw [card_boxZ]; nlinarith
  have hJ := Jpsi_nonneg
  have hP2 : 0 < log P.x ^ P.A₀ / 2 := by linarith
  have : (boxZ A B).card * Jpsi / (log P.x ^ P.A₀ / 2) ≤
      9 * C1 * P.Y * Jpsi / (log P.x ^ P.A₀ / 2) := by
    apply div_le_div_of_nonneg_right _ hP2.le
    exact mul_le_mul_of_nonneg_right hc hJ
  linarith

/-- The cell-shifted pieces of the core kernel. -/
noncomputable def kσ (ω : ℝ × ℝ × ℝ) (pd : Fin P.K → Fin P.J → ℕ) (σ : ℤ)
    (p q : (ℤ × ℤ) × ℤ) : ℂ :=
  if cellOf P ω q.1 - cellOf P ω p.1 = σ then kappaC P ω pd p q else 0

lemma Mbox_nonneg (A B : ℕ) (hY1 : 1 ≤ P.Y) (hP : 1 ≤ log P.x ^ P.A₀) :
    0 ≤ Mbox P.x P.A₀ P.Y C1 A B := by
  unfold Mbox
  have h1 : 0 ≤ P.Y * ((32 * C1 + 40) * (1 / log P.x ^ P.A₀ + P.Y ^ (-0.1 : ℝ)) *
      (1 + Real.log (2 * P.Y))) * Ipsi := by
    have := Ipsi_nonneg; have := C1_nonneg
    have : 0 ≤ Real.log (2 * P.Y) := Real.log_nonneg (by linarith)
    have : 0 ≤ P.Y ^ (-0.1 : ℝ) := Real.rpow_nonneg (by linarith) _
    have : 0 < log P.x ^ P.A₀ := by linarith
    positivity
  have h2 : 0 ≤ ((boxZ A B).card : ℝ) * Jpsi / (log P.x ^ P.A₀ / 2) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) Jpsi_nonneg) (by linarith)
  exact add_nonneg h1 h2

set_option maxHeartbeats 1000000 in
/-- **The block bound.** -/
lemma block_bound (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    (pd : Fin P.K → Fin P.J → ℕ) (hpd : pd ∈ padCands P) (hinj : ∀ i, Function.Injective (pd i))
    (hD1 : P.d₀ ≤ padD P pd) (hD2 : padD P pd < 2 * P.d₀) (hd : 0 < (P.d₀ : ℝ))
    (hY1 : 1 ≤ P.Y) (hYbig : (2 * cLat + 2) ^ 10 ≤ P.Y) (hP : 1 ≤ log P.x ^ P.A₀)
    (σ : ℤ) (hσ : |σ| ≤ 2560) (k : ℤ × (Fin P.K → Fin P.J → ℕ)) :
    BilBound ((P.zSet ×ˢ prodSet P).filter fun p => (cellOf P ω p.1, linesOf P pd p.1) = k)
      ((P.zSet ×ˢ prodSet P).filter fun q => (cellOf P ω q.1 - σ, linesOf P pd q.1) = k)
      (kσ P ω pd σ) (Mbox' P) := by
  classical
  set SP := P.zSet ×ˢ prodSet P
  set Sk := SP.filter fun p => (cellOf P ω p.1, linesOf P pd p.1) = k
  set Tk := SP.filter fun q => (cellOf P ω q.1 - σ, linesOf P pd q.1) = k
  set D := padD P pd
  have hDpos : 1 ≤ D := padD_pos P pd hpd
  have hY0 : 0 < P.Y := by linarith
  have hM' := Mbox'_nonneg P hY1 hP
  have hzp : ∀ z ∈ P.zSet, Int.gcd z.1 z.2 = 1 := by
    intro z hz; exact zSet_gcd hz
  by_cases hex : ∃ p₀ ∈ Sk, T1 P D ω p₀.1 ∧ P.InBox ω p₀.1
  swap
  · refine bilBound_zero _ _ _ _ hM' fun p hp q _ => ?_
    unfold kσ kappaC
    split_ifs with h1 h2
    · exact absurd ⟨p, hp, h2.2.2.2.1, h2.2.2.2.2.1⟩ hex
    · rfl
    · rfl
  obtain ⟨p₀, hp₀, hT₀, hB₀⟩ := hex
  set z₀ := p₀.1
  have hp₀' := mem_filter.1 hp₀
  have hz₀p : Int.gcd z₀.1 z₀.2 = 1 := hzp z₀ (mem_product.1 hp₀'.1).1
  obtain ⟨pp, qq, rr, ss, hdet, A', B', hAB, hA1, hB1, hA2, hB2, hcov⟩ :=
    lattice_box cLat (by unfold cLat; norm_num) P.Y (D * ratioAt ω z₀) hYbig hT₀
  have hA'1 : 1 ≤ A' := by
    have : (1 : ℝ) ≤ P.Y ^ (0.1 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
    exact_mod_cast this.trans hA1
  have hB'1 : 1 ≤ B' := by
    have : (1 : ℝ) ≤ P.Y ^ (0.1 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
    exact_mod_cast this.trans hB1
  set Φ : (ℤ × ℤ) × ℤ → (ℤ × ℤ) × ℤ := fun p => (latCoord pp qq rr ss z₀ D p.1, p.2)
  set Sb := Sk.filter fun p => P.InBox ω p.1
  set Tb := Tk.filter fun q => P.InBox ω q.1
  -- lines and determinants in the block
  have hlinesS : ∀ p ∈ Sk, linesOf P pd p.1 = linesOf P pd z₀ := by
    intro p hp
    have e1 := congrArg Prod.snd (mem_filter.1 hp).2
    have e2 := congrArg Prod.snd hp₀'.2
    simp only at e1 e2
    rw [e1, e2]
  have hlinesT : ∀ q ∈ Tk, linesOf P pd q.1 = linesOf P pd z₀ := by
    intro q hq
    have h1 := (mem_filter.1 hq).2
    have h2 := hp₀'.2
    have e1 := congrArg Prod.snd h1
    have e2 := congrArg Prod.snd h2
    simp only at e1 e2
    rw [e1, e2]
  have hdvdS : ∀ p ∈ Sk, (D : ℤ) ∣ detZ z₀ p.1 := fun p hp =>
    (lines_eq_iff_dvd P hEP pd hpd hinj z₀ p.1 hz₀p
      (hzp p.1 (mem_product.1 (mem_filter.1 hp).1).1)).1 (hlinesS p hp).symm
  have hdvdT : ∀ q ∈ Tk, (D : ℤ) ∣ detZ z₀ q.1 := fun q hq =>
    (lines_eq_iff_dvd P hEP pd hpd hinj z₀ q.1 hz₀p
      (hzp q.1 (mem_product.1 (mem_filter.1 hq).1).1)).1 (hlinesT q hq).symm
  have hcellS : ∀ p ∈ Sk, cellOf P ω p.1 = cellOf P ω z₀ := by
    intro p hp
    have e1 := congrArg Prod.fst (mem_filter.1 hp).2
    have e2 := congrArg Prod.fst hp₀'.2
    simp only at e1 e2
    rw [e1, e2]
  have hcellT : ∀ q ∈ Tk, cellOf P ω q.1 - σ = cellOf P ω z₀ := by
    intro q hq
    have e1 := congrArg Prod.fst (mem_filter.1 hq).2
    have e2 := congrArg Prod.fst hp₀'.2
    simp only at e1 e2
    rw [e1, e2]
  -- the box images
  have hboxS : ∀ p ∈ Sb, latCoord pp qq rr ss z₀ D p.1 ∈ boxZ A' B' := by
    intro p hp
    obtain ⟨hpk, hpb⟩ := mem_filter.1 hp
    obtain ⟨h1, h2⟩ := block_region P ω hω hU hd hY0 z₀ p.1 hB₀ hpb hz₀p D hD1 (hdvdS p hpk)
      (by rw [hcellS p hpk, sub_self, abs_zero]; norm_num)
    exact latCoord_mem_box pp qq rr ss hdet z₀ D p.1 A' B' (hcov _ _ h1 h2)
  have hboxT : ∀ q ∈ Tb, latCoord pp qq rr ss z₀ D q.1 ∈ boxZ A' B' := by
    intro q hq
    obtain ⟨hqk, hqb⟩ := mem_filter.1 hq
    have hc : |cellOf P ω q.1 - cellOf P ω z₀| ≤ 2561 := by
      have := hcellT q hqk
      rw [show cellOf P ω q.1 - cellOf P ω z₀ = σ by omega]; omega
    obtain ⟨h1, h2⟩ := block_region P ω hω hU hd hY0 z₀ q.1 hB₀ hqb hz₀p D hD1 (hdvdT q hqk) hc
    exact latCoord_mem_box pp qq rr ss hdet z₀ D q.1 A' B' (hcov _ _ h1 h2)
  have hinjS : Set.InjOn Φ Sb := by
    intro p hp p' hp' h
    have hp1 := (mem_filter.1 (mem_coe.1 hp)).1
    have hp1' := (mem_filter.1 (mem_coe.1 hp')).1
    simp only [Φ, Prod.mk.injEq] at h
    exact Prod.ext (latCoord_injOn pp qq rr ss hdet z₀ hz₀p D hDpos _ _ (hdvdS p hp1)
      (hdvdS p' hp1') h.1) h.2
  have hinjT : Set.InjOn Φ Tb := by
    intro q hq q' hq' h
    have hq1 := (mem_filter.1 (mem_coe.1 hq)).1
    have hq1' := (mem_filter.1 (mem_coe.1 hq')).1
    simp only [Φ, Prod.mk.injEq] at h
    exact Prod.ext (latCoord_injOn pp qq rr ss hdet z₀ hz₀p D hDpos _ _ (hdvdT q hq1)
      (hdvdT q' hq1') h.1) h.2
  have himS : Sb.image Φ ⊆ boxZ A' B' ×ˢ prodSet P := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
    exact mem_product.2 ⟨hboxS p hp,
      (mem_product.1 (mem_filter.1 (mem_filter.1 hp).1).1).2⟩
  have himT : Tb.image Φ ⊆ boxZ A' B' ×ˢ prodSet P := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hx
    exact mem_product.2 ⟨hboxT q hq,
      (mem_product.1 (mem_filter.1 (mem_filter.1 hq).1).1).2⟩
  have hbox := box_minor_bound P.x P.A₀ P.Y C1 A' B' hY1 hP (by unfold C1; exact hAB) hA2 hB2
    (prodSet P)
  have hK1 := bilBound_comp Sb Tb Φ Φ hinjS hinjT _ _
    (bilBound_subset _ _ _ _ himS himT _ _ hbox)
  have hK2 := bilBound_diag Sb Tb _ _ (fun p => if T1 P D ω p.1 then (1 : ℂ) else 0)
    (fun _ => (1 : ℂ)) 1 1 zero_le_one zero_le_one
    (fun p _ => by split_ifs <;> simp) (fun _ _ => by simp)
    (Mbox_nonneg P A' B' hY1 hP) hK1
  have hK3 : BilBound Sb Tb (kσ P ω pd σ) (Mbox P.x P.A₀ P.Y C1 A' B') := by
    refine bilBound_congr Sb Tb _ _ _ (fun p hp q hq => ?_) (bilBound_mono _ _ _ _ _
      (by rw [one_mul, one_mul]) hK2)
    obtain ⟨hpk, hpb⟩ := mem_filter.1 hp
    obtain ⟨hqk, hqb⟩ := mem_filter.1 hq
    have hcell : cellOf P ω q.1 - cellOf P ω p.1 = σ := by
      have := hcellS p hpk; have := hcellT q hqk; omega
    have hdvd : ((D : ℕ) : ℤ) ∣ detZ p.1 q.1 := by
      have hl : linesOf P pd p.1 = linesOf P pd q.1 := by rw [hlinesS p hpk, hlinesT q hqk]
      exact (lines_eq_iff_dvd P hEP pd hpd hinj p.1 q.1
        (hzp p.1 (mem_product.1 (mem_filter.1 hpk).1).1)
        (hzp q.1 (mem_product.1 (mem_filter.1 hqk).1).1)).1 hl
    have hdl := det_latCoord pp qq rr ss hdet z₀ hz₀p D hDpos p.1 q.1 (hdvdS p hpk) (hdvdT q hqk)
    unfold kσ kappaC
    rw [if_pos hcell]
    simp only [Φ]
    by_cases hT : T1 P D ω p.1
    · have hc : (∀ i, Function.Injective (pd i)) ∧ P.d₀ ≤ padD P pd ∧ padD P pd < 2 * P.d₀ ∧
          T1 P (padD P pd) ω p.1 ∧ P.InBox ω p.1 ∧ P.InBox ω q.1 ∧
          ((padD P pd : ℕ) : ℤ) ∣ detZ p.1 q.1 := ⟨hinj, hD1, hD2, hT, hpb, hqb, hdvd⟩
      rw [if_pos hT, if_pos hc, hdl]; ring
    · have hc : ¬ ((∀ i, Function.Injective (pd i)) ∧ P.d₀ ≤ padD P pd ∧ padD P pd < 2 * P.d₀ ∧
          T1 P (padD P pd) ω p.1 ∧ P.InBox ω p.1 ∧ P.InBox ω q.1 ∧
          ((padD P pd : ℕ) : ℤ) ∣ detZ p.1 q.1) := fun h => hT h.2.2.2.1
      rw [if_neg hT, if_neg hc]; ring
  -- restrict to the box positions
  refine bilBound_of_support Sk Sb Tk Tb (filter_subset _ _) (filter_subset _ _) _ _ hM'
    (fun p hp q hq h => ?_) (bilBound_mono _ _ _ _ _ (Mbox_le P A' B' hA'1 hB'1
      (by unfold C1; exact hAB) hP) hK3)
  unfold kσ kappaC at h
  split_ifs at h with h1 h2
  · exact ⟨mem_filter.2 ⟨hp, h2.2.2.2.2.1⟩, mem_filter.2 ⟨hq, h2.2.2.2.2.2.1⟩⟩
  · exact absurd rfl h
  · exact absurd rfl h

/-- **The core clean kernel bound** ([21] (4.33)–(4.34) before the normalization). -/
theorem kappaC_bilBound (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    (pd : Fin P.K → Fin P.J → ℕ) (hpd : pd ∈ padCands P) (hd : 0 < (P.d₀ : ℝ))
    (hY1 : 1 ≤ P.Y) (hYbig : (2 * cLat + 2) ^ 10 ≤ P.Y) (hP : 1 ≤ log P.x ^ P.A₀) :
    BilBound (P.zSet ×ˢ prodSet P) (P.zSet ×ˢ prodSet P) (kappaC P ω pd) (5121 * Mbox' P) := by
  classical
  set SP := P.zSet ×ˢ prodSet P
  set D := padD P pd
  have hY0 : 0 < P.Y := by linarith
  have hM' := Mbox'_nonneg P hY1 hP
  have hzp : ∀ z ∈ P.zSet, Int.gcd z.1 z.2 = 1 := by
    intro z hz; exact zSet_gcd hz
  by_cases hgood : (∀ i, Function.Injective (pd i)) ∧ P.d₀ ≤ D ∧ D < 2 * P.d₀
  swap
  · refine bilBound_zero _ _ _ _ (by positivity) fun p _ q _ => ?_
    unfold kappaC
    rw [if_neg (fun h => hgood ⟨h.1, h.2.1, h.2.2.1⟩)]
  obtain ⟨hinj, hD1, hD2⟩ := hgood
  set Shs : Finset ℤ := Icc (-2560) 2560
  -- the kernel is the sum of its cell-shifted pieces
  have hsum : ∀ p ∈ SP, ∀ q ∈ SP,
      (fun p q => ∑ σ ∈ Shs, kσ P ω pd σ p q) p q = kappaC P ω pd p q := by
    intro p hp q hq
    simp only [kσ]
    by_cases h0 : kappaC P ω pd p q = 0
    · rw [h0]; simp
    · rw [sum_ite_eq]
      rw [if_pos]
      have h1 := h0
      unfold kappaC at h1
      split_ifs at h1 with hc
      · have h5 := minorKernel_support _ _ _ _ _ _ h1
        have hDr : (0 : ℝ) < D := by exact_mod_cast padD_pos P pd hpd
        have hdet : |(detZ p.1 q.1 : ℝ)| < 10 * P.d₀ * P.Y := by
          have e := int_cast_div_of_dvd (detZ p.1 q.1) D (padD_pos P pd hpd) hc.2.2.2.2.2.2
          rw [e, abs_div, abs_div, abs_of_pos hDr, abs_of_pos hY0, div_div,
            div_lt_iff₀ (by positivity)] at h5
          have : (D : ℝ) < 2 * P.d₀ := by exact_mod_cast hD2
          nlinarith
        have := cell_shift P ω hω hU hd hY0 p.1 q.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hdet
        simp only [Shs, mem_Icc]
        rw [abs_le] at this
        exact ⟨this.1, this.2⟩
      · exact absurd rfl h1
  refine bilBound_congr SP SP _ _ _ hsum ?_
  have hcard : (Shs.card : ℝ) = 5121 := by
    have : Shs.card = 5121 := by simp only [Shs]; rw [Int.card_Icc]; rfl
    rw [this]; norm_num
  rw [← hcard]
  refine bilBound_finsum SP SP Shs _ _ fun σ hσ => ?_
  have hσ' : |σ| ≤ 2560 := by
    simp only [Shs, mem_Icc] at hσ; rw [abs_le]; exact hσ
  refine bilBound_blocks SP SP (SP.image fun p => (cellOf P ω p.1, linesOf P pd p.1))
    (fun p => (cellOf P ω p.1, linesOf P pd p.1)) (fun q => (cellOf P ω q.1 - σ, linesOf P pd q.1))
    _ _ hM' (fun p hp q hq h => ?_) (fun p hp => mem_image_of_mem _ hp)
    (fun k _ => block_bound P hEP ω hω hU pd hpd hinj hD1 hD2 hd hY1 hYbig hP σ hσ' k)
  unfold kσ at h
  split_ifs at h with h1
  · have h2 : kappaC P ω pd p q ≠ 0 := h
    unfold kappaC at h2
    split_ifs at h2 with hc
    · have hl := (lines_eq_iff_dvd P hEP pd hpd hinj p.1 q.1 (hzp p.1 (mem_product.1 hp).1)
        (hzp q.1 (mem_product.1 hq).1)).2 hc.2.2.2.2.2.2
      simp only [Prod.mk.injEq]
      exact ⟨by omega, hl⟩
    · exact absurd rfl h2
  · exact absurd rfl h

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: positions on a prescribed line ([21] (4.40))

* `card_residue_le`: an interval of `n` integers meets a residue class mod `p` in `≤ n/p + 1`;
* `card_lin_cong_le`: a nonzero linear congruence `c₁x + c₂y ≡ 0 (p)` has
  `≤ #box/p + (2A+1) + (2B+1)` solutions in the box `[−A,A] × [−B,B]`;
* `line_rep`: every line `ℓ ≤ p` of `ℙ¹(𝔽_p)` has a primitive representative;
* `card_line_le`: from a good box position `z` (test (i) with the pad product `D`, `p ∤ D`), the
  targets in the `ψ`-window with `D ∣ det` and a prescribed line at `p` number
  `≤ 9C₁Y/p + 4Y^{0.9} + 2`. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

/-- An interval meets a residue class in at most `n/p + 1` points. -/
lemma card_residue_le (a b : ℤ) (hab : a ≤ b) (p : ℕ) (hp : 0 < p) (r : ℤ) :
    (((Icc a b).filter fun y => (p : ℤ) ∣ y - r).card : ℝ) ≤ ((b - a + 1 : ℤ) : ℝ) / p + 1 := by
  classical
  set S := (Icc a b).filter fun y => (p : ℤ) ∣ y - r
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  set f : ℤ → ℤ := fun y => (y - r) / p
  have hinj : Set.InjOn f S := by
    intro y hy y' hy' h
    simp only [S, coe_filter, Set.mem_ofPred_eq, mem_Icc] at hy hy'
    obtain ⟨k, hk⟩ := hy.2
    obtain ⟨k', hk'⟩ := hy'.2
    simp only [f] at h
    rw [hk, hk', Int.mul_ediv_cancel_left _ hp0.ne', Int.mul_ediv_cancel_left _ hp0.ne'] at h
    have : y - r = y' - r := by rw [hk, hk', h]
    linarith
  set lo := ⌈((a - r : ℤ) : ℝ) / p⌉
  set hi := ⌊((b - r : ℤ) : ℝ) / p⌋
  have himg : S.image f ⊆ Icc lo hi := by
    intro k hk
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hk
    simp only [S, mem_filter, mem_Icc] at hy
    obtain ⟨⟨h1, h2⟩, ⟨m, hm⟩⟩ := hy
    simp only [f, mem_Icc]
    rw [hm, Int.mul_ediv_cancel_left _ hp0.ne']
    have e : ((y - r : ℤ) : ℝ) = p * m := by rw [hm]; push_cast; ring
    constructor
    · apply Int.ceil_le.2
      rw [div_le_iff₀ hpR]
      have : ((a - r : ℤ) : ℝ) ≤ ((y - r : ℤ) : ℝ) := by exact_mod_cast (by omega : a - r ≤ y - r)
      linarith
    · apply Int.le_floor.2
      rw [le_div_iff₀ hpR]
      have : ((y - r : ℤ) : ℝ) ≤ ((b - r : ℤ) : ℝ) := by exact_mod_cast (by omega : y - r ≤ b - r)
      linarith
  have hcard : S.card = (S.image f).card := (card_image_of_injOn hinj).symm
  rw [hcard]
  refine le_trans (Nat.cast_le.2 (card_le_card himg)) ?_
  rw [Int.card_Icc]
  have h1 : ((a - r : ℤ) : ℝ) / p ≤ lo := Int.le_ceil _
  have h2 : (hi : ℝ) ≤ ((b - r : ℤ) : ℝ) / p := Int.floor_le _
  by_cases hle : lo ≤ hi + 1
  · have : ((hi + 1 - lo).toNat : ℝ) = (hi : ℝ) + 1 - lo := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; push_cast; ring
    rw [this]
    have e : ((b - a + 1 : ℤ) : ℝ) / p = ((b - r : ℤ) : ℝ) / p - ((a - r : ℤ) : ℝ) / p + 1 / p := by
      push_cast; field_simp; ring
    rw [e]
    have : (0 : ℝ) ≤ 1 / p := by positivity
    linarith
  · have : (hi + 1 - lo).toNat = 0 := by omega
    rw [this, Nat.cast_zero]
    have : (0 : ℝ) ≤ ((b - a + 1 : ℤ) : ℝ) / p := by
      apply div_nonneg _ hpR.le; exact_mod_cast (by omega : (0 : ℤ) ≤ b - a + 1)
    linarith

open Classical in
/-- Solutions of a nonzero linear congruence in the box. -/
lemma card_lin_cong_le (A B : ℕ) (p : ℕ) (hp : p.Prime) (c₁ c₂ : ℤ)
    (hc : ¬ ((p : ℤ) ∣ c₁ ∧ (p : ℤ) ∣ c₂)) :
    (((boxZ A B).filter fun v => (p : ℤ) ∣ c₁ * v.1 + c₂ * v.2).card : ℝ) ≤
      (2 * A + 1) * (2 * B + 1) / p + (2 * A + 1) + (2 * B + 1) := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hA : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hcardIcc : ∀ n : ℕ, ((Icc (-(n : ℤ)) n).card : ℝ) = 2 * n + 1 := by
    intro n; rw [Int.card_Icc]
    have : ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by omega
    rw [this]; push_cast; ring
  have hsplit : (((boxZ A B).filter fun v => (p : ℤ) ∣ c₁ * v.1 + c₂ * v.2).card : ℝ) =
      ∑ x ∈ Icc (-(A : ℤ)) A, (((Icc (-(B : ℤ)) B).filter fun y => (p : ℤ) ∣ c₁ * x + c₂ * y).card : ℝ) := by
    unfold boxZ
    rw [card_filter, sum_product]
    push_cast
    refine sum_congr rfl fun x _ => ?_
    rw [card_filter]; push_cast; rfl
  rw [hsplit]
  by_cases hc2 : (p : ℤ) ∣ c₂
  · have hc1 : ¬ (p : ℤ) ∣ c₁ := fun h => hc ⟨h, hc2⟩
    have hfib : ∀ x : ℤ, (((Icc (-(B : ℤ)) B).filter fun y => (p : ℤ) ∣ c₁ * x + c₂ * y).card : ℝ) =
        if (p : ℤ) ∣ x then 2 * (B : ℝ) + 1 else 0 := by
      intro x
      by_cases hx : (p : ℤ) ∣ x
      · rw [if_pos hx, filter_true_of_mem, hcardIcc]
        intro y _
        exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_left hc2 _)
      · rw [if_neg hx, filter_false_of_mem, card_empty, Nat.cast_zero]
        intro y _ h
        have h1 : (p : ℤ) ∣ c₁ * x := by
          have := dvd_sub h (dvd_mul_of_dvd_left hc2 y)
          simpa using this
        rcases hpp.dvd_or_dvd h1 with h2 | h2
        · exact hc1 h2
        · exact hx h2
    simp_rw [hfib]
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have h1 := card_residue_le (-(A : ℤ)) A (by omega) p hp.pos 0
    simp only [sub_zero] at h1
    have h2 : ((A : ℤ) - -(A : ℤ) + 1 : ℤ) = 2 * A + 1 := by ring
    rw [h2] at h1
    push_cast at h1
    have h3 : (((Icc (-(A : ℤ)) A).filter fun x => (p : ℤ) ∣ x).card : ℝ) * (2 * B + 1) ≤
        ((2 * A + 1) / p + 1) * (2 * B + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
    have : ((2 * (A : ℝ) + 1) / p + 1) * (2 * B + 1) =
        (2 * A + 1) * (2 * B + 1) / p + (2 * B + 1) := by field_simp
    nlinarith
  · have hfib : ∀ x : ℤ, (((Icc (-(B : ℤ)) B).filter fun y => (p : ℤ) ∣ c₁ * x + c₂ * y).card : ℝ) ≤
        (2 * B + 1) / p + 1 := by
      intro x
      set Fx := (Icc (-(B : ℤ)) B).filter fun y => (p : ℤ) ∣ c₁ * x + c₂ * y
      rcases Fx.eq_empty_or_nonempty with h0 | ⟨y₀, hy₀⟩
      · rw [h0, card_empty, Nat.cast_zero]; positivity
      · have hsub : Fx ⊆ (Icc (-(B : ℤ)) B).filter fun y => (p : ℤ) ∣ y - y₀ := by
          intro y hy
          simp only [Fx, mem_filter] at hy hy₀ ⊢
          refine ⟨hy.1, ?_⟩
          have h1 : (p : ℤ) ∣ c₂ * (y - y₀) := by
            have := dvd_sub hy.2 hy₀.2
            rw [show c₁ * x + c₂ * y - (c₁ * x + c₂ * y₀) = c₂ * (y - y₀) by ring] at this
            exact this
          rcases hpp.dvd_or_dvd h1 with h2 | h2
          · exact absurd h2 hc2
          · exact h2
        have h1 := card_residue_le (-(B : ℤ)) B (by omega) p hp.pos y₀
        have h2 : ((B : ℤ) - -(B : ℤ) + 1 : ℤ) = 2 * B + 1 := by ring
        rw [h2] at h1
        push_cast at h1
        exact le_trans (by exact_mod_cast card_le_card hsub) h1
    calc ∑ x ∈ Icc (-(A : ℤ)) A, (((Icc (-(B : ℤ)) B).filter
          fun y => (p : ℤ) ∣ c₁ * x + c₂ * y).card : ℝ) ≤
        ∑ _x ∈ Icc (-(A : ℤ)) A, ((2 * (B : ℝ) + 1) / p + 1) := sum_le_sum fun x _ => hfib x
      _ = (2 * (A : ℝ) + 1) * ((2 * B + 1) / p + 1) := by
          rw [sum_const, nsmul_eq_mul]; congr 1; exact hcardIcc A
      _ = (2 * (A : ℝ) + 1) * (2 * B + 1) / p + (2 * A + 1) := by field_simp
      _ ≤ _ := by linarith


lemma lineOf_le_p (p : ℕ) (hp : 0 < p) (z' : ℤ × ℤ) : lineOf p z' ≤ p := by
  unfold lineOf
  split_ifs
  · exact le_refl _
  · have : NeZero p := ⟨hp.ne'⟩
    exact (ZMod.val_lt _).le

/-- Every line `ℓ ≤ p` has a primitive representative. -/
lemma line_rep (p : ℕ) (hp : p.Prime) (ℓ : ℕ) (hℓ : ℓ ≤ p) :
    ∃ v : ℤ × ℤ, Int.gcd v.1 v.2 = 1 ∧ lineOf p v = ℓ := by
  rcases hℓ.lt_or_eq with h | h
  · refine ⟨(1, ℓ), by simp, ?_⟩
    have : NeZero p := ⟨hp.pos.ne'⟩
    unfold lineOf
    have hnd : ¬ (p : ℤ) ∣ (1 : ℤ) := by
      intro hd
      have : p ∣ 1 := by exact_mod_cast hd
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    rw [if_neg hnd]
    simp only [Int.cast_one, Int.cast_natCast, ZMod.inv_one, mul_one]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]
  · refine ⟨(0, 1), by simp, ?_⟩
    unfold lineOf
    rw [if_pos (dvd_zero _), h]

lemma det_add_smul (h j : ℤ) (z w v : ℤ × ℤ) :
    detZ (h * z.1 + j * w.1, h * z.2 + j * w.2) v = h * detZ z v + j * detZ w v := by
  unfold detZ; ring

open Classical in
/-- **Targets on a prescribed line** ([21] (4.40)). -/
lemma card_line_le (P : MemParams) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    (z : ℤ × ℤ) (hz : P.InBox ω z) (hzp : Int.gcd z.1 z.2 = 1) (D : ℕ) (hD1 : 1 ≤ D)
    (hT : T1 P D ω z) (hY1 : 1 ≤ P.Y) (hYbig : (2 * cLat + 2) ^ 10 ≤ P.Y)
    (p : ℕ) (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ D) (ℓ : ℕ) :
    ((P.zSet.filter fun z' => P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' ∧
      |((detZ z z' / D : ℤ) : ℝ) / P.Y| < 5 ∧ lineOf p z' = ℓ).card : ℝ) ≤
      9 * C1 * P.Y / p + 4 * P.Y ^ (0.9 : ℝ) + 2 := by
  set Sf := P.zSet.filter fun z' => P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' ∧
      |((detZ z z' / D : ℤ) : ℝ) / P.Y| < 5 ∧ lineOf p z' = ℓ
  have hY0 : 0 < P.Y := by linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hC1 := C1_nonneg
  have hRHS : 0 ≤ 9 * C1 * P.Y / p + 4 * P.Y ^ (0.9 : ℝ) + 2 := by
    have := Real.rpow_nonneg hY0.le (0.9 : ℝ); positivity
  by_cases hℓ : ℓ ≤ p
  swap
  · have : Sf = ∅ := by
      ext z'
      simp only [Sf, mem_filter, notMem_empty, iff_false, not_and]
      intro _ _ _ _ h
      exact hℓ (h ▸ lineOf_le_p p hp.pos z')
    rw [this, card_empty, Nat.cast_zero]; exact hRHS
  obtain ⟨v, hvp, hvl⟩ := line_rep p hp ℓ hℓ
  obtain ⟨pp, qq, rr, ss, hdet, A', B', hAB, hA1, hB1, hA2, hB2, hcov⟩ :=
    lattice_box cLat (by unfold cLat; norm_num) P.Y (D * ratioAt ω z) hYbig hT
  set w := complVec z
  have hw : detZ z w = 1 := detZ_complVec z hzp
  set c₁ := pp * detZ z v + D * rr * detZ w v
  set c₂ := qq * detZ z v + D * ss * detZ w v
  set φ := latCoord pp qq rr ss z D
  have hzp' : ∀ z' ∈ Sf, Int.gcd z'.1 z'.2 = 1 := fun z' hz' => by
    exact zSet_gcd (mem_filter.1 hz').1
  -- the image lies in the box and satisfies the congruence
  have hmaps : ∀ z' ∈ Sf, φ z' ∈ (boxZ A' B').filter fun x => (p : ℤ) ∣ c₁ * x.1 + c₂ * x.2 := by
    intro z' hz'
    have hz'' := (mem_filter.1 hz').2
    obtain ⟨hb, hdv, hw5, hl⟩ := hz''
    have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
    -- the region
    have hreg1 : |((detZ z z' / D : ℤ) : ℝ)| ≤ cLat * P.Y := by
      rw [abs_div, abs_of_pos hY0, div_lt_iff₀ hY0] at hw5
      unfold cLat; nlinarith
    have hreg2 : |((detZ z' (complVec z) : ℤ) : ℝ) + ((detZ z z' / D : ℤ) : ℝ) * (D * ratioAt ω z)|
        ≤ cLat := by
      have hτ := tau_pos P ω hω hU z hz
      rw [int_cast_div_of_dvd _ D hD1 hdv]
      have e : (detZ z' (complVec z) : ℝ) + (detZ z z' : ℝ) / D * (D * ratioAt ω z) =
          tauR ω z' / tauR ω z := by
        rw [tauR_decomp' ω z z' hzp hτ.ne']
        have : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
        field_simp
      rw [e]
      have hr := tau_ratio_mem P ω hω hU z z' hz hb
      rw [abs_of_pos (div_pos (tau_pos P ω hω hU z' hb) hτ)]
      unfold cLat; linarith [hr.2]
    have hcv := hcov _ _ hreg1 hreg2
    refine mem_filter.2 ⟨latCoord_mem_box pp qq rr ss hdet z D z' A' B' hcv, ?_⟩
    -- the congruence
    obtain ⟨x, y, _, _, ex, ey⟩ := hcv
    have hφ : φ z' = (x, y) := by
      simp only [φ, latCoord]
      rw [ex, ey]
      ext
      · simp only; linear_combination x * hdet
      · simp only; linear_combination y * hdet
    rw [hφ]
    have hdv' : (p : ℤ) ∣ detZ z' v :=
      (lineOf_eq_iff p hp z' v (hzp' z' hz') hvp).1 (by rw [hl, hvl])
    have hzdec := decomp z w z' hw
    have hdl : detZ z' v = detZ z' w * detZ z v + detZ z z' * detZ w v := by
      conv_lhs => rw [hzdec]
      exact det_add_smul _ _ z w v
    obtain ⟨k, hk⟩ := hdv
    have hlk : detZ z z' / D = k := by rw [hk, Int.mul_ediv_cancel_left _ hD0]
    rw [hlk] at ey
    have : detZ z' v = c₁ * x + c₂ * y := by
      rw [hdl, ex, hk, ey]; simp only [c₁, c₂]; ring
    rw [← this]; exact hdv'
  have hinj : Set.InjOn φ Sf := by
    intro a ha b hb h
    exact latCoord_injOn pp qq rr ss hdet z hzp D hD1 a b (mem_filter.1 ha).2.2.1
      (mem_filter.1 hb).2.2.1 h
  -- the congruence is nonzero
  have hnz : ¬ ((p : ℤ) ∣ c₁ ∧ (p : ℤ) ∣ c₂) := by
    rintro ⟨h1, h2⟩
    have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have ha : (p : ℤ) ∣ detZ z v := by
      have := dvd_sub (dvd_mul_of_dvd_right h1 ss) (dvd_mul_of_dvd_right h2 rr)
      have e : ss * c₁ - rr * c₂ = (pp * ss - qq * rr) * detZ z v := by simp only [c₁, c₂]; ring
      rw [e, hdet, one_mul] at this; exact this
    have hb : (p : ℤ) ∣ D * detZ w v := by
      have := dvd_sub (dvd_mul_of_dvd_right h2 pp) (dvd_mul_of_dvd_right h1 qq)
      have e : pp * c₂ - qq * c₁ = (pp * ss - qq * rr) * (D * detZ w v) := by
        simp only [c₁, c₂]; ring
      rw [e, hdet, one_mul] at this; exact this
    have hb' : (p : ℤ) ∣ detZ w v := by
      rcases hpp.dvd_or_dvd hb with h | h
      · exact absurd h hpD
      · exact h
    have hv := decomp z w v hw
    have h1' : (p : ℤ) ∣ v.1 := by
      rw [hv]
      have : (p : ℤ) ∣ detZ v w := by rw [detZ_swap]; exact dvd_neg.2 hb'
      exact dvd_add (dvd_mul_of_dvd_left this _) (dvd_mul_of_dvd_left ha _)
    have h2' : (p : ℤ) ∣ v.2 := by
      rw [hv]
      have : (p : ℤ) ∣ detZ v w := by rw [detZ_swap]; exact dvd_neg.2 hb'
      exact dvd_add (dvd_mul_of_dvd_left this _) (dvd_mul_of_dvd_left ha _)
    have := Int.dvd_gcd h1' h2'
    rw [hvp] at this
    have : p ∣ 1 := by exact_mod_cast this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hcard : (Sf.card : ℝ) ≤ (((boxZ A' B').filter fun x => (p : ℤ) ∣ c₁ * x.1 + c₂ * x.2).card : ℝ) := by
    rw [← card_image_of_injOn hinj]
    exact_mod_cast card_le_card fun x hx => by
      obtain ⟨z', hz', rfl⟩ := mem_image.1 hx; exact hmaps z' hz'
  refine hcard.trans ((card_lin_cong_le A' B' p hp c₁ c₂ hnz).trans ?_)
  have hA1' : (1 : ℝ) ≤ A' := le_trans (Real.one_le_rpow hY1 (by norm_num)) hA1
  have hB1' : (1 : ℝ) ≤ B' := le_trans (Real.one_le_rpow hY1 (by norm_num)) hB1
  have hAB' : ((2 * A' + 1) * (2 * B' + 1) : ℝ) ≤ 9 * C1 * P.Y := by
    have : (A' : ℝ) * B' ≤ C1 * P.Y := by unfold C1; exact hAB
    nlinarith
  have : (2 * (A' : ℝ) + 1) * (2 * B' + 1) / p ≤ 9 * C1 * P.Y / p :=
    div_le_div_of_nonneg_right hAB' hpR.le
  linarith

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: R3, comparison rows with a promotion ([21] (4.41))

A promoted particle requires a prescribed line of the target at its prime `p ∤ D`; by
`card_line_le` only `≪ Y/p + Y^{0.9}` targets in the `ψ`-window qualify, against the comparison
multiplier `≪ L^{3A₀}/Y`. `rowSum_D1_maj_le`:
`rowSum(D1, maj) ≤ 2^K K · 2B (2+2B)^K · 4L^{3A₀}/Y · (9C₁Y/p_min + 4Y^{0.9} + 2)`. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

lemma not_dvd_padProd (hEP : EP P) (ℓ : P.Lst) (hℓ : ℓ ∈ listCands P.x P.a P.J) (i : Fin P.K)
    (p : ℕ) (hp : p ∈ P.grp i) (hban : p ∉ Set.range (ℓ i)) : ¬ (p : ℤ) ∣ padProd ℓ := by
  intro h
  have hpp := grp_prime hp
  have h' : p ∣ padProd ℓ := by exact_mod_cast h
  simp only [listCands, Fintype.mem_piFinset] at hℓ
  unfold padProd at h'
  obtain ⟨i', -, hi'⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 h'
  obtain ⟨k, -, hk⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hi'
  have hq := grp_prime (hℓ i' k.castSucc)
  have he : p = ℓ i' k.castSucc := (Nat.prime_dvd_prime_iff_eq hpp hq).1 hk
  by_cases hii : i = i'
  · subst hii; exact hban ⟨_, he.symm⟩
  · exact absurd (hEP.hdisj i i' hii) (Finset.not_disjoint_iff.2 ⟨p, hp, he ▸ hℓ i' k.castSucc⟩)

lemma sum_memAt_lines_le (m : P.Mem) (i : Fin P.K) :
    ∑ p ∈ P.grp i, ∑ ℓ ∈ range (p + 1), (P.memAt m (i, p, ℓ) : ℝ) ≤ P.memSize m := by
  classical
  have hmem : ∀ p ∈ P.grp i, ∀ ℓ ∈ range (p + 1), (i, p, ℓ) ∈ P.partSet := by
    intro p hp ℓ hℓ
    unfold MemParams.partSet
    simp only [mem_biUnion, mem_univ, true_and, mem_image]
    exact ⟨i, p, hp, ℓ, hℓ, rfl⟩
  set S := (P.grp i).sigma fun p => range (p + 1)
  set g : (Σ _ : ℕ, ℕ) → Fin P.K × ℕ × ℕ := fun q => (i, q.1, q.2)
  have hS : ∀ q ∈ S, g q ∈ P.partSet := by
    intro q hq
    rw [mem_sigma] at hq
    exact hmem q.1 hq.1 q.2 hq.2
  have hinj : Set.InjOn g S := by
    intro q _ q' _ h
    simp only [g, Prod.mk.injEq] at h
    exact Sigma.ext h.2.1 (heq_of_eq h.2.2)
  calc ∑ p ∈ P.grp i, ∑ ℓ ∈ range (p + 1), (P.memAt m (i, p, ℓ) : ℝ) =
      ∑ q ∈ S, (P.memAt m (g q) : ℝ) := by rw [sum_sigma]
    _ = ∑ q ∈ S.attach, ((m ⟨g q.1, hS q.1 q.2⟩ : ℕ) : ℝ) := by
        rw [← sum_attach]
        refine sum_congr rfl fun q _ => ?_
        rw [memAt_of_mem P m _ (hS q.1 q.2)]
    _ = ∑ y ∈ S.attach.image (fun q => (⟨g q.1, hS q.1 q.2⟩ : P.PT)), ((m y : ℕ) : ℝ) := by
        rw [sum_image]
        intro a _ b _ h
        have := congrArg Subtype.val h
        exact Subtype.ext (hinj a.2 b.2 this)
    _ ≤ ∑ y : P.PT, ((m y : ℕ) : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.cast_nonneg _
    _ = P.memSize m := by unfold MemParams.memSize; push_cast; rfl

/-- The group factor with a forced promotion in group `i₀`. -/
noncomputable def gfD (D : ℕ) (m : P.Mem) (z' : ℤ × ℤ) (i₀ i : Fin P.K) (q : ℕ × Bool) : ℝ :=
  if i = i₀ then (if q.2 ∧ ¬ (q.1 : ℤ) ∣ D then 2 * (P.memAt m (i, q.1, lineOf q.1 z') : ℝ) else 0)
  else gfac P m z' i q

lemma gfD_nonneg (hEP : EP P) (D : ℕ) (m : P.Mem) (z' : ℤ × ℤ) (i₀ i : Fin P.K) (q : ℕ × Bool)
    (hq : q.1 ∈ P.grp i) : 0 ≤ gfD P D m z' i₀ i q := by
  unfold gfD; split_ifs
  · positivity
  · exact le_refl 0
  · exact gfac_nonneg P hEP m z' i q hq

open Classical in
/-- **R3**: comparison rows with a promotion. -/
theorem rowSum_D1_maj_le (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    (j : ℕ) (s : P.MState) (hs : s ∈ P.stSet) (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀)
    (hY1 : 1 ≤ P.Y) (hYbig : (2 * cLat + 2) ^ 10 ≤ P.Y) (pmin : ℝ) (hpmin1 : 1 ≤ pmin)
    (hpmin : ∀ i, ∀ p ∈ P.grp i, pmin ≤ p) :
    rowSum P (clsD1 P) (majK P j) ω s ≤
      2 ^ P.K * P.K * (2 * (4 * log P.x ^ (3 * P.A₀) / P.Y) * (2 + 2 * P.B) ^ P.K *
        ((9 * C1 * P.Y / pmin + 4 * P.Y ^ (0.9 : ℝ) + 2) * P.B)) := by
  obtain ⟨hz, hℓs, hm⟩ := stSet_parts P s hs
  have hY0 : 0 < P.Y := by linarith
  set MA := 4 * log P.x ^ (3 * P.A₀) / P.Y
  have hMA : 0 ≤ MA := by positivity
  set D := padProd s.2.1
  have hD1 : 1 ≤ D := padProd_pos P s hs
  set Cnt := 9 * C1 * P.Y / pmin + 4 * P.Y ^ (0.9 : ℝ) + 2
  have hCnt : 0 ≤ Cnt := by
    have := C1_nonneg; have := Real.rpow_nonneg hY0.le (0.9 : ℝ)
    have : 0 < pmin := by linarith
    positivity
  set Tg := Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool))
  have hB : (P.memSize s.2.2 : ℝ) ≤ P.B := memSize_le P s.2.2 hm
  have hB0 : (0 : ℝ) ≤ P.B := Nat.cast_nonneg _
  rw [rowSum_eq]
  by_cases hsrc : P.InBox ω s.1 ∧ P.d₀ ≤ D ∧ P.GoodAt ω s.1 s.2.1
  swap
  · refine le_trans (le_of_eq (sum_eq_zero fun St _ => sum_eq_zero fun z' _ =>
      sum_eq_zero fun tg _ => ?_)) (by positivity)
    unfold coeffP coeffK
    split_ifs with h1 h2
    · exact absurd ⟨h2.1.2.2.2.2.2.1, h2.1.2.2.1, h2.1.2.2.2.2.2.2.2.1⟩ hsrc
    · simp
    · simp
  have hT1 : T1 P D ω s.1 := T1_of_good P ω s.1 s.2.1 hsrc.2.2
  set W : ℤ × ℤ → ℝ := fun z' => if P.InBox ω z' ∧ (D : ℤ) ∣ detZ s.1 z' ∧
    |((detZ s.1 z' / D : ℤ) : ℝ) / P.Y| < 5 then MA else 0
  have hW : ∀ z', 0 ≤ W z' := fun z' => by simp only [W]; split_ifs <;> linarith
  -- the pointwise bound
  have hstep : ∀ St, ∀ z' ∈ P.zSet, ∀ tg ∈ Tg, ‖coeffP P (clsD1 P) (majK P j) ω s (St, z', tg)‖ ≤
      ∑ i₀, (∏ i, gfD P D s.2.2 z' i₀ i (tg i)) * W z' := by
    intro St z' hz' tg htg
    have hc := ecChoice_mem P St z' hz' tg htg
    have htg' : ∀ i, (tg i).1 ∈ P.grp i := (mem_choices P _ hc).2
    have hnn : ∀ i₀, 0 ≤ (∏ i, gfD P D s.2.2 z' i₀ i (tg i)) * W z' := fun i₀ =>
      mul_nonneg (prod_nonneg fun i _ => gfD_nonneg P hEP D s.2.2 z' i₀ i _ (htg' i)) (hW z')
    unfold coeffP clsD1
    by_cases hI : (promSet P (St, z', tg)).Nonempty
    · rw [if_pos hI]
      obtain ⟨i₀, hi₀⟩ := hI
      have hfl : (tg i₀).2 = true := by simpa [promSet] using hi₀
      refine (norm_coeffK_le P hEP _ ω s _ hc).trans ?_
      by_cases hE : ECond P ω s (St, z', tg)
      · rw [if_pos hE]
        have hban : ¬ (((tg i₀).1 : ℕ) : ℤ) ∣ D :=
          not_dvd_padProd P hEP s.2.1 hℓs i₀ _ (htg' i₀) (hE.1.2.1 i₀)
        have heq : ∏ i, gfac P s.2.2 z' i (tg i) = ∏ i, gfD P D s.2.2 z' i₀ i (tg i) := by
          refine prod_congr rfl fun i _ => ?_
          unfold gfD gfac
          by_cases hii : i = i₀
          · subst hii; rw [if_pos rfl, if_pos hfl, if_pos ⟨hfl, hban⟩]
          · rw [if_neg hii]
        have hk := norm_majK_le P j (detZ s.1 z' / D) (∏ i, (tg i).1) (lastProd s.2.1) D
          hsrc.2.1 hD1 hL hA₀ hY0
        have hWb : ‖majK P j (detZ s.1 z' / D) (∏ i, (tg i).1) (lastProd s.2.1) D‖ ≤ W z' := by
          simp only [W]
          by_cases hw : |((detZ s.1 z' / D : ℤ) : ℝ) / P.Y| < 5
          · rw [if_pos hw, one_mul] at hk
            rw [if_pos ⟨hE.1.2.2.2.2.2.2.1, hE.1.2.2.2.2.1, hw⟩]; exact hk
          · rw [if_neg hw, zero_mul] at hk
            exact hk.trans (by split_ifs <;> linarith)
        rw [heq]
        calc (∏ i, gfD P D s.2.2 z' i₀ i (tg i)) *
              ‖majK P j (detZ s.1 z' / D) (∏ i, (tg i).1) (lastProd s.2.1) D‖ ≤
            (∏ i, gfD P D s.2.2 z' i₀ i (tg i)) * W z' :=
              mul_le_mul_of_nonneg_left hWb
                (prod_nonneg fun i _ => gfD_nonneg P hEP D s.2.2 z' i₀ i _ (htg' i))
          _ ≤ _ := single_le_sum (f := fun i₀ => (∏ i, gfD P D s.2.2 z' i₀ i (tg i)) * W z')
              (fun i _ => hnn i) (mem_univ i₀)
      · rw [if_neg hE]; exact sum_nonneg fun i _ => hnn i
    · rw [if_neg hI, norm_zero]; exact sum_nonneg fun i _ => hnn i
  -- the factor of the promoted group
  set Sp : Fin P.K → ℤ × ℤ → ℝ := fun i₀ z' => ∑ p ∈ P.grp i₀,
    (if ¬ (p : ℤ) ∣ D then 2 * (P.memAt s.2.2 (i₀, p, lineOf p z') : ℝ) else 0)
  have hSp0 : ∀ i₀ z', 0 ≤ Sp i₀ z' := fun i₀ z' =>
    sum_nonneg fun p _ => by split_ifs <;> positivity
  have htgsum : ∀ i₀, ∀ z', ∑ tg ∈ Tg, ∏ i, gfD P D s.2.2 z' i₀ i (tg i) ≤
      Sp i₀ z' * (2 + 2 * P.B) ^ P.K := by
    intro i₀ z'
    rw [← prod_univ_sum]
    have hT : ∀ i, 0 ≤ ∑ q ∈ P.grp i ×ˢ (univ : Finset Bool), gfD P D s.2.2 z' i₀ i q :=
      fun i => sum_nonneg fun q hq => gfD_nonneg P hEP D s.2.2 z' i₀ i q (mem_product.1 hq).1
    rw [← mul_prod_erase univ _ (mem_univ i₀)]
    have h1 : ∑ q ∈ P.grp i₀ ×ˢ (univ : Finset Bool), gfD P D s.2.2 z' i₀ i₀ q = Sp i₀ z' := by
      rw [sum_product]
      refine sum_congr rfl fun p _ => ?_
      rw [Fintype.sum_bool]
      unfold gfD
      by_cases hpD : ((p : ℕ) : ℤ) ∣ D <;> simp [hpD]
    have h2 : ∏ i ∈ univ.erase i₀, ∑ q ∈ P.grp i ×ˢ (univ : Finset Bool),
        gfD P D s.2.2 z' i₀ i q ≤ (2 + 2 * P.B) ^ P.K := by
      calc ∏ i ∈ univ.erase i₀, ∑ q ∈ P.grp i ×ˢ (univ : Finset Bool), gfD P D s.2.2 z' i₀ i q ≤
          ∏ _i ∈ univ.erase i₀, (2 + 2 * (P.B : ℝ)) := by
            refine prod_le_prod (fun i _ => hT i) fun i hi => ?_
            have hne := ne_of_mem_erase hi
            have : ∀ q, gfD P D s.2.2 z' i₀ i q = gfac P s.2.2 z' i q := fun q => by
              unfold gfD; rw [if_neg hne]
            simp_rw [this]
            rw [sum_product]
            calc ∑ p ∈ P.grp i, ∑ fl : Bool, gfac P s.2.2 z' i (p, fl) =
                ∑ p ∈ P.grp i, (P.nu i p + 2 * (P.memAt s.2.2 (i, p, lineOf p z') : ℝ)) := by
                  refine sum_congr rfl fun p _ => ?_
                  rw [Fintype.sum_bool]; unfold gfac
                  simp only [if_true, Bool.false_eq_true, if_false]; ring
              _ = ∑ p ∈ P.grp i, P.nu i p +
                  2 * ∑ p ∈ P.grp i, (P.memAt s.2.2 (i, p, lineOf p z') : ℝ) := by
                  rw [sum_add_distrib, mul_sum]
              _ ≤ 2 + 2 * P.B := by
                  have := hEP.sum_nu_le i
                  have := sum_memAt_le P s.2.2 z' i
                  linarith
        _ = (2 + 2 * (P.B : ℝ)) ^ (P.K - 1) := by
            rw [prod_const, card_erase_of_mem (mem_univ i₀), card_univ, Fintype.card_fin]
        _ ≤ _ := pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 (hSp0 i₀ z')
  have hzsum : ∀ i₀, ∑ z' ∈ P.zSet, W z' * Sp i₀ z' ≤ 2 * MA * Cnt * P.B := by
    intro i₀
    have hp : ∀ p ∈ P.grp i₀, ¬ (p : ℤ) ∣ D → ∑ z' ∈ P.zSet,
        W z' * (P.memAt s.2.2 (i₀, p, lineOf p z') : ℝ) ≤
        MA * Cnt * ∑ ℓ ∈ range (p + 1), (P.memAt s.2.2 (i₀, p, ℓ) : ℝ) := by
      intro p hpg hpD
      have hpp := grp_prime hpg
      have hsplit : ∀ z', W z' * (P.memAt s.2.2 (i₀, p, lineOf p z') : ℝ) =
          ∑ ℓ ∈ range (p + 1), (if lineOf p z' = ℓ then W z' else 0) *
            (P.memAt s.2.2 (i₀, p, ℓ) : ℝ) := by
        intro z'
        rw [sum_eq_single (lineOf p z')]
        · rw [if_pos rfl]
        · intro b _ hb; rw [if_neg (Ne.symm hb), zero_mul]
        · intro h; exact absurd (mem_range.2 (Nat.lt_succ_of_le (lineOf_le_p p hpp.pos z'))) h
      simp_rw [hsplit]
      rw [sum_comm, mul_sum]
      refine sum_le_sum fun ℓ _ => ?_
      rw [← sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      have hc := card_line_le P ω hω hU s.1 hsrc.1 (zSet_prim P s.1 hz) D hD1 hT1 hY1 hYbig p hpp
        hpD ℓ
      calc ∑ z' ∈ P.zSet, (if lineOf p z' = ℓ then W z' else 0) =
          MA * ((P.zSet.filter fun z' => P.InBox ω z' ∧ (D : ℤ) ∣ detZ s.1 z' ∧
            |((detZ s.1 z' / D : ℤ) : ℝ) / P.Y| < 5 ∧ lineOf p z' = ℓ).card : ℝ) := by
            rw [card_filter]; push_cast; rw [mul_sum]
            refine sum_congr rfl fun z' _ => ?_
            simp only [W]
            by_cases h1 : lineOf p z' = ℓ
            · rw [if_pos h1]
              by_cases h2 : P.InBox ω z' ∧ (D : ℤ) ∣ detZ s.1 z' ∧
                  |((detZ s.1 z' / D : ℤ) : ℝ) / P.Y| < 5
              · rw [if_pos h2, if_pos ⟨h2.1, h2.2.1, h2.2.2, h1⟩]; ring
              · rw [if_neg h2, if_neg (fun h => h2 ⟨h.1, h.2.1, h.2.2.1⟩)]; ring
            · rw [if_neg h1, if_neg (fun h => h1 h.2.2.2)]; ring
        _ ≤ MA * Cnt := by
            apply mul_le_mul_of_nonneg_left (hc.trans _) hMA
            have hp0 : (0 : ℝ) < pmin := by linarith
            have : 9 * C1 * P.Y / p ≤ 9 * C1 * P.Y / pmin :=
              div_le_div_of_nonneg_left (by have := C1_nonneg; positivity) hp0 (hpmin i₀ p hpg)
            simp only [Cnt]; linarith
    calc ∑ z' ∈ P.zSet, W z' * Sp i₀ z' = ∑ p ∈ P.grp i₀, (if ¬ (p : ℤ) ∣ D then 2 *
          ∑ z' ∈ P.zSet, W z' * (P.memAt s.2.2 (i₀, p, lineOf p z') : ℝ) else 0) := by
          simp only [Sp, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun p _ => ?_
          by_cases hpD : ¬ ((p : ℕ) : ℤ) ∣ D
          · simp only [if_pos hpD]; exact sum_congr rfl fun z' _ => by ring
          · simp only [if_neg hpD, mul_zero, sum_const_zero]
      _ ≤ ∑ p ∈ P.grp i₀, 2 * (MA * Cnt *
          ∑ ℓ ∈ range (p + 1), (P.memAt s.2.2 (i₀, p, ℓ) : ℝ)) := by
          refine sum_le_sum fun p hpg => ?_
          by_cases hpD : ¬ ((p : ℕ) : ℤ) ∣ D
          · rw [if_pos hpD]; exact mul_le_mul_of_nonneg_left (hp p hpg hpD) (by norm_num)
          · rw [if_neg hpD]
            have : (0 : ℝ) ≤ ∑ ℓ ∈ range (p + 1), (P.memAt s.2.2 (i₀, p, ℓ) : ℝ) :=
              sum_nonneg fun _ _ => Nat.cast_nonneg _
            have hc0 : 0 ≤ MA * Cnt := mul_nonneg hMA hCnt
            positivity
      _ = 2 * MA * Cnt * ∑ p ∈ P.grp i₀, ∑ ℓ ∈ range (p + 1),
          (P.memAt s.2.2 (i₀, p, ℓ) : ℝ) := by rw [mul_sum]; exact sum_congr rfl fun p _ => by ring
      _ ≤ 2 * MA * Cnt * P.B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (sum_memAt_lines_le P s.2.2 i₀).trans hB
  calc ∑ St : Finset (Fin P.K), ∑ z' ∈ P.zSet, ∑ tg ∈ Tg,
        ‖coeffP P (clsD1 P) (majK P j) ω s (St, z', tg)‖ ≤
      ∑ _St : Finset (Fin P.K), ∑ z' ∈ P.zSet, ∑ tg ∈ Tg, ∑ i₀,
        (∏ i, gfD P D s.2.2 z' i₀ i (tg i)) * W z' :=
        sum_le_sum fun St _ => sum_le_sum fun z' hz' => sum_le_sum fun tg htg =>
          hstep St z' hz' tg htg
    _ = ∑ _St : Finset (Fin P.K), ∑ i₀, ∑ z' ∈ P.zSet,
        W z' * ∑ tg ∈ Tg, ∏ i, gfD P D s.2.2 z' i₀ i (tg i) := by
        refine sum_congr rfl fun St _ => ?_
        rw [Finset.sum_congr rfl fun z' (_ : z' ∈ P.zSet) => Finset.sum_comm, Finset.sum_comm]
        refine sum_congr rfl fun i₀ _ => sum_congr rfl fun z' _ => ?_
        rw [mul_sum]; exact sum_congr rfl fun tg _ => by ring
    _ ≤ ∑ _St : Finset (Fin P.K), ∑ _i₀ : Fin P.K,
        (2 + 2 * (P.B : ℝ)) ^ P.K * (2 * MA * Cnt * P.B) := by
        refine sum_le_sum fun St _ => sum_le_sum fun i₀ _ => ?_
        calc ∑ z' ∈ P.zSet, W z' * ∑ tg ∈ Tg, ∏ i, gfD P D s.2.2 z' i₀ i (tg i) ≤
            ∑ z' ∈ P.zSet, W z' * (Sp i₀ z' * (2 + 2 * P.B) ^ P.K) :=
              sum_le_sum fun z' _ => mul_le_mul_of_nonneg_left (htgsum i₀ z') (hW z')
          _ = (2 + 2 * P.B) ^ P.K * ∑ z' ∈ P.zSet, W z' * Sp i₀ z' := by
              rw [mul_sum]; exact sum_congr rfl fun z' _ => by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hzsum i₀) (by positivity)
    _ = _ := by
        rw [sum_const, sum_const, card_univ, card_univ, Fintype.card_finset, Fintype.card_fin,
          nsmul_eq_mul, nsmul_eq_mul]
        push_cast; ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: R1, raw rows with a promotion ([21] (4.35)–(4.38))

Under the source symmetrization the row of a source with lists `ℓ ∘ π` depends on `π` only through
the omission tuple `o = (πᵢ(last))ᵢ`, and every omission tuple has mass `M^{-K}` (`avg_omit`).
For a promoted group set `I` with `i* = max I` and fresh draws `T`, outside the exceptional mass of
test (ii) the integer `D Z` is unique (`uniq_num`), hence so are `o` and the promoted primes
(`uniq_fac`); the other promoted groups are damped by `n ρ^{n−1} ≤ 4`.
`avgRow_D1_raw_le`: `avgRow(D1, raw) ≤ 4^K (32 B 8^K / M^K + 16 (2+4B)^K e^{−L^{0.1}/4})`. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-! ## Omission tuples of slot permutations -/

/-- The omission tuple of a slot permutation: the slot moved to the last position. -/
def omitOf (pr : SlotPerm P) : Fin P.K → Fin (P.J + 1) := fun i => pr i (Fin.last P.J)

lemma omitProd_permL (ℓ : P.Lst) (pr : SlotPerm P) (o : Fin P.K → Fin (P.J + 1)) :
    omitProd (permL P pr ℓ) o = omitProd ℓ (fun i => pr i (o i)) := by
  unfold omitProd permL
  refine prod_congr rfl fun i _ => ?_
  have : (univ.erase (o i)).map (pr i).toEmbedding = univ.erase (pr i (o i)) := by
    ext j
    simp only [mem_map_equiv, mem_erase, mem_univ, and_true]
    rw [ne_eq, ne_eq, Equiv.symm_apply_eq]
  rw [← this, prod_map]
  rfl

lemma padProd_permL (ℓ : P.Lst) (pr : SlotPerm P) :
    padProd (permL P pr ℓ) = omitProd ℓ (omitOf P pr) := by
  rw [← omitProd_last P (permL P pr ℓ), omitProd_permL]; rfl

lemma lastProd_permL (ℓ : P.Lst) (pr : SlotPerm P) :
    lastProd (permL P pr ℓ) = ∏ i, ℓ i (omitOf P pr i) := rfl

lemma omit_mul_last (ℓ : P.Lst) (o : Fin P.K → Fin (P.J + 1)) :
    omitProd ℓ o * ∏ i, ℓ i (o i) = listProd ℓ := by
  unfold omitProd listProd
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ => prod_erase_mul _ _ (mem_univ _)

lemma sepFails_permL (ℓ : P.Lst) (pr : SlotPerm P) (I : Finset (Fin P.K)) (i₀ : Fin P.K)
    (T : Fin P.K → ℕ) (r : ℝ) :
    SepFails P.x P.a (permL P pr ℓ) I i₀ T r ↔ SepFails P.x P.a ℓ I i₀ T r := by
  set e : (Fin P.K → Fin (P.J + 1)) ≃ (Fin P.K → Fin (P.J + 1)) := Equiv.piCongrRight pr
  have he : ∀ o, (fun i => pr i (e.symm o i)) = o := fun o => by
    funext i; exact congrFun (e.apply_symm_apply o) i
  unfold SepFails
  simp only [omitProd_permL]
  constructor
  · rintro ⟨o, o', Z, Z', h⟩; exact ⟨_, _, Z, Z', h⟩
  · rintro ⟨o, o', Z, Z', h⟩
    refine ⟨e.symm o, e.symm o', Z, Z', ?_⟩
    rwa [he o, he o']

lemma goodTestTwo_permL (ℓ : P.Lst) (pr : SlotPerm P) (r : ℝ) :
    GoodTestTwo P.x P.a (permL P pr ℓ) r ↔ GoodTestTwo P.x P.a ℓ r := by
  classical
  unfold GoodTestTwo
  have hsum : ∀ (I : Finset (Fin P.K)) (hI : I.Nonempty),
      (∑ T ∈ freshTuples P.x P.a I, freshWeight P.x P.a I T *
        if SepFails P.x P.a (permL P pr ℓ) I (I.max' hI) T r then (1 : ℝ) else 0) =
      ∑ T ∈ freshTuples P.x P.a I, freshWeight P.x P.a I T *
        if SepFails P.x P.a ℓ I (I.max' hI) T r then (1 : ℝ) else 0 := fun I hI =>
    sum_congr rfl fun T _ => by
      congr 1
      by_cases h : SepFails P.x P.a ℓ I (I.max' hI) T r
      · rw [if_pos ((sepFails_permL P _ _ _ _ _ _).2 h), if_pos h]
      · rw [if_neg (fun h' => h ((sepFails_permL P _ _ _ _ _ _).1 h')), if_neg h]
  simp only [hsum]

/-! ## Every omission tuple has mass `M^{-K}` -/

lemma card_fib_eq (o o' : Fin P.K → Fin (P.J + 1)) :
    (univ.filter fun pr : SlotPerm P => omitOf P pr = o).card =
      (univ.filter fun pr : SlotPerm P => omitOf P pr = o').card := by
  refine card_nbij' (fun pr i => Equiv.swap (o i) (o' i) * pr i)
    (fun pr i => Equiv.swap (o i) (o' i) * pr i) ?_ ?_ ?_ ?_
  · intro pr hpr
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hpr ⊢
    funext i
    simp only [omitOf, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [show pr i (Fin.last P.J) = o i from congrFun hpr i, Equiv.swap_apply_left]
  · intro pr hpr
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hpr ⊢
    funext i
    simp only [omitOf, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [show pr i (Fin.last P.J) = o' i from congrFun hpr i, Equiv.swap_apply_right]
  · intro pr _
    funext i
    show Equiv.swap (o i) (o' i) * (Equiv.swap (o i) (o' i) * pr i) = pr i
    exact Equiv.swap_mul_self_mul _ _ _
  · intro pr _
    funext i
    show Equiv.swap (o i) (o' i) * (Equiv.swap (o i) (o' i) * pr i) = pr i
    exact Equiv.swap_mul_self_mul _ _ _

lemma avg_omit (F : (Fin P.K → Fin (P.J + 1)) → ℝ) :
    ((Fintype.card (SlotPerm P) : ℕ) : ℝ)⁻¹ * ∑ pr : SlotPerm P, F (omitOf P pr) =
      (((P.J + 1 : ℕ) : ℝ) ^ P.K)⁻¹ * ∑ o, F o := by
  classical
  set c := (univ.filter fun pr : SlotPerm P => omitOf P pr = fun _ => Fin.last P.J).card
  have hfib : ∀ o, (univ.filter fun pr : SlotPerm P => omitOf P pr = o).card = c :=
    fun o => card_fib_eq P o _
  have h1 : ∑ pr : SlotPerm P, F (omitOf P pr) = ∑ o, (c : ℝ) * F o := by
    rw [← sum_fiberwise univ (omitOf P) (fun pr => F (omitOf P pr))]
    refine sum_congr rfl fun o _ => ?_
    rw [sum_congr rfl (fun pr hpr => by rw [(mem_filter.1 hpr).2]), sum_const, hfib,
      nsmul_eq_mul]
  have h2 : Fintype.card (SlotPerm P) = (P.J + 1) ^ P.K * c := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := omitOf P) (t := univ)
      (fun _ _ => mem_univ _)]
    simp only [hfib, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul]
  have hN : 0 < Fintype.card (SlotPerm P) := Fintype.card_pos
  have hc : (c : ℝ) ≠ 0 := by
    have : c ≠ 0 := by intro h0; rw [h0, mul_zero] at h2; omega
    exact_mod_cast this
  rw [h1, h2, ← mul_sum]
  push_cast
  field_simp

/-! ## Splitting the target labels by the promoted groups -/

/-- The target tuple with promoted primes `Pp` on `I` and fresh primes `Tf` off `I`. -/
def mkTg (I : Finset (Fin P.K)) (Tf Pp : Fin P.K → ℕ) : Fin P.K → ℕ × Bool :=
  fun i => if i ∈ I then (Pp i, true) else (Tf i, false)

/-- The promoted prime tuples (`1` off `I`). -/
noncomputable def promT (I : Finset (Fin P.K)) : Finset (Fin P.K → ℕ) :=
  Fintype.piFinset fun i => if i ∈ I then P.grp i else {1}

/-- The flagged groups of a target tuple. -/
def flagSet (tg : Fin P.K → ℕ × Bool) : Finset (Fin P.K) := univ.filter fun i => (tg i).2 = true

lemma flagSet_mkTg (I : Finset (Fin P.K)) (Tf Pp : Fin P.K → ℕ) :
    flagSet P (mkTg P I Tf Pp) = I := by
  ext i; unfold flagSet mkTg
  by_cases h : i ∈ I <;> simp [h]

lemma sum_tg_split (H : (Fin P.K → ℕ × Bool) → ℝ) :
    ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
      (if (flagSet P tg).Nonempty then H tg else 0) =
    ∑ I ∈ univ.filter (fun I : Finset (Fin P.K) => I.Nonempty),
      ∑ Tf ∈ freshTuples P.x P.a I, ∑ Pp ∈ promT P I, H (mkTg P I Tf Pp) := by
  classical
  set Tg := Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool))
  rw [← sum_filter, ← sum_fiberwise_of_maps_to (g := flagSet P)
    (t := univ.filter (fun I : Finset (Fin P.K) => I.Nonempty))
    (fun tg htg => by simp only [mem_filter, mem_univ, true_and]; exact (mem_filter.1 htg).2)]
  refine sum_congr rfl fun I hI => ?_
  rw [← sum_product']
  have hback : ∀ tg, tg ∈ Tg → flagSet P tg = I →
      mkTg P I (fun i => if i ∈ I then 1 else (tg i).1)
        (fun i => if i ∈ I then (tg i).1 else 1) = tg := by
    intro tg _ htg2
    funext i
    have hfl : (tg i).2 = true ↔ i ∈ I := by
      rw [← htg2]; simp [flagSet]
    simp only [mkTg]
    split_ifs with h
    · exact Prod.ext rfl (hfl.2 h).symm
    · refine Prod.ext rfl ?_
      simp only
      cases h' : (tg i).2
      · rfl
      · exact absurd (hfl.1 h') h
  refine sum_nbij'
    (fun tg => (fun i => if i ∈ I then 1 else (tg i).1, fun i => if i ∈ I then (tg i).1 else 1))
    (fun q => mkTg P I q.1 q.2) ?_ ?_ ?_ ?_ ?_
  · intro tg htg
    rw [mem_filter, mem_filter] at htg
    have hT := htg.1.1
    simp only [Tg, Fintype.mem_piFinset, mem_product] at hT
    rw [mem_product]
    simp only [freshTuples, promT, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · split_ifs with h
      · exact mem_singleton_self _
      · exact (hT i).1
    · split_ifs with h
      · exact (hT i).1
      · exact mem_singleton_self _
  · intro q hq
    rw [mem_product] at hq
    simp only [freshTuples, promT, Fintype.mem_piFinset] at hq
    rw [mem_filter, mem_filter]
    refine ⟨⟨?_, ?_⟩, flagSet_mkTg P I q.1 q.2⟩
    · simp only [Tg, Fintype.mem_piFinset, mem_product, mem_univ, and_true]
      intro i
      unfold mkTg
      have h1 := hq.1 i; have h2 := hq.2 i
      split_ifs with h
      · rw [if_pos h] at h2; exact h2
      · rw [if_neg h] at h1; exact h1
    · rw [flagSet_mkTg]; exact (mem_filter.1 hI).2
  · intro tg htg
    rw [mem_filter, mem_filter] at htg
    exact hback tg htg.1.1 htg.2
  · intro q hq
    rw [mem_product] at hq
    simp only [freshTuples, promT, Fintype.mem_piFinset] at hq
    ext i
    · simp only [mkTg]
      have h1 := hq.1 i
      split_ifs with h
      · rw [if_pos h] at h1; exact (mem_singleton.1 h1).symm
      · rfl
    · simp only [mkTg]
      have h2 := hq.2 i
      split_ifs with h
      · rfl
      · rw [if_neg h] at h2; exact (mem_singleton.1 h2).symm
  · intro tg htg
    rw [mem_filter, mem_filter] at htg
    rw [hback tg htg.1.1 htg.2]

/-! ## The pointwise bound with damping -/

/-- The damped group factor: `2 n ρ^{n−1}` on a promotion of a particle with count `n`. -/
noncomputable def hf (m : P.Mem) (z' : ℤ × ℤ) (i : Fin P.K) (q : ℕ × Bool) : ℝ :=
  if q.2 then 2 * (P.memAt m (i, q.1, lineOf q.1 z') : ℝ) *
    memRho ^ (P.memAt m (i, q.1, lineOf q.1 z') - 1)
  else P.nu i q.1

lemma hf_nonneg (hEP : EP P) (m : P.Mem) (z' : ℤ × ℤ) (i : Fin P.K) (q : ℕ × Bool)
    (hq : q.1 ∈ P.grp i) : 0 ≤ hf P m z' i q := by
  unfold hf; split_ifs
  · have := memRho_nonneg; positivity
  · exact hEP.nu_nonneg i _ hq

/-- The target-side conditions of a nonzero raw coefficient from the source `(z, ℓ ∘ π, m)` with
omission tuple `o`. -/
def Cnd (ω : ℝ × ℝ × ℝ) (z : ℤ × ℤ) (ℓ : P.Lst) (m : P.Mem) (o : Fin P.K → Fin (P.J + 1))
    (tg : Fin P.K → ℕ × Bool) (z' : ℤ × ℤ) : Prop :=
  P.InBox ω z' ∧
    detZ z z' = (omitProd ℓ o : ℤ) * (((∏ i, ℓ i (o i) : ℕ) : ℤ) - ((∏ i, (tg i).1 : ℕ) : ℤ)) ∧
    (∀ i, (tg i).1 ∉ Set.range (ℓ i)) ∧
    (∀ i, (tg i).2 = true → 1 ≤ P.memAt m (i, (tg i).1, lineOf (tg i).1 z'))

lemma promCount_le_one (z' : ℤ × ℤ) (tg : Fin P.K → ℕ × Bool) (i : Fin P.K) (y : P.PT)
    (hy : y.1 = P.promPart z' tg i) : P.promCount z' tg y ≤ 1 := by
  classical
  unfold MemParams.promCount
  rw [card_le_one]
  intro a ha b hb
  simp only [mem_filter, mem_univ, true_and] at ha hb
  have h1 : a = i := by
    have := congrArg Prod.fst (ha.2.trans hy); simpa [MemParams.promPart] using this
  have h2 : b = i := by
    have := congrArg Prod.fst (hb.2.trans hy); simpa [MemParams.promPart] using this
  rw [h1, h2]

open Classical in
lemma hits_ge (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P) (hE : ECond P ω s c) :
    ∑ i ∈ promSet P c, (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) - 1) ≤
      P.hitCount c.2.1 (P.edgeOutMem s c) := by
  have hmem : ∀ i ∈ promSet P c, P.promPart c.2.1 c.2.2 i ∈ P.partSet := fun i hi =>
    hE.2.1 i (by simpa [promSet] using hi)
  set g : {i // i ∈ promSet P c} → P.PT := fun x => ⟨P.promPart c.2.1 c.2.2 x.1, hmem x.1 x.2⟩
  have hginj : Set.InjOn g ((promSet P c).attach : Set {i // i ∈ promSet P c}) := by
    intro a _ b _ h
    have := congrArg (fun y : P.PT => y.1.1) h
    exact Subtype.ext this
  calc ∑ i ∈ promSet P c, (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) - 1) =
      ∑ x ∈ (promSet P c).attach, (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 x.1) - 1) :=
        (sum_attach _ _).symm
    _ ≤ ∑ x ∈ (promSet P c).attach, P.edgeOutMem s c (g x) := by
        refine sum_le_sum fun x _ => ?_
        rw [memAt_of_mem P _ _ (hmem x.1 x.2)]
        change s.2.2 (g x) - 1 ≤ _
        have h1 := promCount_le_one P c.2.1 c.2.2 x.1 (g x) rfl
        unfold MemParams.edgeOutMem
        omega
    _ = ∑ y ∈ (promSet P c).attach.image g, P.edgeOutMem s c y := (sum_image hginj).symm
    _ = ∑ y ∈ (promSet P c).attach.image g,
          (if P.IsHit c.2.1 y then P.edgeOutMem s c y else 0) := by
        refine sum_congr rfl fun y hy => ?_
        obtain ⟨x, -, rfl⟩ := mem_image.1 hy
        rw [if_pos]
        rfl
    _ ≤ ∑ y : P.PT, (if P.IsHit c.2.1 y then P.edgeOutMem s c y else 0) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.zero_le _
    _ = P.hitCount c.2.1 (P.edgeOutMem s c) := by unfold MemParams.hitCount; rfl

lemma rfac_le_hf (hEP : EP P) (ω : ℝ × ℝ × ℝ) (s : P.MState) (c : EC P)
    (hc : c ∈ P.edgeChoices) (hE : ECond P ω s c) :
    rfac P s c ≤ ∏ i, hf P s.2.2 c.2.1 i (c.2.2 i) := by
  classical
  have hρ0 := memRho_nonneg
  have hρ1 : memRho ≤ 1 := by unfold memRho; norm_num
  have hg := (mem_choices P c hc).2
  set A : Fin P.K → ℝ := fun i => if (c.2.2 i).2 then
    (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1
  set B : Fin P.K → ℝ := fun i => if (c.2.2 i).2 then
    memRho ^ (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) - 1) else 1
  have hA : ∀ i, 0 ≤ A i := fun i => by
    simp only [A]; split_ifs
    · exact div_nonneg (Nat.cast_nonneg _) (hEP.Vpos i).le
    · exact hEP.nu_nonneg i _ (hg i)
  have hB : ∀ i, 0 ≤ B i := fun i => by simp only [B]; split_ifs <;> positivity
  have hdamp : memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c) ≤ ∏ i, B i := by
    have h1 : ∏ i, B i = memRho ^ (∑ i ∈ promSet P c,
        (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) - 1)) := by
      rw [← prod_pow_eq_pow_sum, promSet, prod_filter]
    rw [h1]
    exact pow_le_pow_of_le_one hρ0 hρ1 (hits_ge P ω s c hE)
  unfold rfac
  calc memRho ^ P.hitCount s.1 s.2.2 * (∏ i, A i) * memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c)
      ≤ 1 * (∏ i, A i) * ∏ i, B i := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (memRho_pow_le1 _)
          (prod_nonneg fun i _ => hA i)) hdamp (pow_nonneg hρ0 _)
          (mul_nonneg zero_le_one (prod_nonneg fun i _ => hA i))
    _ = ∏ i, (A i * B i) := by rw [one_mul, prod_mul_distrib]
    _ ≤ ∏ i, hf P s.2.2 c.2.1 i (c.2.2 i) := by
        refine prod_le_prod (fun i _ => mul_nonneg (hA i) (hB i)) fun i _ => ?_
        simp only [A, B, hf]
        split_ifs with h
        · have hV := hEP.hV1 i
          have hVp := hEP.Vpos i
          have h0 : (0 : ℝ) ≤ P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) := Nat.cast_nonneg _
          have hp0 : 0 ≤ memRho ^ (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) - 1) :=
            pow_nonneg hρ0 _
          unfold MemParams.promPart at h0 hp0 ⊢
          refine mul_le_mul_of_nonneg_right ?_ hp0
          rw [div_le_iff₀ hVp]
          nlinarith
        · rw [mul_one]

lemma range_permL (ℓ : P.Lst) (pr : SlotPerm P) (i : Fin P.K) :
    Set.range (permL P pr ℓ i) = Set.range (ℓ i) := by
  unfold permL
  exact (pr i).surjective.range_comp _

open Classical in
lemma coeff_D1_raw_le (hEP : EP P) (ω : ℝ × ℝ × ℝ) (s : P.MState) (hs : s ∈ P.stSet)
    (pr : SlotPerm P) (St : Finset (Fin P.K)) (z' : ℤ × ℤ) (hz' : z' ∈ P.zSet)
    (tg : Fin P.K → ℕ × Bool)
    (htg : tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool))) :
    ‖coeffP P (clsD1 P) (rawK P) ω (permS P pr s) (St, z', tg)‖ ≤
      if (flagSet P tg).Nonempty ∧ Cnd P ω s.1 s.2.1 s.2.2 (omitOf P pr) tg z' then
        ∏ i, hf P s.2.2 z' i (tg i) else 0 := by
  classical
  have hc := ecChoice_mem P St z' hz' tg htg
  have hg := (mem_choices P _ hc).2
  have hRHS : 0 ≤ if (flagSet P tg).Nonempty ∧ Cnd P ω s.1 s.2.1 s.2.2 (omitOf P pr) tg z' then
      ∏ i, hf P s.2.2 z' i (tg i) else 0 := by
    split_ifs
    · exact prod_nonneg fun i _ => hf_nonneg P hEP _ _ i _ (hg i)
    · exact le_refl 0
  have hs' : permS P pr s ∈ P.stSet := (mem_stSet_permS P pr s).2 hs
  unfold coeffP clsD1
  by_cases hI : (promSet P (St, z', tg)).Nonempty
  · rw [if_pos hI]
    unfold coeffK
    by_cases hE : ECond P ω (permS P pr s) (St, z', tg)
    · rw [if_pos hE, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (rfac_nonneg P (fun i p hp => hEP.nu_nonneg i p hp)
          (fun i => (hEP.Vpos i).le) _ _ hc)]
      have hD1 : 1 ≤ padProd (permS P pr s).2.1 := padProd_pos P _ hs'
      have hk := norm_rawK_le P (detZ (permS P pr s).1 (St, z', tg).2.1 /
        padProd (permS P pr s).2.1) (∏ i, ((St, z', tg).2.2 i).1) (lastProd (permS P pr s).2.1)
        (padProd (permS P pr s).2.1) hE.1.2.2.1 hD1
      have hr0 : 0 ≤ rfac P (permS P pr s) (St, z', tg) :=
        rfac_nonneg P (fun i p hp => hEP.nu_nonneg i p hp) (fun i => (hEP.Vpos i).le) _ _ hc
      split_ifs at hk with heq
      · have hcnd : Cnd P ω s.1 s.2.1 s.2.2 (omitOf P pr) tg z' := by
          refine ⟨hE.1.2.2.2.2.2.2.1, ?_, fun i => ?_, fun i hfl => ?_⟩
          · have hdvd := hE.1.2.2.2.2.1
            simp only [permS] at hdvd heq
            rw [padProd_permL] at hdvd heq
            rw [lastProd_permL] at heq
            have h2 : detZ s.1 z' / (omitProd s.2.1 (omitOf P pr) : ℤ) =
                ((∏ i, s.2.1 i (omitOf P pr i) : ℕ) : ℤ) - ((∏ i, (tg i).1 : ℕ) : ℤ) := by
              linarith
            rw [← h2, Int.mul_ediv_cancel' hdvd]
          · have h := hE.1.2.1 i
            simp only [permS] at h
            rwa [range_permL] at h
          · have hmem : P.promPart z' tg i ∈ P.partSet := hE.2.1 i hfl
            set y : P.PT := ⟨P.promPart z' tg i, hmem⟩
            have hle : P.promCount z' tg y ≤ s.2.2 y := hE.2.2.2 y
            have hpos : 1 ≤ P.promCount z' tg y := by
              unfold MemParams.promCount
              exact card_pos.2 ⟨i, mem_filter.2 ⟨mem_univ _, hfl, rfl⟩⟩
            have h3 : P.memAt s.2.2 (i, (tg i).1, lineOf (tg i).1 z') = s.2.2 y :=
              memAt_of_mem P s.2.2 _ hmem
            rw [h3]; exact le_trans hpos hle
        have hfl' : (flagSet P tg).Nonempty := hI
        rw [if_pos ⟨hfl', hcnd⟩]
        calc rfac P (permS P pr s) (St, z', tg) * ‖rawK P _ _ _ _‖ ≤
            rfac P (permS P pr s) (St, z', tg) * 1 := mul_le_mul_of_nonneg_left hk hr0
          _ ≤ _ := by
            rw [mul_one]
            exact rfac_le_hf P hEP ω (permS P pr s) _ hc hE
      · calc rfac P (permS P pr s) (St, z', tg) * ‖rawK P _ _ _ _‖ ≤
            rfac P (permS P pr s) (St, z', tg) * 0 := mul_le_mul_of_nonneg_left hk hr0
          _ ≤ _ := by rw [mul_zero]; exact hRHS
    · rw [if_neg hE, norm_zero]; exact hRHS
  · rw [if_neg hI, norm_zero]; exact hRHS

/-! ## Arithmetic helpers -/

lemma n_rho_le (n : ℕ) : (n : ℝ) * memRho ^ (n - 1) ≤ 4 := by
  have hρ0 := memRho_nonneg
  have hρ1 : memRho ≤ 1 := by unfold memRho; norm_num
  calc (n : ℝ) * memRho ^ (n - 1) = ∑ _k ∈ range n, memRho ^ (n - 1) := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ ∑ k ∈ range n, memRho ^ k := by
        refine sum_le_sum fun k hk => ?_
        exact pow_le_pow_of_le_one hρ0 hρ1 (by have := mem_range.1 hk; omega)
    _ = 4 * (1 - memRho ^ n) := by
        rw [geom_sum_eq (by unfold memRho; norm_num)]
        unfold memRho; field_simp; ring
    _ ≤ 4 := by have := pow_nonneg hρ0 n; linarith

lemma not_dvd_listProd (hEP : EP P) (ℓ : P.Lst) (hℓ : ℓ ∈ listCands P.x P.a P.J) (i : Fin P.K)
    (p : ℕ) (hp : p ∈ P.grp i) (hban : p ∉ Set.range (ℓ i)) : ¬ p ∣ listProd ℓ := by
  intro h'
  have hpp := grp_prime hp
  simp only [listCands, Fintype.mem_piFinset] at hℓ
  unfold listProd at h'
  obtain ⟨i', -, hi'⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 h'
  obtain ⟨k, -, hk⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).1 hi'
  have hq := grp_prime (hℓ i' k)
  have he : p = ℓ i' k := (Nat.prime_dvd_prime_iff_eq hpp hq).1 hk
  by_cases hii : i = i'
  · subst hii; exact hban ⟨_, he.symm⟩
  · exact absurd (hEP.hdisj i i' hii) (Finset.not_disjoint_iff.2 ⟨p, hp, he ▸ hℓ i' k⟩)

/-- The Plücker relation in the basis `(z, w)`. -/
lemma det_uj (z w a b : ℤ × ℤ) (hw : detZ z w = 1) :
    detZ a b = detZ a w * detZ z b - detZ z a * detZ b w := by
  unfold detZ at *
  linear_combination (-(a.1 * b.2 - a.2 * b.1)) * hw

lemma prod_ite_pull {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (X : ℝ) (Y : ι → ℝ) :
    ∏ i, (if i = i₀ then X else Y i) = X * ∏ i, (if i = i₀ then 1 else Y i) := by
  rw [← mul_prod_erase univ _ (mem_univ i₀), ← mul_prod_erase univ _ (mem_univ i₀)]
  rw [if_pos rfl, if_pos rfl, one_mul]
  congr 1
  refine prod_congr rfl fun i hi => ?_
  rw [if_neg (ne_of_mem_erase hi), if_neg (ne_of_mem_erase hi)]

/-- The promoted part `Z` of a promoted tuple (`1` at `i₀` and off `I`). -/
def Zof (I : Finset (Fin P.K)) (i₀ : Fin P.K) (Pp : Fin P.K → ℕ) : Fin P.K → ℕ :=
  fun i => if i ∈ I ∧ i ≠ i₀ then Pp i else 1

lemma prod_mkTg_fst (I : Finset (Fin P.K)) (i₀ : Fin P.K) (hi₀ : i₀ ∈ I) (Tf Pp : Fin P.K → ℕ)
    (hTf : Tf ∈ freshTuples P.x P.a I) (hPp : Pp ∈ promT P I) :
    ∏ i, (mkTg P I Tf Pp i).1 = Pp i₀ * (∏ i, Zof P I i₀ Pp i) * ∏ i, Tf i := by
  classical
  simp only [freshTuples, promT, Fintype.mem_piFinset] at hTf hPp
  have h : ∀ i, (mkTg P I Tf Pp i).1 =
      (if i = i₀ then Pp i₀ else 1) * Zof P I i₀ Pp i * Tf i := by
    intro i
    have h1 := hTf i; have h2 := hPp i
    unfold mkTg Zof
    by_cases hI : i ∈ I
    · rw [if_pos hI] at h1; rw [mem_singleton] at h1
      by_cases hii : i = i₀
      · subst hii; simp [hI, h1]
      · simp [hI, hii, h1]
    · rw [if_neg hI] at h2; rw [mem_singleton] at h2
      have hii : i ≠ i₀ := fun h => hI (h ▸ hi₀)
      simp [hI, hii]
  simp only [h, prod_mul_distrib, prod_ite_eq', mem_univ, if_true]

/-! ## Uniqueness of the omission and the promoted primes ([21] (4.35)–(4.36)) -/

/-- **The product `D Z` is unique** outside the exceptional fresh draws. -/
lemma uniq_num (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (z : ℤ × ℤ)
    (hz : P.InBox ω z) (hzp : Int.gcd z.1 z.2 = 1) (ℓ : P.Lst) (hℓ : ℓ ∈ listCands P.x P.a P.J)
    (m : P.Mem) (I : Finset (Fin P.K)) (i₀ : Fin P.K) (hi₀ : i₀ ∈ I) (Tf : Fin P.K → ℕ)
    (hTf : Tf ∈ freshTuples P.x P.a I) (p₀ : ℕ) (hp₀ : p₀ ∈ P.grp i₀)
    (o₁ o₂ : Fin P.K → Fin (P.J + 1)) (Pp₁ Pp₂ : Fin P.K → ℕ) (hPp₁ : Pp₁ ∈ promT P I)
    (hPp₂ : Pp₂ ∈ promT P I) (h₁ : Pp₁ i₀ = p₀) (h₂ : Pp₂ i₀ = p₀) (z'₁ z'₂ : ℤ × ℤ)
    (hz'₁ : z'₁ ∈ P.zSet) (hz'₂ : z'₂ ∈ P.zSet)
    (hC₁ : Cnd P ω z ℓ m o₁ (mkTg P I Tf Pp₁) z'₁) (hC₂ : Cnd P ω z ℓ m o₂ (mkTg P I Tf Pp₂) z'₂)
    (hline : lineOf p₀ z'₁ = lineOf p₀ z'₂)
    (hsep : ¬ SepFails P.x P.a ℓ I i₀ Tf (ratioAt ω z)) :
    omitProd ℓ o₁ * ∏ i, Zof P I i₀ Pp₁ i = omitProd ℓ o₂ * ∏ i, Zof P I i₀ Pp₂ i := by
  classical
  by_contra hne
  apply hsep
  have hpp := grp_prime hp₀
  set w := complVec z
  have hw : detZ z w = 1 := detZ_complVec z hzp
  set r := ratioAt ω z
  set n₁ := omitProd ℓ o₁ * ∏ i, Zof P I i₀ Pp₁ i
  set n₂ := omitProd ℓ o₂ * ∏ i, Zof P I i₀ Pp₂ i
  set T := ∏ i, Tf i
  -- the determinants
  have hj : ∀ (o : Fin P.K → Fin (P.J + 1)) (Pp : Fin P.K → ℕ) (z' : ℤ × ℤ),
      Pp ∈ promT P I → Pp i₀ = p₀ → Cnd P ω z ℓ m o (mkTg P I Tf Pp) z' →
      detZ z z' = (listProd ℓ : ℤ) - p₀ * ((omitProd ℓ o * ∏ i, Zof P I i₀ Pp i : ℕ) : ℤ) * T := by
    intro o Pp z' hPp hp hC
    rw [hC.2.1, prod_mkTg_fst P I i₀ hi₀ Tf Pp hTf hPp, hp, ← omit_mul_last P ℓ o]
    simp only [T]; push_cast; ring
  have hj₁ := hj o₁ Pp₁ z'₁ hPp₁ h₁ hC₁
  have hj₂ := hj o₂ Pp₂ z'₂ hPp₂ h₂ hC₂
  -- the line condition
  have hdvd : (p₀ : ℤ) ∣ detZ z'₁ z'₂ :=
    (lineOf_eq_iff p₀ hpp z'₁ z'₂ (zSet_prim P z'₁ hz'₁) (zSet_prim P z'₂ hz'₂)).1 hline
  rw [det_uj z w z'₁ z'₂ hw, hj₁, hj₂] at hdvd
  set u₁ := detZ z'₁ w
  set u₂ := detZ z'₂ w
  have hban : p₀ ∉ Set.range (ℓ i₀) := by
    have := hC₁.2.2.1 i₀
    simp only [mkTg, if_pos hi₀] at this
    rwa [h₁] at this
  have hPf : ¬ (p₀ : ℤ) ∣ listProd ℓ := by
    intro h
    exact not_dvd_listProd P hEP ℓ hℓ i₀ p₀ hp₀ hban (by exact_mod_cast h)
  have hdu : (p₀ : ℤ) ∣ u₁ - u₂ := by
    have h3 : (p₀ : ℤ) ∣ (listProd ℓ : ℤ) * (u₁ - u₂) := by
      have : (listProd ℓ : ℤ) * (u₁ - u₂) = u₁ * ((listProd ℓ : ℤ) - p₀ * (n₂ : ℤ) * T) -
          ((listProd ℓ : ℤ) - p₀ * (n₁ : ℤ) * T) * u₂ - p₀ * (T * ((n₁ : ℤ) * u₂ - (n₂ : ℤ) * u₁)) := by
        ring
      rw [this]
      exact dvd_sub hdvd (dvd_mul_right _ _)
    exact ((Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd h3).resolve_left hPf
  obtain ⟨κ, hκ⟩ := hdu
  -- the real window
  have hτ := (tau_pos P ω hω hU z hz).ne'
  have hr₁ : (1 / 16 : ℝ) ≤ (u₁ : ℝ) + (((listProd ℓ : ℤ) - p₀ * (n₁ : ℤ) * T : ℤ) : ℝ) * r ∧
      (u₁ : ℝ) + (((listProd ℓ : ℤ) - p₀ * (n₁ : ℤ) * T : ℤ) : ℝ) * r ≤ 16 := by
    have := tau_ratio_mem P ω hω hU z z'₁ hz hC₁.1
    rw [tauR_decomp' ω z z'₁ hzp hτ, hj₁] at this
    exact this
  have hr₂ : (1 / 16 : ℝ) ≤ (u₂ : ℝ) + (((listProd ℓ : ℤ) - p₀ * (n₂ : ℤ) * T : ℤ) : ℝ) * r ∧
      (u₂ : ℝ) + (((listProd ℓ : ℤ) - p₀ * (n₂ : ℤ) * T : ℤ) : ℝ) * r ≤ 16 := by
    have := tau_ratio_mem P ω hω hU z z'₂ hz hC₂.1
    rw [tauR_decomp' ω z z'₂ hzp hτ, hj₂] at this
    exact this
  have hp0 : (0 : ℝ) < p₀ := by exact_mod_cast hpp.pos
  have hu : (u₁ : ℝ) - u₂ = p₀ * κ := by exact_mod_cast hκ
  set X : ℤ := ((n₁ : ℤ) - (n₂ : ℤ)) * T
  have hwin : |(X : ℝ) * r - κ| < 16 / p₀ := by
    rw [lt_div_iff₀ hp0, ← abs_of_pos hp0, ← abs_mul]
    have : ((X : ℝ) * r - κ) * p₀ = -((u₁ - u₂ : ℝ) + ((listProd ℓ - p₀ * n₁ * T : ℤ) - (listProd ℓ - p₀ * n₂ * T : ℤ) : ℝ) * r) := by
      simp only [X]; push_cast; rw [hu]; ring
    rw [this, abs_neg, abs_lt]
    constructor <;> linarith [hr₁.1, hr₁.2, hr₂.1, hr₂.2]
  have hcirc : circNorm ((X : ℝ) * r) < 100 * exp (-(log P.x ^ P.a i₀)) := by
    have hpe : exp (log P.x ^ P.a i₀) ≤ p₀ := by
      simp only [MemParams.grp, primeGroup, mem_filter] at hp₀; exact hp₀.2.2
    calc circNorm ((X : ℝ) * r) ≤ |(X : ℝ) * r - κ| := round_le _ κ
      _ < 16 / p₀ := hwin
      _ ≤ 16 / exp (log P.x ^ P.a i₀) := div_le_div_of_nonneg_left (by norm_num) (exp_pos _) hpe
      _ = 16 * exp (-(log P.x ^ P.a i₀)) := by rw [exp_neg]; ring
      _ < 100 * exp (-(log P.x ^ P.a i₀)) := by
          have := exp_pos (-(log P.x ^ P.a i₀)); linarith
  have hZ : ∀ Pp ∈ promT P I, Zof P I i₀ Pp ∈ zTuples P.x P.a I i₀ := by
    intro Pp hPp
    simp only [promT, Fintype.mem_piFinset] at hPp
    simp only [zTuples, Fintype.mem_piFinset]
    intro i
    unfold Zof
    split_ifs with h
    · have := hPp i; rw [if_pos h.1] at this; exact this
    · exact mem_singleton_self _
  exact ⟨o₁, o₂, Zof P I i₀ Pp₁, Zof P I i₀ Pp₂, hZ Pp₁ hPp₁, hZ Pp₂ hPp₂, hne, hcirc⟩

/-- **`D Z` determines the omission and the promoted primes** (unique factorization, the ban
and disjoint groups). -/
lemma uniq_fac (hEP : EP P) (ℓ : P.Lst) (hℓ : ℓ ∈ listCands P.x P.a P.J)
    (hinj : ∀ i, Function.Injective (ℓ i)) (I : Finset (Fin P.K)) (i₀ : Fin P.K)
    (Pp₁ Pp₂ : Fin P.K → ℕ) (hPp₁ : Pp₁ ∈ promT P I) (hPp₂ : Pp₂ ∈ promT P I)
    (hban₁ : ∀ i ∈ I, Pp₁ i ∉ Set.range (ℓ i)) (hban₂ : ∀ i ∈ I, Pp₂ i ∉ Set.range (ℓ i))
    (o₁ o₂ : Fin P.K → Fin (P.J + 1))
    (h : omitProd ℓ o₁ * ∏ i, Zof P I i₀ Pp₁ i = omitProd ℓ o₂ * ∏ i, Zof P I i₀ Pp₂ i) :
    o₁ = o₂ ∧ ∀ i, i ∈ I → i ≠ i₀ → Pp₁ i = Pp₂ i := by
  classical
  simp only [listCands, Fintype.mem_piFinset] at hℓ
  simp only [promT, Fintype.mem_piFinset] at hPp₁ hPp₂
  have hZ : ∀ Pp : Fin P.K → ℕ, (∀ i, Pp i ∈ (if i ∈ I then P.grp i else {1})) →
      (∀ i ∈ I, Pp i ∉ Set.range (ℓ i)) → ∀ i k, ¬ ℓ i k ∣ ∏ j, Zof P I i₀ Pp j := by
    intro Pp hPp hban i k hdvd
    have hq := grp_prime (hℓ i k)
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 hdvd
    unfold Zof at hj
    split_ifs at hj with hjI
    · have hPj : Pp j ∈ P.grp j := by have := hPp j; rwa [if_pos hjI.1] at this
      have he : ℓ i k = Pp j := (Nat.prime_dvd_prime_iff_eq hq (grp_prime hPj)).1 hj
      by_cases hij : i = j
      · subst hij; exact hban i hjI.1 ⟨k, he⟩
      · exact absurd (hEP.hdisj i j hij) (Finset.not_disjoint_iff.2 ⟨_, hℓ i k, he ▸ hPj⟩)
    · exact hq.one_lt.ne' (Nat.dvd_one.1 hj)
  have hO : ∀ o : Fin P.K → Fin (P.J + 1), ∀ i, ¬ ℓ i (o i) ∣ omitProd ℓ o := by
    intro o i hdvd
    have hq := grp_prime (hℓ i (o i))
    unfold omitProd at hdvd
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 hdvd
    obtain ⟨k, hk, hk'⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 hj
    have he : ℓ i (o i) = ℓ j k := (Nat.prime_dvd_prime_iff_eq hq (grp_prime (hℓ j k))).1 hk'
    by_cases hij : i = j
    · subst hij
      exact (mem_erase.1 hk).1 (hinj i he).symm
    · exact absurd (hEP.hdisj i j hij) (Finset.not_disjoint_iff.2 ⟨_, hℓ i (o i), he ▸ hℓ j k⟩)
  have hoeq : o₁ = o₂ := by
    funext i
    by_contra hne
    have hq := grp_prime (hℓ i (o₁ i))
    have h1 : ℓ i (o₁ i) ∣ omitProd ℓ o₂ := by
      unfold omitProd
      exact (dvd_prod_of_mem (ℓ i) (mem_erase.2 ⟨hne, mem_univ _⟩)).trans
        (dvd_prod_of_mem (fun j => ∏ k ∈ univ.erase (o₂ j), ℓ j k) (mem_univ i))
    have h2 : ℓ i (o₁ i) ∣ omitProd ℓ o₁ * ∏ j, Zof P I i₀ Pp₁ j := h ▸ dvd_mul_of_dvd_left h1 _
    rcases (Nat.Prime.dvd_mul hq).1 h2 with h3 | h3
    · exact hO o₁ i h3
    · exact hZ Pp₁ hPp₁ hban₁ i (o₁ i) h3
  refine ⟨hoeq, fun i hiI hii => ?_⟩
  subst hoeq
  have hpos : 0 < omitProd ℓ o₁ := by
    unfold omitProd
    exact prod_pos fun j _ => prod_pos fun k _ => (grp_prime (hℓ j k)).pos
  have hZeq := Nat.eq_of_mul_eq_mul_left hpos h
  have hPi : Pp₁ i ∈ P.grp i := by have := hPp₁ i; rwa [if_pos hiI] at this
  have hq := grp_prime hPi
  have h1 : Pp₁ i ∣ ∏ j, Zof P I i₀ Pp₂ j := by
    rw [← hZeq]
    have : Zof P I i₀ Pp₁ i = Pp₁ i := by unfold Zof; rw [if_pos ⟨hiI, hii⟩]
    exact this ▸ dvd_prod_of_mem (Zof P I i₀ Pp₁) (mem_univ i)
  obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff hq.prime _).1 h1
  unfold Zof at hj
  split_ifs at hj with hjI
  · have hPj : Pp₂ j ∈ P.grp j := by have := hPp₂ j; rwa [if_pos hjI.1] at this
    have he : Pp₁ i = Pp₂ j := (Nat.prime_dvd_prime_iff_eq hq (grp_prime hPj)).1 hj
    by_cases hij : i = j
    · subst hij; exact he
    · exact absurd (hEP.hdisj i j hij) (Finset.not_disjoint_iff.2 ⟨_, hPi, he ▸ hPj⟩)
  · exact absurd (Nat.dvd_one.1 hj) hq.one_lt.ne'

lemma mkTg_eq_of (I : Finset (Fin P.K)) (i₀ : Fin P.K) (Tf Pp₁ Pp₂ : Fin P.K → ℕ)
    (hPp₁ : Pp₁ ∈ promT P I) (hPp₂ : Pp₂ ∈ promT P I) (h₀ : Pp₁ i₀ = Pp₂ i₀)
    (h : ∀ i, i ∈ I → i ≠ i₀ → Pp₁ i = Pp₂ i) : Pp₁ = Pp₂ := by
  simp only [promT, Fintype.mem_piFinset] at hPp₁ hPp₂
  funext i
  by_cases hiI : i ∈ I
  · by_cases hii : i = i₀
    · subst hii; exact h₀
    · exact h i hiI hii
  · have h1 := hPp₁ i; have h2 := hPp₂ i
    rw [if_neg hiI, mem_singleton] at h1 h2
    rw [h1, h2]

open Classical in
/-- **One fiber** (fixed promoted groups, fresh draws, promoted prime and anchor in group `i₀`):
at most 16 target positions and a single omission tuple and promoted tuple. -/
lemma fiber_bound (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (s : P.MState)
    (hs : s ∈ P.stSet) (hz : P.InBox ω s.1) (hinj : ∀ i, Function.Injective (s.2.1 i))
    (I : Finset (Fin P.K)) (i₀ : Fin P.K) (hi₀ : i₀ ∈ I) (Tf : Fin P.K → ℕ)
    (hTf : Tf ∈ freshTuples P.x P.a I) (hsep : ¬ SepFails P.x P.a s.2.1 I i₀ Tf (ratioAt ω s.1))
    (p₀ : ℕ) (hp₀ : p₀ ∈ P.grp i₀) (l₀ : ℕ) :
    ∑ Pp ∈ (promT P I).filter (fun Pp => Pp i₀ = p₀), ∑ o, ∑ z' ∈ P.zSet,
      (if Cnd P ω s.1 s.2.1 s.2.2 o (mkTg P I Tf Pp) z' ∧ lineOf p₀ z' = l₀ then
        ∏ i, hf P s.2.2 z' i (mkTg P I Tf Pp i) else 0) ≤
    16 * (2 * (P.memAt s.2.2 (i₀, p₀, l₀) : ℝ) *
      ∏ i, (if i = i₀ then 1 else if i ∈ I then 8 else P.nu i (Tf i))) := by
  obtain ⟨hzs, hℓ, hm⟩ := stSet_parts P s hs
  have hzp := zSet_prim P s.1 hzs
  have hTf' := hTf
  simp only [freshTuples, Fintype.mem_piFinset] at hTf'
  have hρ0 := memRho_nonneg
  have hρ1 : memRho ≤ 1 := by unfold memRho; norm_num
  set Fr := ∏ i, (if i = i₀ then (1 : ℝ) else if i ∈ I then 8 else P.nu i (Tf i))
  have hFr : 0 ≤ Fr := by
    refine prod_nonneg fun i _ => ?_
    split_ifs with h1 h2
    · norm_num
    · norm_num
    · have := hTf' i; rw [if_neg h2] at this; exact hEP.nu_nonneg i _ this
  set Bnd := 2 * (P.memAt s.2.2 (i₀, p₀, l₀) : ℝ) * Fr
  have hBnd : 0 ≤ Bnd := by positivity
  set S := (((promT P I).filter (fun Pp => Pp i₀ = p₀)) ×ˢ (univ ×ˢ P.zSet)).filter
    (fun q => Cnd P ω s.1 s.2.1 s.2.2 q.2.1 (mkTg P I Tf q.1) q.2.2 ∧ lineOf p₀ q.2.2 = l₀)
    with hS
  have hsum : ∑ Pp ∈ (promT P I).filter (fun Pp => Pp i₀ = p₀), ∑ o, ∑ z' ∈ P.zSet,
      (if Cnd P ω s.1 s.2.1 s.2.2 o (mkTg P I Tf Pp) z' ∧ lineOf p₀ z' = l₀ then
        ∏ i, hf P s.2.2 z' i (mkTg P I Tf Pp i) else 0) =
      ∑ q ∈ S, ∏ i, hf P s.2.2 q.2.2 i (mkTg P I Tf q.1 i) := by
    symm
    rw [hS, sum_filter, sum_product]
    refine sum_congr rfl fun Pp _ => ?_
    rw [sum_product]
  have hbound : ∀ q ∈ S, ∏ i, hf P s.2.2 q.2.2 i (mkTg P I Tf q.1 i) ≤ Bnd := by
    intro q hq
    rw [mem_filter, mem_product, mem_product, mem_filter] at hq
    obtain ⟨⟨⟨hPp, hPp0⟩, -, -⟩, -, hline⟩ := hq
    have hPp' := hPp
    simp only [promT, Fintype.mem_piFinset] at hPp'
    calc ∏ i, hf P s.2.2 q.2.2 i (mkTg P I Tf q.1 i) ≤
        ∏ i, (if i = i₀ then 2 * (P.memAt s.2.2 (i₀, p₀, l₀) : ℝ)
          else if i ∈ I then 8 else P.nu i (Tf i)) := by
          refine prod_le_prod (fun i _ => hf_nonneg P hEP _ _ i _ ?_) fun i _ => ?_
          · unfold mkTg; split_ifs with h
            · have := hPp' i; rwa [if_pos h] at this
            · have := hTf' i; rwa [if_neg h] at this
          · unfold hf mkTg
            by_cases hii : i = i₀
            · subst hii
              rw [if_pos hi₀, if_pos rfl]
              simp only [ite_true, hPp0, hline]
              have := pow_le_one₀ hρ0 hρ1 (n := P.memAt s.2.2 (i, p₀, l₀) - 1)
              have h0 : (0 : ℝ) ≤ P.memAt s.2.2 (i, p₀, l₀) := Nat.cast_nonneg _
              nlinarith
            · rw [if_neg hii]
              by_cases hiI : i ∈ I
              · rw [if_pos hiI, if_pos hiI]
                simp only [ite_true]
                have := n_rho_le (P.memAt s.2.2 (i, q.1 i, lineOf (q.1 i) q.2.2))
                linarith
              · rw [if_neg hiI, if_neg hiI]
                simp
      _ = Bnd := by rw [prod_ite_pull]
  have hcard : (S.card : ℝ) ≤ 16 := by
    rcases S.eq_empty_or_nonempty with hS | ⟨q₀, hq₀⟩
    · rw [hS, card_empty]; norm_num
    have hq₀' := hq₀
    rw [mem_filter, mem_product, mem_product, mem_filter] at hq₀'
    obtain ⟨⟨⟨hPp₀, hPp₀0⟩, -, hz₀⟩, hC₀, hline₀⟩ := hq₀'
    have hsub : S ⊆ ({q₀.1} : Finset (Fin P.K → ℕ)) ×ˢ (({q₀.2.1} : Finset _) ×ˢ
        P.zSet.filter fun z' => P.InBox ω z' ∧ detZ s.1 z' = detZ s.1 q₀.2.2) := by
      intro q hq
      have hq' := hq
      rw [mem_filter, mem_product, mem_product, mem_filter] at hq'
      obtain ⟨⟨⟨hPp, hPp0⟩, -, hz'⟩, hC, hline⟩ := hq'
      have hnum := uniq_num P hEP ω hω hU s.1 hz hzp s.2.1 hℓ s.2.2 I i₀ hi₀ Tf hTf p₀ hp₀
        q₀.2.1 q.2.1 q₀.1 q.1 hPp₀ hPp hPp₀0 hPp0 q₀.2.2 q.2.2 hz₀ hz' hC₀ hC
        (hline₀.trans hline.symm) hsep
      have hban : ∀ (Pp : Fin P.K → ℕ) (o : Fin P.K → Fin (P.J + 1)) (z' : ℤ × ℤ),
          Cnd P ω s.1 s.2.1 s.2.2 o (mkTg P I Tf Pp) z' → ∀ i ∈ I, Pp i ∉ Set.range (s.2.1 i) := by
        intro Pp o z' hC i hi
        have := hC.2.2.1 i
        simp only [mkTg, if_pos hi] at this
        exact this
      obtain ⟨ho, hPeq⟩ := uniq_fac P hEP s.2.1 hℓ hinj I i₀ q₀.1 q.1 hPp₀ hPp
        (hban _ _ _ hC₀) (hban _ _ _ hC) q₀.2.1 q.2.1 hnum
      have hPP := mkTg_eq_of P I i₀ Tf q₀.1 q.1 hPp₀ hPp (hPp₀0.trans hPp0.symm) hPeq
      rw [mem_product, mem_product, mem_singleton, mem_singleton, mem_filter]
      refine ⟨hPP.symm, ho.symm, hz', hC.1, ?_⟩
      rw [hC.2.1, hC₀.2.1, ho, hPP]
    calc (S.card : ℝ) ≤ ((({q₀.1} : Finset (Fin P.K → ℕ)) ×ˢ (({q₀.2.1} : Finset _) ×ˢ
        P.zSet.filter fun z' => P.InBox ω z' ∧ detZ s.1 z' = detZ s.1 q₀.2.2)).card : ℝ) := by
          exact_mod_cast card_le_card hsub
      _ ≤ 16 := by
          rw [card_product, card_product, card_singleton, card_singleton, one_mul, one_mul]
          exact card_fixed_det_le P ω hω hU s.1 hz hzp _
  rw [hsum]
  calc ∑ q ∈ S, ∏ i, hf P s.2.2 q.2.2 i (mkTg P I Tf q.1 i) ≤ ∑ _q ∈ S, Bnd := sum_le_sum hbound
    _ = S.card * Bnd := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 16 * Bnd := mul_le_mul_of_nonneg_right hcard hBnd

/-! ## The exceptional fresh draws: crude count -/

/-- The particles of group `i` with prime `p`, summed over anchors. -/
noncomputable def muL (m : P.Mem) (i : Fin P.K) (p : ℕ) : ℝ :=
  ∑ l ∈ range (p + 1), (P.memAt m (i, p, l) : ℝ)

lemma muL_nonneg (m : P.Mem) (i : Fin P.K) (p : ℕ) : 0 ≤ muL P m i p :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

open Classical in
lemma sum_z_crude (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (s : P.MState)
    (hs : s ∈ P.stSet) (hz : P.InBox ω s.1) (o : Fin P.K → Fin (P.J + 1))
    (tg : Fin P.K → ℕ × Bool) (htg : ∀ i, (tg i).1 ∈ P.grp i) :
    ∑ z' ∈ P.zSet, (if Cnd P ω s.1 s.2.1 s.2.2 o tg z' then ∏ i, hf P s.2.2 z' i (tg i) else 0) ≤
      16 * ∏ i, (if (tg i).2 then 2 * muL P s.2.2 i (tg i).1 else P.nu i (tg i).1) := by
  obtain ⟨hzs, -, -⟩ := stSet_parts P s hs
  have hρ0 := memRho_nonneg
  have hρ1 : memRho ≤ 1 := by unfold memRho; norm_num
  set Q := ∏ i, (if (tg i).2 then 2 * muL P s.2.2 i (tg i).1 else P.nu i (tg i).1)
  have hQ : 0 ≤ Q := prod_nonneg fun i _ => by
    split_ifs
    · have := muL_nonneg P s.2.2 i (tg i).1; positivity
    · exact hEP.nu_nonneg i _ (htg i)
  set J0 : ℤ := (omitProd s.2.1 o : ℤ) *
    (((∏ i, s.2.1 i (o i) : ℕ) : ℤ) - ((∏ i, (tg i).1 : ℕ) : ℤ))
  calc ∑ z' ∈ P.zSet, (if Cnd P ω s.1 s.2.1 s.2.2 o tg z' then ∏ i, hf P s.2.2 z' i (tg i) else 0)
      ≤ ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ detZ s.1 z' = J0 then Q else 0) := by
        refine sum_le_sum fun z' _ => ?_
        by_cases hC : Cnd P ω s.1 s.2.1 s.2.2 o tg z'
        · rw [if_pos hC, if_pos ⟨hC.1, hC.2.1⟩]
          refine prod_le_prod (fun i _ => hf_nonneg P hEP _ _ i _ (htg i)) fun i _ => ?_
          unfold hf
          split_ifs
          · have hp := (grp_prime (htg i)).pos
            have h1 : (P.memAt s.2.2 (i, (tg i).1, lineOf (tg i).1 z') : ℝ) ≤
                muL P s.2.2 i (tg i).1 :=
              single_le_sum (f := fun l => (P.memAt s.2.2 (i, (tg i).1, l) : ℝ))
                (fun _ _ => Nat.cast_nonneg _)
                (mem_range.2 (Nat.lt_succ_of_le (lineOf_le _ hp z')))
            have h2 := pow_le_one₀ hρ0 hρ1
              (n := P.memAt s.2.2 (i, (tg i).1, lineOf (tg i).1 z') - 1)
            have h3 := pow_nonneg hρ0 (P.memAt s.2.2 (i, (tg i).1, lineOf (tg i).1 z') - 1)
            have h0 : (0 : ℝ) ≤ P.memAt s.2.2 (i, (tg i).1, lineOf (tg i).1 z') :=
              Nat.cast_nonneg _
            nlinarith
          · exact le_refl _
        · rw [if_neg hC]; split_ifs <;> linarith
    _ = ((P.zSet.filter fun z' => P.InBox ω z' ∧ detZ s.1 z' = J0).card : ℝ) * Q := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ 16 * Q := mul_le_mul_of_nonneg_right
        (card_fixed_det_le P ω hω hU s.1 hz (zSet_prim P s.1 hzs) J0) hQ

open Classical in
/-- The exceptional fresh draws of one promoted set: the crude `B^K` count. -/
lemma exc_IT (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (s : P.MState)
    (hs : s ∈ P.stSet) (hz : P.InBox ω s.1) (I : Finset (Fin P.K)) (Tf : Fin P.K → ℕ)
    (hTf : Tf ∈ freshTuples P.x P.a I) :
    ∑ Pp ∈ promT P I, ∑ o, ∑ z' ∈ P.zSet,
      (if Cnd P ω s.1 s.2.1 s.2.2 o (mkTg P I Tf Pp) z' then
        ∏ i, hf P s.2.2 z' i (mkTg P I Tf Pp i) else 0) ≤
    (((P.J + 1 : ℕ) : ℝ) ^ P.K * 16) * ∏ i, (if i ∈ I then 2 * (P.B : ℝ) else P.nu i (Tf i)) := by
  obtain ⟨-, -, hm⟩ := stSet_parts P s hs
  have hTf' := hTf
  simp only [freshTuples, Fintype.mem_piFinset] at hTf'
  have hmk : ∀ Pp ∈ promT P I, ∀ i, (mkTg P I Tf Pp i).1 ∈ P.grp i := by
    intro Pp hPp i
    simp only [promT, Fintype.mem_piFinset] at hPp
    unfold mkTg; split_ifs with h
    · have := hPp i; rwa [if_pos h] at this
    · have := hTf' i; rwa [if_neg h] at this
  set h : Fin P.K → ℕ → ℝ := fun i q => if i ∈ I then 2 * muL P s.2.2 i q else P.nu i (Tf i)
  have hprod : ∀ Pp, ∏ i, (if (mkTg P I Tf Pp i).2 then 2 * muL P s.2.2 i (mkTg P I Tf Pp i).1
      else P.nu i (mkTg P I Tf Pp i).1) = ∏ i, h i (Pp i) := by
    intro Pp
    refine prod_congr rfl fun i _ => ?_
    simp only [mkTg, h]
    split_ifs <;> simp_all
  calc ∑ Pp ∈ promT P I, ∑ o, ∑ z' ∈ P.zSet,
        (if Cnd P ω s.1 s.2.1 s.2.2 o (mkTg P I Tf Pp) z' then
          ∏ i, hf P s.2.2 z' i (mkTg P I Tf Pp i) else 0) ≤
      ∑ Pp ∈ promT P I, ∑ _o : Fin P.K → Fin (P.J + 1), 16 * ∏ i, h i (Pp i) := by
        refine sum_le_sum fun Pp hPp => sum_le_sum fun o _ => ?_
        rw [← hprod]
        exact sum_z_crude P hEP ω hω hU s hs hz o _ (hmk Pp hPp)
    _ = (((P.J + 1 : ℕ) : ℝ) ^ P.K * 16) * ∏ i, ∑ q ∈ (if i ∈ I then P.grp i else {1}), h i q := by
        rw [prod_univ_sum, mul_sum]
        refine sum_congr rfl fun Pp _ => ?_
        rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast; ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (prod_le_prod (fun i _ => ?_) fun i _ => ?_)
          (by positivity)
        · refine sum_nonneg fun q hq => ?_
          simp only [h]; split_ifs with hi
          · have := muL_nonneg P s.2.2 i q; positivity
          · have := hTf' i; rw [if_neg hi] at this; exact hEP.nu_nonneg i _ this
        · by_cases hi : i ∈ I
          · simp only [h, if_pos hi]
            rw [← mul_sum]
            have := (sum_memAt_lines_le P s.2.2 i).trans (memSize_le P s.2.2 hm)
            simp only [muL]
            linarith
          · simp only [h, if_neg hi, sum_singleton]
            exact le_refl _

open Classical in
/-- The non-exceptional fresh draws of one promoted set. -/
lemma main_IT (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (s : P.MState)
    (hs : s ∈ P.stSet) (hz : P.InBox ω s.1) (hinj : ∀ i, Function.Injective (s.2.1 i))
    (I : Finset (Fin P.K)) (i₀ : Fin P.K) (hi₀ : i₀ ∈ I) (Tf : Fin P.K → ℕ)
    (hTf : Tf ∈ freshTuples P.x P.a I) (hsep : ¬ SepFails P.x P.a s.2.1 I i₀ Tf (ratioAt ω s.1)) :
    ∑ Pp ∈ promT P I, ∑ o, ∑ z' ∈ P.zSet,
      (if Cnd P ω s.1 s.2.1 s.2.2 o (mkTg P I Tf Pp) z' then
        ∏ i, hf P s.2.2 z' i (mkTg P I Tf Pp i) else 0) ≤
    16 * (2 * (P.B : ℝ)) * ∏ i, (if i = i₀ then 1 else if i ∈ I then 8 else P.nu i (Tf i)) := by
  obtain ⟨-, -, hm⟩ := stSet_parts P s hs
  set Fr := ∏ i, (if i = i₀ then (1 : ℝ) else if i ∈ I then 8 else P.nu i (Tf i))
  have hTf' := hTf
  simp only [freshTuples, Fintype.mem_piFinset] at hTf'
  have hFr : 0 ≤ Fr := by
    refine prod_nonneg fun i _ => ?_
    split_ifs with h1 h2
    · norm_num
    · norm_num
    · have := hTf' i; rw [if_neg h2] at this; exact hEP.nu_nonneg i _ this
  set F : (Fin P.K → ℕ) → (Fin P.K → Fin (P.J + 1)) → ℤ × ℤ → ℝ := fun Pp o z' =>
    if Cnd P ω s.1 s.2.1 s.2.2 o (mkTg P I Tf Pp) z' then
      ∏ i, hf P s.2.2 z' i (mkTg P I Tf Pp i) else 0
  rw [← sum_fiberwise_of_maps_to (g := fun Pp => Pp i₀) (t := P.grp i₀) (fun Pp hPp => by
    simp only [promT, Fintype.mem_piFinset] at hPp
    have := hPp i₀; rwa [if_pos hi₀] at this)]
  calc ∑ p₀ ∈ P.grp i₀, ∑ Pp ∈ (promT P I).filter (fun Pp => Pp i₀ = p₀), ∑ o, ∑ z' ∈ P.zSet,
        F Pp o z' ≤
      ∑ p₀ ∈ P.grp i₀, ∑ l₀ ∈ range (p₀ + 1),
        16 * (2 * (P.memAt s.2.2 (i₀, p₀, l₀) : ℝ) * Fr) := by
        refine sum_le_sum fun p₀ hp₀ => ?_
        have hp := (grp_prime hp₀).pos
        set G : ℕ → (Fin P.K → ℕ) → (Fin P.K → Fin (P.J + 1)) → ℤ × ℤ → ℝ := fun l₀ Pp o z' =>
          if Cnd P ω s.1 s.2.1 s.2.2 o (mkTg P I Tf Pp) z' ∧ lineOf p₀ z' = l₀ then
            ∏ i, hf P s.2.2 z' i (mkTg P I Tf Pp i) else 0
        have hFG : ∀ Pp o z', F Pp o z' = ∑ l₀ ∈ range (p₀ + 1), G l₀ Pp o z' := by
          intro Pp o z'
          simp only [F, G]
          by_cases hC : Cnd P ω s.1 s.2.1 s.2.2 o (mkTg P I Tf Pp) z'
          · simp only [hC, true_and, if_true]
            rw [sum_ite_eq, if_pos (mem_range.2 (Nat.lt_succ_of_le (lineOf_le _ hp z')))]
          · simp [hC]
        calc ∑ Pp ∈ (promT P I).filter (fun Pp => Pp i₀ = p₀), ∑ o, ∑ z' ∈ P.zSet, F Pp o z' =
            ∑ Pp ∈ (promT P I).filter (fun Pp => Pp i₀ = p₀), ∑ o, ∑ l₀ ∈ range (p₀ + 1),
              ∑ z' ∈ P.zSet, G l₀ Pp o z' := by
              refine sum_congr rfl fun Pp _ => sum_congr rfl fun o _ => ?_
              rw [sum_comm]
              exact sum_congr rfl fun z' _ => hFG Pp o z'
          _ = ∑ Pp ∈ (promT P I).filter (fun Pp => Pp i₀ = p₀), ∑ l₀ ∈ range (p₀ + 1), ∑ o,
              ∑ z' ∈ P.zSet, G l₀ Pp o z' :=
              sum_congr rfl fun Pp _ => sum_comm
          _ = ∑ l₀ ∈ range (p₀ + 1), ∑ Pp ∈ (promT P I).filter (fun Pp => Pp i₀ = p₀), ∑ o,
              ∑ z' ∈ P.zSet, G l₀ Pp o z' := sum_comm
          _ ≤ _ := sum_le_sum fun l₀ _ =>
              fiber_bound P hEP ω hω hU s hs hz hinj I i₀ hi₀ Tf hTf hsep p₀ hp₀ l₀
    _ = 16 * 2 * Fr * ∑ p₀ ∈ P.grp i₀, ∑ l₀ ∈ range (p₀ + 1), (P.memAt s.2.2 (i₀, p₀, l₀) : ℝ) := by
        rw [mul_sum]
        refine sum_congr rfl fun p₀ _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun l₀ _ => by ring
    _ ≤ 16 * 2 * Fr * P.B := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (sum_memAt_lines_le P s.2.2 i₀).trans (memSize_le P s.2.2 hm)
    _ = _ := by ring

/-! ## The exceptional mass (test (ii)) and the row bound -/

lemma nu_le_fresh (hEP : EP P) (i : Fin P.K) (p : ℕ) (hp : p ∈ P.grp i) :
    P.nu i p ≤ 2 * (1 / ((p : ℝ) * P.Vg i)) := by
  have hb := hEP.hb p (grp_gPrimes hp)
  have hV := hEP.Vpos i
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (grp_prime hp).pos
  unfold MemParams.nu
  rw [show 2 * (1 / ((p : ℝ) * P.Vg i)) = 1 / ((p : ℝ) * P.Vg i / 2) by field_simp]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have : P.Vg i * ((p : ℝ) + 1) * P.bprime p - (p : ℝ) * P.Vg i / 2 =
      P.Vg i * (((p : ℝ) + 1) * (P.bprime p - 1 / 2) + 1 / 2) := by ring
  have h2 : 0 ≤ P.Vg i * (((p : ℝ) + 1) * (P.bprime p - 1 / 2) + 1 / 2) := by
    have : 0 ≤ ((p : ℝ) + 1) * (P.bprime p - 1 / 2) := mul_nonneg (by positivity) (by linarith)
    positivity
  linarith

open Classical in
lemma exc_mass (hEP : EP P) (ℓ : P.Lst) (r : ℝ) (hgood : GoodTestTwo P.x P.a ℓ r)
    (I : Finset (Fin P.K)) (hI : I.Nonempty) (C : ℝ) (hC : 2 ≤ C) (hBC : 2 * (P.B : ℝ) ≤ C) :
    ∑ Tf ∈ freshTuples P.x P.a I, (if SepFails P.x P.a ℓ I (I.max' hI) Tf r then
      ∏ i, (if i ∈ I then 2 * (P.B : ℝ) else P.nu i (Tf i)) else 0) ≤
    C ^ P.K * exp (-(log P.x ^ P.a (I.max' hI)) / 4) := by
  have hC0 : 0 ≤ C := by linarith
  have hB0 : (0 : ℝ) ≤ P.B := Nat.cast_nonneg _
  have hterm : ∀ Tf ∈ freshTuples P.x P.a I,
      (if SepFails P.x P.a ℓ I (I.max' hI) Tf r then
        ∏ i, (if i ∈ I then 2 * (P.B : ℝ) else P.nu i (Tf i)) else 0) ≤
      C ^ P.K * (freshWeight P.x P.a I Tf *
        (if SepFails P.x P.a ℓ I (I.max' hI) Tf r then 1 else 0)) := by
    intro Tf hTf
    simp only [freshTuples, Fintype.mem_piFinset] at hTf
    split_ifs
    · rw [mul_one, freshWeight, show C ^ P.K = ∏ _i : Fin P.K, C by simp, ← prod_mul_distrib]
      refine prod_le_prod (fun i _ => ?_) fun i _ => ?_
      · split_ifs with hi
        · positivity
        · have := hTf i; rw [if_neg hi] at this; exact hEP.nu_nonneg i _ this
      · by_cases hi : i ∈ I
        · rw [if_pos hi, if_pos hi, mul_one]; exact hBC
        · rw [if_neg hi, if_neg hi]
          have hTi := hTf i; rw [if_neg hi] at hTi
          have h1 := nu_le_fresh P hEP i (Tf i) hTi
          have hp0 : (0 : ℝ) < Tf i := by exact_mod_cast (grp_prime hTi).pos
          have h2 : (0 : ℝ) ≤ 1 / ((Tf i : ℝ) * P.Vg i) := by
            have := hEP.Vpos i; positivity
          have h3 : 2 * (1 / ((Tf i : ℝ) * P.Vg i)) ≤ C * (1 / ((Tf i : ℝ) * P.Vg i)) :=
            mul_le_mul_of_nonneg_right hC h2
          exact h1.trans h3
    · rw [mul_zero, mul_zero]
  calc ∑ Tf ∈ freshTuples P.x P.a I, (if SepFails P.x P.a ℓ I (I.max' hI) Tf r then
        ∏ i, (if i ∈ I then 2 * (P.B : ℝ) else P.nu i (Tf i)) else 0) ≤
      ∑ Tf ∈ freshTuples P.x P.a I, C ^ P.K * (freshWeight P.x P.a I Tf *
        (if SepFails P.x P.a ℓ I (I.max' hI) Tf r then 1 else 0)) := sum_le_sum hterm
    _ = C ^ P.K * ∑ Tf ∈ freshTuples P.x P.a I, freshWeight P.x P.a I Tf *
        (if SepFails P.x P.a ℓ I (I.max' hI) Tf r then 1 else 0) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hgood I hI) (by positivity)

lemma sum_Fr_le (hEP : EP P) (I : Finset (Fin P.K)) (i₀ : Fin P.K) (hi₀ : i₀ ∈ I) :
    ∑ Tf ∈ freshTuples P.x P.a I,
      ∏ i, (if i = i₀ then (1 : ℝ) else if i ∈ I then 8 else P.nu i (Tf i)) ≤ 8 ^ P.K := by
  unfold freshTuples
  rw [← prod_univ_sum (t := fun i => if i ∈ I then {1} else primeGroup P.x (P.a i))
    (f := fun i q => if i = i₀ then (1 : ℝ) else if i ∈ I then 8 else P.nu i q)]
  calc ∏ i, ∑ q ∈ (if i ∈ I then {1} else primeGroup P.x (P.a i)),
        (if i = i₀ then (1 : ℝ) else if i ∈ I then 8 else P.nu i q) ≤ ∏ _i : Fin P.K, (8 : ℝ) := by
        refine prod_le_prod (fun i _ => sum_nonneg fun q hq => ?_) fun i _ => ?_
        · split_ifs with h1 h2
          · norm_num
          · norm_num
          · rw [if_neg h2] at hq; exact hEP.nu_nonneg i q hq
        · by_cases hi : i ∈ I
          · rw [if_pos hi, sum_singleton]
            split_ifs <;> norm_num
          · have hii : i ≠ i₀ := fun h => hi (h ▸ hi₀)
            rw [if_neg hi]
            simp only [if_neg hii, if_neg hi]
            have := hEP.sum_nu_le i
            exact this.trans (by norm_num)
    _ = 8 ^ P.K := by simp

open Classical in
/-- **R1**: averaged raw rows with a promotion ([21] (4.38)). -/
theorem avgRow_D1_raw_le (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    (s : P.MState) (hs : s ∈ P.stSet) (E : ℝ) (hE0 : 0 ≤ E)
    (hE : ∀ i, exp (-(log P.x ^ P.a i) / 4) ≤ E) :
    avgRow P (clsD1 P) (rawK P) ω s ≤
      4 ^ P.K * (32 * P.B * 8 ^ P.K / ((P.J + 1 : ℕ) : ℝ) ^ P.K +
        16 * (2 + 4 * (P.B : ℝ)) ^ P.K * E) := by
  obtain ⟨hzs, hℓ, hm⟩ := stSet_parts P s hs
  set M := ((P.J + 1 : ℕ) : ℝ)
  have hM : 0 < M := by positivity
  have hB0 : (0 : ℝ) ≤ P.B := Nat.cast_nonneg _
  have hRHS : 0 ≤ 4 ^ P.K * (32 * P.B * 8 ^ P.K / M ^ P.K + 16 * (2 + 4 * (P.B : ℝ)) ^ P.K * E) := by
    positivity
  set Tg := Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool))
  by_cases hsrc : P.InBox ω s.1 ∧ GoodTestTwo P.x P.a s.2.1 (ratioAt ω s.1) ∧
    ∀ i, Function.Injective (s.2.1 i)
  swap
  · have h0 : ∀ pr, rowSum P (clsD1 P) (rawK P) ω (permS P pr s) = 0 := by
      intro pr
      unfold rowSum
      refine sum_eq_zero fun c _ => ?_
      unfold coeffP coeffK
      split_ifs with h1 h2
      · exfalso; apply hsrc
        refine ⟨h2.1.2.2.2.2.2.1, ?_, fun i => ?_⟩
        · have hg : IsGoodRatio P.x P.Y P.a (permL P pr s.2.1) (ratioAt ω s.1) :=
            h2.1.2.2.2.2.2.2.2.1
          exact (goodTestTwo_permL P s.2.1 pr _).1 hg.2
        · have h3 : Function.Injective (permL P pr s.2.1 i) := h2.1.1 i
          have h4 : Function.Injective (permL P pr s.2.1 i ∘ (pr i).symm) :=
            h3.comp (pr i).symm.injective
          have h5 : permL P pr s.2.1 i ∘ (pr i).symm = s.2.1 i := by
            funext k; simp [permL]
          rwa [h5] at h4
      · simp
      · simp
    unfold avgRow
    simp only [h0, sum_const_zero, mul_zero]
    exact hRHS
  obtain ⟨hz, hgood, hinj⟩ := hsrc
  -- the row at a permuted source
  set Sg : (Fin P.K → Fin (P.J + 1)) → ℝ := fun o => ∑ tg ∈ Tg,
    (if (flagSet P tg).Nonempty then ∑ z' ∈ P.zSet,
      (if Cnd P ω s.1 s.2.1 s.2.2 o tg z' then ∏ i, hf P s.2.2 z' i (tg i) else 0) else 0)
  have hpt : ∀ pr, rowSum P (clsD1 P) (rawK P) ω (permS P pr s) ≤ 2 ^ P.K * Sg (omitOf P pr) := by
    intro pr
    rw [rowSum_eq]
    calc ∑ St : Finset (Fin P.K), ∑ z' ∈ P.zSet, ∑ tg ∈ Tg,
          ‖coeffP P (clsD1 P) (rawK P) ω (permS P pr s) (St, z', tg)‖ ≤
        ∑ _St : Finset (Fin P.K), ∑ z' ∈ P.zSet, ∑ tg ∈ Tg,
          (if (flagSet P tg).Nonempty ∧ Cnd P ω s.1 s.2.1 s.2.2 (omitOf P pr) tg z' then
            ∏ i, hf P s.2.2 z' i (tg i) else 0) :=
          sum_le_sum fun St _ => sum_le_sum fun z' hz' => sum_le_sum fun tg htg =>
            coeff_D1_raw_le P hEP ω s hs pr St z' hz' tg htg
      _ = ∑ _St : Finset (Fin P.K), Sg (omitOf P pr) := by
          refine sum_congr rfl fun St _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun tg _ => ?_
          by_cases hA : (flagSet P tg).Nonempty
          · simp only [hA, true_and, if_true]
          · simp only [hA, false_and, if_false, sum_const_zero]
      _ = 2 ^ P.K * Sg (omitOf P pr) := by
          rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- the sum over omission tuples
  have hSg : ∑ o, Sg o ≤ 2 ^ P.K * (M ^ P.K * (16 * (2 + 4 * (P.B : ℝ)) ^ P.K * E) +
      16 * (2 * (P.B : ℝ)) * 8 ^ P.K) := by
    set H : (Fin P.K → ℕ × Bool) → ℝ := fun tg => ∑ o : Fin P.K → Fin (P.J + 1), ∑ z' ∈ P.zSet,
      (if Cnd P ω s.1 s.2.1 s.2.2 o tg z' then ∏ i, hf P s.2.2 z' i (tg i) else 0)
    have h1 : ∑ o, Sg o = ∑ tg ∈ Tg, (if (flagSet P tg).Nonempty then H tg else 0) := by
      simp only [Sg, H]
      rw [sum_comm]
      refine sum_congr rfl fun tg _ => ?_
      by_cases hA : (flagSet P tg).Nonempty
      · simp only [hA, if_true]
      · simp only [hA, if_false, sum_const_zero]
    rw [h1, sum_tg_split]
    calc ∑ I ∈ univ.filter (fun I : Finset (Fin P.K) => I.Nonempty),
          ∑ Tf ∈ freshTuples P.x P.a I, ∑ Pp ∈ promT P I, H (mkTg P I Tf Pp) ≤
        ∑ _I ∈ univ.filter (fun I : Finset (Fin P.K) => I.Nonempty),
          (M ^ P.K * (16 * (2 + 4 * (P.B : ℝ)) ^ P.K * E) + 16 * (2 * (P.B : ℝ)) * 8 ^ P.K) := by
          refine sum_le_sum fun I hI => ?_
          have hIne : I.Nonempty := (mem_filter.1 hI).2
          set i₀ := I.max' hIne
          have hi₀ : i₀ ∈ I := I.max'_mem hIne
          set Fr : (Fin P.K → ℕ) → ℝ := fun Tf =>
            ∏ i, (if i = i₀ then (1 : ℝ) else if i ∈ I then 8 else P.nu i (Tf i))
          have hFr : ∀ Tf ∈ freshTuples P.x P.a I, 0 ≤ Fr Tf := by
            intro Tf hTf
            simp only [freshTuples, Fintype.mem_piFinset] at hTf
            refine prod_nonneg fun i _ => ?_
            split_ifs with h1 h2
            · norm_num
            · norm_num
            · have := hTf i; rw [if_neg h2] at this; exact hEP.nu_nonneg i _ this
          set X : (Fin P.K → ℕ) → ℝ := fun Tf => if SepFails P.x P.a s.2.1 I i₀ Tf (ratioAt ω s.1)
            then ∏ i, (if i ∈ I then 2 * (P.B : ℝ) else P.nu i (Tf i)) else 0
          calc ∑ Tf ∈ freshTuples P.x P.a I, ∑ Pp ∈ promT P I, H (mkTg P I Tf Pp) ≤
              ∑ Tf ∈ freshTuples P.x P.a I,
                ((M ^ P.K * 16) * X Tf + 16 * (2 * (P.B : ℝ)) * Fr Tf) := by
                refine sum_le_sum fun Tf hTf => ?_
                have hFr0 := hFr Tf hTf
                simp only [H, X]
                by_cases hsep : SepFails P.x P.a s.2.1 I i₀ Tf (ratioAt ω s.1)
                · rw [if_pos hsep]
                  have := exc_IT P hEP ω hω hU s hs hz I Tf hTf
                  have h2 : 0 ≤ 16 * (2 * (P.B : ℝ)) * Fr Tf := by positivity
                  linarith
                · rw [if_neg hsep, mul_zero, zero_add]
                  exact main_IT P hEP ω hω hU s hs hz hinj I i₀ hi₀ Tf hTf hsep
            _ = (M ^ P.K * 16) * ∑ Tf ∈ freshTuples P.x P.a I, X Tf +
                16 * (2 * (P.B : ℝ)) * ∑ Tf ∈ freshTuples P.x P.a I, Fr Tf := by
                rw [sum_add_distrib, mul_sum, mul_sum]
            _ ≤ (M ^ P.K * 16) * ((2 + 4 * (P.B : ℝ)) ^ P.K * E) +
                16 * (2 * (P.B : ℝ)) * 8 ^ P.K := by
                refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity))
                  (mul_le_mul_of_nonneg_left (sum_Fr_le P hEP I i₀ hi₀) (by positivity))
                refine (exc_mass P hEP s.2.1 (ratioAt ω s.1) hgood I hIne (2 + 4 * (P.B : ℝ))
                  (by linarith) (by linarith)).trans ?_
                exact mul_le_mul_of_nonneg_left (hE _) (by positivity)
            _ = _ := by ring
      _ ≤ ∑ _I : Finset (Fin P.K),
          (M ^ P.K * (16 * (2 + 4 * (P.B : ℝ)) ^ P.K * E) + 16 * (2 * (P.B : ℝ)) * 8 ^ P.K) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      _ = _ := by
          rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  -- assemble
  unfold avgRow
  calc ((Fintype.card (SlotPerm P) : ℕ) : ℝ)⁻¹ *
        ∑ pr : SlotPerm P, rowSum P (clsD1 P) (rawK P) ω (permS P pr s) ≤
      ((Fintype.card (SlotPerm P) : ℕ) : ℝ)⁻¹ * ∑ pr : SlotPerm P, 2 ^ P.K * Sg (omitOf P pr) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun pr _ => hpt pr) (by positivity)
    _ = (M ^ P.K)⁻¹ * ∑ o, 2 ^ P.K * Sg o := avg_omit P (fun o => 2 ^ P.K * Sg o)
    _ = (M ^ P.K)⁻¹ * 2 ^ P.K * ∑ o, Sg o := by rw [← mul_sum]; ring
    _ ≤ (M ^ P.K)⁻¹ * 2 ^ P.K * (2 ^ P.K * (M ^ P.K * (16 * (2 + 4 * (P.B : ℝ)) ^ P.K * E) +
        16 * (2 * (P.B : ℝ)) * 8 ^ P.K)) := mul_le_mul_of_nonneg_left hSg (by positivity)
    _ = _ := by
        have hMK : M ^ P.K ≠ 0 := by positivity
        rw [show (4 : ℝ) ^ P.K = 2 ^ P.K * 2 ^ P.K by rw [← mul_pow]; norm_num]
        field_simp
        ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: the edge bound at fixed parameters ([21] (4.34), (4.39), (4.41))

`edge_opBound`: under the parameter facts `EP`, `‖E_j‖ ≤ Ctot`, the sum of the clean bound
(`clean_reduce ∘ kblock_bilBound ∘ kappaC_bilBound`), the two dirty raw pieces
(`piece_sym_bound` with rows R1/R2) and the two dirty comparison pieces (rows R3/R4). -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

lemma avgRow_mono (Qc₁ Qc₂ : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (h : ∀ St I, Qc₁ St I → Qc₂ St I) (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ) (s : P.MState) :
    avgRow P Qc₁ κ ω s ≤ avgRow P Qc₂ κ ω s := by
  unfold avgRow rowSum
  exact mul_le_mul_of_nonneg_left (sum_le_sum fun pr _ => sum_le_sum fun c _ =>
    norm_coeffP_mono P Qc₁ Qc₂ h κ ω _ c) (by positivity)

lemma avgRow_or (Qc₁ Qc₂ Qc : Finset (Fin P.K) → Finset (Fin P.K) → Prop)
    (h : ∀ St I, Qc St I → Qc₁ St I ∨ Qc₂ St I) (κ : ℤ → ℕ → ℕ → ℕ → ℂ) (ω : ℝ × ℝ × ℝ)
    (s : P.MState) : avgRow P Qc κ ω s ≤ avgRow P Qc₁ κ ω s + avgRow P Qc₂ κ ω s := by
  unfold avgRow rowSum
  rw [← mul_add, ← sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun pr _ => ?_) (by positivity)
  rw [← sum_add_distrib]
  exact sum_le_sum fun c _ => norm_coeffP_or P Qc₁ Qc₂ Qc h κ ω _ c

/-- R1: raw rows with a promotion. -/
noncomputable def R1c (E : ℝ) : ℝ :=
  4 ^ P.K * (32 * P.B * 8 ^ P.K / ((P.J + 1 : ℕ) : ℝ) ^ P.K + 16 * (2 + 4 * (P.B : ℝ)) ^ P.K * E)

/-- R2: raw rows without promotions. -/
noncomputable def R2c : ℝ := 2 ^ P.K * 16 * 2 ^ P.K

/-- R3: comparison rows with a promotion. -/
noncomputable def R3c (pmin : ℝ) : ℝ :=
  2 ^ P.K * P.K * (2 * (4 * log P.x ^ (3 * P.A₀) / P.Y) * (2 + 2 * P.B) ^ P.K *
    ((9 * C1 * P.Y / pmin + 4 * P.Y ^ (0.9 : ℝ) + 2) * P.B))

/-- R4: crude comparison rows. -/
noncomputable def R4c : ℝ :=
  2 ^ P.K * (16 * (10 * P.Y + 1) * (4 * log P.x ^ (3 * P.A₀) / P.Y)) * (2 + 2 * P.B) ^ P.K

/-- The clean bound. -/
noncomputable def Ecl (pmin : ℝ) : ℝ :=
  4 ^ P.K / P.Y * (5121 * Mbox' P) + P.K * (4 / pmin * 2 ^ P.K) * Ccr P

/-- The total edge bound. -/
noncomputable def Ctot (pmin E : ℝ) : ℝ :=
  Ecl P pmin + (√(R1c P E) * √(3 ^ P.K * (R2c P + R1c P E)) + √(R2c P) * √(3 ^ P.K * R1c P E)) +
    (√(R3c P pmin) * √(3 ^ P.K * R4c P) + √(R4c P) * √(3 ^ P.K * R3c P pmin))

/-- **The edge bound at fixed parameters.** -/
theorem edge_opBound (hEP : EP P) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (j : ℕ)
    (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀) (hP : 1 ≤ log P.x ^ P.A₀) (hY1 : 1 ≤ P.Y)
    (hYbig : (2 * cLat + 2) ^ 10 ≤ P.Y) (hd : 0 < (P.d₀ : ℝ)) (pmin : ℝ) (hpmin1 : 1 ≤ pmin)
    (hpmin : ∀ i, ∀ p ∈ P.grp i, pmin ≤ p) (E : ℝ) (hE0 : 0 ≤ E)
    (hE : ∀ i, exp (-(log P.x ^ P.a i) / 4) ≤ E) :
    P.OpBound (P.edgeOp ω j) (Ctot P pmin E) := by
  have hY0 : 0 < P.Y := by linarith
  have hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p := fun i p hp => hEP.nu_nonneg i p hp
  have hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s := fun s hs => stWeight_nonneg P hnu s hs
  have hB0 : (0 : ℝ) ≤ P.B := Nat.cast_nonneg _
  have hR1 : 0 ≤ R1c P E := by unfold R1c; positivity
  have hR2 : 0 ≤ R2c P := by unfold R2c; positivity
  have hR3 : 0 ≤ R3c P pmin := by
    unfold R3c
    have := C1_nonneg; have := Real.rpow_nonneg hY0.le (0.9 : ℝ)
    have : 0 < pmin := by linarith
    positivity
  have hR4 : 0 ≤ R4c P := by unfold R4c; positivity
  have hCcr : 0 ≤ Ccr P := by unfold Ccr; positivity
  have hEcl : 0 ≤ Ecl P pmin := by
    unfold Ecl; have := Mbox'_nonneg P hY1 hP
    have : 0 < pmin := by linarith
    positivity
  have hC : 0 ≤ Ctot P pmin E := by unfold Ctot; positivity
  -- the rows
  have rowR1 : ∀ s ∈ P.stSet, avgRow P (clsD1 P) (rawK P) ω s ≤ R1c P E := fun s hs =>
    avgRow_D1_raw_le P hEP ω hω hU s hs E hE0 hE
  have rowR2 : ∀ s ∈ P.stSet, avgRow P (clsNoProm P) (rawK P) ω s ≤ R2c P := fun s hs =>
    avgRow_le_of_rowSum P _ _ ω _ (fun s hs => rowSum_noProm_raw_le P hEP ω hω hU s hs) s hs
  have rowR3 : ∀ s ∈ P.stSet, avgRow P (clsD1 P) (majK P j) ω s ≤ R3c P pmin := fun s hs =>
    avgRow_le_of_rowSum P _ _ ω _ (fun s hs => rowSum_D1_maj_le P hEP ω hω hU j s hs hL hA₀ hY1
      hYbig pmin hpmin1 hpmin) s hs
  have rowR4 : ∀ s ∈ P.stSet, avgRow P (clsAll P) (majK P j) ω s ≤ R4c P := fun s hs =>
    avgRow_le_of_rowSum P _ _ ω _ (fun s hs => rowSum_all_maj_le P hEP ω hω hU j s hs hL hA₀ hY0)
      s hs
  refine opBound_of_bilin P _ _ hC hμ fun g f => ?_
  rw [ipμ_edgeOp_split]
  -- the clean piece
  have hcl := clean_reduce P ω j (Ecl P pmin) hEcl hnu (fun pd hpd m _ =>
    kblock_bilBound P hEP ω hω hU j pd hpd m pmin (by linarith) hpmin hL hA₀ hY0 _
      (by have := Mbox'_nonneg P hY1 hP; positivity)
      (kappaC_bilBound P hEP ω hω hU pd hpd hd hY1 hYbig hP)) (P.symM g) (P.symM f)
  have hwg := wNorm_symM_le P hμ g
  have hwf := wNorm_symM_le P hμ f
  have hwg0 : 0 ≤ P.wNorm (P.symM g) := Real.sqrt_nonneg _
  have hwf0 : 0 ≤ P.wNorm (P.symM f) := Real.sqrt_nonneg _
  have hg0 : 0 ≤ P.wNorm g := Real.sqrt_nonneg _
  have hcl' : ‖pieceB P (clsClean P) (P.edgeMult j) ω (P.symM g) (P.symM f)‖ ≤
      Ecl P pmin * P.wNorm g * P.wNorm f := by
    refine hcl.trans ?_
    calc Ecl P pmin * P.wNorm (P.symM g) * P.wNorm (P.symM f) ≤
        Ecl P pmin * P.wNorm g * P.wNorm (P.symM f) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwg hEcl) hwf0
      _ ≤ _ := mul_le_mul_of_nonneg_left hwf (mul_nonneg hEcl hg0)
  -- the dirty pieces
  have h1 := piece_sym_bound P (clsD1 P) (clsS P) (fun _ _ h => h) (rawK P)
    (fun t a b D => (norm_rawK_swap P t a b D).symm.le) ω hnu hEP.hV1 hEP.hV2 (R1c P E)
    (R2c P + R1c P E) hR1 (by positivity) rowR1
    (fun s hs => (avgRow_or P (clsNoProm P) (clsD1 P) (clsS P)
      (fun St I _ => by
        rcases I.eq_empty_or_nonempty with h | h
        · exact Or.inl h
        · exact Or.inr h) (rawK P) ω s).trans (add_le_add (rowR2 s hs) (rowR1 s hs))) g f
  have h2 := piece_sym_bound P (clsD2 P) (clsD1 P) (fun _ _ h => h.2) (rawK P)
    (fun t a b D => (norm_rawK_swap P t a b D).symm.le) ω hnu hEP.hV1 hEP.hV2 (R2c P)
    (R1c P E) hR2 hR1
    (fun s hs => (avgRow_mono P (clsD2 P) (clsNoProm P) (fun _ _ h => h.1) (rawK P) ω s).trans
      (rowR2 s hs)) rowR1 g f
  have h3 := piece_sym_bound P (clsD1 P) (clsS P) (fun _ _ h => h) (majK P j)
    (fun t a b D => (norm_majK_swap P j t a b D).symm.le) ω hnu hEP.hV1 hEP.hV2 (R3c P pmin)
    (R4c P) hR3 hR4 rowR3
    (fun s hs => (avgRow_mono P (clsS P) (clsAll P) (fun _ _ _ => trivial) (majK P j) ω s).trans
      (rowR4 s hs)) g f
  have h4 := piece_sym_bound P (clsD2 P) (clsD1 P) (fun _ _ h => h.2) (majK P j)
    (fun t a b D => (norm_majK_swap P j t a b D).symm.le) ω hnu hEP.hV1 hEP.hV2 (R4c P)
    (R3c P pmin) hR4 hR3
    (fun s hs => (avgRow_mono P (clsD2 P) (clsAll P) (fun _ _ _ => trivial) (majK P j) ω s).trans
      (rowR4 s hs)) rowR3 g f
  set A := pieceB P (clsClean P) (P.edgeMult j) ω (P.symM g) (P.symM f)
  set B1 := pieceB P (clsD1 P) (rawK P) ω (P.symM g) (P.symM f)
  set C1' := pieceB P (clsD1 P) (majK P j) ω (P.symM g) (P.symM f)
  set B2 := pieceB P (clsD2 P) (rawK P) ω (P.symM g) (P.symM f)
  set C2 := pieceB P (clsD2 P) (majK P j) ω (P.symM g) (P.symM f)
  calc ‖A + (B1 - C1') + (B2 - C2)‖ ≤ ‖A‖ + (‖B1‖ + ‖C1'‖) + (‖B2‖ + ‖C2‖) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add le_rfl (norm_sub_le _ _))) (norm_sub_le _ _))
    _ ≤ Ecl P pmin * P.wNorm g * P.wNorm f +
        (√(R1c P E) * √(3 ^ P.K * (R2c P + R1c P E)) * P.wNorm g * P.wNorm f +
          √(R3c P pmin) * √(3 ^ P.K * R4c P) * P.wNorm g * P.wNorm f) +
        (√(R2c P) * √(3 ^ P.K * R1c P E) * P.wNorm g * P.wNorm f +
          √(R4c P) * √(3 ^ P.K * R3c P pmin) * P.wNorm g * P.wNorm f) := by
        gcongr
    _ = Ctot P pmin E * P.wNorm g * P.wNorm f := by unfold Ctot; ring

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: D7d, the edge bound `‖E_j‖ ≤ L^{-G}` ([21] (4.42))

* `edgeOp_eq_zero`: if no label product lies in `(Y, 4Y)` the edge vanishes;
* `Y_bounds`: otherwise `e^{K L^{0.1}}/4 < Y < e^{2K L^{0.2}}`;
* `ev_EP`: for large `x` the parameter facts `EP` hold (Mertens for `Vᵢ`, `b'_p ≥ 1/2`, disjoint
  groups);
* `Ctot_le`: with `A₀ = G + 2` and `0.01K ≥ 2G + 4`, `Ctot ≤ L^{-G}` for large `L`;
* **`chk_edge_bound`**: `EdgeBoundStmt` verbatim. -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset Filter

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-! ## Vanishing edges -/

lemma edgeOp_eq_zero (ω : ℝ × ℝ × ℝ) (j : ℕ)
    (h : ∀ lab ∈ labCands P, dyadicBump (((∏ i, lab i : ℕ) : ℝ) / P.Y) = 0)
    (f : P.MState → ℂ) : P.edgeOp ω j f = fun _ => 0 := by
  have hE : ∀ F, P.edgeOrd ω j F = fun _ => 0 := by
    intro F; funext s
    unfold MemParams.edgeOrd
    refine sum_eq_zero fun c hc => ?_
    have hz : P.edgeCoeff ω j s c = 0 := by
      rw [edgeCoeff_eq]
      unfold coeffK
      by_cases hEc : ECond P ω s c
      · rw [if_pos hEc]
        have hl : (fun i => (c.2.2 i).1) ∈ labCands P := by
          simp only [labCands, Fintype.mem_piFinset]; exact (mem_choices P c hc).2
        have h0 := h _ hl
        beta_reduce at h0
        unfold MemParams.edgeMult
        rw [h0]
        simp
      · rw [if_neg hEc]
    rw [hz, zero_mul]
  funext s
  unfold MemParams.edgeOp
  rw [hE]
  unfold MemParams.symM MemParams.listSym
  simp

lemma opBound_of_vanish (ω : ℝ × ℝ × ℝ) (j : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ lab ∈ labCands P, dyadicBump (((∏ i, lab i : ℕ) : ℝ) / P.Y) = 0) :
    P.OpBound (P.edgeOp ω j) C := by
  intro f
  rw [edgeOp_eq_zero P ω j h f]
  unfold MemParams.wNorm
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    sum_const_zero, Real.sqrt_zero]
  exact mul_nonneg hC (Real.sqrt_nonneg _)

/-- A nonvanishing edge forces `e^{K L^{0.1}}/4 < Y < e^{2K L^{0.2}}`. -/
lemma Y_bounds (hL : 1 ≤ log P.x) (ha : ∀ i, (0.1 : ℝ) < P.a i ∧ P.a i < 0.2) (hY : 0 < P.Y)
    (lab : Fin P.K → ℕ) (hlab : lab ∈ labCands P)
    (hη : dyadicBump (((∏ i, lab i : ℕ) : ℝ) / P.Y) ≠ 0) :
    exp (P.K * log P.x ^ (0.1 : ℝ)) / 4 < P.Y ∧ P.Y < exp (2 * P.K * log P.x ^ (0.2 : ℝ)) := by
  have h14 := L102D.dyadicBump_ne_zero hη
  simp only [labCands, Fintype.mem_piFinset] at hlab
  have hb : ∀ i, exp (log P.x ^ (0.1 : ℝ)) ≤ (lab i : ℝ) ∧
      (lab i : ℝ) ≤ exp (2 * log P.x ^ (0.2 : ℝ)) := by
    intro i
    have h := le_of_mem_primeGroup' (hlab i)
    have e1 : log P.x ^ (0.1 : ℝ) ≤ log P.x ^ P.a i :=
      Real.rpow_le_rpow_of_exponent_le hL (ha i).1.le
    have e2 : log P.x ^ P.a i ≤ log P.x ^ (0.2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL (ha i).2.le
    exact ⟨(exp_le_exp.2 e1).trans h.1, h.2.trans (exp_le_exp.2 (by linarith))⟩
  have hlo : exp (P.K * log P.x ^ (0.1 : ℝ)) ≤ ((∏ i, lab i : ℕ) : ℝ) := by
    push_cast
    calc exp (P.K * log P.x ^ (0.1 : ℝ)) = ∏ _i : Fin P.K, exp (log P.x ^ (0.1 : ℝ)) := by
          rw [prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
      _ ≤ ∏ i, (lab i : ℝ) := prod_le_prod (fun i _ => (exp_pos _).le) fun i _ => (hb i).1
  have hhi : ((∏ i, lab i : ℕ) : ℝ) ≤ exp (2 * P.K * log P.x ^ (0.2 : ℝ)) := by
    push_cast
    calc ∏ i, (lab i : ℝ) ≤ ∏ _i : Fin P.K, exp (2 * log P.x ^ (0.2 : ℝ)) :=
          prod_le_prod (fun i _ => Nat.cast_nonneg _) fun i _ => (hb i).2
      _ = exp (2 * P.K * log P.x ^ (0.2 : ℝ)) := by
          rw [prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; ring_nf
  obtain ⟨h1, h4⟩ := h14
  rw [lt_div_iff₀ hY] at h1
  rw [div_lt_iff₀ hY] at h4
  constructor <;> linarith

/-! ## Real asymptotics -/

lemma ev_poly_exp (c d ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, c * L ^ d * exp (-(ε * L ^ (0.1 : ℝ))) ≤ 1 := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * d) ε hε
  have h2 : Tendsto (fun L : ℝ => L ^ (0.1 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  have h3 := (h1.comp h2).const_mul c
  rw [mul_zero] at h3
  filter_upwards [h3.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop 0] with L hL hL0
  simp only [Function.comp_apply] at hL
  have e : (L ^ (0.1 : ℝ)) ^ (10 * d) = L ^ d := by
    rw [← Real.rpow_mul hL0.le, show (0.1 : ℝ) * (10 * d) = d by ring]
  rw [e, neg_mul] at hL
  linarith [show c * L ^ d * exp (-(ε * L ^ (0.1 : ℝ))) =
    c * (L ^ d * exp (-(ε * L ^ (0.1 : ℝ)))) by ring]

lemma ev_rpow_small (c e : ℝ) (he : 0 < e) : ∀ᶠ L : ℝ in atTop, c * L ^ (-e) ≤ 1 := by
  have h := (tendsto_rpow_neg_atTop he).const_mul c
  rw [mul_zero] at h
  exact (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun L hL => hL.le

/-! ## The parameter facts for large `x` -/

lemma eventually_Vg_ge_half' {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j) := by
  refine Filter.eventually_all.2 fun j => ?_
  have hm := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  have hlog : (1 : ℝ) / 2 < log (2 / 1) := by
    rw [div_one]; have := Real.log_two_gt_d9; linarith
  have hev := hm.eventually (lt_mem_nhds hlog)
  have hy : Filter.Tendsto (fun x : ℝ => exp (log x ^ a j)) Filter.atTop Filter.atTop :=
    tendsto_exp_atTop.comp ((tendsto_rpow_atTop (ha j)).comp tendsto_log_atTop)
  filter_upwards [hy.eventually hev] with x hx
  refine hx.le.trans ?_
  unfold groupReciprocalSum primeGroup
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
  simp only [mem_filter, mem_range] at hp ⊢
  have e2 : exp (log x ^ a j) ^ (2 : ℝ) = exp (2 * log x ^ a j) := by
    rw [← Real.exp_mul]; ring_nf
  rw [e2, Real.rpow_one] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2.le⟩

lemma eventually_Vg_le' {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ j, groupReciprocalSum x (a j) ≤ 3 / 2 := by
  refine Filter.eventually_all.2 fun j => ?_
  have hm := mertens_prime_reciprocals (1 / 2) 2 (by norm_num) (by norm_num)
  have hlog : log (2 / (1 / 2)) < 3 / 2 := by
    have e : (2 : ℝ) / (1 / 2) = 2 * 2 := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_two_lt_d9; linarith
  have hev := hm.eventually (gt_mem_nhds hlog)
  have hy : Filter.Tendsto (fun x : ℝ => exp (log x ^ a j)) Filter.atTop Filter.atTop :=
    tendsto_exp_atTop.comp ((tendsto_rpow_atTop (ha j)).comp tendsto_log_atTop)
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < log x ^ a j :=
    ((tendsto_rpow_atTop (ha j)).comp tendsto_log_atTop).eventually_gt_atTop 0
  filter_upwards [hy.eventually hev, hpos] with x hx hx0
  refine le_trans ?_ hx.le
  unfold groupReciprocalSum primeGroup
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
  simp only [mem_filter, mem_range] at hp ⊢
  have e2 : exp (log x ^ a j) ^ (2 : ℝ) = exp (2 * log x ^ a j) := by
    rw [← Real.exp_mul]; ring_nf
  have e3 : exp (log x ^ a j) ^ ((1 : ℝ) / 2) = exp (log x ^ a j / 2) := by
    rw [← Real.exp_mul]; ring_nf
  rw [e2, e3]
  refine ⟨hp.1, hp.2.1, lt_of_lt_of_le ?_ hp.2.2⟩
  exact exp_lt_exp.2 (by linarith)

lemma eventually_disjoint_groups' {K : ℕ} (a : Fin K → ℝ) (ha : StrictMono a) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i j, i ≠ j →
      Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
  have hL : ∀ᶠ L : ℝ in Filter.atTop, ∀ i j : Fin K, a i < a j → 2 * L ^ a i < L ^ a j := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : a i < a j
    · filter_upwards [eventually_rpow_le_rpow' hij (ε := 1 / 3) (by norm_num),
        Filter.eventually_gt_atTop 0] with L h1 h2 _
      have : 0 < L ^ a j := by positivity
      linarith
    · exact Filter.Eventually.of_forall fun L h => absurd h hij
  filter_upwards [Real.tendsto_log_atTop.eventually hL] with x hx
  intro i j hij
  have key : ∀ i j : Fin K, a i < a j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
    intro i j h
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    have h1 := (le_of_mem_primeGroup' hp).2
    have h2 := (le_of_mem_primeGroup' hp').1
    have := exp_lt_exp.2 (hx i j h)
    linarith
  rcases lt_or_gt_of_ne (ha.injective.ne hij) with h | h
  · exact key i j h
  · exact (key j i h).symm

/-! ## The total bound is `≤ L^{-G}` -/

lemma sqrt_le_of_sq (X g : ℝ) (hg : 0 ≤ g) (h : X ≤ g ^ 2) : √X ≤ g := by
  rw [show g = √(g ^ 2) by rw [Real.sqrt_sq hg]]
  exact Real.sqrt_le_sqrt h

/-- Facts about `Y` in the nonvanishing range. -/
lemma Y_facts (hK1 : 1 ≤ P.K) (hL : 1 ≤ log P.x) (hY1 : 1 ≤ P.Y)
    (hYlo : exp (P.K * log P.x ^ (0.1 : ℝ)) / 4 < P.Y)
    (hYhi : P.Y < exp (2 * P.K * log P.x ^ (0.2 : ℝ))) :
    P.Y ^ (-(0.1 : ℝ)) ≤ 4 * exp (-(0.1 * log P.x ^ (0.1 : ℝ))) ∧
      1 / P.Y ≤ 4 * exp (-(log P.x ^ (0.1 : ℝ))) ∧
      1 + log (2 * P.Y) ≤ 4 * P.K * log P.x ^ (0.2 : ℝ) := by
  set L := log P.x
  set ℓ := L ^ (0.1 : ℝ)
  have hℓ1 : 1 ≤ ℓ := Real.one_le_rpow hL (by norm_num)
  have hK : (1 : ℝ) ≤ P.K := by exact_mod_cast hK1
  have hY0 : 0 < P.Y := by linarith
  have hL2 : 1 ≤ L ^ (0.2 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hlogY : P.K * ℓ - log 4 < log P.Y := by
    have := Real.log_lt_log (by positivity) hYlo
    rwa [Real.log_div (exp_pos _).ne' (by norm_num), Real.log_exp] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hY0]
    have h4 : 0 ≤ log 4 := Real.log_nonneg (by norm_num)
    calc exp (log P.Y * -(0.1 : ℝ)) ≤ exp (-(0.1 * ℓ) + log 4) := by
          apply exp_le_exp.2
          have : ℓ ≤ P.K * ℓ := le_mul_of_one_le_left (by linarith) hK
          linarith
      _ = 4 * exp (-(0.1 * ℓ)) := by rw [exp_add, exp_log (by norm_num)]; ring
  · have h1 : exp ℓ / 4 ≤ P.Y := by
      refine le_trans ?_ hYlo.le
      gcongr
      exact le_mul_of_one_le_left (by linarith) hK
    calc 1 / P.Y ≤ 1 / (exp ℓ / 4) := one_div_le_one_div_of_le (by positivity) h1
      _ = 4 * exp (-ℓ) := by rw [exp_neg]; field_simp
  · rw [Real.log_mul (by norm_num) hY0.ne']
    have h1 : log P.Y < 2 * P.K * L ^ (0.2 : ℝ) := by
      have := Real.log_lt_log hY0 hYhi
      rwa [Real.log_exp] at this
    have h2 : log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have h3 : 1 ≤ (P.K : ℝ) * L ^ (0.2 : ℝ) := one_le_mul_of_one_le_of_one_le hK hL2
    linarith

/-- The clean part is `≤ L^{-G}/4`. -/
lemma Ecl_le (G : ℝ) (hG : 0 < G) (hA : P.A₀ = G + 2) (hK1 : 1 ≤ P.K) (hL : 1 ≤ log P.x) (hY1 : 1 ≤ P.Y)
    (hYm : P.Y ^ (-(0.1 : ℝ)) ≤ 4 * exp (-(0.1 * log P.x ^ (0.1 : ℝ))))
    (hl2Y : 1 + log (2 * P.Y) ≤ 4 * P.K * log P.x ^ (0.2 : ℝ))
    (F2 : 4 * exp (-(0.1 * log P.x ^ (0.1 : ℝ))) ≤ log P.x ^ (-(G + 2)))
    (F3 : 4 ^ P.K * 5121 * (8 * P.K * (32 * C1 + 40) * Ipsi + 18 * C1 * Jpsi) *
      (log P.x ^ (0.2 : ℝ) * log P.x ^ (-(G + 2))) ≤ log P.x ^ (-G) / 8)
    (F4 : P.K * 4 * 2 ^ P.K * 720 * log P.x ^ (3 * (G + 2)) * exp (-(log P.x ^ (0.1 : ℝ))) ≤
      log P.x ^ (-G) / 8) :
    Ecl P (exp (log P.x ^ (0.1 : ℝ))) ≤ log P.x ^ (-G) / 4 := by
  set L := log P.x
  set ℓ := L ^ (0.1 : ℝ)
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < P.Y := by linarith
  have hL2 : 1 ≤ L ^ (0.2 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hLA' : L ^ (-(G + 2)) = 1 / L ^ (G + 2) := by rw [Real.rpow_neg hL0.le, one_div]
  have hC1 := C1_nonneg
  have hI := Ipsi_nonneg
  have hJ := Jpsi_nonneg
  have hK : (1 : ℝ) ≤ P.K := by exact_mod_cast hK1
  unfold Ecl Mbox' Ccr
  rw [hA]
  have e1 : 4 ^ P.K / P.Y * (5121 * (P.Y * ((32 * C1 + 40) * (1 / L ^ (G + 2) +
      P.Y ^ (-0.1 : ℝ)) * (1 + Real.log (2 * P.Y))) * Ipsi +
      9 * C1 * P.Y * Jpsi / (L ^ (G + 2) / 2))) =
      4 ^ P.K * 5121 * ((32 * C1 + 40) * (1 / L ^ (G + 2) + P.Y ^ (-0.1 : ℝ)) *
        (1 + Real.log (2 * P.Y)) * Ipsi + 18 * C1 * Jpsi * (1 / L ^ (G + 2))) := by
    have : 0 < L ^ (G + 2) := Real.rpow_pos_of_pos hL0 _
    field_simp; ring
  rw [e1]
  have hpos : 0 ≤ L ^ (-(G + 2)) := by positivity
  have hsum : 1 / L ^ (G + 2) + P.Y ^ (-0.1 : ℝ) ≤ 2 * L ^ (-(G + 2)) := by
    rw [hLA'] at F2 ⊢
    have : P.Y ^ (-0.1 : ℝ) = P.Y ^ (-(0.1 : ℝ)) := by norm_num
    rw [this]; linarith only [hYm, F2]
  have hpart1 : 4 ^ P.K * 5121 * ((32 * C1 + 40) * (1 / L ^ (G + 2) + P.Y ^ (-0.1 : ℝ)) *
      (1 + Real.log (2 * P.Y)) * Ipsi + 18 * C1 * Jpsi * (1 / L ^ (G + 2))) ≤
      4 ^ P.K * 5121 * (8 * P.K * (32 * C1 + 40) * Ipsi + 18 * C1 * Jpsi) *
        (L ^ (0.2 : ℝ) * L ^ (-(G + 2))) := by
    have hs0 : 0 ≤ 1 / L ^ (G + 2) + P.Y ^ (-0.1 : ℝ) := by
      have h1 := Real.rpow_nonneg hY0.le (-0.1 : ℝ)
      have h2 : 0 ≤ 1 / L ^ (G + 2) := by positivity
      exact add_nonneg h2 h1
    have hl0 : 0 ≤ 1 + Real.log (2 * P.Y) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * P.Y by linarith only [hY1])
      linarith only [this]
    have hX : (1 / L ^ (G + 2) + P.Y ^ (-0.1 : ℝ)) * (1 + Real.log (2 * P.Y)) ≤
        (2 * L ^ (-(G + 2))) * (4 * P.K * L ^ (0.2 : ℝ)) :=
      mul_le_mul hsum hl2Y hl0 (by positivity)
    have hX2 : 1 / L ^ (G + 2) ≤ L ^ (0.2 : ℝ) * L ^ (-(G + 2)) := by
      rw [← hLA']; exact le_mul_of_one_le_left hpos hL2
    calc 4 ^ P.K * 5121 * ((32 * C1 + 40) * (1 / L ^ (G + 2) + P.Y ^ (-0.1 : ℝ)) *
          (1 + Real.log (2 * P.Y)) * Ipsi + 18 * C1 * Jpsi * (1 / L ^ (G + 2))) =
        4 ^ P.K * 5121 * ((32 * C1 + 40) * ((1 / L ^ (G + 2) + P.Y ^ (-0.1 : ℝ)) *
          (1 + Real.log (2 * P.Y))) * Ipsi + 18 * C1 * Jpsi * (1 / L ^ (G + 2))) := by ring
      _ ≤ 4 ^ P.K * 5121 * ((32 * C1 + 40) * ((2 * L ^ (-(G + 2))) * (4 * P.K * L ^ (0.2 : ℝ))) *
          Ipsi + 18 * C1 * Jpsi * (L ^ (0.2 : ℝ) * L ^ (-(G + 2)))) := by gcongr
      _ = _ := by ring
  have hpart2 : P.K * (4 / exp ℓ * 2 ^ P.K) * (16 + 16 * (10 * P.Y + 1) *
      (4 * L ^ (3 * (G + 2)) / P.Y)) ≤
      P.K * 4 * 2 ^ P.K * 720 * L ^ (3 * (G + 2)) * exp (-ℓ) := by
    have hL3 : 1 ≤ L ^ (3 * (G + 2)) := Real.one_le_rpow hL (by linarith only [hG])
    have hc : 16 + 16 * (10 * P.Y + 1) * (4 * L ^ (3 * (G + 2)) / P.Y) ≤
        720 * L ^ (3 * (G + 2)) := by
      have : 16 * (10 * P.Y + 1) * (4 * L ^ (3 * (G + 2)) / P.Y) =
          64 * L ^ (3 * (G + 2)) * (10 + 1 / P.Y) := by field_simp; ring
      rw [this]
      have hYi1 : 1 / P.Y ≤ 1 := by rw [div_le_one hY0]; exact hY1
      have h5 : L ^ (3 * (G + 2)) * (10 + 1 / P.Y) ≤ L ^ (3 * (G + 2)) * 11 :=
        mul_le_mul_of_nonneg_left (by linarith only [hYi1]) (by positivity)
      linarith only [h5, hL3]
    rw [show (4 : ℝ) / exp ℓ = 4 * exp (-ℓ) by rw [exp_neg]; ring]
    have : 0 ≤ (P.K : ℝ) * (4 * exp (-ℓ) * 2 ^ P.K) := by positivity
    calc P.K * (4 * exp (-ℓ) * 2 ^ P.K) * (16 + 16 * (10 * P.Y + 1) *
          (4 * L ^ (3 * (G + 2)) / P.Y)) ≤ P.K * (4 * exp (-ℓ) * 2 ^ P.K) *
          (720 * L ^ (3 * (G + 2))) := mul_le_mul_of_nonneg_left hc this
      _ = _ := by ring
  linarith only [hpart1, hpart2, F3, F4]

/-- The dirty raw part is `≤ L^{-G}/8`. -/
lemma raw_le (G : ℝ) (hG : 0 < G) (hL : 1 ≤ log P.x) (hB : (P.B : ℝ) ≤ 2 * log P.x ^ 2)
    (hM : log P.x ^ (0.01 : ℝ) ≤ ((P.J + 1 : ℕ) : ℝ))
    (F5 : 4 ^ P.K * (32 * (2 * log P.x ^ 2) * 8 ^ P.K / (log P.x ^ (0.01 : ℝ)) ^ P.K) ≤
      (log P.x ^ (-G)) ^ 2 / (2 * (8192 * 12 ^ P.K)))
    (F6 : 4 ^ P.K * (16 * (2 + 4 * (2 * log P.x ^ 2)) ^ P.K * exp (-(log P.x ^ (0.1 : ℝ)) / 4)) ≤
      (log P.x ^ (-G)) ^ 2 / (2 * (8192 * 12 ^ P.K))) :
    √(R1c P (exp (-(log P.x ^ (0.1 : ℝ)) / 4))) *
        √(3 ^ P.K * (R2c P + R1c P (exp (-(log P.x ^ (0.1 : ℝ)) / 4)))) +
      √(R2c P) * √(3 ^ P.K * R1c P (exp (-(log P.x ^ (0.1 : ℝ)) / 4))) ≤ log P.x ^ (-G) / 8 := by
  set L := log P.x
  set E := exp (-(L ^ (0.1 : ℝ)) / 4)
  set g := L ^ (-G)
  have hL0 : 0 < L := by linarith only [hL]
  have hg0 : 0 < g := Real.rpow_pos_of_pos hL0 _
  have hg1 : g ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith only [hG])
  set c3 : ℝ := 8192 * 12 ^ P.K
  have hc3 : 1 ≤ c3 := by
    have : (1 : ℝ) ≤ 12 ^ P.K := one_le_pow₀ (by norm_num)
    simp only [c3]; linarith only [this]
  have h12 : (12 : ℝ) ^ P.K = 3 ^ P.K * 4 ^ P.K := by rw [← mul_pow]; norm_num
  have h4 : (4 : ℝ) ^ P.K = 2 ^ P.K * 2 ^ P.K := by rw [← mul_pow]; norm_num
  have hR1 : R1c P E ≤ g ^ 2 / c3 := by
    unfold R1c
    have hMK : (L ^ (0.01 : ℝ)) ^ P.K ≤ ((P.J + 1 : ℕ) : ℝ) ^ P.K :=
      pow_le_pow_left₀ (Real.rpow_nonneg hL0.le _) hM P.K
    have hLK : 0 < (L ^ (0.01 : ℝ)) ^ P.K := pow_pos (Real.rpow_pos_of_pos hL0 _) _
    have t1 : 32 * (P.B : ℝ) * 8 ^ P.K / ((P.J + 1 : ℕ) : ℝ) ^ P.K ≤
        32 * (2 * L ^ 2) * 8 ^ P.K / (L ^ (0.01 : ℝ)) ^ P.K :=
      div_le_div₀ (by positivity) (by gcongr) hLK hMK
    have t2 : 16 * (2 + 4 * (P.B : ℝ)) ^ P.K * E ≤ 16 * (2 + 4 * (2 * L ^ 2)) ^ P.K * E := by
      have : (0 : ℝ) ≤ P.B := Nat.cast_nonneg _
      gcongr
    have := mul_le_mul_of_nonneg_left (add_le_add t1 t2) (by positivity : (0 : ℝ) ≤ 4 ^ P.K)
    rw [mul_add] at this
    have e : g ^ 2 / c3 = g ^ 2 / (2 * c3) + g ^ 2 / (2 * c3) := by field_simp; ring
    rw [e]
    have f5 : 4 ^ P.K * (32 * (2 * L ^ 2) * 8 ^ P.K / (L ^ (0.01 : ℝ)) ^ P.K) ≤
        g ^ 2 / (2 * c3) := F5
    have f6 : 4 ^ P.K * (16 * (2 + 4 * (2 * L ^ 2)) ^ P.K * E) ≤ g ^ 2 / (2 * c3) := F6
    linarith only [this, f5, f6]
  have hR1n : 0 ≤ R1c P E := by unfold R1c; positivity
  have hR2e : R2c P = 16 * 4 ^ P.K := by unfold R2c; rw [h4]; ring
  have hR2n : 0 ≤ R2c P := by rw [hR2e]; positivity
  have hρ : g ^ 2 / c3 ≤ R2c P := by
    rw [hR2e]
    have h1 : g ^ 2 ≤ 1 := pow_le_one₀ hg0.le hg1
    have h2 : g ^ 2 / c3 ≤ 1 := div_le_one_of_le₀ (h1.trans hc3) (by linarith only [hc3])
    have h3 : (1 : ℝ) ≤ 4 ^ P.K := one_le_pow₀ (by norm_num)
    linarith only [h2, h3]
  have hc3e : c3 = 8192 * (3 ^ P.K * 4 ^ P.K) := by simp only [c3]; rw [h12]
  have hc3p : 0 < c3 := by linarith only [hc3]
  have b1 : R1c P E * (3 ^ P.K * (R2c P + R1c P E)) ≤ (g / 16) ^ 2 := by
    calc R1c P E * (3 ^ P.K * (R2c P + R1c P E)) ≤ (g ^ 2 / c3) * (3 ^ P.K * (2 * R2c P)) := by
          apply mul_le_mul hR1 _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith only [hR1, hρ]) (by positivity)
      _ = (g / 16) ^ 2 := by rw [hR2e, hc3e]; field_simp; ring
  have b2 : R2c P * (3 ^ P.K * R1c P E) ≤ (g / 16) ^ 2 := by
    calc R2c P * (3 ^ P.K * R1c P E) ≤ R2c P * (3 ^ P.K * (g ^ 2 / c3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR1 (by positivity)) hR2n
      _ = g ^ 2 / 512 := by rw [hR2e, hc3e]; field_simp; ring
      _ ≤ (g / 16) ^ 2 := by
          have : 0 ≤ g ^ 2 := sq_nonneg g
          linarith only [this, show (g / 16) ^ 2 = g ^ 2 / 256 by ring]
  rw [← Real.sqrt_mul hR1n, ← Real.sqrt_mul hR2n]
  have s1 := sqrt_le_of_sq _ (g / 16) (by positivity) b1
  have s2 := sqrt_le_of_sq _ (g / 16) (by positivity) b2
  linarith only [s1, s2]

/-- The dirty comparison part is `≤ L^{-G}/4`. -/
lemma cmp_le (G : ℝ) (hA : P.A₀ = G + 2) (hL : 1 ≤ log P.x) (hY1 : 1 ≤ P.Y)
    (hB : (P.B : ℝ) ≤ 2 * log P.x ^ 2)
    (hYm : P.Y ^ (-(0.1 : ℝ)) ≤ 4 * exp (-(0.1 * log P.x ^ (0.1 : ℝ))))
    (hYi : 1 / P.Y ≤ 4 * exp (-(log P.x ^ (0.1 : ℝ))))
    (F7 : 3 ^ P.K * (2 ^ P.K * P.K * 8 * log P.x ^ (3 * (G + 2)) * (2 + 4 * log P.x ^ 2) ^ P.K *
      (2 * log P.x ^ 2) * ((9 * C1 + 24) * exp (-(0.1 * log P.x ^ (0.1 : ℝ))))) *
      (2 ^ P.K * 704 * log P.x ^ (3 * (G + 2)) * (2 + 4 * log P.x ^ 2) ^ P.K) ≤
      (log P.x ^ (-G)) ^ 2 / 64) :
    √(R3c P (exp (log P.x ^ (0.1 : ℝ)))) * √(3 ^ P.K * R4c P) +
      √(R4c P) * √(3 ^ P.K * R3c P (exp (log P.x ^ (0.1 : ℝ)))) ≤ log P.x ^ (-G) / 4 := by
  set L := log P.x
  set ℓ := L ^ (0.1 : ℝ)
  set g := L ^ (-G)
  have hL0 : 0 < L := by linarith only [hL]
  have hg0 : 0 < g := Real.rpow_pos_of_pos hL0 _
  have hY0 : 0 < P.Y := by linarith only [hY1]
  have hC1 := C1_nonneg
  have hB0 : (0 : ℝ) ≤ P.B := Nat.cast_nonneg _
  have hℓ0 : 0 ≤ ℓ := by positivity
  have hexp1 : exp (-ℓ) ≤ exp (-(0.1 * ℓ)) := exp_le_exp.2 (by linarith only [hℓ0])
  have hBB : (2 + 2 * (P.B : ℝ)) ^ P.K ≤ (2 + 4 * L ^ 2) ^ P.K :=
    pow_le_pow_left₀ (by positivity) (by linarith only [hB]) P.K
  have hR3 : R3c P (exp ℓ) ≤ 2 ^ P.K * P.K * 8 * L ^ (3 * (G + 2)) * (2 + 4 * L ^ 2) ^ P.K *
      (2 * L ^ 2) * ((9 * C1 + 24) * exp (-(0.1 * ℓ))) := by
    unfold R3c
    rw [hA]
    have hY09 : P.Y ^ (0.9 : ℝ) = P.Y * P.Y ^ (-(0.1 : ℝ)) := by
      rw [show (0.9 : ℝ) = 1 + (-(0.1 : ℝ)) by norm_num, Real.rpow_add hY0, Real.rpow_one]
    have hQ : 4 * L ^ (3 * (G + 2)) / P.Y * (9 * C1 * P.Y / exp ℓ + 4 * P.Y ^ (0.9 : ℝ) + 2) =
        4 * L ^ (3 * (G + 2)) * (9 * C1 * exp (-ℓ) + 4 * P.Y ^ (-(0.1 : ℝ)) + 2 * (1 / P.Y)) := by
      rw [hY09, exp_neg]; field_simp
    have hQb : 9 * C1 * exp (-ℓ) + 4 * P.Y ^ (-(0.1 : ℝ)) + 2 * (1 / P.Y) ≤
        (9 * C1 + 24) * exp (-(0.1 * ℓ)) := by
      have h1 := mul_le_mul_of_nonneg_left hexp1 (by positivity : (0 : ℝ) ≤ 9 * C1)
      have h2 : 2 * (1 / P.Y) ≤ 8 * exp (-(0.1 * ℓ)) := by linarith only [hYi, hexp1]
      linarith only [h1, h2, hYm]
    have h0 : 0 ≤ 9 * C1 * exp (-ℓ) + 4 * P.Y ^ (-(0.1 : ℝ)) + 2 * (1 / P.Y) := by
      have := Real.rpow_nonneg hY0.le (-(0.1 : ℝ)); positivity
    calc 2 ^ P.K * P.K * (2 * (4 * L ^ (3 * (G + 2)) / P.Y) * (2 + 2 * P.B) ^ P.K *
          ((9 * C1 * P.Y / exp ℓ + 4 * P.Y ^ (0.9 : ℝ) + 2) * P.B)) =
        2 ^ P.K * P.K * 2 * (2 + 2 * P.B) ^ P.K * P.B *
          (4 * L ^ (3 * (G + 2)) / P.Y * (9 * C1 * P.Y / exp ℓ + 4 * P.Y ^ (0.9 : ℝ) + 2)) := by
          ring
      _ = 2 ^ P.K * P.K * 2 * (2 + 2 * P.B) ^ P.K * P.B *
          (4 * L ^ (3 * (G + 2)) * (9 * C1 * exp (-ℓ) + 4 * P.Y ^ (-(0.1 : ℝ)) + 2 * (1 / P.Y))) := by
          rw [hQ]
      _ ≤ 2 ^ P.K * P.K * 2 * (2 + 4 * L ^ 2) ^ P.K * (2 * L ^ 2) *
          (4 * L ^ (3 * (G + 2)) * ((9 * C1 + 24) * exp (-(0.1 * ℓ)))) := by gcongr
      _ = _ := by ring
  have hR4 : R4c P ≤ 2 ^ P.K * 704 * L ^ (3 * (G + 2)) * (2 + 4 * L ^ 2) ^ P.K := by
    unfold R4c
    rw [hA]
    have e : 16 * (10 * P.Y + 1) * (4 * L ^ (3 * (G + 2)) / P.Y) =
        64 * L ^ (3 * (G + 2)) * (10 + 1 / P.Y) := by field_simp; ring
    rw [e]
    have hYi1 : 1 / P.Y ≤ 1 := by rw [div_le_one hY0]; exact hY1
    have h5 : 64 * L ^ (3 * (G + 2)) * (10 + 1 / P.Y) ≤ 704 * L ^ (3 * (G + 2)) := by
      have := mul_le_mul_of_nonneg_left (show 10 + 1 / P.Y ≤ 11 by linarith only [hYi1])
        (by positivity : (0 : ℝ) ≤ 64 * L ^ (3 * (G + 2)))
      linarith only [this]
    calc 2 ^ P.K * (64 * L ^ (3 * (G + 2)) * (10 + 1 / P.Y)) * (2 + 2 * P.B) ^ P.K ≤
        2 ^ P.K * (704 * L ^ (3 * (G + 2))) * (2 + 4 * L ^ 2) ^ P.K := by gcongr
      _ = _ := by ring
  have hR3n : 0 ≤ R3c P (exp ℓ) := by
    unfold R3c
    have := Real.rpow_nonneg hY0.le (0.9 : ℝ)
    positivity
  have hR4n : 0 ≤ R4c P := by unfold R4c; positivity
  have hprod : R3c P (exp ℓ) * (3 ^ P.K * R4c P) ≤ (g / 8) ^ 2 := by
    calc R3c P (exp ℓ) * (3 ^ P.K * R4c P) = 3 ^ P.K * R3c P (exp ℓ) * R4c P := by ring
      _ ≤ 3 ^ P.K * (2 ^ P.K * P.K * 8 * L ^ (3 * (G + 2)) * (2 + 4 * L ^ 2) ^ P.K *
          (2 * L ^ 2) * ((9 * C1 + 24) * exp (-(0.1 * ℓ)))) *
          (2 ^ P.K * 704 * L ^ (3 * (G + 2)) * (2 + 4 * L ^ 2) ^ P.K) := by gcongr
      _ ≤ g ^ 2 / 64 := F7
      _ = (g / 8) ^ 2 := by ring
  rw [← Real.sqrt_mul hR3n, ← Real.sqrt_mul hR4n]
  have e : R4c P * (3 ^ P.K * R3c P (exp ℓ)) = R3c P (exp ℓ) * (3 ^ P.K * R4c P) := by ring
  rw [e]
  have s1 := sqrt_le_of_sq _ (g / 8) (by positivity) hprod
  linarith only [s1]

/-- **The asymptotic bound**, given the large-`L` inequalities `F2`–`F7`. -/
theorem Ctot_le (G : ℝ) (hG : 0 < G) (hA : P.A₀ = G + 2) (hK1 : 1 ≤ P.K)
    (hL : 1 ≤ log P.x) (hB : (P.B : ℝ) ≤ 2 * log P.x ^ 2)
    (hM : log P.x ^ (0.01 : ℝ) ≤ ((P.J + 1 : ℕ) : ℝ))
    (hY1 : 1 ≤ P.Y) (hYlo : exp (P.K * log P.x ^ (0.1 : ℝ)) / 4 < P.Y)
    (hYhi : P.Y < exp (2 * P.K * log P.x ^ (0.2 : ℝ)))
    (F2 : 4 * exp (-(0.1 * log P.x ^ (0.1 : ℝ))) ≤ log P.x ^ (-(G + 2)))
    (F3 : 4 ^ P.K * 5121 * (8 * P.K * (32 * C1 + 40) * Ipsi + 18 * C1 * Jpsi) *
      (log P.x ^ (0.2 : ℝ) * log P.x ^ (-(G + 2))) ≤ log P.x ^ (-G) / 8)
    (F4 : P.K * 4 * 2 ^ P.K * 720 * log P.x ^ (3 * (G + 2)) * exp (-(log P.x ^ (0.1 : ℝ))) ≤
      log P.x ^ (-G) / 8)
    (F5 : 4 ^ P.K * (32 * (2 * log P.x ^ 2) * 8 ^ P.K / (log P.x ^ (0.01 : ℝ)) ^ P.K) ≤
      (log P.x ^ (-G)) ^ 2 / (2 * (8192 * 12 ^ P.K)))
    (F6 : 4 ^ P.K * (16 * (2 + 4 * (2 * log P.x ^ 2)) ^ P.K * exp (-(log P.x ^ (0.1 : ℝ)) / 4)) ≤
      (log P.x ^ (-G)) ^ 2 / (2 * (8192 * 12 ^ P.K)))
    (F7 : 3 ^ P.K * (2 ^ P.K * P.K * 8 * log P.x ^ (3 * (G + 2)) * (2 + 4 * log P.x ^ 2) ^ P.K *
      (2 * log P.x ^ 2) * ((9 * C1 + 24) * exp (-(0.1 * log P.x ^ (0.1 : ℝ))))) *
      (2 ^ P.K * 704 * log P.x ^ (3 * (G + 2)) * (2 + 4 * log P.x ^ 2) ^ P.K) ≤
      (log P.x ^ (-G)) ^ 2 / 64) :
    Ctot P (exp (log P.x ^ (0.1 : ℝ))) (exp (-(log P.x ^ (0.1 : ℝ)) / 4)) ≤ log P.x ^ (-G) := by
  obtain ⟨hYm, hYi, hl2Y⟩ := Y_facts P hK1 hL hY1 hYlo hYhi
  have h1 := Ecl_le P G hG hA hK1 hL hY1 hYm hl2Y F2 F3 F4
  have h2 := raw_le P G hG hL hB hM F5 F6
  have h3 := cmp_le P G hA hL hY1 hB hYm hYi F7
  have hg : 0 ≤ log P.x ^ (-G) := Real.rpow_nonneg (by linarith only [hL]) _
  calc Ctot P (exp (log P.x ^ (0.1 : ℝ))) (exp (-(log P.x ^ (0.1 : ℝ)) / 4)) =
      Ecl P (exp (log P.x ^ (0.1 : ℝ))) + (√(R1c P (exp (-(log P.x ^ (0.1 : ℝ)) / 4))) *
        √(3 ^ P.K * (R2c P + R1c P (exp (-(log P.x ^ (0.1 : ℝ)) / 4)))) +
        √(R2c P) * √(3 ^ P.K * R1c P (exp (-(log P.x ^ (0.1 : ℝ)) / 4)))) +
      (√(R3c P (exp (log P.x ^ (0.1 : ℝ)))) * √(3 ^ P.K * R4c P) +
        √(R4c P) * √(3 ^ P.K * R3c P (exp (log P.x ^ (0.1 : ℝ))))) := rfl
    _ ≤ log P.x ^ (-G) / 4 + log P.x ^ (-G) / 8 + log P.x ^ (-G) / 4 :=
        add_le_add (add_le_add h1 h2) h3
    _ ≤ log P.x ^ (-G) := by linarith only [hg]

/-! ## The large-`L` inequalities -/

lemma conv_exp {L c d G k X : ℝ} (hL : 0 < L) (hk : 0 < k)
    (h : k * c * L ^ (d + G) * X ≤ 1) : c * L ^ d * X ≤ L ^ (-G) / k := by
  rw [Real.rpow_add hL] at h
  rw [Real.rpow_neg hL.le, le_div_iff₀ hk]
  have hG : 0 < L ^ G := Real.rpow_pos_of_pos hL _
  rw [inv_eq_one_div, le_div_iff₀ hG]
  calc c * L ^ d * X * k * L ^ G = k * c * (L ^ d * L ^ G) * X := by ring
    _ ≤ 1 := h

lemma rpow_neg_sq {L G : ℝ} (hL : 0 < L) : (L ^ (-G)) ^ 2 = L ^ (-(2 * G)) := by
  rw [sq, ← Real.rpow_add hL]; ring_nf

lemma ev_F2 (G : ℝ) : ∀ᶠ L : ℝ in atTop,
    4 * exp (-(0.1 * L ^ (0.1 : ℝ))) ≤ L ^ (-(G + 2)) := by
  filter_upwards [eventually_gt_atTop 0, ev_poly_exp 4 (0 + (G + 2)) 0.1 (by norm_num)]
    with L hL0 hF2
  have := conv_exp (c := 4) (d := 0) (G := G + 2) (k := 1) (X := exp (-(0.1 * L ^ (0.1 : ℝ))))
    hL0 one_pos (by rw [one_mul]; exact hF2)
  rwa [Real.rpow_zero, mul_one, div_one] at this

lemma ev_F3 (G cA : ℝ) : ∀ᶠ L : ℝ in atTop,
    cA * (L ^ (0.2 : ℝ) * L ^ (-(G + 2))) ≤ L ^ (-G) / 8 := by
  filter_upwards [eventually_gt_atTop 0, ev_rpow_small (8 * cA) 1.8 (by norm_num)] with L hL0 hF3
  have e : L ^ (0.2 : ℝ) * L ^ (-(G + 2)) = L ^ (-(1.8 : ℝ)) * L ^ (-G) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; ring_nf
  rw [e]
  have h1 := mul_le_mul_of_nonneg_right hF3 (div_nonneg (Real.rpow_nonneg hL0.le (-G))
    (by norm_num : (0 : ℝ) ≤ 8))
  have e2 : 8 * cA * L ^ (-(1.8 : ℝ)) * (L ^ (-G) / 8) = cA * (L ^ (-(1.8 : ℝ)) * L ^ (-G)) := by
    ring
  linarith only [h1, e2]

lemma ev_F4 (G c4 : ℝ) : ∀ᶠ L : ℝ in atTop,
    c4 * L ^ (3 * (G + 2)) * exp (-(L ^ (0.1 : ℝ))) ≤ L ^ (-G) / 8 := by
  filter_upwards [eventually_gt_atTop 0, ev_poly_exp (8 * c4) (3 * (G + 2) + G) 1 one_pos]
    with L hL0 hF4
  rw [one_mul] at hF4
  exact conv_exp (k := 8) hL0 (by norm_num) hF4

lemma ev_F5 (G : ℝ) (K : ℕ) (hKG : 2 * G + 4 ≤ (0.01 : ℝ) * K) : ∀ᶠ L : ℝ in atTop,
    4 ^ K * (32 * (2 * L ^ 2) * 8 ^ K / (L ^ (0.01 : ℝ)) ^ K) ≤
      (L ^ (-G)) ^ 2 / (2 * (8192 * 12 ^ K)) := by
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_pow_atTop (two_ne_zero)).eventually_ge_atTop (128 * (8192 * 12 ^ K) * 32 ^ K)]
    with L hL hF5
  set c3 : ℝ := 8192 * 12 ^ K
  have hL0 : 0 < L := by linarith only [hL]
  have hLK : L ^ (2 * G + 4) ≤ (L ^ (0.01 : ℝ)) ^ K := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    exact Real.rpow_le_rpow_of_exponent_le hL hKG
  have hp : 0 < L ^ (2 * G + 4) := Real.rpow_pos_of_pos hL0 _
  have e4 : L ^ (2 * G + 4) = L ^ (2 * G) * L ^ 2 * L ^ 2 := by
    rw [Real.rpow_add hL0, show (4 : ℝ) = (2 : ℕ) + (2 : ℕ) by norm_num, Real.rpow_add hL0,
      Real.rpow_natCast]; ring
  have h2G : 0 < L ^ (2 * G) := Real.rpow_pos_of_pos hL0 _
  have hL2 : 0 < L ^ 2 := pow_pos hL0 2
  have hc3 : 0 < c3 := by positivity
  rw [rpow_neg_sq hL0, Real.rpow_neg hL0.le]
  have h32 : (4 : ℝ) ^ K * 8 ^ K = 32 ^ K := by rw [← mul_pow]; norm_num
  have e1 : 4 ^ K * (32 * (2 * L ^ 2) * 8 ^ K / (L ^ (0.01 : ℝ)) ^ K) =
      64 * 32 ^ K * L ^ 2 / (L ^ (0.01 : ℝ)) ^ K := by rw [← h32]; ring
  rw [e1]
  have h32p : (0 : ℝ) < 32 ^ K := by positivity
  calc 64 * 32 ^ K * L ^ 2 / (L ^ (0.01 : ℝ)) ^ K ≤ 64 * 32 ^ K * L ^ 2 / L ^ (2 * G + 4) :=
        div_le_div_of_nonneg_left (by positivity) hp hLK
    _ ≤ (L ^ (2 * G))⁻¹ / (2 * c3) := by
        rw [e4, div_le_div_iff₀ (by positivity) (by positivity)]
        have e5 : (L ^ (2 * G))⁻¹ * (L ^ (2 * G) * L ^ 2 * L ^ 2) = L ^ 2 * L ^ 2 := by
          field_simp
        rw [e5]
        have := mul_le_mul_of_nonneg_left hF5 hL2.le
        nlinarith only [this, hL2]

lemma ev_F6 (G : ℝ) (K : ℕ) : ∀ᶠ L : ℝ in atTop,
    4 ^ K * (16 * (2 + 4 * (2 * L ^ 2)) ^ K * exp (-(L ^ (0.1 : ℝ)) / 4)) ≤
      (L ^ (-G)) ^ 2 / (2 * (8192 * 12 ^ K)) := by
  filter_upwards [eventually_ge_atTop 1,
    ev_poly_exp (2 * (8192 * 12 ^ K) * (16 * 40 ^ K)) ((2 * K : ℝ) + 2 * G) (1 / 4) (by norm_num)]
    with L hL hF6
  set c3 : ℝ := 8192 * 12 ^ K
  have hL0 : 0 < L := by linarith only [hL]
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hb : 2 + 4 * (2 * L ^ 2) ≤ 10 * L ^ 2 := by linarith only [hL2]
  have e : L ^ ((2 * K : ℝ) + 2 * G) = (L ^ 2) ^ K * L ^ (2 * G) := by
    rw [Real.rpow_add hL0, show (2 * K : ℝ) = ((2 * K : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
  rw [e] at hF6
  rw [rpow_neg_sq hL0, Real.rpow_neg hL0.le]
  have h2G : 0 < L ^ (2 * G) := Real.rpow_pos_of_pos hL0 _
  have hc3 : 0 < c3 := by positivity
  have e2 : exp (-(L ^ (0.1 : ℝ)) / 4) = exp (-(1 / 4 * L ^ (0.1 : ℝ))) := by ring_nf
  rw [e2]
  have hX : 0 ≤ exp (-(1 / 4 * L ^ (0.1 : ℝ))) := (exp_pos _).le
  calc 4 ^ K * (16 * (2 + 4 * (2 * L ^ 2)) ^ K * exp (-(1 / 4 * L ^ (0.1 : ℝ)))) ≤
      4 ^ K * (16 * (10 * L ^ 2) ^ K * exp (-(1 / 4 * L ^ (0.1 : ℝ)))) := by
        gcongr
    _ = 16 * 40 ^ K * (L ^ 2) ^ K * exp (-(1 / 4 * L ^ (0.1 : ℝ))) := by
        rw [mul_pow, show (40 : ℝ) ^ K = 4 ^ K * 10 ^ K by rw [← mul_pow]; norm_num]; ring
    _ ≤ (L ^ (2 * G))⁻¹ / (2 * c3) := by
        rw [le_div_iff₀ (by positivity), inv_eq_one_div, le_div_iff₀ h2G]
        calc 16 * 40 ^ K * (L ^ 2) ^ K * exp (-(1 / 4 * L ^ (0.1 : ℝ))) * (2 * c3) *
            L ^ (2 * G) = 2 * c3 * (16 * 40 ^ K) * ((L ^ 2) ^ K * L ^ (2 * G)) *
              exp (-(1 / 4 * L ^ (0.1 : ℝ))) := by ring
          _ ≤ 1 := hF6

lemma ev_F7 (G : ℝ) (K : ℕ) : ∀ᶠ L : ℝ in atTop,
    3 ^ K * (2 ^ K * K * 8 * L ^ (3 * (G + 2)) * (2 + 4 * L ^ 2) ^ K *
      (2 * L ^ 2) * ((9 * C1 + 24) * exp (-(0.1 * L ^ (0.1 : ℝ))))) *
      (2 ^ K * 704 * L ^ (3 * (G + 2)) * (2 + 4 * L ^ 2) ^ K) ≤ (L ^ (-G)) ^ 2 / 64 := by
  set Cc : ℝ := 3 ^ K * 4 ^ K * 36 ^ K * K * 11264 * (9 * C1 + 24)
  filter_upwards [eventually_ge_atTop 1,
    ev_poly_exp (64 * Cc) ((3 * (G + 2) + 3 * (G + 2) + 2 + 4 * K) + 2 * G) 0.1 (by norm_num)]
    with L hL hF7
  have hC1 := C1_nonneg
  have hL0 : 0 < L := by linarith only [hL]
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hb : 2 + 4 * L ^ 2 ≤ 6 * L ^ 2 := by linarith only [hL2]
  have e : L ^ ((3 * (G + 2) + 3 * (G + 2) + 2 + 4 * K) + 2 * G) =
      L ^ (3 * (G + 2)) * L ^ (3 * (G + 2)) * L ^ 2 * ((L ^ 2) ^ K * (L ^ 2) ^ K) *
        L ^ (2 * G) := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (4 * K : ℝ) = ((4 * K : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [← pow_add, ← pow_mul]; ring_nf
  rw [e] at hF7
  rw [rpow_neg_sq hL0, Real.rpow_neg hL0.le]
  have h2G : 0 < L ^ (2 * G) := Real.rpow_pos_of_pos hL0 _
  have hL3 : 0 ≤ L ^ (3 * (G + 2)) := Real.rpow_nonneg hL0.le _
  set X := exp (-(0.1 * L ^ (0.1 : ℝ)))
  have hX : 0 ≤ X := (exp_pos _).le
  calc 3 ^ K * (2 ^ K * K * 8 * L ^ (3 * (G + 2)) * (2 + 4 * L ^ 2) ^ K * (2 * L ^ 2) *
        ((9 * C1 + 24) * X)) * (2 ^ K * 704 * L ^ (3 * (G + 2)) * (2 + 4 * L ^ 2) ^ K) ≤
      3 ^ K * (2 ^ K * K * 8 * L ^ (3 * (G + 2)) * (6 * L ^ 2) ^ K * (2 * L ^ 2) *
        ((9 * C1 + 24) * X)) * (2 ^ K * 704 * L ^ (3 * (G + 2)) * (6 * L ^ 2) ^ K) := by
        gcongr
    _ = Cc * (L ^ (3 * (G + 2)) * L ^ (3 * (G + 2)) * L ^ 2 * ((L ^ 2) ^ K * (L ^ 2) ^ K)) *
        X := by
        simp only [Cc]
        rw [mul_pow, show (36 : ℝ) ^ K = 6 ^ K * 6 ^ K by rw [← mul_pow]; norm_num,
          show (4 : ℝ) ^ K = 2 ^ K * 2 ^ K by rw [← mul_pow]; norm_num]
        ring
    _ ≤ (L ^ (2 * G))⁻¹ / 64 := by
        rw [le_div_iff₀ (by norm_num), inv_eq_one_div, le_div_iff₀ h2G]
        calc Cc * (L ^ (3 * (G + 2)) * L ^ (3 * (G + 2)) * L ^ 2 *
              ((L ^ 2) ^ K * (L ^ 2) ^ K)) * X * 64 * L ^ (2 * G) =
            64 * Cc * (L ^ (3 * (G + 2)) * L ^ (3 * (G + 2)) * L ^ 2 *
              ((L ^ 2) ^ K * (L ^ 2) ^ K) * L ^ (2 * G)) * X := by ring
          _ ≤ 1 := hF7

lemma ev_F8 : ∀ᶠ L : ℝ in atTop, (2 * cLat + 2) ^ 10 ≤ exp (L ^ (0.1 : ℝ)) / 4 := by
  have hℓ : Tendsto (fun L : ℝ => L ^ (0.1 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [hℓ.eventually_ge_atTop (4 * (2 * cLat + 2) ^ 10)] with L hF8
  have := Real.add_one_le_exp (L ^ (0.1 : ℝ))
  linarith only [this, hF8]

/-- All large-`L` inequalities at once. -/
lemma ev_all (G : ℝ) (K : ℕ) (hKG : 2 * G + 4 ≤ (0.01 : ℝ) * K) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧
      (4 * exp (-(0.1 * L ^ (0.1 : ℝ))) ≤ L ^ (-(G + 2))) ∧
      (4 ^ K * 5121 * (8 * K * (32 * C1 + 40) * Ipsi + 18 * C1 * Jpsi) *
        (L ^ (0.2 : ℝ) * L ^ (-(G + 2))) ≤ L ^ (-G) / 8) ∧
      (K * 4 * 2 ^ K * 720 * L ^ (3 * (G + 2)) * exp (-(L ^ (0.1 : ℝ))) ≤ L ^ (-G) / 8) ∧
      (4 ^ K * (32 * (2 * L ^ 2) * 8 ^ K / (L ^ (0.01 : ℝ)) ^ K) ≤
        (L ^ (-G)) ^ 2 / (2 * (8192 * 12 ^ K))) ∧
      (4 ^ K * (16 * (2 + 4 * (2 * L ^ 2)) ^ K * exp (-(L ^ (0.1 : ℝ)) / 4)) ≤
        (L ^ (-G)) ^ 2 / (2 * (8192 * 12 ^ K))) ∧
      (3 ^ K * (2 ^ K * K * 8 * L ^ (3 * (G + 2)) * (2 + 4 * L ^ 2) ^ K *
        (2 * L ^ 2) * ((9 * C1 + 24) * exp (-(0.1 * L ^ (0.1 : ℝ))))) *
        (2 ^ K * 704 * L ^ (3 * (G + 2)) * (2 + 4 * L ^ 2) ^ K) ≤ (L ^ (-G)) ^ 2 / 64) ∧
      ((2 * cLat + 2) ^ 10 ≤ exp (L ^ (0.1 : ℝ)) / 4) :=
  (eventually_ge_atTop 1).and ((ev_F2 G).and ((ev_F3 G _).and ((ev_F4 G _).and
    ((ev_F5 G K hKG).and ((ev_F6 G K).and ((ev_F7 G K).and ev_F8))))))

lemma opBound_mono {O : (P.MState → ℂ) → (P.MState → ℂ)} {C C' : ℝ} (h : P.OpBound O C)
    (hC : C ≤ C') : P.OpBound O C' := fun f =>
  (h f).trans (mul_le_mul_of_nonneg_right hC (Real.sqrt_nonneg _))

end ArtinPrimitiveRoots.L102G

namespace ArtinPrimitiveRoots

open Real Finset Filter L102G

/-- **D7d** ([21] (4.23)–(4.42), the edge bound): `EdgeBoundStmt` verbatim, with `A₀ = G + 2`
and `K₀ = ⌈100 (2G + 4)⌉`. -/
theorem chk_edge_bound (δ c₁ c₂ : ℝ) : L102D.EdgeBoundStmt δ c₁ c₂ := by
  intro G hG
  refine ⟨G + 2, by linarith only [hG], ⌈100 * (2 * G + 4)⌉₊, ?_⟩
  intro K hK1 hK0 a ha hab
  have hKG : 2 * G + 4 ≤ (0.01 : ℝ) * K := by
    have := (Nat.ceil_le).1 hK0
    linarith only [this]
  have ha0 : ∀ i, 0 < a i := fun i => by linarith only [(hab i).1]
  have ha1 : ∀ i, (0.1 : ℝ) < a i := fun i => (hab i).1
  have hev := (eventually_Vg_ge_half' a ha0).and ((eventually_Vg_le' a ha0).and
    ((L102D.eventually_groupPrimes_ge a ha1 4).and ((eventually_disjoint_groups' a ha).and
    ((tendsto_log_atTop.eventually (ev_all G K hKG)).and (eventually_gt_atTop 0)))))
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨x₀, ?_⟩
  intro x Hm Hn hx hHm hHn _ _ Y hY k P ω hω j _
  obtain ⟨hV1, hV2, hgp, hdisj, ⟨hL, F2, F3, F4, F5, F6, F7, F8⟩, hx0⟩ := hx₀ x hx
  have hgG : 0 ≤ log x ^ (-G) := Real.rpow_nonneg (by linarith only [hL]) _
  by_cases hvan : ∀ lab ∈ labCands P, dyadicBump (((∏ i, lab i : ℕ) : ℝ) / P.Y) = 0
  · exact opBound_of_vanish P ω j _ hgG hvan
  push Not at hvan
  obtain ⟨lab, hlab, hη⟩ := hvan
  have hY0 : 0 < P.Y := by show 0 < Y; linarith only [hY]
  obtain ⟨hYlo, hYhi⟩ := Y_bounds P hL hab hY0 lab hlab hη
  -- the parameter facts
  have hEP : EP P := by
    refine ⟨fun i => hV1 i, fun i => hV2 i, fun p hp => ?_, fun i i' h => hdisj i i' h⟩
    refine L102D.bprime_ge_half P ?_
    have h := hgp p hp
    have : (4 * (momentPower x + 1) : ℝ) ≤ p := h
    have h2 : 4 * (momentPower x + 1) ≤ p := by exact_mod_cast this
    show 2 * (2 * momentPower x) + 1 ≤ p
    omega
  have hU : 0 < P.U := by
    show 0 < 2 ^ k * Y * Hm
    have h1 : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 _
    have h2 : (0 : ℝ) < 2 ^ k := pow_pos two_pos k
    have h3 : 0 < Hm := by linarith only [h1, hHm]
    exact mul_pos (mul_pos h2 (by linarith only [hY])) h3
  have hℓ0 : 0 ≤ log x ^ (0.1 : ℝ) := Real.rpow_nonneg (by linarith only [hL]) _
  have hpmin : ∀ i, ∀ p ∈ P.grp i, exp (log x ^ (0.1 : ℝ)) ≤ p := by
    intro i p hp
    have h := (le_of_mem_primeGroup' hp).1
    have e : log x ^ (0.1 : ℝ) ≤ log x ^ a i := Real.rpow_le_rpow_of_exponent_le hL (hab i).1.le
    exact (exp_le_exp.2 e).trans h
  have hE : ∀ i, exp (-(log P.x ^ P.a i) / 4) ≤ exp (-(log x ^ (0.1 : ℝ)) / 4) := by
    intro i
    apply exp_le_exp.2
    have e : log x ^ (0.1 : ℝ) ≤ log x ^ a i := Real.rpow_le_rpow_of_exponent_le hL (hab i).1.le
    show -(log x ^ a i) / 4 ≤ -(log x ^ (0.1 : ℝ)) / 4
    linarith only [e]
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hYbig : (2 * cLat + 2) ^ 10 ≤ P.Y := by
    refine F8.trans (le_trans ?_ hYlo.le)
    gcongr
    exact le_mul_of_one_le_left hℓ0 hK1'
  have hop := edge_opBound P hEP ω hω hU j hL (by show (0 : ℝ) ≤ G + 2; linarith only [hG])
    (Real.one_le_rpow hL (by show (0 : ℝ) ≤ G + 2; linarith only [hG])) hY hYbig
    (by show (0 : ℝ) < ((2 ^ k : ℕ) : ℝ); positivity) _ (Real.one_le_exp hℓ0) hpmin _
    (exp_pos _).le hE
  refine opBound_mono P hop ?_
  have hB : (P.B : ℝ) ≤ 2 * log P.x ^ 2 := by
    show ((⌈log x ^ 2⌉₊ : ℕ) : ℝ) ≤ 2 * log x ^ 2
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ log x ^ 2 by positivity)
    have h1 : (1 : ℝ) ≤ log x ^ 2 := one_le_pow₀ hL
    linarith only [this, h1]
  have hM : log P.x ^ (0.01 : ℝ) ≤ ((P.J + 1 : ℕ) : ℝ) := by
    show log x ^ (0.01 : ℝ) ≤ ((padCount x + 1 : ℕ) : ℝ)
    unfold padCount
    push_cast
    exact (Nat.lt_floor_add_one _).le
  exact Ctot_le P G hG rfl hK1 hL hB hM hY hYlo hYhi F2 F3 F4 F5 F6 F7

end ArtinPrimitiveRoots
end

section
/-! Check module: `chk_opBound_edgeOp`, the published statement `opBound_edgeOp` verbatim, proved
from the development (`chk_edge_bound`). -/

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (δ c₁ c₂ : ℝ) :
    ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          let P := dyadParams x a A₀ Y Hm Hn k
          ∀ ω, P.RootIn ω → ∀ j < P.N, P.OpBound (P.edgeOp ω j) (log x ^ (-G)) :=
  chk_edge_bound δ c₁ c₂
end
