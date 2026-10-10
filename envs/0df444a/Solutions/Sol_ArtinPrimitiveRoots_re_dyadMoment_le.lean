-- Prove2me | solution 1 for ArtinPrimitiveRoots.re_dyadMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:55:39.773058+00:00
-- url     : https://prove2.me/submissions/15bb6126-2447-4dd9-b703-41edb87e341a

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare
import Theorems.Thm_ArtinPrimitiveRoots_momentSum_eq_sum_pathPhi
import Theorems.Thm_ArtinPrimitiveRoots_norm_sum_pathPhi_sub_integral_rootIL_le_of_pos
import Theorems.Thm_ArtinPrimitiveRoots_rootIL_eq_baseline_mul_memMomentD
import Theorems.Thm_ArtinPrimitiveRoots_norm_memMomentD_sub_truncated_le
import Theorems.Thm_ArtinPrimitiveRoots_opBound_edgeOp
import Theorems.Thm_ArtinPrimitiveRoots_norm_memMomentD_le_of_opBound_edgeOp

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

/-- **D7** ([21] Prop. 4.1, (4.1)): for every `E₀` one can choose `A₀`, then `K₀`, so that at every
dyad `d₀ = 2^k` the moment is `≤ U V L^{-E₀ N}`, `U = d₀ Y H_m`, `V = H_n`, `N = 2R`. -/
def MomentBoundStmt (δ c₁ c₂ : ℝ) : Prop :=
  ∀ E₀ : ℝ, 0 < E₀ → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
        (dyadMoment x a A₀ Y Hm Hn k).re ≤
          2 ^ k * Y * Hm * Hn * log x ^ (-(E₀ * (2 * momentPower x)))

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

/-- **D7p** (exact path expansion in root coordinates). For disjoint groups, `R ≥ 1` and
`U, V ≥ 1`, the physical moment `∑_P ⟨u_P, (AA*)^R u_P⟩_σ` equals the sum over the primitive
roots `P₀ ∈ Ω` of the path functional at the root `P₀` with physical divisibility. -/
def PathExpansionStmt : Prop :=
  ∀ (x : ℝ) (K : ℕ) (a : Fin K → ℝ) (A₀ Y : ℝ) (J R d₀ : ℕ) (U V : ℝ) (B : ℕ),
    (∀ i i', i ≠ i' → Disjoint (primeGroup x (a i)) (primeGroup x (a i'))) →
    1 ≤ R → 1 ≤ U → 1 ≤ V →
    momentSum x a A₀ Y J R d₀ U V =
      ∑ P₀ ∈ posBox U V,
        (⟨x, K, a, A₀, Y, J, 2 * R, d₀, U, V, B⟩ : MemParams).pathPhi (rootOf P₀) (physDelta P₀)

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

/-- **D7b** ([21] (4.16), truncation). Truncating the memory at `B = ⌈L²⌉` changes the distinct
memory moment by at most `L^{-AN}`, uniformly in the root. -/
def TruncationStmt (δ c₁ c₂ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
        let P := dyadParams x a A₀ Y Hm Hn k
        ∀ ω, P.RootIn ω →
          ‖(P.withB P.gPrimes.card).memMomentD ω - P.memMomentD ω‖ ≤ log x ^ (-(A * P.N))

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
/-! # L102D: the spectral Hölder step of [21] §3.3, (3.20), in abstract form

For a finite-dimensional complex inner product space `E`, an operator `A` and `B = A A†`:

* `re_inner_pow_eq_sum`: `re ⟪v, Tᵏ v⟫ = ∑ λᵢᵏ ‖cᵢ‖²` in an eigenbasis of a symmetric `T`;
* `re_inner_le_pow` (spectral Hölder): `re ⟪f, B f⟫ ≤ ‖f‖^{2(1-1/R)} (re ⟪f, Bᴿ f⟫)^{1/R}`
  for a positive symmetric `B`;
* `norm_inner_apply_le_moment`: `‖⟪f, A g⟫‖ ≤ ‖g‖ ‖f‖^{1-1/R} (re ⟪f, (A A†)ᴿ f⟫)^{1/(2R)}`;
* `re_inner_sum_le_trace` (largest eigenvalue ≤ trace): for `f = ∑ cₚ uₚ` and a positive `C`,
  `re ⟪f, C f⟫ ≤ (∑ |cₚ|²) (∑ re ⟪uₚ, C uₚ⟫)`;
* `norm_sum_inner_le_moment` (the localized Hölder step): for blocks `j`,
  `‖∑ⱼ ⟪fⱼ, A gⱼ⟫‖ ≤ (∑ ‖gⱼ‖²)^{1/2} (∑ ‖fⱼ‖²)^{(1-1/R)/2} (∑ⱼ re ⟪fⱼ, (A A†)ᴿ fⱼ⟫)^{1/(2R)}`.

These are exactly the inequalities used between (3.19) and (3.20) of [21]; the concrete inputs
(the slope-interval partition with `O(H)` primitive positions per interval, and the norm bounds
(3.18)) are separate. -/

namespace ArtinPrimitiveRoots.L102D

open RCLike Finset
open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the localized spectral Hölder step of (3.20) for matrices

For a matrix `A` on a finite index set of states with positions `pos : ι → P`, a vector `f`
constant on positions, and a block index `blk : P → ℤ` such that `A` only connects blocks at
distance `≤ W` and each block has `≤ κ` positions,
`|⟨f, A f⟩| ≤ ((2W+1)‖f‖²)^{1/2} (‖f‖²)^{(1-1/R)/2} (κ F² M)^{1/(2R)}`,
`M = ∑_P ⟨u_P, (AA*)^R u_P⟩`, `F = sup |f|`. -/

namespace ArtinPrimitiveRoots.L102D

open Finset Matrix WithLp
open scoped InnerProductSpace ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end ArtinPrimitiveRoots.L102D
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinBV

open Finset

end ArtinBV
end

section
/-! # L102D: the exact outer reduction of (10.9) ([21] §3.1, (3.10)–(3.11))

`Q_Y − Q_Y^maj = Q^sh − Q^{maj,sh} + Q^min`, where `Q^sh`, `Q^{maj,sh}` are the parts of the two
squares over label pairs whose products `a, b` are not coprime, and `Q^min` is the coprime part
of the minor-arc square, with kernel `ψ(t/Y) ∫_{[0,1) ∖ 𝔐} e(θ(t − b + a)) dθ`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary inputs -/

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
/-! # L102D: good positions and their measure ([21] §3.2, Lemma 3.2)

For lists `ℓ` of `M` primes in each group, the omission products `D` (omit one label per group),
the two good-state tests on a ratio `r ∈ ℝ/ℤ` (realized on `(0, 1]`), and Lemma 3.2: the set of
`r` failing goodness has measure at most `exp(-c L^{0.1})`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Distance to the nearest integer and its level sets -/

/-! ## Test (i): the union bound -/

/-! ## Markov's inequality for a finite weighted family of bad sets -/

/-! ## Test (ii): one fresh draw, then Markov over the fresh draws -/

lemma pos_of_mem_primeGroup {x b : ℝ} {p : ℕ} (h : p ∈ primeGroup x b) : 0 < p := by
  unfold primeGroup at h
  exact (Finset.mem_filter.1 h).2.1.pos

/-! ## Counting and asymptotics -/

/-- `L^b ≤ ε L^c` eventually, for `b < c` and `ε > 0`. -/
lemma eventually_rpow_le_rpow {b c : ℝ} (hbc : b < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, L ^ b ≤ ε * L ^ c := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.2 hbc)).eventually (ge_mem_nhds hε)
  filter_upwards [h, Filter.eventually_gt_atTop 0] with L hL hL0
  have : L ^ b = L ^ (-(c - b)) * L ^ c := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hL (by positivity)

/-! ## Lemma 3.2 -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the divisor input (3.9) of [21] §3.1

`∑_{h ≤ Z} τ(1 + l h)² ≤ 4 (Z + T)(1 + log T)³` whenever every `m` with `m⁴ ≤ (1 + lZ)³` is
`≤ T`. The proof replaces `τ(n)² = #{(d₁, d₂) : d₁, d₂ ∣ n}` by four times the number of divisor
pairs with `lcm⁴ ≤ n³` (one of `(d₁,d₂)`, `(n/d₁,n/d₂)`, `(d₁,n/d₂)`, `(n/d₁,d₂)` qualifies), and
then counts `h` in one residue class modulo the `lcm`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the shared-label parts are negligible ([21] §3.1 (3.9), §4.9 (4.61), (4.63))

Bounds for the inner sums `rawInner`, `majInner` at one pair of label products, for the measure of
the major arcs, and for the normalized mass of label pairs with a common prime. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary facts about the cutoffs and coefficients -/

lemma dyadicBump_nonneg (u : ℝ) : 0 ≤ dyadicBump u := by
  unfold dyadicBump
  rcases le_or_gt u 0 with hu | hu
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]; simp
  · exact sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

lemma dyadicBump_le_one (u : ℝ) : dyadicBump u ≤ 1 := by
  unfold dyadicBump
  linarith [Real.smoothTransition.le_one (u - 1), Real.smoothTransition.nonneg (u / 2 - 1)]

lemma abs_dyadicBump_le_one (u : ℝ) : |dyadicBump u| ≤ 1 := by
  rw [abs_of_nonneg (dyadicBump_nonneg u)]; exact dyadicBump_le_one u

/-! ## The measure of the major arcs -/

/-! ## The raw inner sum at one pair of label products -/

/-! ## The major inner sum at one pair of label products -/

/-! ## The mass of label pairs with a common prime -/

/-- The harmonic weight `∏ᵢ 1/(pᵢ Vᵢ)` of a label tuple. -/
noncomputable def labelWeight (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (p : Fin K → ℕ) : ℝ :=
  ∏ i, 1 / ((p i : ℝ) * groupReciprocalSum x (a i))

lemma groupReciprocalSum_nonneg (x b : ℝ) : 0 ≤ groupReciprocalSum x b :=
  sum_nonneg fun p _ => by positivity

lemma labelWeight_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (p : Fin K → ℕ) :
    0 ≤ labelWeight x a p :=
  prod_nonneg fun i _ => by have := groupReciprocalSum_nonneg x (a i); positivity

lemma sum_inv_mul_groupReciprocalSum_le (x b : ℝ) :
    ∑ q ∈ primeGroup x b, 1 / ((q : ℝ) * groupReciprocalSum x b) ≤ 1 := by
  have hV : groupReciprocalSum x b = ∑ q ∈ primeGroup x b, 1 / (q : ℝ) := rfl
  rw [show ∑ q ∈ primeGroup x b, 1 / ((q : ℝ) * groupReciprocalSum x b) =
      (∑ q ∈ primeGroup x b, 1 / (q : ℝ)) / groupReciprocalSum x b by
    rw [sum_div]; exact sum_congr rfl fun q _ => by rw [div_div], ← hV]
  exact div_self_le_one _

lemma sum_labelWeight_le_one (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    ∑ p ∈ labelTuples x a, labelWeight x a p ≤ 1 := by
  unfold labelTuples labelWeight
  rw [← Finset.prod_univ_sum (fun i => primeGroup x (a i))
    (fun i (q : ℕ) => 1 / ((q : ℝ) * groupReciprocalSum x (a i)))]
  refine prod_le_one (fun i _ => sum_nonneg fun q _ => ?_) fun i _ =>
    sum_inv_mul_groupReciprocalSum_le x (a i)
  have := groupReciprocalSum_nonneg x (a i); positivity

/-- The `j`-marginal of the harmonic weight: `∑_{p : p_j = q} w(p) ≤ 1/(q V_j)`. -/
lemma sum_labelWeight_eq_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (j : Fin K) (q : ℕ) :
    ∑ p ∈ labelTuples x a, labelWeight x a p * (if p j = q then 1 else 0) ≤
      1 / ((q : ℝ) * groupReciprocalSum x (a j)) := by
  classical
  set g : (i : Fin K) → ℕ → ℝ := fun i y =>
    1 / ((y : ℝ) * groupReciprocalSum x (a i)) * (if i = j then (if y = q then 1 else 0) else 1)
  have hrw : ∀ p : Fin K → ℕ, labelWeight x a p * (if p j = q then 1 else 0) = ∏ i, g i (p i) := by
    intro p
    simp only [g, labelWeight, prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' univ j (fun i => if p i = q then (1 : ℝ) else 0)]
    simp
  simp only [hrw]
  unfold labelTuples
  rw [← Finset.prod_univ_sum (fun i => primeGroup x (a i)) g]
  have hV := fun i => groupReciprocalSum_nonneg x (a i)
  calc ∏ i, ∑ y ∈ primeGroup x (a i), g i y
      ≤ ∏ i, (if i = j then 1 / ((q : ℝ) * groupReciprocalSum x (a j)) else 1) := by
        refine prod_le_prod (fun i _ => sum_nonneg fun y _ => ?_) fun i _ => ?_
        · simp only [g]; have := hV i; split_ifs <;> positivity
        · by_cases hij : i = j
          · subst hij
            simp only [g, if_true]
            calc ∑ y ∈ primeGroup x (a i), 1 / ((y : ℝ) * groupReciprocalSum x (a i)) *
                  (if y = q then 1 else 0)
                ≤ ∑ y ∈ primeGroup x (a i), (if y = q then
                    1 / ((q : ℝ) * groupReciprocalSum x (a i)) else 0) :=
                  sum_le_sum fun y _ => by split_ifs with h <;> simp [h]
              _ ≤ 1 / ((q : ℝ) * groupReciprocalSum x (a i)) := by
                  rw [sum_ite_eq']; split_ifs <;> [rfl; (have := hV i; positivity)]
          · simp only [g, hij, if_false, mul_one]
            exact sum_inv_mul_groupReciprocalSum_le x (a i)
    _ = _ := by rw [Finset.prod_ite_eq']; simp

/-- Label products with a common prime share a label. -/
lemma exists_eq_of_not_coprime {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p p' : Fin K → ℕ}
    (hp : p ∈ labelTuples x a) (hp' : p' ∈ labelTuples x a)
    (h : ¬ Nat.Coprime (∏ i, p i) (∏ i, p' i)) : ∃ i j, p i = p' j := by
  obtain ⟨q, hq, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.1 h
  have hpr : ∀ (r : Fin K → ℕ), r ∈ labelTuples x a → ∀ i, (r i).Prime := by
    intro r hr i
    have := (Fintype.mem_piFinset.1 hr) i
    unfold primeGroup at this
    exact (mem_filter.1 this).2.1
  obtain ⟨i, -, hi⟩ := (Nat.prime_iff.1 hq).dvd_finsetProd_iff _ |>.1 h1
  obtain ⟨j, -, hj⟩ := (Nat.prime_iff.1 hq).dvd_finsetProd_iff _ |>.1 h2
  exact ⟨i, j, ((Nat.prime_dvd_prime_iff_eq hq (hpr p hp i)).1 hi).symm.trans
    ((Nat.prime_dvd_prime_iff_eq hq (hpr p' hp' j)).1 hj)⟩

lemma abs_dyadicBump_le_div (u : ℕ) (Y : ℝ) (hY : 0 < Y) (hu : 0 < u) :
    |dyadicBump (u / Y)| ≤ 4 * Y / u := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  by_cases h : dyadicBump (u / Y) = 0
  · rw [h, abs_zero]; positivity
  · have := (dyadicBump_ne_zero h).2
    rw [div_lt_iff₀ hY] at this
    rw [le_div_iff₀ hu']
    have := mul_le_of_le_one_left hu'.le (abs_dyadicBump_le_one (u / Y))
    linarith

/-- **The shared-label mass.** If all `Vⱼ ≥ 1/2` and all group primes are `≥ P`, then
`∏Vᵢ⁻² ∑_{(a,b) > 1} |η(a/Y) η(b/Y)| ≤ 32 K² Y²/P`. -/
lemma shared_mass_le (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y P : ℝ) (hY : 0 < Y) (hP : 0 < P)
    (hV : ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j))
    (hPp : ∀ i, ∀ q ∈ primeGroup x (a i), P ≤ q) :
    ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
      (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else
        squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)|) ≤
      32 * K ^ 2 * Y ^ 2 / P := by
  classical
  have hVpos : ∀ j, 0 < groupReciprocalSum x (a j) := fun j => by linarith [hV j]
  have hpos : ∀ r ∈ labelTuples x a, ∀ i, 0 < r i := by
    intro r hr i
    exact pos_of_mem_primeGroup ((Fintype.mem_piFinset.1 hr) i)
  -- pointwise: `sqN |η η| ≤ 16 Y² w(p) w(p')`
  have hpt : ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a,
      squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)| ≤
        16 * Y ^ 2 * (labelWeight x a p * labelWeight x a p') := by
    intro p hp p' hp'
    have ha : 0 < ∏ i, p i := prod_pos fun i _ => hpos p hp i
    have hb : 0 < ∏ i, p' i := prod_pos fun i _ => hpos p' hp' i
    have h1 := abs_dyadicBump_le_div _ Y hY ha
    have h2 := abs_dyadicBump_le_div _ Y hY hb
    have hsq : 0 ≤ squareNorm x a := prod_nonneg fun i _ => by positivity
    rw [abs_mul]
    calc squareNorm x a * (|dyadicBump ((∏ i, p i : ℕ) / Y)| *
          |dyadicBump ((∏ i, p' i : ℕ) / Y)|)
        ≤ squareNorm x a * ((4 * Y / (∏ i, p i : ℕ)) * (4 * Y / (∏ i, p' i : ℕ))) := by
          gcongr
      _ = 16 * Y ^ 2 * (labelWeight x a p * labelWeight x a p') := by
          have hpi : ∀ i, (p i : ℝ) ≠ 0 := fun i => by exact_mod_cast (hpos p hp i).ne'
          have hpi' : ∀ i, (p' i : ℝ) ≠ 0 := fun i => by exact_mod_cast (hpos p' hp' i).ne'
          have hVi : ∀ i, groupReciprocalSum x (a i) ≠ 0 := fun i => (hVpos i).ne'
          have hPi : (∏ i, (p i : ℝ)) ≠ 0 := prod_ne_zero_iff.2 fun i _ => hpi i
          have hPi' : (∏ i, (p' i : ℝ)) ≠ 0 := prod_ne_zero_iff.2 fun i _ => hpi' i
          have h_aux : ∏ i, (groupReciprocalSum x (a i))⁻¹ ^ 2 =
              labelWeight x a p * labelWeight x a p' * ((∏ i, (p i : ℝ)) * ∏ i, (p' i : ℝ)) := by
            unfold labelWeight
            rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
            refine prod_congr rfl fun i _ => ?_
            have := hpi i; have := hpi' i; have := hVi i
            field_simp
          unfold squareNorm
          push_cast
          rw [h_aux]
          field_simp
          ring
  -- `[¬cop] ≤ ∑_{i,j} [p i = p' j]`
  have hind : ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a,
      (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then (0 : ℝ) else 1) ≤
        ∑ i, ∑ j, (if p' j = p i then (1 : ℝ) else 0) := by
    intro p hp p' hp'
    split_ifs with hc
    · exact sum_nonneg fun i _ => sum_nonneg fun j _ => by split_ifs <;> norm_num
    · obtain ⟨i, j, hij⟩ := exists_eq_of_not_coprime hp hp' hc
      calc (1 : ℝ) = if p' j = p i then 1 else 0 := by rw [if_pos hij.symm]
        _ ≤ ∑ j', (if p' j' = p i then (1 : ℝ) else 0) :=
            single_le_sum (f := fun j' => if p' j' = p i then (1 : ℝ) else 0)
              (fun j' _ => by split_ifs <;> norm_num) (mem_univ j)
        _ ≤ ∑ i', ∑ j', (if p' j' = p i' then (1 : ℝ) else 0) :=
            single_le_sum (f := fun i' => ∑ j', (if p' j' = p i' then (1 : ℝ) else 0))
              (fun i' _ => sum_nonneg fun j' _ => by split_ifs <;> norm_num) (mem_univ i)
  have hstep : ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a,
      (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else
        squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)|) ≤
      16 * Y ^ 2 * (labelWeight x a p * ∑ i, ∑ j,
        (labelWeight x a p' * if p' j = p i then (1 : ℝ) else 0)) := by
    intro p hp p' hp'
    have hw := labelWeight_nonneg x a p
    have hw' := labelWeight_nonneg x a p'
    have e : (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else
        squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)|) =
        (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then (0 : ℝ) else 1) *
        (squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)|) := by
      split_ifs <;> simp
    rw [e]
    have hsq : 0 ≤ squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) *
        dyadicBump ((∏ i, p' i : ℕ) / Y)| :=
      mul_nonneg (prod_nonneg fun i _ => by positivity) (abs_nonneg _)
    have hind0 : (0 : ℝ) ≤ if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else 1 := by
      split_ifs <;> norm_num
    calc _ ≤ (∑ i, ∑ j, (if p' j = p i then (1 : ℝ) else 0)) *
          (16 * Y ^ 2 * (labelWeight x a p * labelWeight x a p')) :=
          mul_le_mul (hind p hp p' hp') (hpt p hp p' hp') hsq
            (sum_nonneg fun i _ => sum_nonneg fun j _ => by split_ifs <;> norm_num)
      _ = _ := by simp only [sum_mul, mul_sum]; refine sum_congr rfl fun i _ =>
            sum_congr rfl fun j _ => by ring
  refine (sum_le_sum fun p hp => sum_le_sum fun p' hp' => hstep p hp p' hp').trans ?_
  -- sum over `p'` with the marginal bound, then over `p`
  have hmarg : ∀ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a, 16 * Y ^ 2 *
      (labelWeight x a p * ∑ i, ∑ j, (labelWeight x a p' * if p' j = p i then (1 : ℝ) else 0)) ≤
      16 * Y ^ 2 * (labelWeight x a p * (K ^ 2 * (2 / P))) := by
    intro p hp
    rw [← mul_sum, ← mul_sum]
    gcongr
    · exact labelWeight_nonneg x a p
    rw [sum_comm]
    calc ∑ i, ∑ p' ∈ labelTuples x a, ∑ j, (labelWeight x a p' * if p' j = p i then (1 : ℝ) else 0)
        = ∑ i, ∑ j, ∑ p' ∈ labelTuples x a,
            (labelWeight x a p' * if p' j = p i then (1 : ℝ) else 0) :=
          sum_congr rfl fun i _ => sum_comm
      _ ≤ ∑ _i : Fin K, ∑ _j : Fin K, 2 / P := by
          refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
          refine (sum_labelWeight_eq_le x a j (p i)).trans ?_
          have hq : P ≤ (p i : ℝ) := hPp i _ ((Fintype.mem_piFinset.1 hp) i)
          have hVj := hV j
          have hpi0 : (0 : ℝ) < p i := by exact_mod_cast hpos p hp i
          rw [div_le_div_iff₀ (mul_pos hpi0 (hVpos j)) hP]
          nlinarith
      _ = K ^ 2 * (2 / P) := by
          rw [sum_const, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
          ring
  refine (sum_le_sum hmarg).trans ?_
  rw [← mul_sum, ← sum_mul]
  have hsum := sum_labelWeight_le_one x a
  have h0 : (0 : ℝ) ≤ K ^ 2 * (2 / P) := by positivity
  calc 16 * Y ^ 2 * ((∑ p ∈ labelTuples x a, labelWeight x a p) * (K ^ 2 * (2 / P)))
      ≤ 16 * Y ^ 2 * (1 * (K ^ 2 * (2 / P))) := by gcongr
    _ = 32 * K ^ 2 * Y ^ 2 / P := by ring

/-! ## Inputs about the groups for large `x` -/

lemma le_of_mem_primeGroup {x b : ℝ} {q : ℕ} (h : q ∈ primeGroup x b) :
    exp (log x ^ b) ≤ q ∧ (q : ℝ) ≤ exp (2 * log x ^ b) := by
  unfold primeGroup at h
  simp only [mem_filter, mem_range] at h
  refine ⟨h.2.2, ?_⟩
  have := Nat.lt_succ_iff.1 h.1
  exact (Nat.cast_le.2 this).trans (Nat.floor_le (exp_pos _).le)

/-! ## Numerics -/


/-! ## D1b: the shared-label bound -/

/-- Common setting: the hypotheses used by both halves of D1b, at one `x`. -/
structure SharedSetting (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (C : ℝ) :
    Prop where
  hL1 : 1 ≤ log x
  hx : 0 < x
  hHm : 0 < Hm
  hHn : 0 < Hn
  hY : 1 ≤ Y
  hX1 : 1 ≤ Hm * Hn
  hα0 : α 0 = 0
  hβ0 : β 0 = 0
  hαb : ∀ m, ‖α m‖ ≤ log x ^ C
  hβb : ∀ n, ‖β n‖ ≤ log x ^ C
  hV : ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j)
  hab : ∀ i, (0.1 : ℝ) < a i
  hlog : 1 + log (17 * (Hm * Hn)) ≤ 2 * log x

lemma SharedSetting.mass {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {Y Hm Hn : ℝ} {α β : ℕ → ℂ} {C : ℝ}
    (S : SharedSetting x a Y Hm Hn α β C) :
    ∑ p ∈ labelTuples x a, ∑ p' ∈ labelTuples x a,
      (if Nat.Coprime (∏ i, p i) (∏ i, p' i) then 0 else
        squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)|) ≤
      32 * K ^ 2 * Y ^ 2 / exp (log x ^ (0.1 : ℝ)) := by
  refine shared_mass_le x a Y _ (by linarith [S.hY]) (exp_pos _) S.hV fun i q hq => ?_
  refine le_trans (exp_le_exp.2 ?_) (le_of_mem_primeGroup hq).1
  exact Real.rpow_le_rpow_of_exponent_le S.hL1 (S.hab i).le


end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D5, the pairing from the moment ([21] §3.3, (3.20)), for the operator model

The concrete inputs to `norm_qform_le_blocks`: `A` only connects slope blocks at distance `≤ 12`,
a slope block of length `H/U²` holds `≤ 17(512H + 1)` primitive positions, `f` depends only on the
position, `|f| ≤ L^{2C}`, and `σ ∑ |f|² ≤ 32 U V L^{4C}` ((3.18)). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

section Geometry

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ}

end Geometry

/-! ## Slope blocks -/

/-! ## The endpoint norm (3.18) -/

section Norm

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

end Norm


/-! ## D5 at one `x` -/


/-! ## Large-`x` inputs and D5 -/

/-- For large `x` the prime groups are pairwise disjoint. -/
lemma eventually_disjoint_groups {K : ℕ} (a : Fin K → ℝ) (ha : StrictMono a)
    (_hpos : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
  have hL : ∀ᶠ L : ℝ in Filter.atTop, ∀ i j : Fin K, a i < a j → 2 * L ^ a i < L ^ a j := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : a i < a j
    · filter_upwards [eventually_rpow_le_rpow hij (ε := 1 / 3) (by norm_num),
        Filter.eventually_gt_atTop 0] with L h1 h2 _
      have : 0 < L ^ a j := by positivity
      linarith
    · exact Filter.Eventually.of_forall fun L h => absurd h hij
  filter_upwards [Real.tendsto_log_atTop.eventually hL] with x hx
  intro i j hij
  have key : ∀ i j : Fin K, a i < a j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
    intro i j h
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    have h1 := (le_of_mem_primeGroup hp).2
    have h2 := (le_of_mem_primeGroup hp').1
    have := exp_lt_exp.2 (hx i j h)
    linarith
  rcases lt_or_gt_of_ne (ha.injective.ne hij) with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- For large `x` every group is nonempty (Bertrand), so every `Vᵢ > 0`. -/
lemma eventually_groupReciprocalSum_pos {K : ℕ} (a : Fin K → ℝ) (hpos : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i, 0 < groupReciprocalSum x (a i) := by
  refine Filter.eventually_all.2 fun i => ?_
  have hy : Filter.Tendsto (fun x : ℝ => log x ^ a i) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (hpos i)).comp tendsto_log_atTop
  filter_upwards [hy.eventually_ge_atTop 2] with x hx
  set y := exp (log x ^ a i)
  have hy3 : 3 ≤ y := by
    have : exp 2 ≤ y := exp_le_exp.2 hx
    linarith [Real.exp_one_gt_d9, Real.add_one_le_exp (1 : ℝ), show exp 2 = exp 1 * exp 1 by
      rw [← exp_add]; norm_num, show (2.7182818283 : ℝ) * 2.7182818283 ≥ 3 by norm_num,
      mul_le_mul (le_of_lt Real.exp_one_gt_d9) (le_of_lt Real.exp_one_gt_d9) (by norm_num)
        (exp_pos 1).le]
  set n := ⌈y⌉₊
  have hn0 : n ≠ 0 := by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith
  obtain ⟨p, hp, hnp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul n hn0
  have hmem : p ∈ primeGroup x (a i) := by
    unfold primeGroup
    refine mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor ?_)), hp, ?_⟩
    · have h1 : (n : ℝ) < y + 1 := Nat.ceil_lt_add_one (by linarith)
      have h2 : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2
      have h3 : exp (2 * log x ^ a i) = y * y := by rw [← exp_add]; ring_nf
      rw [h3]; nlinarith
    · have : (n : ℝ) < p := by exact_mod_cast hnp
      linarith [Nat.le_ceil y]
  have : 0 < (1 : ℝ) / p := by have := hp.pos; positivity
  exact lt_of_lt_of_le this (single_le_sum (f := fun q : ℕ => (1 : ℝ) / q)
    (fun q _ => by positivity) hmem)

end ArtinPrimitiveRoots.L102D
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

lemma bprime_mem (P : MemParams) {p : ℕ} (hp : P.N < p) : 0 < P.bprime p ∧ P.bprime p ≤ 1 := by
  have hs : ∑ j ∈ range (P.N + 1), P.etav j ≤ P.N + 1 := by
    calc ∑ j ∈ range (P.N + 1), P.etav j ≤ ∑ _j ∈ range (P.N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => (etav_mem P j).2
      _ = P.N + 1 := by simp
  have hs0 : 0 ≤ ∑ j ∈ range (P.N + 1), P.etav j := sum_nonneg fun j _ => (etav_mem P j).1
  have hp' : (P.N : ℝ) + 1 < p + 1 := by
    have : (P.N : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold MemParams.bprime
  constructor
  · rw [sub_pos, div_lt_one (by positivity)]
    linarith
  · have := div_nonneg hs0 (by positivity : (0 : ℝ) ≤ (p : ℝ) + 1)
    linarith

lemma abs_baseline_le (P : MemParams) (h : ∀ p ∈ P.gPrimes, P.N < p) : |P.baseline| ≤ 1 := by
  unfold MemParams.baseline
  rw [abs_of_nonneg (prod_nonneg fun p hp => (bprime_mem P (h p hp)).1.le)]
  exact prod_le_one (fun p hp => (bprime_mem P (h p hp)).1.le) fun p hp => (bprime_mem P (h p hp)).2

/-- `y⁵ + 2 ≤ exp y` for `y ≥ 722` (from `y⁶/6! ≤ exp y`). -/
lemma pow_five_add_two_le_exp {y : ℝ} (hy : 722 ≤ y) : y ^ 5 + 2 ≤ exp y := by
  have h6 := Real.pow_div_factorial_le_exp y (show 0 ≤ y by linarith) 6
  have hf : ((6 : ℕ).factorial : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hf] at h6
  have hy5 : (720 : ℝ) ≤ y ^ 5 := by
    calc (720 : ℝ) ≤ 722 ^ 5 := by norm_num
      _ ≤ y ^ 5 := by gcongr
  have : y ^ 5 + 2 ≤ y ^ 6 / 720 := by
    have e : y ^ 6 / 720 = y * y ^ 5 / 720 := by ring
    rw [e, le_div_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- Eventually every group prime exceeds the path length `N = 2R`. -/
lemma eventually_pathLength_lt {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, (0.1 : ℝ) < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ p ∈ groupPrimes x a, 2 * momentPower x < p := by
  have hL : Filter.Tendsto (fun x : ℝ => log x ^ (0.1 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  filter_upwards [hL.eventually_ge_atTop 722, Filter.eventually_ge_atTop (exp 1)] with x hx hx1
  intro p hp
  have hlog : 1 ≤ log x := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) hx1
  simp only [groupPrimes, mem_biUnion, mem_univ, true_and] at hp
  obtain ⟨i, hi⟩ := hp
  simp only [primeGroup, mem_filter] at hi
  have hpge : exp (log x ^ a i) ≤ p := hi.2.2
  have h1 : log x ^ (0.1 : ℝ) ≤ log x ^ a i := rpow_le_rpow_of_exponent_le hlog (ha i).le
  have h5 : (log x ^ (0.1 : ℝ)) ^ 5 = log x ^ (0.5 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul (by linarith)]; norm_num
  have hmp : (2 * momentPower x : ℝ) < log x ^ (0.5 : ℝ) + 2 := by
    unfold momentPower
    have := Nat.ceil_lt_add_one (show 0 ≤ log x ^ (0.5 : ℝ) / 2 by positivity)
    linarith
  have hexp := pow_five_add_two_le_exp hx
  rw [h5] at hexp
  have : (2 * momentPower x : ℝ) < p := by
    calc (2 * momentPower x : ℝ) < log x ^ (0.5 : ℝ) + 2 := hmp
      _ ≤ exp (log x ^ (0.1 : ℝ)) := hexp
      _ ≤ exp (log x ^ a i) := exp_le_exp.2 h1
      _ ≤ p := hpge
  exact_mod_cast this

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D7 (`MomentBoundStmt`) from its seven cuts

`moment_bound_of_cuts`: the moment (4.1) from D7p (path expansion), D7r (root replacement),
D7a (memory identity), D7b (truncation), D7c (ghosts), D7d (edges), D7e (distinctness).
Choice of constants: `G = E₀ + 3` in D7d/D7e (so `G − 1 = E₀ + 2`), `A = E₀ + 2` in D7b/D7r;
the root integral has mass `15`, `UV/ζ(2) = 6UV/π² ≤ UV`, and `L^{-2N} ≤ 1/36` absorbs the
constant `1 + 2 · 15 ≤ 32`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- The interval-integral mass bound over the normalized roots. -/
lemma norm_root_integral_le (F : ℝ × ℝ × ℝ → ℂ) (U V M : ℝ)
    (hF : ∀ u ∈ Set.Icc (1 : ℝ) 16, ∀ v ∈ Set.Icc (1 : ℝ) 2, ∀ r ∈ Set.Icc (0 : ℝ) 1,
      ‖F (U * u, V * v, r)‖ ≤ M) :
    ‖∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, F (U * u, V * v, r)‖ ≤ 15 * M := by
  have hM : ∀ u ∈ Set.Icc (1 : ℝ) 16, ∀ v ∈ Set.Icc (1 : ℝ) 2,
      ‖∫ r in (0 : ℝ)..1, F (U * u, V * v, r)‖ ≤ M := by
    intro u hu v hv
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun r => F (U * u, V * v, r)) (C := M) fun r hr => by
        rw [Set.uIoc_of_le (by norm_num)] at hr
        exact hF u hu v hv r ⟨hr.1.le, hr.2⟩
    simpa using this
  have hM2 : ∀ u ∈ Set.Icc (1 : ℝ) 16,
      ‖∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, F (U * u, V * v, r)‖ ≤ M := by
    intro u hu
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := 2)
      (f := fun v => ∫ r in (0 : ℝ)..1, F (U * u, V * v, r)) (C := M) fun v hv => by
        rw [Set.uIoc_of_le (by norm_num)] at hv
        exact hM u hu v ⟨hv.1.le, hv.2⟩
    norm_num at this
    simpa using this
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1) (b := 16)
    (f := fun u => ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, F (U * u, V * v, r)) (C := M)
    fun u hu => by
      rw [Set.uIoc_of_le (by norm_num)] at hu
      exact hM2 u ⟨hu.1.le, hu.2⟩
  have e : |(16 : ℝ) - 1| = 15 := by norm_num
  rw [e] at this
  linarith

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: statement forms proposed for publication (round 4b)

`DistinctnessStmtNG`: D7e without the ghost hypothesis of `DistinctnessStmt` (its proof does not use
it). With it, D7 needs no ghost cut (`moment_bound_of_pub_cuts`, `L102D_PubMain`). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-- D7e without the ghost hypothesis (which the proof does not use): the form proposed for
publication. -/
def DistinctnessStmtNG (δ c₁ c₂ : ℝ) : Prop :=
  ∀ G : ℝ, 0 < G → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    (∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
        let P := dyadParams x a A₀ Y Hm Hn k
        ∀ ω, P.RootIn ω → ∀ j < P.N, P.OpBound (P.edgeOp ω j) (log x ^ (-G))) →
    ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
        let P := dyadParams x a A₀ Y Hm Hn k
        ∀ ω, P.RootIn ω → ‖P.memMomentD ω‖ ≤ log x ^ (-((G - 1) * P.N))

/-- D7a as published (`rootIL_eq_baseline_mul_memMomentD`, with F's hypothesis `1 ≤ N`). -/
def MemoryIdentityStmtN : Prop :=
  ∀ (P : MemParams) (ω : ℝ × ℝ × ℝ),
    (∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) →
    (∀ p ∈ P.gPrimes, P.bprime p ≠ 0) → (∀ i, P.Vg i ≠ 0) → 1 ≤ P.N →
    P.rootIL ω = (P.baseline : ℂ) * (P.withB P.gPrimes.card).memMomentD ω

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D7 from the cuts proposed for publication (round 4b)

A copy of prover F's `moment_bound_of_cuts'` (`L102F_MomentMain`, itself D's `moment_bound_of_cuts`
with D7a corrected to `1 ≤ N`) taking D7e as `DistinctnessStmtNG`, so the ghost bound D7c is no
longer a cut of D7 (it enters D7e's proof directly). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- **D7 from the cuts proposed for publication**: D7a with `1 ≤ N` (F), D7e without the ghost
hypothesis, no ghost cut. -/
theorem moment_bound_of_pub_cuts (δ c₁ c₂ : ℝ) (hδ : 0 < δ)
    (hp : PathExpansionStmt) (hr : RootReplacementStmt δ c₁ c₂) (ha : MemoryIdentityStmtN)
    (hb : TruncationStmt δ c₁ c₂) (hd : EdgeBoundStmt δ c₁ c₂)
    (he : DistinctnessStmtNG δ c₁ c₂) : MomentBoundStmt δ c₁ c₂ := by
  intro E₀ hE₀
  obtain ⟨A₀, hA₀, K₀, hK⟩ := hd (E₀ + 3) (by linarith)
  refine ⟨A₀, hA₀, K₀, fun K hK1 hKK a hmono hband => ?_⟩
  have hpos : ∀ i, 0 < a i := fun i => by linarith [(hband i).1]
  obtain ⟨x₁, h1⟩ := he (E₀ + 3) (by linarith) A₀ hA₀ K hK1 a hmono hband
    (hK K hK1 hKK a hmono hband)
  obtain ⟨x₂, h2⟩ := hb (E₀ + 2) (by linarith) A₀ hA₀ K hK1 a hmono hband
  obtain ⟨x₃, h3⟩ := hr (E₀ + 2) (by linarith) A₀ hA₀ K hK1 a hmono hband
  obtain ⟨x₄, h4⟩ := Filter.eventually_atTop.1 ((eventually_disjoint_groups a hmono hpos).and
    ((eventually_groupReciprocalSum_pos a hpos).and
      ((eventually_pathLength_lt a fun i => (hband i).1).and
        (Filter.eventually_ge_atTop (exp 6)))))
  refine ⟨max (max x₁ x₂) (max x₃ x₄), fun x Hm Hn hx hHm hHn hlo hhi Y hY k => ?_⟩
  have hx1 : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : x₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : x₄ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hdisj, hVpos, hNlt, hx5⟩ := h4 x hx4
  set P := dyadParams x a A₀ Y Hm Hn k with hPdef
  have hlog5 : 6 ≤ log x := by
    rw [← log_exp 6]; exact log_le_log (exp_pos 6) hx5
  have hxone : 1 ≤ x := le_trans (by linarith [add_one_le_exp (6 : ℝ)]) hx5
  have hδx : 1 ≤ x ^ δ := one_le_rpow hxone hδ.le
  have hHm1 : 1 ≤ Hm := le_trans hδx hHm
  have hHn1 : 1 ≤ Hn := le_trans hδx hHn
  have hU : 1 ≤ P.U := by
    show 1 ≤ 2 ^ k * Y * Hm
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have : 1 ≤ 2 ^ k * Y := by nlinarith
    nlinarith
  have hV : 1 ≤ P.V := hHn1
  have hR : 1 ≤ momentPower x := by
    unfold momentPower
    rw [Nat.one_le_ceil_iff]
    have : 0 < log x := by linarith
    positivity
  have hN1 : (1 : ℝ) ≤ P.N := by
    show (1 : ℝ) ≤ ((2 * momentPower x : ℕ) : ℝ)
    have : (1 : ℝ) ≤ momentPower x := by exact_mod_cast hR
    push_cast; linarith
  -- the independent-line moment is small at every root
  have hgp : ∀ p ∈ P.gPrimes, P.N < p := fun p hp => hNlt p hp
  have hIL : ∀ ω, P.RootIn ω → ‖P.rootIL ω‖ ≤ 2 * log x ^ (-((E₀ + 2) * P.N)) := by
    intro ω hω
    have hid := ha P ω (fun i i' h => hdisj i i' h) (fun p hp => (bprime_mem P (hgp p hp)).1.ne')
      (fun i => (hVpos i).ne') (show 1 ≤ 2 * momentPower x by omega)
    rw [hid, norm_mul]
    have hbase : ‖(P.baseline : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_baseline_le P hgp
    have htr := h2 x Hm Hn hx2 hHm hHn hlo hhi Y hY k ω hω
    have hdist := h1 x Hm Hn hx1 hHm hHn hlo hhi Y hY k ω hω
    have e : (E₀ + 3 - 1) = E₀ + 2 := by ring
    rw [e] at hdist
    have htri : ‖(P.withB P.gPrimes.card).memMomentD ω‖ ≤
        ‖(P.withB P.gPrimes.card).memMomentD ω - P.memMomentD ω‖ + ‖P.memMomentD ω‖ := by
      have := norm_add_le ((P.withB P.gPrimes.card).memMomentD ω - P.memMomentD ω)
        (P.memMomentD ω)
      simpa using this
    have hnn : 0 ≤ ‖(P.withB P.gPrimes.card).memMomentD ω‖ := norm_nonneg _
    calc ‖(P.baseline : ℂ)‖ * ‖(P.withB P.gPrimes.card).memMomentD ω‖
        ≤ 1 * ‖(P.withB P.gPrimes.card).memMomentD ω‖ :=
          mul_le_mul_of_nonneg_right hbase hnn
      _ ≤ 2 * log x ^ (-((E₀ + 2) * P.N)) := by
          rw [one_mul]; linarith
  -- the root integral
  have hint : ‖∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
      P.rootIL (P.U * u, P.V * v, r)‖ ≤ 15 * (2 * log x ^ (-((E₀ + 2) * P.N))) := by
    apply norm_root_integral_le
    intro u hu v hv r hr
    apply hIL
    refine ⟨?_, ?_, ?_, ?_, hr.1, hr.2⟩
    · nlinarith [hu.1]
    · nlinarith [hu.2]
    · nlinarith [hv.1]
    · nlinarith [hv.2]
  have hrr := h3 x Hm Hn hx3 hHm hHn hlo hhi Y hY k
  have hpe := hp x K a A₀ Y (padCount x) (momentPower x) (2 ^ k) (2 ^ k * Y * Hm) Hn
    ⌈log x ^ 2⌉₊ hdisj hR hU hV
  -- assemble
  have hπ : 6 / π ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hUV : 0 ≤ P.U * P.V := by positivity
  set E := log x ^ (-((E₀ + 2) * P.N)) with hE
  have hEnn : 0 ≤ E := by positivity
  have hmain : ‖dyadMoment x a A₀ Y Hm Hn k‖ ≤ 32 * (P.U * P.V) * E := by
    have hds : dyadMoment x a A₀ Y Hm Hn k = ∑ P₀ ∈ posBox P.U P.V,
        P.pathPhi (rootOf P₀) (physDelta P₀) := hpe
    rw [hds]
    set S := ∑ P₀ ∈ posBox P.U P.V, P.pathPhi (rootOf P₀) (physDelta P₀)
    set I := ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
      P.rootIL (P.U * u, P.V * v, r)
    have hcI : ‖((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) * I‖ ≤ (P.U * P.V) * (30 * E) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 6 / π ^ 2 * P.U * P.V)]
      have : 6 / π ^ 2 * P.U * P.V ≤ P.U * P.V := by nlinarith
      calc 6 / π ^ 2 * P.U * P.V * ‖I‖ ≤ (P.U * P.V) * (15 * (2 * E)) :=
            mul_le_mul this hint (norm_nonneg _) hUV
        _ = (P.U * P.V) * (30 * E) := by ring
    have hS : ‖S‖ ≤ ‖S - ((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) * I‖ +
        ‖((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) * I‖ := by
      have := norm_add_le (S - ((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) * I)
        (((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) * I)
      simpa using this
    have hrr' : ‖S - ((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) * I‖ ≤ P.U * P.V * E := hrr
    nlinarith
  -- `E ≤ L^{-E₀ N} / 25`
  have hLpos : 0 < log x := by linarith
  have hsplit : E = log x ^ (-(E₀ * (2 * momentPower x))) * log x ^ (-(2 * (P.N : ℝ))) := by
    rw [hE, ← rpow_add hLpos]
    congr 1
    have : (P.N : ℝ) = 2 * momentPower x := by
      show ((2 * momentPower x : ℕ) : ℝ) = _; push_cast; ring
    rw [this]; ring
  have hsmall : log x ^ (-(2 * (P.N : ℝ))) ≤ 1 / 36 := by
    have h2N : (2 : ℝ) ≤ 2 * P.N := by linarith
    have : log x ^ (2 : ℝ) ≤ log x ^ (2 * (P.N : ℝ)) :=
      rpow_le_rpow_of_exponent_le (by linarith) h2N
    have h25 : (36 : ℝ) ≤ log x ^ (2 : ℝ) := by
      rw [rpow_two]; nlinarith
    rw [rpow_neg hLpos.le, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hre : (dyadMoment x a A₀ Y Hm Hn k).re ≤ ‖dyadMoment x a A₀ Y Hm Hn k‖ :=
    Complex.re_le_norm _
  have hT : 0 ≤ log x ^ (-(E₀ * (2 * momentPower x))) := by positivity
  have hUVe : P.U * P.V = 2 ^ k * Y * Hm * Hn := rfl
  calc (dyadMoment x a A₀ Y Hm Hn k).re ≤ 32 * (P.U * P.V) * E := le_trans hre hmain
    _ = 32 * (P.U * P.V) * log x ^ (-(E₀ * (2 * momentPower x))) *
          log x ^ (-(2 * (P.N : ℝ))) := by rw [hsplit]; ring
    _ ≤ 32 * (P.U * P.V) * log x ^ (-(E₀ * (2 * momentPower x))) * (1 / 36) := by
          gcongr
    _ ≤ 2 ^ k * Y * Hm * Hn * log x ^ (-(E₀ * (2 * momentPower x))) := by
          rw [← hUVe]; nlinarith

end ArtinPrimitiveRoots.L102D
end

section
/-! Check module: `chk_re_dyadMoment_le`, the published statement `re_dyadMoment_le` verbatim, proved from the
development and the cuts `momentSum_eq_sum_pathPhi`, `norm_sum_pathPhi_sub_integral_rootIL_le_of_pos`, `rootIL_eq_baseline_mul_memMomentD`, `norm_memMomentD_sub_truncated_le`, `opBound_edgeOp`, `norm_memMomentD_le_of_opBound_edgeOp`. -/

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (δ c₁ c₂ : ℝ) (hδ : 0 < δ) :
    ∀ E₀ : ℝ, 0 < E₀ → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          (dyadMoment x a A₀ Y Hm Hn k).re ≤
            2 ^ k * Y * Hm * Hn * log x ^ (-(E₀ * (2 * momentPower x))) :=
  L102D.moment_bound_of_pub_cuts δ c₁ c₂ hδ momentSum_eq_sum_pathPhi
    (norm_sum_pathPhi_sub_integral_rootIL_le_of_pos δ c₁ c₂ hδ) rootIL_eq_baseline_mul_memMomentD
    (norm_memMomentD_sub_truncated_le δ c₁ c₂) (opBound_edgeOp δ c₁ c₂)
    (norm_memMomentD_le_of_opBound_edgeOp δ c₁ c₂)
end
