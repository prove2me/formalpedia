-- Prove2me | solution 1 for ArtinPrimitiveRoots.sum_norm_edgeCoeff_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:31:42.084978+00:00
-- url     : https://prove2.me/submissions/be504951-7fdd-452f-aa98-014071d50030

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel
import Definitions.Def_ArtinSieve
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

/-! ## The weighted inner product -/

/-! ## The slot symmetrization -/

/-! ## One piece of a choice-indexed operator -/

variable {γ : Type*}

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

/-! ## The Fock measure identity -/

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

end ArtinPrimitiveRoots.L102G
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

/-! ## Counting and asymptotics -/

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

lemma abs_arcCutoff_le (u : ℝ) : |arcCutoff u| ≤ if |u| < 5 then 1 else 0 := by
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

/-! ## The measure of the major arcs -/

/-! ## The raw inner sum at one pair of label products -/

/-! ## The major inner sum at one pair of label products -/

lemma norm_majorKernel_le (x A₀ Y : ℝ) (t a b : ℤ) :
    ‖majorKernel x A₀ Y t a b‖ ≤
      (if |(t : ℝ) / Y| < 5 then 1 else 0) * (volume (majorArcs x A₀ Y)).toReal := by
  unfold majorKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hfin : volume (majorArcs x A₀ Y) < ⊤ :=
    (measure_mono (majorArcs_subset x A₀ Y)).trans_lt (by simp)
  have hint : ‖∫ θ in majorArcs x A₀ Y,
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))‖ ≤
      1 * volume.real (majorArcs x A₀ Y) := by
    refine norm_setIntegral_le_of_norm_le_const hfin fun θ _ => ?_
    rw [Complex.norm_exp]
    simp
  rw [one_mul] at hint
  exact mul_le_mul (abs_arcCutoff_le _) hint (norm_nonneg _) (by split_ifs <;> norm_num)

/-! ## The mass of label pairs with a common prime -/

/-! ## Inputs about the groups for large `x` -/

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


end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: root coordinates of a primitive position (for D7p)

For a primitive `P₀ = (u, v)` with `u ≥ 1`: `c = (−v⁻¹ mod u)`, `d = (1 + vc)/u`, the completion
`g = (u c; v d) ∈ SL₂(ℤ)`, `g z = (u z₁ + c z₂, v z₁ + d z₂)` and its inverse. Box conditions,
divisibility, goodness and the damping count transfer between `P = g z` and `z`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-! ## Goodness is invariant under integer shifts of the ratio -/

/-! ## The ratio of `g z` -/

lemma detZ_complVec {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) : detZ z (complVec z) = 1 := by
  unfold detZ complVec; dsimp only
  have := Int.gcd_eq_gcd_ab z.1 z.2
  rw [hz] at this; push_cast at this
  linarith

/-! ## The damping count -/

end ArtinPrimitiveRoots.L102D
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

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: membership in the memory model's finite sets, in closed form

`(Finset.mem_product.1 h).2` on `h : x ∈ P.edgeChoices` (or `P.stSet`, `P.ghostChoices`) makes the
elaborator unify through the membership instances down to `Multiset.bind` of `zSet` (≈ 1 s per use,
measured). These closed-form iff lemmas avoid it. -/

namespace ArtinPrimitiveRoots.L102D

open Finset

variable (P : MemParams)

lemma mem_edgeChoices_iff' (c : Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)) :
    c ∈ P.edgeChoices ↔ c.1 ∈ (univ : Finset (Finset (Fin P.K))) ∧ c.2.1 ∈ P.zSet ∧
      c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ (univ : Finset Bool) := by
  rw [MemParams.edgeChoices, mem_product, mem_product]

lemma tg_mem_of_mem_edgeChoices {c : Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)}
    (hc : c ∈ P.edgeChoices) :
    c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ (univ : Finset Bool) :=
  ((mem_edgeChoices_iff' P c).1 hc).2.2

lemma mem_stSet_iff' (s : P.MState) :
    s ∈ P.stSet ↔ s.1 ∈ P.zSet ∧ s.2.1 ∈ listCands P.x P.a P.J ∧ s.2.2 ∈ P.memSet := by
  rw [MemParams.stSet, mem_product, mem_product]

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: crude edge rows ([21] (4.23)–(4.25)) with forced fresh labels (for D7e)

* `target_count`: at most `16` targets `z'` in the box with `det(z, z') = j₁` (`z' = h z + j₁ w`,
  `τ(z')/τ(z) ∈ [1/16, 16]`);
* `norm_edgeMult_le`: `‖edgeMult‖ ≤ 1[|t| < 5Y] (1[t = b − a] + vol 𝔐)`;
* `edge_row`: the weighted absolute row sum of an edge with any multiplier `κ` of that shape, with
  the fresh labels of the groups in `C` forced into a set `V`. Uses prover G's `coeffK`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

section Geo

variable (P : MemParams)

lemma tauR_decomp (ω : ℝ × ℝ × ℝ) {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) (z' : ℤ × ℤ) :
    tauR ω z' = (detZ z' (complVec z) : ℝ) * tauR ω z + (detZ z z' : ℝ) * tauR ω (complVec z) := by
  have hdet := detZ_complVec hz
  unfold detZ at hdet ⊢
  unfold tauR
  have h1 : (z'.1 : ℝ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1 : ℤ) * z.1 +
      (z.1 * z'.2 - z.2 * z'.1 : ℤ) * (complVec z).1 := by
    have : (z'.1 : ℤ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1) * z.1 +
        (z.1 * z'.2 - z.2 * z'.1) * (complVec z).1 := by linear_combination (-z'.1) * hdet
    exact_mod_cast this
  have h2 : (z'.2 : ℝ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1 : ℤ) * z.2 +
      (z.1 * z'.2 - z.2 * z'.1 : ℤ) * (complVec z).2 := by
    have : (z'.2 : ℤ) = (z'.1 * (complVec z).2 - z'.2 * (complVec z).1) * z.2 +
        (z.1 * z'.2 - z.2 * z'.1) * (complVec z).2 := by linear_combination (-z'.2) * hdet
    exact_mod_cast this
  rw [h1, h2]; push_cast; ring

lemma eq_of_det_eq {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) {z' z'' : ℤ × ℤ}
    (h1 : detZ z z' = detZ z z'') (h2 : detZ z' (complVec z) = detZ z'' (complVec z)) : z' = z'' := by
  have hdet := detZ_complVec hz
  unfold detZ at hdet h1 h2
  ext
  · linear_combination (z''.1 - z'.1) * hdet + (complVec z).1 * h1 + z.1 * h2
  · linear_combination (z''.2 - z'.2) * hdet + (complVec z).2 * h1 + z.2 * h2

open Classical in
/-- **At most 16 targets per determinant.** -/
lemma target_count (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) {z : ℤ × ℤ}
    (hz : Int.gcd z.1 z.2 = 1) (hbox : P.InBox ω z) (j₁ : ℤ) :
    (P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = j₁)).card ≤ 16 := by
  obtain ⟨hu1, hu2, -, -, -, -⟩ := hω
  have hu : 0 < ω.1 := by linarith
  have htz : P.U / ω.1 ≤ tauR ω z := by
    rw [div_le_iff₀ hu, mul_comm]; exact hbox.1
  have htz0 : 0 < tauR ω z := lt_of_lt_of_le (by positivity) htz
  set w := complVec z
  set lo : ℝ := (P.U / ω.1 - j₁ * tauR ω w) / tauR ω z
  -- the coordinate `h = det(z', w)` lies in a window of length 15
  have hwin : ∀ z' ∈ P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = j₁),
      detZ z' w ∈ Icc ⌈lo⌉ (⌈lo⌉ + 15) := by
    intro z' hz'
    obtain ⟨-, hb', hd'⟩ := mem_filter.1 hz'
    have hdec := tauR_decomp ω hz z'
    rw [hd'] at hdec
    have hlow : P.U / ω.1 ≤ tauR ω z' := by
      rw [div_le_iff₀ hu, mul_comm]; exact hb'.1
    have hhigh : tauR ω z' ≤ 16 * P.U / ω.1 := by
      rw [le_div_iff₀ hu, mul_comm]; exact hb'.2.1
    have hh : (detZ z' w : ℝ) = (tauR ω z' - j₁ * tauR ω w) / tauR ω z := by
      rw [eq_div_iff htz0.ne']; linarith
    have hge : lo ≤ detZ z' w := by
      rw [hh]; exact div_le_div_of_nonneg_right (by linarith) htz0.le
    have hle : (detZ z' w : ℝ) ≤ lo + 15 := by
      rw [hh]
      have : (tauR ω z' - j₁ * tauR ω w) / tauR ω z ≤ lo + 15 * P.U / ω.1 / tauR ω z := by
        rw [show lo + 15 * P.U / ω.1 / tauR ω z = (P.U / ω.1 - j₁ * tauR ω w + 15 * P.U / ω.1) /
          tauR ω z by simp only [lo]; field_simp]
        exact div_le_div_of_nonneg_right (by
          have : 16 * P.U / ω.1 = P.U / ω.1 + 15 * P.U / ω.1 := by ring
          linarith) htz0.le
      have h15 : 15 * P.U / ω.1 / tauR ω z ≤ 15 := by
        rw [div_le_iff₀ htz0]
        calc 15 * P.U / ω.1 = 15 * (P.U / ω.1) := by ring
          _ ≤ 15 * tauR ω z := by linarith
      linarith
    rw [mem_Icc]
    constructor
    · exact Int.ceil_le.2 hge
    · have : (detZ z' w : ℝ) ≤ ⌈lo⌉ + 15 := le_trans hle (by linarith [Int.le_ceil lo])
      exact_mod_cast this
  calc (P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = j₁)).card
      ≤ (Icc ⌈lo⌉ (⌈lo⌉ + 15)).card := by
        refine card_le_card_of_injOn (fun z' => detZ z' w) (fun z' hz' => hwin z' hz') ?_
        intro z' hz' z'' hz'' heq
        have h1 : detZ z z' = detZ z z'' := by
          rw [(mem_filter.1 hz').2.2, (mem_filter.1 hz'').2.2]
        exact eq_of_det_eq hz h1 heq
    _ = 16 := by simp only [Int.card_Icc]; omega

end Geo

/-! ## The kernel -/

lemma norm_minorKernel_le (x A₀ Y : ℝ) (t a b : ℤ) :
    ‖minorKernel x A₀ Y t a b‖ ≤ (if |(t : ℝ) / Y| < 5 then 1 else 0) *
      ((if t - b + a = 0 then 1 else 0) + (volume (majorArcs x A₀ Y)).toReal) := by
  rw [minorKernel_eq]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖(arcCutoff (t / Y) : ℂ) * (if t - b + a = 0 then 1 else 0)‖ ≤
      (if |(t : ℝ) / Y| < 5 then 1 else 0) * (if t - b + a = 0 then 1 else 0) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul (abs_arcCutoff_le _) (by split_ifs <;> simp) (norm_nonneg _)
      (by split_ifs <;> norm_num)
  have h2 := norm_majorKernel_le x A₀ Y t a b
  rw [mul_add]
  linarith

lemma norm_edgeMult_le (P : MemParams) (j : ℕ) (t : ℤ) (a b D : ℕ) (hD : P.d₀ ≤ D) :
    ‖P.edgeMult j t a b D‖ ≤ (if |(t : ℝ) / P.Y| < 5 then 1 else 0) *
      ((if t = (b : ℤ) - a then 1 else 0) + (volume (majorArcs P.x P.A₀ P.Y)).toReal) := by
  unfold MemParams.edgeMult
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hb0 := dyadicBump_nonneg ((b : ℝ) / P.Y)
  have ha0 := dyadicBump_nonneg ((a : ℝ) / P.Y)
  have hfac : |((P.d₀ : ℝ) / D) * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    have h1 : (P.d₀ : ℝ) / D ≤ 1 := by
      rcases Nat.eq_zero_or_pos D with h | h
      · simp [h]
      · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast hD
    have := dyadicBump_le_one ((b : ℝ) / P.Y)
    have := dyadicBump_le_one ((a : ℝ) / P.Y)
    have := dyadicBump_nonneg ((b : ℝ) / P.Y)
    have := dyadicBump_nonneg ((a : ℝ) / P.Y)
    have : (0 : ℝ) ≤ P.d₀ / D := by positivity
    calc (P.d₀ : ℝ) / D * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y) ≤ 1 * 1 * 1 := by
          gcongr
      _ = 1 := by ring
  have hk : ‖(if Even j then minorKernel P.x P.A₀ P.Y t a b
      else (starRingEnd ℂ) (minorKernel P.x P.A₀ P.Y (-t) b a))‖ ≤
      (if |(t : ℝ) / P.Y| < 5 then 1 else 0) *
        ((if t = (b : ℤ) - a then 1 else 0) + (volume (majorArcs P.x P.A₀ P.Y)).toReal) := by
    by_cases hj : Even j
    · rw [if_pos hj]
      refine (norm_minorKernel_le _ _ _ _ _ _).trans ?_
      have : (t - b + a = 0) ↔ (t = (b : ℤ) - a) := by omega
      simp only [this]; exact le_rfl
    · rw [if_neg hj, Complex.norm_conj]
      refine (norm_minorKernel_le _ _ _ _ _ _).trans ?_
      have e1 : |((-t : ℤ) : ℝ) / P.Y| = |(t : ℝ) / P.Y| := by push_cast; rw [neg_div, abs_neg]
      have e2 : (-t - a + b = 0) ↔ (t = (b : ℤ) - a) := by omega
      simp only [e1, e2]; exact le_rfl
  calc |((P.d₀ : ℝ) / D) * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y)| *
        ‖(if Even j then minorKernel P.x P.A₀ P.Y t a b
          else (starRingEnd ℂ) (minorKernel P.x P.A₀ P.Y (-t) b a))‖ ≤ 1 *
        ((if |(t : ℝ) / P.Y| < 5 then 1 else 0) *
        ((if t = (b : ℤ) - a then 1 else 0) + (volume (majorArcs P.x P.A₀ P.Y)).toReal)) :=
        mul_le_mul hfac hk (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-! ## The crude edge row -/

section Row

variable (P : MemParams)

/-- The kernel envelope `1[|t/Y| < 5] (1[t = b − a] + ε)`. -/
noncomputable def kEnv (ε : ℝ) (t : ℤ) (a b : ℕ) : ℝ :=
  (if |(t : ℝ) / P.Y| < 5 then 1 else 0) * ((if t = (b : ℤ) - a then 1 else 0) + ε)

lemma kEnv_nonneg {ε : ℝ} (hε : 0 ≤ ε) (t : ℤ) (a b : ℕ) : 0 ≤ kEnv P ε t a b := by
  unfold kEnv; split_ifs <;> positivity

lemma sum_kEnv_le (hY : 0 < P.Y) {ε : ℝ} (hε : 0 ≤ ε) (a b : ℕ) (T : Finset ℤ) :
    ∑ t ∈ T, kEnv P ε t a b ≤ 1 + (10 * P.Y + 1) * ε := by
  classical
  set M : ℤ := ⌊5 * P.Y⌋
  have hsupp : ∀ t ∈ T, t ∉ Icc (-M) M → kEnv P ε t a b = 0 := by
    intro t _ ht
    unfold kEnv
    rw [if_neg, zero_mul]
    intro h
    apply ht
    rw [abs_lt, lt_div_iff₀ hY, div_lt_iff₀ hY] at h
    rw [mem_Icc]
    constructor
    · have : -t ≤ M := Int.le_floor.2 (by push_cast; linarith)
      omega
    · exact Int.le_floor.2 (by linarith)
  calc ∑ t ∈ T, kEnv P ε t a b ≤ ∑ t ∈ T ∩ Icc (-M) M, kEnv P ε t a b := by
        rw [← sum_filter_add_sum_filter_not T (· ∈ Icc (-M) M)]
        rw [sum_eq_zero fun t ht => hsupp t (mem_filter.1 ht).1 (mem_filter.1 ht).2, add_zero,
          filter_mem_eq_inter]
    _ ≤ ∑ t ∈ Icc (-M) M, kEnv P ε t a b :=
        sum_le_sum_of_subset_of_nonneg inter_subset_right fun t _ _ => kEnv_nonneg P hε t a b
    _ ≤ ∑ t ∈ Icc (-M) M, ((if t = (b : ℤ) - a then 1 else 0) + ε) := by
        refine sum_le_sum fun t _ => ?_
        unfold kEnv
        have : 0 ≤ (if t = (b : ℤ) - a then (1 : ℝ) else 0) + ε := by split_ifs <;> positivity
        split_ifs <;> linarith
    _ ≤ 1 + (10 * P.Y + 1) * ε := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
        have h1 : ∑ t ∈ Icc (-M) M, (if t = (b : ℤ) - a then (1 : ℝ) else 0) ≤ 1 := by
          rw [sum_ite_eq']; split_ifs <;> norm_num
        have h2 : ((Icc (-M) M).card : ℝ) ≤ 10 * P.Y + 1 := by
          rw [Int.card_Icc]
          have hM0 : 0 ≤ M := Int.floor_nonneg.2 (by positivity)
          have : ((M + 1 - -M).toNat : ℝ) = 2 * M + 1 := by
            rw [show M + 1 - -M = 2 * M + 1 by ring]
            have : (0 : ℤ) ≤ 2 * M + 1 := by omega
            rw [← Int.cast_natCast, Int.toNat_of_nonneg this]; push_cast; ring
          rw [this]
          have : (M : ℝ) ≤ 5 * P.Y := Int.floor_le _
          linarith
        nlinarith

open Classical in
/-- The `z'`-sum of the kernel envelope: at most 16 targets per determinant. -/
lemma zsum_kEnv_le (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y) {ε : ℝ}
    (hε : 0 ≤ ε) {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1) (hbox : P.InBox ω z) (D : ℕ) (hD : 0 < D)
    (a b : ℕ) :
    ∑ z' ∈ P.zSet, (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then kEnv P ε (detZ z z' / D) a b else 0)
      ≤ 16 * (1 + (10 * P.Y + 1) * ε) := by
  set g : ℤ × ℤ → ℤ := fun z' => detZ z z' / D
  rw [← sum_fiberwise_of_maps_to (s := P.zSet) (t := P.zSet.image g) (g := g)
    (fun z' hz' => mem_image_of_mem g hz')]
  have hfib : ∀ t ∈ P.zSet.image g, ∑ z' ∈ P.zSet.filter (fun z' => g z' = t),
      (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then kEnv P ε (detZ z z' / D) a b else 0) ≤
      16 * kEnv P ε t a b := by
    intro t _
    calc ∑ z' ∈ P.zSet.filter (fun z' => g z' = t),
          (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then kEnv P ε (detZ z z' / D) a b else 0)
        = ∑ z' ∈ (P.zSet.filter (fun z' => g z' = t)).filter
            (fun z' => P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z'), kEnv P ε (detZ z z' / D) a b :=
          (sum_filter _ _).symm
      _ = ∑ z' ∈ (P.zSet.filter (fun z' => g z' = t)).filter
            (fun z' => P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z'), kEnv P ε t a b := by
          refine sum_congr rfl fun z' hz' => ?_
          rw [show detZ z z' / D = t from (mem_filter.1 (mem_filter.1 hz').1).2]
      _ ≤ ∑ z' ∈ P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = D * t), kEnv P ε t a b := by
          refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => kEnv_nonneg P hε _ _ _)
          intro z' hz'
          simp only [mem_filter] at hz' ⊢
          obtain ⟨⟨hzz, hg⟩, hb, hd⟩ := hz'
          refine ⟨hzz, hb, ?_⟩
          rw [← hg]
          exact (Int.mul_ediv_cancel' hd).symm
      _ = (P.zSet.filter (fun z' => P.InBox ω z' ∧ detZ z z' = D * t)).card * kEnv P ε t a b := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 16 * kEnv P ε t a b := by
          refine mul_le_mul_of_nonneg_right ?_ (kEnv_nonneg P hε _ _ _)
          exact_mod_cast target_count P ω hω hU hz hbox (D * t)
  calc ∑ t ∈ P.zSet.image g, ∑ z' ∈ P.zSet.filter (fun z' => g z' = t),
        (if P.InBox ω z' ∧ (D : ℤ) ∣ detZ z z' then kEnv P ε (detZ z z' / D) a b else 0)
      ≤ ∑ t ∈ P.zSet.image g, 16 * kEnv P ε t a b := sum_le_sum hfib
    _ = 16 * ∑ t ∈ P.zSet.image g, kEnv P ε t a b := by rw [mul_sum]
    _ ≤ 16 * (1 + (10 * P.Y + 1) * ε) := by
        gcongr; exact sum_kEnv_le P hY hε a b _

end Row

section RowMain

variable (P : MemParams)

lemma lineOf_le {p : ℕ} (hp : 0 < p) (z : ℤ × ℤ) : lineOf p z ≤ p := by
  unfold lineOf
  split_ifs
  · exact le_rfl
  · have : NeZero p := ⟨hp.ne'⟩
    exact (ZMod.val_lt _).le

/-- The label weight of a target choice, uniform in the target position. -/
noncomputable def wBar (m : P.Mem) (i : Fin P.K) (x : ℕ × Bool) : ℝ :=
  if x.2 then (∑ l ∈ range (x.1 + 1), (P.memAt m (i, x.1, l) : ℝ)) / P.Vg i else P.nu i x.1

lemma wBar_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV : ∀ i, 0 < P.Vg i) (m : P.Mem)
    (i : Fin P.K) (x : ℕ × Bool) (hx : x.1 ∈ P.grp i) : 0 ≤ wBar P m i x := by
  unfold wBar; split_ifs
  · have := hV i; positivity
  · exact hnu i _ hx

lemma sum_memAt_le (m : P.Mem) (i : Fin P.K) :
    ∑ p ∈ P.grp i, ∑ l ∈ range (p + 1), (P.memAt m (i, p, l) : ℝ) ≤ P.memSize m := by
  classical
  have hmem : ∀ x : Fin P.K × ℕ × ℕ, (P.memAt m x : ℝ) =
      ∑ y : P.PT, if y.1 = x then (m y : ℝ) else 0 := by
    intro x
    unfold MemParams.memAt
    split_ifs with h
    · rw [sum_eq_single ⟨x, h⟩]
      · simp
      · intro y _ hy; rw [if_neg (fun h' => hy (Subtype.ext h'))]
      · simp
    · rw [Nat.cast_zero]; symm; refine sum_eq_zero fun y _ => ?_
      rw [if_neg]; intro h'; exact h (h' ▸ y.2)
  simp only [hmem]
  rw [sum_congr rfl fun p _ => sum_comm, sum_comm]
  unfold MemParams.memSize
  push_cast
  refine sum_le_sum fun y _ => ?_
  have h1 : ∀ p ∈ P.grp i, ∑ l ∈ range (p + 1), (if y.1 = (i, p, l) then (m y : ℝ) else 0) ≤
      if y.1.2.1 = p then (m y : ℝ) else 0 := by
    intro p _
    by_cases hp : y.1.2.1 = p
    · rw [if_pos hp]
      calc ∑ l ∈ range (p + 1), (if y.1 = (i, p, l) then (m y : ℝ) else 0)
          ≤ ∑ l ∈ range (p + 1), (if y.1.2.2 = l then (m y : ℝ) else 0) := by
            refine sum_le_sum fun l _ => ?_
            by_cases hl : y.1 = (i, p, l)
            · rw [if_pos hl, if_pos (by rw [hl])]
            · rw [if_neg hl]; split_ifs <;> positivity
        _ ≤ m y := by
            rw [sum_ite_eq]; split_ifs
            · exact le_rfl
            · positivity
    · refine le_of_eq_of_le (sum_eq_zero fun l _ => if_neg fun h => hp (by rw [h])) ?_
      rw [if_neg hp]
  calc ∑ p ∈ P.grp i, ∑ l ∈ range (p + 1), (if y.1 = (i, p, l) then (m y : ℝ) else 0)
      ≤ ∑ p ∈ P.grp i, (if y.1.2.1 = p then (m y : ℝ) else 0) := sum_le_sum h1
    _ ≤ m y := by
        rw [sum_ite_eq]; split_ifs
        · exact le_rfl
        · positivity

end RowMain

section RowThm

variable (P : MemParams)

lemma sum_storeCount_le (z : ℤ × ℤ) (ℓ : P.Lst) (St : Finset (Fin P.K)) :
    ∑ y : P.PT, P.storeCount z ℓ St y ≤ St.card := by
  classical
  unfold MemParams.storeCount
  simp only [card_filter]
  rw [sum_comm]
  calc ∑ i ∈ St, ∑ y : P.PT, (if P.storedPart z ℓ i = y.1 then 1 else 0)
      ≤ ∑ _i ∈ St, 1 := sum_le_sum fun i _ => by
        rw [← card_filter]
        exact card_le_one.2 fun a ha b hb =>
          Subtype.ext ((mem_filter.1 ha).2.symm.trans (mem_filter.1 hb).2)
    _ = St.card := by simp

lemma memSize_edgeOut_le (s : P.MState) (c : L102G.EC P) :
    P.memSize (P.edgeOutMem s c) ≤ P.memSize s.2.2 + c.1.card := by
  unfold MemParams.memSize MemParams.edgeOutMem
  calc ∑ y, (s.2.2 y - P.promCount c.2.1 c.2.2 y + P.storeCount s.1 s.2.1 c.1 y)
      ≤ ∑ y, (s.2.2 y + P.storeCount s.1 s.2.1 c.1 y) := sum_le_sum fun y _ => by omega
    _ = ∑ y, s.2.2 y + ∑ y, P.storeCount s.1 s.2.1 c.1 y := sum_add_distrib
    _ ≤ ∑ y, s.2.2 y + c.1.card := by
        have := sum_storeCount_le P s.1 s.2.1 c.1; omega

open Classical in
/-- The per-choice envelope of an edge coefficient. -/
lemma norm_coeffK_le (ω : ℝ × ℝ × ℝ) (κ : ℤ → ℕ → ℕ → ℕ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hκ : ∀ t a b D, P.d₀ ≤ D → ‖κ t a b D‖ ≤ kEnv P ε t a b)
    (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV : ∀ i, 0 < P.Vg i) (s : P.MState)
    (c : L102G.EC P) (hc : c ∈ P.edgeChoices) :
    ‖L102G.coeffK P κ ω s c‖ ≤
      (if P.InBox ω c.2.1 ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 c.2.1 then
        kEnv P ε (detZ s.1 c.2.1 / padProd s.2.1) (∏ i, (c.2.2 i).1) (lastProd s.2.1) else 0) *
      ∏ i, wBar P s.2.2 i (c.2.2 i) := by
  have htg : c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ univ :=
    tg_mem_of_mem_edgeChoices P hc
  have hgrp : ∀ i, (c.2.2 i).1 ∈ P.grp i := fun i =>
    (mem_product.1 (Fintype.mem_piFinset.1 htg i)).1
  have hW0 : ∀ i, 0 ≤ wBar P s.2.2 i (c.2.2 i) := fun i => wBar_nonneg P hnu hV _ i _ (hgrp i)
  unfold L102G.coeffK
  split_ifs with hE hB
  · obtain ⟨hOK, -, -, -⟩ := hE
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hρ : (0 : ℝ) ≤ memRho := by unfold memRho; norm_num
    have hρ1 : memRho ≤ 1 := by unfold memRho; norm_num
    have hfac : ∀ i, 0 ≤ (if (c.2.2 i).2 then
        (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) := by
      intro i; split_ifs
      · have := hV i; positivity
      · exact hnu i _ (hgrp i)
    have hrf0 : 0 ≤ L102G.rfac P s c := by
      unfold L102G.rfac
      exact mul_nonneg (mul_nonneg (pow_nonneg hρ _) (prod_nonneg fun i _ => hfac i))
        (pow_nonneg hρ _)
    rw [abs_of_nonneg hrf0]
    have hrf : L102G.rfac P s c ≤ ∏ i, wBar P s.2.2 i (c.2.2 i) := by
      unfold L102G.rfac
      have h1 : memRho ^ P.hitCount s.1 s.2.2 ≤ 1 := pow_le_one₀ hρ hρ1
      have h2 : memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c) ≤ 1 := pow_le_one₀ hρ hρ1
      have h3 : (∏ i, if (c.2.2 i).2 then
          (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) ≤
          ∏ i, wBar P s.2.2 i (c.2.2 i) := by
        refine prod_le_prod (fun i _ => hfac i) fun i _ => ?_
        unfold wBar
        split_ifs with hfl
        · have hVi := hV i
          refine div_le_div_of_nonneg_right ?_ hVi.le
          have hp0 : 0 < (c.2.2 i).1 := by
            have := hgrp i; simp only [MemParams.grp, primeGroup, mem_filter] at this
            exact this.2.1.pos
          have hl : lineOf (c.2.2 i).1 c.2.1 ∈ range ((c.2.2 i).1 + 1) :=
            mem_range.2 (Nat.lt_succ_of_le (lineOf_le hp0 _))
          unfold MemParams.promPart
          exact single_le_sum (f := fun l => (P.memAt s.2.2 (i, (c.2.2 i).1, l) : ℝ))
            (fun _ _ => by positivity) hl
        · exact le_rfl
      calc memRho ^ P.hitCount s.1 s.2.2 * (∏ i, if (c.2.2 i).2 then
            (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) *
            memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c) ≤ 1 * (∏ i, wBar P s.2.2 i (c.2.2 i)) * 1 := by
            have hP0 : 0 ≤ ∏ i, (if (c.2.2 i).2 then
                (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) :=
              prod_nonneg fun i _ => hfac i
            have hW : 0 ≤ ∏ i, wBar P s.2.2 i (c.2.2 i) := prod_nonneg fun i _ => hW0 i
            calc memRho ^ P.hitCount s.1 s.2.2 * (∏ i, if (c.2.2 i).2 then
                (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) *
                memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c) ≤
                1 * (∏ i, if (c.2.2 i).2 then
                (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i else P.nu i (c.2.2 i).1) * 1 := by
                  apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hP0) h2 (by positivity)
                    (by positivity)
              _ ≤ 1 * (∏ i, wBar P s.2.2 i (c.2.2 i)) * 1 := by gcongr
        _ = ∏ i, wBar P s.2.2 i (c.2.2 i) := by ring
    have hk := hκ (detZ s.1 c.2.1 / padProd s.2.1) (∏ i, (c.2.2 i).1) (lastProd s.2.1)
      (padProd s.2.1) hOK.2.2.1
    rw [mul_comm]
    exact mul_le_mul hk hrf hrf0 (kEnv_nonneg P hε _ _ _)
  · exfalso; exact hB ⟨hE.1.2.2.2.2.2.2.1, hE.1.2.2.2.2.1⟩
  · rw [norm_zero]
    exact mul_nonneg (kEnv_nonneg P hε _ _ _) (prod_nonneg fun i _ => hW0 i)
  · rw [norm_zero, zero_mul]

end RowThm

section RowSum

variable (P : MemParams)

lemma sum_pow_card_univ {K : ℕ} (v₀ : ℝ) :
    ∑ St : Finset (Fin K), v₀ ^ St.card = (1 + v₀) ^ K := by
  have := Finset.sum_pow_mul_eq_add_pow v₀ 1 (univ : Finset (Fin K))
  simp only [one_pow, mul_one, card_univ, Fintype.card_fin, powerset_univ] at this
  rw [this, add_comm]

open Classical in
/-- **The crude edge row** ([21] (4.25)), weighted by `v₀^{memory}`, with the fresh labels of the
groups in `C` forced into `V`. -/
theorem edge_row (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y)
    (κ : ℤ → ℕ → ℕ → ℕ → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hκ : ∀ t a b D, P.d₀ ≤ D → ‖κ t a b D‖ ≤ kEnv P ε t a b)
    (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV : ∀ i, 1 / 2 ≤ P.Vg i)
    (C : Finset (Fin P.K)) (Vs : Finset ℕ) {v₀ : ℝ} (hv₀ : 1 ≤ v₀) (s : P.MState)
    (hs : s ∈ P.stSet) :
    ∑ c ∈ P.edgeChoices, ‖L102G.coeffK P κ ω s c‖ *
      (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs then 1 else 0) *
        v₀ ^ P.memSize (P.edgeOutMem s c) ≤
    (1 + v₀) ^ P.K * (16 * (1 + (10 * P.Y + 1) * ε)) *
      (∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
        else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2)) * v₀ ^ P.memSize s.2.2 := by
  have hVpos : ∀ i, 0 < P.Vg i := fun i => by linarith [hV i]
  obtain ⟨hzs, hℓ, hm⟩ := (mem_stSet_iff' P s).1 hs
  have hzp : Int.gcd s.1.1 s.1.2 = 1 := by
    unfold MemParams.zSet at hzs; exact (mem_filter.1 hzs).2
  have hD : 0 < padProd s.2.1 := by
    unfold padProd
    simp only [listCands, Fintype.mem_piFinset] at hℓ
    exact prod_pos fun i _ => prod_pos fun k _ => by
      have := hℓ i k.castSucc; simp only [primeGroup, mem_filter] at this; exact this.2.1.pos
  have hRHS0 : 0 ≤ (1 + v₀) ^ P.K * (16 * (1 + (10 * P.Y + 1) * ε)) *
      (∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
        else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2)) * v₀ ^ P.memSize s.2.2 := by
    refine mul_nonneg (mul_nonneg (by positivity) (prod_nonneg fun i _ => ?_)) (by positivity)
    split_ifs
    · exact sum_nonneg fun p hp => hnu i p (mem_filter.1 hp).1
    · exact add_nonneg (sum_nonneg fun p hp => hnu i p hp) (by positivity)
  by_cases hbz : P.InBox ω s.1
  swap
  · refine le_trans (le_of_eq (sum_eq_zero fun c _ => ?_)) hRHS0
    unfold L102G.coeffK
    rw [if_neg (fun hE => hbz hE.1.2.2.2.2.2.1)]; simp
  set g : Fin P.K → ℕ × Bool → ℝ := fun i x => wBar P s.2.2 i x *
    (if (i ∈ C → (x.2 = false ∧ x.1 ∈ Vs)) then 1 else 0) with hg
  set E : (ℤ × ℤ) → (Fin P.K → ℕ × Bool) → ℝ := fun z' tg =>
    if P.InBox ω z' ∧ (padProd s.2.1 : ℤ) ∣ detZ s.1 z' then
      kEnv P ε (detZ s.1 z' / padProd s.2.1) (∏ i, (tg i).1) (lastProd s.2.1) else 0 with hE
  have hterm : ∀ c ∈ P.edgeChoices, ‖L102G.coeffK P κ ω s c‖ *
      (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs then 1 else 0) *
        v₀ ^ P.memSize (P.edgeOutMem s c) ≤
      v₀ ^ P.memSize s.2.2 * (v₀ ^ c.1.card * ((∏ i, g i (c.2.2 i)) * E c.2.1 c.2.2)) := by
    intro c hc
    have h1 := norm_coeffK_le P ω κ hε hκ hnu hVpos s c hc
    have hc2 : (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs then (1 : ℝ) else 0) =
        ∏ i, (if (i ∈ C → ((c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs)) then 1 else 0) := by
      rw [prod_boole]; simp
    have h3 : v₀ ^ P.memSize (P.edgeOutMem s c) ≤ v₀ ^ P.memSize s.2.2 * v₀ ^ c.1.card := by
      rw [← pow_add]; exact pow_le_pow_right₀ hv₀ (memSize_edgeOut_le P s c)
    have htg : c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ univ :=
      tg_mem_of_mem_edgeChoices P hc
    have hW0 : ∀ i, 0 ≤ wBar P s.2.2 i (c.2.2 i) := fun i => wBar_nonneg P hnu hVpos _ i _
      (mem_product.1 (Fintype.mem_piFinset.1 htg i)).1
    have hE0 : 0 ≤ E c.2.1 c.2.2 := by
      rw [hE]; dsimp only; split_ifs
      · exact kEnv_nonneg P hε _ _ _
      · exact le_rfl
    rw [hc2]
    calc ‖L102G.coeffK P κ ω s c‖ *
          (∏ i, (if (i ∈ C → ((c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs)) then (1 : ℝ) else 0)) *
          v₀ ^ P.memSize (P.edgeOutMem s c) ≤
        (E c.2.1 c.2.2 * ∏ i, wBar P s.2.2 i (c.2.2 i)) *
          (∏ i, (if (i ∈ C → ((c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs)) then (1 : ℝ) else 0)) *
          (v₀ ^ P.memSize s.2.2 * v₀ ^ c.1.card) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right h1 (prod_nonneg fun i _ => by
            split_ifs <;> norm_num)) h3 (by positivity) (mul_nonneg (mul_nonneg hE0
              (prod_nonneg fun i _ => hW0 i)) (prod_nonneg fun i _ => by split_ifs <;> norm_num))
      _ = v₀ ^ P.memSize s.2.2 * (v₀ ^ c.1.card * ((∏ i, g i (c.2.2 i)) * E c.2.1 c.2.2)) := by
          rw [hg]; dsimp only; rw [prod_mul_distrib]; ring
  refine (sum_le_sum hterm).trans ?_
  unfold MemParams.edgeChoices
  rw [sum_product]
  simp only [sum_product]
  rw [show (∑ St : Finset (Fin P.K), ∑ z' ∈ P.zSet,
      ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
        v₀ ^ P.memSize s.2.2 * (v₀ ^ St.card * ((∏ i, g i (tg i)) * E z' tg))) =
      v₀ ^ P.memSize s.2.2 * ((∑ St : Finset (Fin P.K), v₀ ^ St.card) *
        ∑ z' ∈ P.zSet, ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
          (∏ i, g i (tg i)) * E z' tg) by
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm.trans (sum_congr rfl fun _ _ => Finset.sum_comm)]
  -- the target and label sums
  have hzt : ∑ z' ∈ P.zSet, ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
      (∏ i, g i (tg i)) * E z' tg ≤ (16 * (1 + (10 * P.Y + 1) * ε)) *
        ∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
          else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2) := by
    rw [sum_comm]
    have hg0 : ∀ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
        0 ≤ ∏ i, g i (tg i) := by
      intro tg htg
      refine prod_nonneg fun i _ => mul_nonneg (wBar_nonneg P hnu hVpos _ i _
        (mem_product.1 (Fintype.mem_piFinset.1 htg i)).1) (by split_ifs <;> norm_num)
    calc ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
          ∑ z' ∈ P.zSet, (∏ i, g i (tg i)) * E z' tg
        = ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
          (∏ i, g i (tg i)) * ∑ z' ∈ P.zSet, E z' tg := by
          refine sum_congr rfl fun tg _ => by rw [mul_sum]
      _ ≤ ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
          (∏ i, g i (tg i)) * (16 * (1 + (10 * P.Y + 1) * ε)) :=
          sum_le_sum fun tg htg => mul_le_mul_of_nonneg_left
            (zsum_kEnv_le P ω hω hU hY hε hzp hbz _ hD _ _) (hg0 tg htg)
      _ = (16 * (1 + (10 * P.Y + 1) * ε)) * ∏ i, ∑ x ∈ P.grp i ×ˢ (univ : Finset Bool), g i x := by
          rw [← sum_mul, mul_comm, ← prod_univ_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (prod_le_prod (fun i _ => sum_nonneg fun x hx =>
            mul_nonneg (wBar_nonneg P hnu hVpos _ i _ (mem_product.1 hx).1)
              (by split_ifs <;> norm_num)) fun i _ => ?_) (by positivity)
          rw [sum_product]
          simp only [Fintype.sum_bool]
          by_cases hiC : i ∈ C
          · rw [if_pos hiC, sum_filter]
            refine le_of_eq ?_
            refine sum_congr rfl fun p _ => ?_
            by_cases hp : p ∈ Vs
            · simp [hg, wBar, hiC, hp]
            · simp [hg, wBar, hiC, hp]
          · rw [if_neg hiC]
            simp only [hg, hiC, false_implies, if_true, mul_one, wBar, if_false, Bool.false_eq_true]
            rw [sum_add_distrib, add_comm]
            gcongr
            calc ∑ p ∈ P.grp i, (∑ l ∈ range (p + 1), (P.memAt s.2.2 (i, p, l) : ℝ)) / P.Vg i
                = (∑ p ∈ P.grp i, ∑ l ∈ range (p + 1), (P.memAt s.2.2 (i, p, l) : ℝ)) / P.Vg i := by
                  rw [sum_div]
              _ ≤ P.memSize s.2.2 / (1 / 2) := by
                  gcongr
                  all_goals first | exact hV i | exact sum_memAt_le P s.2.2 i | norm_num
              _ = 2 * P.memSize s.2.2 := by ring
  calc v₀ ^ P.memSize s.2.2 * ((∑ St : Finset (Fin P.K), v₀ ^ St.card) *
        ∑ z' ∈ P.zSet, ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)),
          (∏ i, g i (tg i)) * E z' tg)
      ≤ v₀ ^ P.memSize s.2.2 * ((1 + v₀) ^ P.K * ((16 * (1 + (10 * P.Y + 1) * ε)) *
        ∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
          else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2))) := by
        rw [sum_pow_card_univ]
        gcongr
    _ = _ := by ring

end RowSum

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the weighted Schur test for choice-indexed operators

An operator in the row convention, `(O f)(s) = ∑_{c ∈ Ch} coeff(s, c) f(out(s, c))` (outputs
outside the state set `St` dropped), on `ℓ²(St, μ)`. With a positive Schur weight `w`, a weighted
row bound `R` and a weighted column bound `C` give `‖O f‖² ≤ R C ‖f‖²` ([21] §4.4). -/

namespace ArtinPrimitiveRoots.L102D

open Finset

variable {α γ : Type*} [DecidableEq α]

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the crude norm of a modified edge ([21] (4.23)–(4.25)) (for D7e)

An edge whose coefficients are multiplied by anything of modulus `≤ 1` (phases, validity checks) has
norm `≤ √R · √(3^K R)` on `H_B`, `R = 2^K · 16 (1 + (10Y+1) vol 𝔐) · (2 + 2B)^K`: rows by `edge_row`,
columns by prover G's reversal (`L102G.col_via_rev`), and G's bilinear Cauchy–Schwarz
(`L102G.piece_bound`, `L102G.opBound_of_bilin`). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory
open scoped ComplexConjugate

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

lemma kEnv_of_edgeMult (j : ℕ) (t : ℤ) (a b D : ℕ) (hD : P.d₀ ≤ D) :
    ‖P.edgeMult j t a b D‖ ≤ kEnv P (volume (majorArcs P.x P.A₀ P.Y)).toReal t a b := by
  have := norm_edgeMult_le P j t a b D hD
  unfold kEnv; exact this

open Classical in
/-- **The crude weighted edge row with forced fresh labels** for the edge coefficient itself
(`edge_row` with `κ = edgeMult j`). -/
theorem edge_row_edgeCoeff (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y)
    (j : ℕ) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hV : ∀ i, 1 / 2 ≤ P.Vg i)
    (C : Finset (Fin P.K)) (Vs : Finset ℕ) {v₀ : ℝ} (hv₀ : 1 ≤ v₀) (s : P.MState)
    (hs : s ∈ P.stSet) :
    ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j s c‖ *
      (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs then 1 else 0) *
        v₀ ^ P.memSize (P.edgeOutMem s c) ≤
    (1 + v₀) ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
      (∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
        else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2)) * v₀ ^ P.memSize s.2.2 := by
  have h := edge_row P ω hω hU hY (P.edgeMult j) ENNReal.toReal_nonneg (kEnv_of_edgeMult P j)
    hnu hV C Vs hv₀ s hs
  simp only [← L102G.edgeCoeff_eq] at h
  exact h

end ArtinPrimitiveRoots.L102D
end

section
/-! Check module: `chk_sum_norm_edgeCoeff_mul_pow_le`, the published statement `sum_norm_edgeCoeff_mul_pow_le` verbatim, proved from the
development. -/

namespace ArtinPrimitiveRoots

open Finset MeasureTheory

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Finset MeasureTheory
set_option maxRecDepth 100000 in
theorem solution (P : MemParams) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω)
    (hU : 0 < P.U) (hY : 0 < P.Y) (j : ℕ) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p)
    (hV : ∀ i, 1 / 2 ≤ P.Vg i) (C : Finset (Fin P.K)) (Vs : Finset ℕ) {v₀ : ℝ} (hv₀ : 1 ≤ v₀)
    (s : P.MState) (hs : s ∈ P.stSet) :
    ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j s c‖ *
      (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs then 1 else 0) *
        v₀ ^ P.memSize (P.edgeOutMem s c) ≤
    (1 + v₀) ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
      (∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
        else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2)) * v₀ ^ P.memSize s.2.2 :=
  L102D.edge_row_edgeCoeff P ω hω hU hY j hnu hV C Vs hv₀ s hs
end
