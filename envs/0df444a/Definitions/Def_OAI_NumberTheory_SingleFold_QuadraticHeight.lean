-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
-- name    : OAI_NumberTheory_SingleFold_QuadraticHeight
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:13:55.346522+00:00
-- url     : https://prove2.me/theorems/bd5aa2b7-ac24-438f-acd9-be6ddd28796e
-- title:
--   Tate's limit and the canonical height of $y^2=x^3-25x$
-- statement:
--   1. **Tate's limit.** Let $A$ be an abelian group and $h:A\to\mathbb{R}$ with $h(0)=0$ and $|h(P+Q)+h(P-Q)-2h(P)-2h(Q)|\le C$. Then $4^{-n}h(2^nP)$ converges to a limit $L(P)$ with $|h(P)-L(P)|\le C/3$. The limit satisfies the exact parallelogram law, $L(nP)=n^2L(P)$ for $n\in\mathbb{Z}$, $L(0)=0$, and $L\ge0$ if $h\ge0$.
--   2. **Northcott property.** For $E:y^2=x^3-25x$ the naive height $h_{\mathrm{naive}}(P)=h(x(P))$ is nonnegative, vanishes at $O$, and has only finitely many points below any bound; each $x$-coordinate carries at most two points.
--   3. **Canonical height.** $\hat h(P)=\frac12L(P)$ for $L$ built from $h_{\mathrm{naive}}$. It is nonnegative, $\hat h(nP)=n^2\hat h(P)$, and for some $c>0$
--   $$
--   \bigl|h_{\mathrm{naive}}(P)-2\hat h(P)\bigr|\le c\qquad\text{for all }P .
--   $$
--
--   The canonical height is an exact quadratic form on $E(\mathbb{Q})$, and it stays within bounded distance of half the naive height.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/QuadraticHeight.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/QuadraticHeight.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight

namespace OAI

namespace SingleFold.QuadraticLimit

universe u

open Filter Topology

variable {A : Type u} [AddCommGroup A]

noncomputable def sequence (h : A → ℝ) (P : A) (n : ℕ) : ℝ :=
  (1/4 : ℝ)^n * h ((2^n) • P)

variable (h : A → ℝ) (C : ℝ)
variable (hzero : h 0 = 0)
variable (hpara : ∀ P Q, |h (P+Q)+h (P-Q)-2*(h P+h Q)| ≤ C)

include hzero hpara in
lemma step_bound (P : A) (n : ℕ) :
    dist (sequence h P n) (sequence h P (n+1)) ≤ (C/4)*(1/4:ℝ)^n := by
  have hb := hpara ((2^n) • P) ((2^n) • P)
  rw [sub_self, hzero, add_zero] at hb
  have hd : (2^(n+1)) • P = (2^n) • P + (2^n) • P := by
    rw [pow_succ, mul_comm, mul_nsmul, two_nsmul, nsmul_add]
  rw [Real.dist_eq, sequence, sequence, hd, pow_succ]
  have he : (1/4:ℝ)^n * h ((2^n) • P) -
      ((1/4:ℝ)^n * (1/4)) * h ((2^n) • P + (2^n) • P) =
      -((1/4:ℝ)^n / 4) *
        (h ((2^n) • P + (2^n) • P) - 2*(h ((2^n) • P)+h ((2^n) • P))) := by ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
  calc
    (1/4:ℝ)^n / 4 * |h ((2^n) • P + (2^n) • P) -
        2*(h ((2^n) • P)+h ((2^n) • P))| ≤ (1/4:ℝ)^n / 4 * C :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

include hzero hpara in
lemma sequence_cauchy (P : A) : CauchySeq (sequence h P) :=
  cauchySeq_of_le_geometric (1/4:ℝ) (C/4) (by norm_num) (step_bound h C hzero hpara P)

noncomputable def limit (h : A → ℝ) (P : A) : ℝ := limUnder atTop (sequence h P)

include hzero hpara in
lemma tendsto_sequence (P : A) : Tendsto (sequence h P) atTop (𝓝 (limit h P)) :=
  (sequence_cauchy h C hzero hpara P).tendsto_limUnder

include hzero hpara in
lemma error_bound (P : A) : |h P - limit h P| ≤ C/3 := by
  have hh := dist_le_of_le_geometric_of_tendsto₀ (1/4:ℝ) (C/4) (by norm_num)
    (step_bound h C hzero hpara P) (tendsto_sequence h C hzero hpara P)
  norm_num [sequence, Real.dist_eq] at hh
  linarith

include hzero hpara in
lemma limit_zero : limit h (0:A) = 0 := by
  apply tendsto_nhds_unique (tendsto_sequence h C hzero hpara 0)
  convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)) using 1
  ext n
  simp [sequence, hzero]

include hzero hpara in
lemma limit_nonneg (hnonneg : ∀ P, 0 ≤ h P) (P : A) : 0 ≤ limit h P := by
  exact ge_of_tendsto (tendsto_sequence h C hzero hpara P)
    (Eventually.of_forall fun n => mul_nonneg (by positivity) (hnonneg _))

include hzero hpara in
lemma limit_parallelogram (P Q : A) :
    limit h (P+Q)+limit h (P-Q) = 2*(limit h P+limit h Q) := by
  let f : ℕ → ℝ := fun n => sequence h (P+Q) n + sequence h (P-Q) n -
    2*(sequence h P n + sequence h Q n)
  have hf : Tendsto f atTop (𝓝 (limit h (P+Q)+limit h (P-Q)-
      2*(limit h P+limit h Q))) :=
    ((tendsto_sequence h C hzero hpara (P+Q)).add
      (tendsto_sequence h C hzero hpara (P-Q))).sub
      (tendsto_const_nhds.mul ((tendsto_sequence h C hzero hpara P).add
        (tendsto_sequence h C hzero hpara Q)))
  have hbound (n : ℕ) : |f n| ≤ C*(1/4:ℝ)^n := by
    have hp := hpara ((2^n) • P) ((2^n) • Q)
    have he : f n = (1/4:ℝ)^n * (h ((2^n) • P + (2^n) • Q) +
        h ((2^n) • P - (2^n) • Q) - 2*(h ((2^n) • P)+h ((2^n) • Q))) := by
      dsimp [f, sequence]
      rw [nsmul_add, nsmul_sub]
      ring
    rw [he, abs_mul, abs_of_nonneg (by positivity), mul_comm C]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hz : Tendsto (fun n : ℕ => C*(1/4:ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num : (1/4:ℝ) < 1)).const_mul C
  have hf0 : Tendsto f atTop (𝓝 0) := squeeze_zero_norm (fun n => hbound n) hz
  have := tendsto_nhds_unique hf hf0
  linarith

include hzero hpara in
lemma limit_nsmul (P : A) (n : ℕ) : limit h (n • P) = (n:ℝ)^2 * limit h P := by
  induction n using Nat.twoStepInduction with
  | zero => simp [limit_zero h C hzero hpara]
  | one => simp
  | more n hn hn1 =>
    have hp := limit_parallelogram h C hzero hpara ((n+1) • P) P
    have ha : (n+1) • P + P = (n+2) • P := by simp [add_nsmul]; abel
    have hs : (n+1) • P - P = n • P := by simp [add_nsmul]
    rw [ha, hs, hn, hn1] at hp
    push_cast at hp ⊢
    nlinarith

include hzero hpara in
lemma limit_neg (P : A) : limit h (-P) = limit h P := by
  have hp := limit_parallelogram h C hzero hpara 0 P
  simp only [zero_add, zero_sub, limit_zero h C hzero hpara, zero_add] at hp
  linarith

include hzero hpara in
lemma limit_zsmul (P : A) (n : ℤ) : limit h (n • P) = (n:ℝ)^2 * limit h P := by
  cases n with
  | ofNat n => simpa using limit_nsmul h C hzero hpara P n
  | negSucc n =>
    rw [Int.negSucc_eq, neg_smul, limit_neg h C hzero hpara]
    rw [← Nat.cast_add_one, natCast_zsmul]
    rw [limit_nsmul h C hzero hpara]
    push_cast
    ring

end SingleFold.QuadraticLimit

namespace SingleFold.CurveHeight

open WeierstrassCurve.Affine.Point
open Filter Topology

@[simp] lemma naiveHeight_zero : naiveHeight (0:E.Point) = 0 := by
  rw [naiveHeight, xRep_zero, Height.logHeight_swap, ← Height.logHeight₁_eq_logHeight]
  simp

lemma naiveHeight_nonneg (P : E.Point) : 0 ≤ naiveHeight P := Height.logHeight_nonneg _

lemma finite_x_fiber (x : ℚ) : {P : E.Point | P.xRep = ![x,1]}.Finite := by
  by_cases hn : {P : E.Point | P.xRep = ![x,1]}.Nonempty
  · obtain ⟨P,hP⟩ := hn
    apply (Set.finite_singleton P |>.union (Set.finite_singleton (-P))).subset
    intro Q hQ
    have he := xRep_eq_xRep_iff.mp (hQ.trans hP.symm)
    simpa [or_comm] using he
  · rw [Set.not_nonempty_iff_eq_empty.mp hn]
    exact Set.finite_empty

instance : Northcott naiveHeight where
  finite_le B := by
    have hs := Northcott.finite_le (h := Height.logHeight₁ (K := ℚ)) B
    have ht := hs.biUnion (fun x _ => finite_x_fiber x)
    apply (Set.finite_singleton (0:E.Point) |>.union ht).subset
    intro P hP
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
      right
      apply Set.mem_iUnion.mpr
      refine ⟨x, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · simpa [naiveHeight, ← Height.logHeight₁_eq_logHeight] using hP
      · exact xRep_some h

noncomputable def canonicalHeight (P : E.Point) : ℝ :=
  (1/2:ℝ) * QuadraticLimit.limit naiveHeight P

lemma canonicalHeight_nonneg (P : E.Point) : 0 ≤ canonicalHeight P := by
  obtain ⟨C,hC⟩ := approximate_parallelogram
  exact mul_nonneg (by norm_num)
    (QuadraticLimit.limit_nonneg naiveHeight C naiveHeight_zero hC naiveHeight_nonneg P)

@[simp] lemma canonicalHeight_zero : canonicalHeight (0:E.Point) = 0 := by
  obtain ⟨C,hC⟩ := approximate_parallelogram
  simp [canonicalHeight, QuadraticLimit.limit_zero naiveHeight C naiveHeight_zero hC]

lemma canonicalHeight_zsmul (P : E.Point) (n : ℤ) :
    canonicalHeight (n • P) = (n:ℝ)^2 * canonicalHeight P := by
  obtain ⟨C,hC⟩ := approximate_parallelogram
  unfold canonicalHeight
  rw [QuadraticLimit.limit_zsmul naiveHeight C naiveHeight_zero hC]
  ring

lemma canonicalHeight_nsmul (P : E.Point) (n : ℕ) :
    canonicalHeight (n • P) = (n:ℝ)^2 * canonicalHeight P := by
  simpa using canonicalHeight_zsmul P (n:ℤ)

theorem uniform_height : ∃ c : ℝ, 0 < c ∧ ∀ P : E.Point,
    |naiveHeight P - 2*canonicalHeight P| ≤ c := by
  obtain ⟨C,hC⟩ := approximate_parallelogram
  refine ⟨|C|/3+1, by positivity, ?_⟩
  intro P
  have hh := QuadraticLimit.error_bound naiveHeight C naiveHeight_zero hC P
  have he : 2*canonicalHeight P = QuadraticLimit.limit naiveHeight P := by
    unfold canonicalHeight
    ring
  rw [he]
  exact hh.trans (by linarith [le_abs_self C])

end SingleFold.CurveHeight

end OAI


