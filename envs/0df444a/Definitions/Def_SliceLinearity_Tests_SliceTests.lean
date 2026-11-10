-- Prove2me | Definitions.Def_SliceLinearity_Tests_SliceTests
-- name    : SliceLinearity_Tests_SliceTests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:37:14.112202+00:00
-- url     : https://prove2.me/theorems/fdfa0892-9ab9-42e9-a3b6-d4b6c5299544
-- title:
--   The Boolean cube $\mathbb F_2^n$, slices $S(w)$, affine maps, agreement and $k$-query parity tests
-- statement:
--   Throughout, $\mathbb F_2^n$ is the Boolean cube and $|x|$ is the number of nonzero coordinates of $x$.
--
--   1. The **slice** of weight $w$ is $S(w)=\{x\in\mathbb F_2^n : |x|=w\}$ (Definition 2.6).
--   2. A **linear map** is $x\mapsto\langle a,x\rangle=\sum_i a_ix_i$ and an **affine map** is $x\mapsto\langle a,x\rangle+c$ with $a\in\mathbb F_2^n$, $c\in\mathbb F_2$. In $\pm1$ notation these are the signed characters $\sigma\chi$.
--   3. The **agreement** of $f,g:\mathbb F_2^n\to\mathbb F_2$ on a finite set $S$ is $\mathrm{agr}_S(f,g)=\#\{x\in S: f(x)=g(x)\}/\#S$, the probability that they agree at a uniform point of $S$ (Definition 2.4). $\max_{\text{affine }\varphi}\mathrm{agr}_S(f,\varphi)$ is the best such agreement with an affine map.
--   4. A **$k$-query parity test on $S$** is a probability distribution on $k$-tuples $(x_1,\dots,x_k)\in S^k$ with $x_1+\dots+x_k=0$. It is fixed before the input, so it never depends on $f$. It queries $f$ at the sampled tuple and **accepts** when $\sum_i f(x_i)=0$ in $\mathbb F_2$ (equivalently $\prod_i(-1)^{f(x_i)}=1$). Repetitions among the $x_i$ are allowed.
--   5. A test is **perfectly complete** if it accepts every linear map with probability one.
--
--   **Formalization Note** The test is a structure carrying real weights on `Fin k → Cube n`, with a proof that they form a distribution on zero-sum tuples of $S^k$. `accW D f` is the acceptance probability for an arbitrary weight function $D$; it is also used for the conditioned and pivot tests. The input $f$ is total on $\mathbb F_2^n$, but only its values on $S$ are ever queried or measured.
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §1 p. 1 (PDF 3), §1.1 p. 2 (PDF 4), §2 pp. 8–10 (PDF 10–12): Definitions 2.4, 2.6; parity tests p. 2 and p. 32 (PDF 34)

import Mathlib

set_option autoImplicit false

namespace SliceLinearity.Tests

/-! # The Boolean cube, slices, affine maps, agreement and parity tests

Aydin, Larsen, Mittal, Richelson, Roy, *Low Soundness Linearity Testing on Subsets of the Hypercube*,
STOC 2027 submission (manuscript sha256 457be236…), §1 p. 1 (PDF 3), §1.1 p. 2 (PDF 4),
§2 pp. 8–10 (PDF 10–12, Definitions 2.4, 2.6), §5.2 p. 32 (PDF 34).

`Cube n` is `F₂ⁿ = Fin n → ZMod 2`. A k-query parity test on a set `S` is a probability
distribution on k-tuples of points of `S` whose sum is zero, fixed before the input `f`; it accepts
`f` when `∑ᵢ f(xᵢ) = 0` in `F₂`. -/

/-- The Boolean cube `F₂ⁿ`. -/
abbrev Cube (n : ℕ) : Type := Fin n → ZMod 2

/-- The Hamming weight `|x|`: the number of nonzero coordinates of `x` (Definition 2.6). -/
def hammingWeight {n : ℕ} (x : Cube n) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

/-- The slice `S(w) = {x ∈ F₂ⁿ : |x| = w}` (Definition 2.6). -/
def slice (n w : ℕ) : Finset (Cube n) :=
  Finset.univ.filter fun x => hammingWeight x = w

/-- The linear map `x ↦ ⟨a, x⟩ = ∑ᵢ aᵢ xᵢ` over `F₂`. -/
def linMap {n : ℕ} (a x : Cube n) : ZMod 2 :=
  ∑ i, a i * x i

/-- The affine map `x ↦ ⟨a, x⟩ + c` over `F₂`. -/
def affMap {n : ℕ} (a : Cube n) (c : ZMod 2) (x : Cube n) : ZMod 2 :=
  linMap a x + c

/-- Agreement on `S` under the uniform measure (Definition 2.4):
`agr_S(f, g) = #{x ∈ S : f x = g x} / #S`. -/
noncomputable def agreement {n : ℕ} (S : Finset (Cube n)) (f g : Cube n → ZMod 2) : ℝ :=
  ((S.filter fun x => f x = g x).card : ℝ) / (S.card : ℝ)

/-- The best agreement on `S` of `f` with an affine map `x ↦ ⟨a, x⟩ + c` (equivalently, with a
signed character `σχ`). -/
noncomputable def maxAffAgr {n : ℕ} (S : Finset (Cube n)) (f : Cube n → ZMod 2) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun ac : Cube n × ZMod 2 => agreement S f (affMap ac.1 ac.2)

/-- The acceptance probability of the parity test whose query tuples have weights `D`: the
`D`-mass of the tuples `t` with `∑ᵢ f(tᵢ) = 0`. -/
noncomputable def accW {n k : ℕ} (D : (Fin k → Cube n) → ℝ) (f : Cube n → ZMod 2) : ℝ :=
  ∑ t, D t * if ∑ i, f (t i) = 0 then 1 else 0

/-- `D` is (the query distribution of) a `k`-query parity test on `S`: nonnegative weights summing to
one, every tuple of positive weight lies in `S^k` and sums to zero (p. 2, p. 32). -/
def IsParityTestOn {n k : ℕ} (S : Finset (Cube n)) (D : (Fin k → Cube n) → ℝ) : Prop :=
  (∀ t, 0 ≤ D t) ∧ ∑ t, D t = 1 ∧ ∀ t, D t ≠ 0 → (∀ i, t i ∈ S) ∧ ∑ i, t i = 0

/-- A `k`-query parity test on `S ⊆ F₂ⁿ`: a distribution on zero-sum `k`-tuples of points of `S`,
fixed independently of the input. -/
structure ParityTest (n k : ℕ) (S : Finset (Cube n)) where
  /-- the query distribution -/
  dist : (Fin k → Cube n) → ℝ
  /-- it is a distribution on zero-sum tuples of `S^k` -/
  isTest : IsParityTestOn S dist

/-- `Pr[the test accepts f]`, the probability that `∑ᵢ f(xᵢ) = 0` for the sampled tuple. -/
noncomputable def ParityTest.accProb {n k : ℕ} {S : Finset (Cube n)} (T : ParityTest n k S)
    (f : Cube n → ZMod 2) : ℝ :=
  accW T.dist f

/-- Perfect completeness: every linear map is accepted with probability one (p. 1). -/
def ParityTest.PerfectlyComplete {n k : ℕ} {S : Finset (Cube n)} (T : ParityTest n k S) : Prop :=
  ∀ a : Cube n, T.accProb (linMap a) = 1

end SliceLinearity.Tests


