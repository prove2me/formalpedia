-- Prove2me | Definitions.Def_ShamirLLR_leakageLaws
-- name    : ShamirLLR_leakageLaws
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:59.352624+00:00
-- url     : https://prove2.me/theorems/8c662881-51ef-4bab-9371-c57f862ab6db
-- title:
--   Moment forms $L_i$, kernels $K_f$ and the two leakage experiments
-- statement:
--   Fix places $a=(a_i)_{i\in\iota}$ in $\mathbb F_p$ and $r\ge 1$. The **moment linear forms** evaluate the polynomial with coefficient vector $x=(x_0,\dots,x_{r-1})\in\mathbb F_p^r$:
--   $$
--   L_i(x)=\sum_{h=0}^{r-1}x_h a_i^h .
--   $$
--   A **probability map** is $f:\mathbb F_p\to[0,1]$; on input $z$ it outputs $1$ with probability $f(z)$, with kernel $K_f(1\mid z)=f(z)$, $K_f(0\mid z)=1-f(z)$. A one-bit leakage function $f:\mathbb F_p\to\{0,1\}$ is the probability map with values in $\{0,1\}$. For maps $f=(f_i)_i$ and an output profile $y\in\{0,1\}^\iota$, the **codeword experiment** and the **independent-input experiment** are
--   $$
--   P_{a,f}(y)=\mathbb E_{x\in\mathbb F_p^r}\prod_i K_{f_i}(y_i\mid L_i(x)),\qquad Q_f(y)=\prod_i\mathbb E_{z\in\mathbb F_p}K_{f_i}(y_i\mid z),
--   $$
--   the laws of the leaked bits on a uniform Reed–Solomon codeword of $C_r(a)$ and on independent uniform inputs; output bits are independent given their inputs.
--
--   These are the two laws whose statistical distance is the codeword versus independent-input comparison.
--
--   **Formalization Note** Bits are `Bool` (`true` for $1$). The index set $\iota$ is an arbitrary finite type. Averaging over $x\in\mathbb F_p^r$ is averaging over polynomials of degree less than $r$.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), §1.1, p.2; §1.2, p.5; §2, Eq. (7), p.13; Eq. (12), p.15 (PDF pp.3, 6, 14, 16)

import Mathlib

set_option autoImplicit false

namespace ShamirLLR

/-- The moment linear form `L_i(x) = ∑_{h=0}^{r-1} x_h a_i^h` evaluating at the place `a_i` the
polynomial with coefficient vector `x = (x₀, …, x_{r-1}) ∈ 𝔽_p^r`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
§1.1, p.2; Eq. (12), p.15.

**Formalization Note.** The index set `ι` of the places is an arbitrary type, so that the
shortened tuple `a_{J^c}` of Lemma 2.1 is the restriction of `a` to `{i // i ∉ J}`. -/
def momentForm {p : ℕ} {ι : Type*} (a : ι → ZMod p) (r : ℕ) (i : ι) (x : Fin r → ZMod p) :
    ZMod p :=
  ∑ h : Fin r, x h * a i ^ (h : ℕ)

/-- A probability map `f : 𝔽_p → [0, 1]` (§1.2, p.5; §2, p.13): on input `z` it outputs the bit
`1` with probability `f z`. -/
def IsProbMap {p : ℕ} (f : ZMod p → ℝ) : Prop :=
  ∀ z, 0 ≤ f z ∧ f z ≤ 1

/-- The output kernel `K_f(1 | z) = f(z)`, `K_f(0 | z) = 1 − f(z)` of a probability map
(§2, p.13). **Formalization Note.** Output bits are `Bool`, with `true` for `1`. -/
def kern {p : ℕ} (f : ZMod p → ℝ) (y : Bool) (z : ZMod p) : ℝ :=
  if y then f z else 1 - f z

/-- A one-bit leakage function `f : 𝔽_p → {0, 1}` viewed as the probability map with values
`0` and `1` ("The original deterministic leakage functions are exactly the maps taking values in
{0, 1}", p.5). -/
def bitMap {p : ℕ} (f : ZMod p → Bool) : ZMod p → ℝ :=
  fun z => if f z then 1 else 0

/-- The codeword experiment of Eq. (7), p.13: the probability that the leaked bits equal
`y ∈ {0,1}^ι` when the inputs are a uniform codeword `(L_i(x))_i` of the Reed–Solomon code
`C_r(a)`, `x` uniform in `𝔽_p^r`, and the output bits are independent given their inputs:
`P_{a,f}(y) = 𝔼_x ∏_i K_{f_i}(y_i | L_i(x))`.

**Formalization Note.** "Averaging over x ∈ 𝔽_p^r is the same as averaging over polynomials P"
(p.16), so the uniform polynomial of degree `< r` is its coefficient vector. -/
noncomputable def codeLaw {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι] (a : ι → ZMod p) (r : ℕ)
    (f : ι → ZMod p → ℝ) (y : ι → Bool) : ℝ :=
  ((p : ℝ) ^ r)⁻¹ * ∑ x : Fin r → ZMod p, ∏ i, kern (f i) (y i) (momentForm a r i x)

/-- The independent-input experiment of Eq. (7), p.13: the probability that the leaked bits equal
`y` when the inputs `U_i` are independent and uniform in `𝔽_p`:
`Q_f(y) = 𝔼_U ∏_i K_{f_i}(y_i | U_i) = ∏_i 𝔼_{z} K_{f_i}(y_i | z)`. -/
noncomputable def indepLaw {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι] (f : ι → ZMod p → ℝ)
    (y : ι → Bool) : ℝ :=
  ∏ i, ((p : ℝ)⁻¹ * ∑ z : ZMod p, kern (f i) (y i) z)

end ShamirLLR


