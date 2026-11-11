-- Prove2me | Definitions.Def_QaryCVP_qaryLattice
-- name    : QaryCVP_qaryLattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:58:18.258198+00:00
-- url     : https://prove2.me/theorems/7b0c62b4-b0d0-4fd3-b13b-62754d4aedf4
-- title:
--   The q-ary lattice $\Lambda$, squared distances, $\gamma$-CVP, rounding and the density tests
-- statement:
--   For integers $q\ge2$, $m\ge0$, $n\ge1$ and a matrix $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$, the **q-ary lattice** of $H$ is
--
--   $$\Lambda=\{x\in\mathbb Z^n:\ Hx\equiv 0_m \pmod q\}.$$
--
--   For $x\in\mathbb Z^n$ and $y\in\mathbb Q^n$ write $\|x-y\|^2=\sum_i (x_i-y_i)^2$. A vector $x$ solves **$\gamma$-CVP** for $(H,y)$ if $x\in\Lambda$ and $\|x-y\|\le\gamma\min_{a\in\Lambda}\|a-y\|$ (Definition 2.6); $x$ is a **closest point** if this holds with $\gamma=1$. Rounding is $\lfloor y\rceil=\lfloor y+1/2\rfloor$, coordinatewise on vectors.
--
--   The **density** is $\delta=m\log_2 q/n$. The two density ranges of the paper are tested exactly: $\delta\le1$ iff $q^m\le2^n$, and $\delta\le3/2$ iff $q^{2m}\le2^{3n}$.
--
--   The module also records the output specification of an exact ball search (Definition 3.4): for $b\in\mathbb Q_{\ge0}$, return a vector of minimum distance from $y$ in $\{x\in\Lambda:\|x-y\|^2\le b\}$, or $\bot$ exactly when this set is empty (optionally restricted to nonzero $x$), and the count $|B|=\sum_{j\le\lfloor\beta n_0\rfloor}\binom{n_0}{j}$ of binary vectors of weight at most $\lfloor\beta n_0\rfloor$ (Lemma 4.2).
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** The approximation is stated squared, against every $a\in\Lambda$: $\|x-y\|^2\le\gamma^2\|a-y\|^2$. The minimum exists since $\Lambda\supseteq q\mathbb Z^n$ is discrete, so this is the same condition. The congruence is computed in $\mathbb Z/q\mathbb Z$; for $m=0$, $\Lambda=\mathbb Z^n$.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), §2.1, p.12; §2.3 and Definition 2.6, p.14; Definition 3.4, p.24; Lemma 4.2, p.35; density tests p.35

import Mathlib

namespace QaryCVP

/-- The q-ary lattice of `H ∈ (Z/qZ)^{m×n}` (§2.3, p.14):
`Λ = {x ∈ Zⁿ : Hx ≡ 0_m (mod q)}`.
Kim, Kwon, Lee, Lee, *Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary
Lattices*, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), §2.3, p.14.

**Formalization Note.** The congruence is computed in `ZMod q` after casting each integer
coordinate. For `m = 0` the matrix is empty and `Λ = Zⁿ`. -/
def qaryLattice {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) : Set (Fin n → ℤ) :=
  {x | H.mulVec (fun j => (x j : ZMod q)) = 0}

/-- Squared Euclidean distance `‖x − y‖²` between an integer vector and a rational vector
(§2.1, p.12: `‖x‖ = (Σ xᵢ²)^{1/2}`). -/
def sqDist {n : ℕ} (x : Fin n → ℤ) (y : Fin n → ℚ) : ℚ :=
  ∑ i, ((x i : ℚ) - y i) ^ 2

/-- Squared Euclidean norm of an integer vector. -/
def sqNormZ {n : ℕ} (x : Fin n → ℤ) : ℚ :=
  ∑ i, ((x i : ℚ)) ^ 2

/-- `x` is a closest point of `Λ` to `y` (the output specification of Lemma 4.1, p.35). -/
def IsClosest {m n q : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ)
    (x : Fin n → ℤ) : Prop :=
  x ∈ qaryLattice H ∧ ∀ a ∈ qaryLattice H, sqDist x y ≤ sqDist a y

/-- γ-CVP (Definition 2.6, p.14): `x ∈ Λ` and `‖x − y‖ ≤ γ min_{a∈Λ} ‖a − y‖`.

**Formalization Note.** The inequality is stated squared, for every `a ∈ Λ`:
`‖x − y‖² ≤ γ² ‖a − y‖²`. The minimum exists because `Λ ⊇ qZⁿ` is discrete, so for `γ > 0`
this is the same condition. -/
def IsApproxCVP {m n q : ℕ} (γ : ℚ) (H : Matrix (Fin m) (Fin n) (ZMod q)) (y : Fin n → ℚ)
    (x : Fin n → ℤ) : Prop :=
  x ∈ qaryLattice H ∧ ∀ a ∈ qaryLattice H, sqDist x y ≤ γ ^ 2 * sqDist a y

/-- Rounding `⌊y⌉ = ⌊y + 1/2⌋` (§2.1, p.12). -/
def roundQ (y : ℚ) : ℤ := ⌊y + 1 / 2⌋

/-- Coordinatewise rounding `⌊y⌉ ∈ Zⁿ` (§2.1, p.12). -/
def roundVec {n : ℕ} (y : Fin n → ℚ) : Fin n → ℤ := fun i => roundQ (y i)

/-- Density at most one, `δ = m log₂ q / n ≤ 1`, tested exactly as `qᵐ ≤ 2ⁿ` (p.35: "the test
`qᵐ ≤ 2ⁿ` selects the parameter range"). -/
def DensityLeOne (q m n : ℕ) : Prop := q ^ m ≤ 2 ^ n

/-- Density at most three halves, `δ ≤ 3/2`, tested exactly as `q^{2m} ≤ 2^{3n}`. -/
def DensityLeThreeHalves (q m n : ℕ) : Prop := q ^ (2 * m) ≤ 2 ^ (3 * n)

/-- The density `δ = m log₂ q / n` as a real number (§1, p.1; §2.3). For `n = 0` it is `0`
(junk; every statement using it has `n ≥ 1`). -/
noncomputable def density (q m n : ℕ) : ℝ := (m : ℝ) * Real.logb 2 q / n

/-- The output specification of an exact ball search (Definition 3.4, p.24), for the solutions
satisfying an extra predicate `Q` (`Q = True` for `E_τ`; `Q x = (x ≠ 0)` for the nonzero variant
`E^{≠0}_τ` of p.27): `o = none` (`⊥`) exactly when no `x ∈ Λ` with `Q x` has `‖x − y‖² ≤ b`, and a
returned `x` is such a solution of minimum distance from `y`. -/
def IsSearchOutput {m n q : ℕ} (Q : (Fin n → ℤ) → Prop) (H : Matrix (Fin m) (Fin n) (ZMod q))
    (y : Fin n → ℚ) (b : ℚ) (o : Option (Fin n → ℤ)) : Prop :=
  (o = none ↔ ¬ ∃ x ∈ qaryLattice H, Q x ∧ sqDist x y ≤ b) ∧
    ∀ x, o = some x → x ∈ qaryLattice H ∧ Q x ∧ sqDist x y ≤ b ∧
      ∀ a ∈ qaryLattice H, Q a → sqDist a y ≤ b → sqDist x y ≤ sqDist a y

/-- `|B| = Σ_{j ≤ ⌊βn₀⌋} C(n₀, j)`, the number of binary vectors of length `n₀` and weight at
most `⌊βn₀⌋` (Lemma 4.2, p.35). -/
noncomputable def ballCard (n0 : ℕ) (β : ℚ) : ℕ :=
  ∑ j ∈ Finset.range (⌊β * n0⌋₊ + 1), n0.choose j

end QaryCVP


