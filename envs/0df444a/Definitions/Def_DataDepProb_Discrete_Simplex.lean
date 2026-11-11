-- Prove2me | Definitions.Def_DataDepProb_Discrete_Simplex
-- name    : DataDepProb_Discrete_Simplex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:09:50.144368+00:00
-- url     : https://prove2.me/theorems/a981b613-6b68-4bc8-8160-61dfb21c4e66
-- title:
--   The simplex $\Delta_d$, the truncated simplex $\tilde\Delta_d$, $E_p[f]$, the empirical distribution, $\tilde D=(D+u)/2$, $e_s=(\hat D_s+u)/2$, the answer $2E_q[f]-E_u[f]$, and the laws of samples
-- statement:
--   The domain is $[d]=\{1,\dots,d\}$, encoded as $\{0,\dots,d-1\}$. A **distribution** on $[d]$ is a vector $D\in\mathbb R^d$ with $D(x)\ge0$ and $\sum_x D(x)=1$; their set is the **simplex** $\Delta_d$. The **truncated simplex** is
--   $$\tilde\Delta_d=\{q\in\Delta_d : q(x)\ge \tfrac1{2d}\ \text{for every } x\}.$$
--   For vectors $p,f$ write $E_p[f]=\sum_x p(x)f(x)$, and let $u$ be the uniform distribution, $u(x)=1/d$. For a sample $s=(s_1,\dots,s_n)\in[d]^n$ the **empirical distribution** is $\hat D_s(x)=n^{-1}\#\{i : s_i=x\}$. The **shifted target** is $\tilde D=(D+u)/2$ and the **initialization** is $e_s=(\hat D_s+u)/2$. The estimator's **answer** for a distribution $q$ and a query $f$ is $2E_q[f]-E_u[f]$.
--
--   The probability of a sample under $S\sim D^n$ is $D^n(s)=\prod_i D(s_i)$; $\|p-q\|_1=\sum_x|p(x)-q(x)|$. On a finite set, the measure $\sum_x w(x)\delta_x$ with weights $w$ is the law with probability vector $w$; the law of $S\sim D^n$ on $[d]^n$ is of this form.
--
--   **Formalization Note.** `Fin d` (0-based) encodes $[d]$; distributions are real vectors with explicit nonnegativity and normalization. Lean division gives $a/0=0$, so $\hat D_s$ is the zero vector when $n=0$; statements that use $e_s$ assume $n\ge1$. `finLaw` clips negative weights at $0$; it is only applied to probability vectors.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 8, §4.1; p. 11, §5 (∆̃_d, D̃, e_s); p. 12, Eq. (1)

import Mathlib

open MeasureTheory

namespace DataDepProb.Discrete

/-!
# The simplex, the truncated simplex, empirical distributions, and finite laws

Feldman, Kale, Majid, Talwar, *Data-Dependent Probability Estimation via Sample Amplification*,
STOC 2027 submission (manuscript sha256 28400f1c…), §4.1 p. 8 (notation), §5 pp. 11–12
(`∆̃_d`, `D̃`, `e_s`, Eq. (1)).

* The domain `[d] = {1, …, d}` is encoded as `Fin d = {0, …, d − 1}`; a sample `s ∈ [d]^n` is a
  function `Fin n → Fin d`.
* A distribution on `[d]` is a vector `D : Fin d → ℝ` with nonnegative entries summing to `1`.
* `finLaw w` is the measure `∑_x w(x) δ_x` on a finite type; for a distribution it is the law
  with probability vector `w`. All laws of samples are built this way, so they are explicit
  finite sums of Dirac masses.
-/

/-- The probability simplex `∆_d` on `[d]` (§4.1). -/
def simplex (d : ℕ) : Set (Fin d → ℝ) :=
  {p | (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1}

/-- The truncated simplex `∆̃_d = {q ∈ ∆_d | q(x) ≥ 1/(2d) for every x}` (§5, p. 11). -/
def truncSimplex (d : ℕ) : Set (Fin d → ℝ) :=
  {q | q ∈ simplex d ∧ ∀ x, 1 / (2 * (d : ℝ)) ≤ q x}

/-- The uniform distribution `u` on `[d]`. -/
noncomputable def unif (d : ℕ) : Fin d → ℝ :=
  fun _ => 1 / (d : ℝ)

/-- `E_p[f] = ∑_x p(x) f(x)` (§4.1). -/
noncomputable def expect {d : ℕ} (p f : Fin d → ℝ) : ℝ :=
  ∑ x, p x * f x

/-- The empirical distribution `D̂_s(x) = n⁻¹ ∑_i 1{s_i = x}` of a sample `s ∈ [d]^n` (§4.1). -/
noncomputable def empirical {n d : ℕ} (s : Fin n → Fin d) : Fin d → ℝ :=
  fun x => ((Finset.univ.filter fun i => s i = x).card : ℝ) / (n : ℝ)

/-- The shifted distribution `D̃ = (D + u)/2` (§5, p. 11). -/
noncomputable def shift {d : ℕ} (D : Fin d → ℝ) : Fin d → ℝ :=
  fun x => (D x + unif d x) / 2

/-- The initialization `e_s = (D̂_s + u)/2` (§5, p. 11). -/
noncomputable def eInit {n d : ℕ} (s : Fin n → Fin d) : Fin d → ℝ :=
  shift (empirical s)

/-- The answer `2E_q[f] − E_u[f]` returned by the estimator (§5, Eq. (1) and Algorithm 1). -/
noncomputable def answer {d : ℕ} (q f : Fin d → ℝ) : ℝ :=
  2 * expect q f - expect (unif d) f

/-- The probability `D^n(s) = ∏_i D(s_i)` of a sample `s ∈ [d]^n` under `S ∼ D^n`. -/
noncomputable def sampleProb {n d : ℕ} (D : Fin d → ℝ) (s : Fin n → Fin d) : ℝ :=
  ∏ i, D (s i)

/-- The `ℓ₁` distance `‖p − q‖₁ = ∑_x |p(x) − q(x)|`. -/
noncomputable def l1dist {d : ℕ} (p q : Fin d → ℝ) : ℝ :=
  ∑ x, |p x - q x|

/-- The measure `∑_x w(x) δ_x` on a finite type (weights clipped at `0`). For a probability
vector `w` this is the law with `P{x} = w(x)`. -/
noncomputable def finLaw {X : Type*} [Fintype X] [MeasurableSpace X] (w : X → ℝ) : Measure X :=
  ∑ x, ENNReal.ofReal (w x) • Measure.dirac x

/-- The law `D^n` of an i.i.d. sample `S = (X_1, …, X_n)`, `X_i ∼ D`, on `[d]^n`. -/
noncomputable def sampleLaw (n : ℕ) {d : ℕ} (D : Fin d → ℝ) : Measure (Fin n → Fin d) :=
  finLaw (sampleProb D)

end DataDepProb.Discrete


