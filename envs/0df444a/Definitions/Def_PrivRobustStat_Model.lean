-- Prove2me | Definitions.Def_PrivRobustStat_Model
-- name    : PrivRobustStat_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:15.67224+00:00
-- url     : https://prove2.me/theorems/6faf0bad-36c5-4514-a2c6-5115385490a2
-- title:
--   Points, weights, $\hat\mu(w)$, $\hat\Sigma(w,c)$, the potential $\Psi$, Model 1 and the adversary
-- statement:
--   Points live in $\mathbb R^d$ with the Euclidean norm $\|\cdot\|_2$, and datasets are $x_{[n]}=(x_1,\dots,x_n)$ (0-based in Lean). For a weight vector $w\in\mathbb R^n$ write $\|w\|_1=\sum_i|w_i|$ and, for $I\subseteq[n]$, $w_I$ for the vector that agrees with $w$ on $I$ and vanishes elsewhere. The weights of the paper lie in
--
--   $$\mathcal W=\{w\in[0,\tfrac1n]^n:\ w\neq0_n\}.$$
--
--   For $w\in\mathcal W$ and a centre $c\in\mathbb R^d$, the **weighted mean** and the **unnormalized covariance** of (8) are
--
--   $$\hat\mu(w)=\frac{\sum_i w_ix_i}{\|w\|_1},\qquad \hat\Sigma(w,c)=\sum_i w_i(x_i-c)(x_i-c)^\top,$$
--
--   and $\hat\Sigma(w):=\hat\Sigma(w,\hat\mu(w))$. With $p=\lceil\log_2(2d)\rceil$ and $q=2p+1$, the **potential** with a fixed public centre $c$ is $\Psi(w)=\operatorname{Tr}(\hat\Sigma(w,c)^q)$ (10). The total variation distance of normalized weights is $\mathrm{TV}(v/\|v\|_1,w/\|w\|_1)=\tfrac12\sum_i|v_i/\|v\|_1-w_i/\|w\|_1|$.
--
--   **Model 1** (bounded covariance): a probability distribution $D$ on $\mathbb R^d$ with finite second moment, mean $\mu=\mathbb E_D[x]$ and covariance $\Sigma\preceq I$, i.e. $\mathbb E_D\langle u,x-\mu\rangle^2\le\|u\|_2^2$ for all $u$. An **adversary** (Definition 1) is any map $A:(\mathbb R^d)^n\to(\mathbb R^d)^n$ that changes at most $\alpha n$ coordinates of every dataset. The module also fixes the Frobenius norm, the Euclidean projection onto a ball $B(q,R)$, and the recursion $\Gamma_0=I$, $\Gamma_j=A_j\Gamma_{j-1}A_j+\eta_jI$ of (14).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\hat\Sigma$ has no division by $\|w\|_1$, as in (8). Model 1 asks for `MemLp id 2`: without it Lean's integral of a non-integrable function is $0$ and $\Sigma\preceq I$ would hold vacuously. The adversary need not be measurable. The projection is written explicitly, $\Pi_{B(q,R)}(y)=y$ if $\|y-q\|\le R$ and $q+\frac{R}{\|y-q\|}(y-q)$ otherwise.
-- source:
--   Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, Efficient Private and Robust Statistics, STOC 2027 submission (manuscript sha256 1a69e17a…), §2.1 notation, p.10; Definition 1, p.11; (8), p.12; Model 1, p.14; (10), p.15; (14), p.19

import Mathlib

open MeasureTheory

namespace PrivRobustStat

/-!
# Points, weights, weighted means and covariances, Model 1, and the adversary

Gu, Jambulapati, Kumar, Mouzakis, Tian, Yang, *Efficient Private and Robust Statistics*, STOC 2027
submission (manuscript sha256 1a69e17a…): notation of §2.1, p.10; Definition 1, p.11; the set `W`
and display (8), p.12; Model 1, p.14; (10), p.15.

**Formalization Note.**
* Points live in `EuclideanSpace ℝ (Fin d)`, so `‖·‖` is the Euclidean norm `‖·‖₂` (Mathlib's norm
  on `Fin d → ℝ` is the sup norm and is never used).
* Indices are 0-based: the paper's `[n] = {1, …, n}` is `Fin n`.
* `Σ̂(w, c)` is unnormalized, as in (8): no division by `‖w‖₁`.
* `A ⪯ B` is `(B − A).PosSemidef`.
* `µ̂(w)` divides by `‖w‖₁`; on `w = 0` Lean returns `0`, and `W` excludes `w = 0`.
-/

/-- A point of `ℝ^d` with the Euclidean norm. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The rank-one matrix `v v⊤`. -/
def outer {d : ℕ} (v : Vec d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.vecMulVec (fun a => v a) (fun a => v a)

/-- `‖w‖₁ = ∑ᵢ |wᵢ|`. -/
def l1 {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i, |w i|

/-- `w_I`: agrees with `w` on `I` and is zero elsewhere (§2.1, p.10). -/
def restrict {n : ℕ} (w : Fin n → ℝ) (I : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ I then w i else 0

/-- `w ∈ [0, 1/n]^n` (the internal weights of Algorithms 1–4, 7). -/
def InBox (n : ℕ) (w : Fin n → ℝ) : Prop := ∀ i, 0 ≤ w i ∧ w i ≤ 1 / (n : ℝ)

/-- `W := {w ∈ [0, 1/n]^n : w ≠ 0_n}` (p.12). -/
def InW (n : ℕ) (w : Fin n → ℝ) : Prop := InBox n w ∧ w ≠ 0

/-- The weighted mean `µ̂(w) := ∑ᵢ wᵢ xᵢ / ‖w‖₁` of (8). -/
noncomputable def wMean {d n : ℕ} (x : Fin n → Vec d) (w : Fin n → ℝ) : Vec d :=
  (l1 w)⁻¹ • ∑ i, w i • x i

/-- The unnormalized covariance `Σ̂(w, c) := ∑ᵢ wᵢ (xᵢ − c)(xᵢ − c)⊤` of (8). -/
noncomputable def covC {d n : ℕ} (x : Fin n → Vec d) (w : Fin n → ℝ) (c : Vec d) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ i, w i • outer (x i - c)

/-- `Σ̂(w) := Σ̂(w, µ̂(w))`, the default centre (p.12). -/
noncomputable def cov {d n : ℕ} (x : Fin n → Vec d) (w : Fin n → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  covC x w (wMean x w)

/-- `TV(v/‖v‖₁, w/‖w‖₁) = ½ ∑ᵢ |vᵢ/‖v‖₁ − wᵢ/‖w‖₁|`, the total variation distance of the normalized
weight vectors on the finite domain `[n]` (p.10). -/
noncomputable def tvW {n : ℕ} (v w : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, |v i / l1 v - w i / l1 w|

/-- The replay depth `p := ⌈log₂(2d)⌉` of Algorithm 1, Line 1. -/
def pDepth (d : ℕ) : ℕ := Nat.clog 2 (2 * d)

/-- The potential exponent `q := 2⌈log₂(2d)⌉ + 1` of (10). -/
def qExp (d : ℕ) : ℕ := 2 * pDepth d + 1

/-- The potential `Ψ(w) := Tr(Σ̂(w, c)^q)` of (10), with the fixed public centre `c` of §3. -/
noncomputable def potential {d n : ℕ} (x : Fin n → Vec d) (c : Vec d) (w : Fin n → ℝ) : ℝ :=
  Matrix.trace (covC x w c ^ qExp d)

/-- The population mean `µ := E_{x∼D}[x]` (Bochner integral). -/
noncomputable def popMean {d : ℕ} (D : Measure (Vec d)) : Vec d := ∫ x, x ∂D

/-- Model 1 (p.14) for a distribution `D` on `ℝ^d` (a probability measure, supplied as an instance
where it is used): `D` has finite second moment, mean `µ` and covariance `Σ ⪯ I`, i.e.
`E⟨u, x − µ⟩² ≤ ‖u‖²` for all `u`. The finite second moment (`MemLp id 2`) is the condition under
which the mean and covariance exist; without it Lean's integral of a non-integrable function is `0`
and the covariance bound would hold vacuously. -/
def IsModel1 {d : ℕ} (D : Measure (Vec d)) : Prop :=
  MemLp id 2 D ∧ ∀ u : Vec d, ∫ x, (inner ℝ u (x - popMean D)) ^ 2 ∂D ≤ ‖u‖ ^ 2

/-- An adversary of Definition 1 (p.11): after inspecting the whole sample `X`, it replaces at most
`αn` points. Any map, measurable or not. -/
def IsAdversary {d n : ℕ} (α : ℝ) (A : (Fin n → Vec d) → (Fin n → Vec d)) : Prop :=
  ∀ X, ((Finset.univ.filter fun i => A X i ≠ X i).card : ℝ) ≤ α * n

/-- The Frobenius norm `‖Z‖_F = (∑ Z_{ab}²)^{1/2}`. -/
noncomputable def frob {d r : ℕ} (Z : Matrix (Fin d) (Fin r) ℝ) : ℝ :=
  Real.sqrt (∑ a, ∑ b, Z a b ^ 2)

/-- The projection `Π_{B(q, R)}` onto the Euclidean ball `B(q, R) = {y : ‖y − q‖₂ ≤ R}`, written
explicitly: `y` if `‖y − q‖ ≤ R`, else `q + (R/‖y − q‖)(y − q)`. -/
noncomputable def projBall {d : ℕ} (q : Vec d) (R : ℝ) (y : Vec d) : Vec d :=
  if ‖y - q‖ ≤ R then y else q + (R / ‖y - q‖) • (y - q)

/-- The recursion `Γ₀ := I`, `Γ_j := A_j Γ_{j−1} A_j + η_j I` of (14) (p.19), Lemma 11 and Lemma 12
(p.25), with the paper's 1-based indices: `A j` and `η j` are used for `j ≥ 1`. -/
noncomputable def gammaSeq {d : ℕ} (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (η : ℕ → ℝ) :
    ℕ → Matrix (Fin d) (Fin d) ℝ
  | 0 => 1
  | j + 1 => A (j + 1) * gammaSeq A η j * A (j + 1) + η (j + 1) • (1 : Matrix (Fin d) (Fin d) ℝ)

end PrivRobustStat


