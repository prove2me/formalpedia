-- Prove2me | Definitions.Def_LpBallVI_Affine_Geometry
-- name    : LpBallVI_Affine_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:10:09.060043+00:00
-- url     : https://prove2.me/theorems/aad37ce2-2a05-413f-8129-a1dce489e309
-- title:
--   Inner product, Euclidean and ℓp norms, ℓp balls, the VI gap, the duality map J_p, the support point S_R and the constants r_p, µ_p, C_p, θ_p
-- statement:
--   For a finite index set $\iota$ and $x, y \in \mathbb R^\iota$, $\langle x, y\rangle = \sum_i x_i y_i$ and $\|x\| = (\sum_i x_i^2)^{1/2}$ (the Euclidean norm). For a real exponent $p$, $\|x\|_p = (\sum_i |x_i|^p)^{1/p}$ (real powers), and $\|x\|_\infty = \max_i |x_i|$. An **exponent of the problem** is a rational $p$ or $p = \infty$; $B_p = \{x : \|x\|_p \le 1\}$ is its unit ball and, for real $p$ and $R$, $B_p(R) = \{x : \|x\|_p \le R\}$.
--
--   For a set $K$, an operator $F : \mathbb R^\iota \to \mathbb R^\iota$ and a point $x$, the **VI gap is at most $\varepsilon$** when
--   $$\operatorname{Gap}_K(x;F) = \max_{x' \in K} \langle x' - x, F(x)\rangle \le \varepsilon,$$
--   written as $\langle x' - x, F(x)\rangle \le \varepsilon$ for every $x' \in K$ (maximization convention of Definition 2.1).
--
--   For $1 < p < \infty$: the dual exponent $q = p/(p-1)$; the duality map $J_p(z)_i = |z_i|^{p-2} z_i$; the support point $S_R(z) = R\,J_q(z)/\|z\|_q^{q-1}$; and the constants of (8): $r_p = 2$, $\mu_p = (p-1)/2$, $C_p = 2^{2-p}$ for $p \le 2$; $r_p = p$, $\mu_p = 2^{2-p}/p$, $C_p = p - 1$ for $p > 2$; $\theta_p = \min\{1, p-1\}$.
--
--   **Formalization Note** The gap is the $\forall$-form, which equals the max form for nonempty compact $K$ (every ball here). $\|\cdot\|_p$ uses `Real.rpow`; $J_p(z)_i = 0$ when $z_i = 0$.
-- source:
--   Anagnostides, Panageas, Yan, On the Role of Geometry in Solving Variational Inequalities, arXiv:2611.04151 (held copy, sha256 a3f8212d…0a5cbe), p. 4; p. 12; p. 13, Definition 2.1; p. 15, (5) and the duality map; p. 16, (8) and Lemma 3.4

import Mathlib

set_option autoImplicit false

namespace LpBallVI.Affine

open scoped BigOperators

/-- The Euclidean inner product `⟨x, y⟩ = ∑ᵢ xᵢ yᵢ` on `ℝ^ι` (Anagnostides–Panageas–Yan, *On the
Role of Geometry in Solving Variational Inequalities*, arXiv:2611.04151, §2, p. 12–13). -/
def dot {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ := ∑ i, x i * y i

/-- The Euclidean norm `‖x‖ = (∑ᵢ xᵢ²)^{1/2}` ("An unsubscripted norm denotes the Euclidean
norm", p. 12). -/
noncomputable def eucNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- The `ℓp` norm `‖x‖_p = (∑ᵢ |xᵢ|^p)^{1/p}` for a real exponent `p` (p. 12), with real powers
(`Real.rpow`). It is the `ℓp` norm for `p ≥ 1`. -/
noncomputable def lpNorm {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

/-- The max norm `‖x‖_∞ = maxᵢ |xᵢ|` (p. 12); `0` on the empty index type. -/
noncomputable def supNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ⨆ i, |x i|

/-- An exponent of the problem `Ballp-VI`: a rational `p` (`fin p`), or `p = ∞` (`infty`)
(p. 4: "For a parameter p ≥ 1, or p = ∞"). -/
inductive Exponent where
  | fin (p : ℚ)
  | infty

/-- `‖x‖_p` for an exponent of the problem: `lpNorm p` for a rational `p`, `supNorm` for `∞`. -/
noncomputable def Exponent.norm {ι : Type*} [Fintype ι] : Exponent → (ι → ℝ) → ℝ
  | .fin p, x => lpNorm (p : ℝ) x
  | .infty, x => supNorm x

/-- The ball `B_p(R) = {x : ‖x‖_p ≤ R}` for a real exponent `p` (p. 12). -/
def ball {ι : Type*} [Fintype ι] (p R : ℝ) : Set (ι → ℝ) := {x | lpNorm p x ≤ R}

/-- The unit ball `B_p = {x : ‖x‖_p ≤ 1}` for an exponent of the problem, `p` rational or `∞`
(p. 4). -/
def Exponent.unitBall {ι : Type*} [Fintype ι] (p : Exponent) : Set (ι → ℝ) :=
  {x | p.norm x ≤ 1}

/-- **VI gap at most `ε`** (Definition 2.1, p. 13): `Gap_K(x; F) = max_{x' ∈ K} ⟨x' − x, F(x)⟩ ≤ ε`,
written as `⟨x' − x, F(x)⟩ ≤ ε` for every `x' ∈ K` (maximization convention). For a nonempty
compact `K` the maximum exists and the two statements agree. -/
def GapLE {ι : Type*} [Fintype ι] (K : Set (ι → ℝ)) (F : (ι → ℝ) → ι → ℝ) (x : ι → ℝ)
    (ε : ℝ) : Prop :=
  ∀ x' ∈ K, dot (x' - x) (F x) ≤ ε

/-- The dual exponent `q = p / (p − 1)` of `1 < p < ∞` (p. 12). -/
noncomputable def dualExp (p : ℝ) : ℝ := p / (p - 1)

/-- The duality map `J_p(z)ᵢ = |zᵢ|^{p−2} zᵢ` (§3, p. 15); `J_p(z)ᵢ = 0` when `zᵢ = 0`. -/
noncomputable def dualityMap {ι : Type*} (p : ℝ) (z : ι → ℝ) : ι → ℝ :=
  fun i => |z i| ^ (p - 2) * z i

/-- The support point `S_R(z) = R J_q(z) / ‖z‖_q^{q−1}`, `q = p/(p−1)` (Lemma 3.1, (5), p. 15),
for `z ≠ 0`. -/
noncomputable def supportPt {ι : Type*} [Fintype ι] (p R : ℝ) (z : ι → ℝ) : ι → ℝ :=
  fun i => R * dualityMap (dualExp p) z i / lpNorm (dualExp p) z ^ (dualExp p - 1)

/-- `r_p` of (8), p. 16: `2` for `1 < p ≤ 2`, `p` for `p > 2`. -/
noncomputable def rP (p : ℝ) : ℝ := if p ≤ 2 then 2 else p

/-- `µ_p` of (8), p. 16: `(p − 1)/2` for `1 < p ≤ 2`, `2^{2−p}/p` for `p > 2`. -/
noncomputable def muP (p : ℝ) : ℝ := if p ≤ 2 then (p - 1) / 2 else (2 : ℝ) ^ (2 - p) / p

/-- `C_p` of (8), p. 16: `2^{2−p}` for `1 < p ≤ 2`, `p − 1` for `p > 2`. -/
noncomputable def CP (p : ℝ) : ℝ := if p ≤ 2 then (2 : ℝ) ^ (2 - p) else p - 1

/-- `θ_p = min{1, p − 1}` (Lemma 3.4, p. 16). -/
noncomputable def thetaP (p : ℝ) : ℝ := min 1 (p - 1)

end LpBallVI.Affine


