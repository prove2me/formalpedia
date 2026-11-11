-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_ConvexGeometry
-- name    : MixedVolFPRAS_Main_ConvexGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:28:49.965969+00:00
-- url     : https://prove2.me/theorems/6c1b1385-cfd3-47de-b067-6a2a22b04f4a
-- title:
--   Convex bodies, support functions, Minkowski sums and the ε-neighbourhood / ε-interior in ℝⁿ
-- statement:
--   Work in $\mathbb{R}^n$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|_2$. Write $B_2^n=\{x:\|x\|_2\le 1\}$ for the closed unit ball and $S^{n-1}=\{x:\|x\|_2=1\}$ for the unit sphere. A **convex body** is a compact convex set $K\subseteq\mathbb{R}^n$ with nonempty interior. $\mathrm{Vol}_n(K)$ is the Lebesgue measure of $K$. For finitely many sets $K_i$ ($i\in S$) the **Minkowski sum** is $\sum_{i\in S}K_i=\{\sum_{i\in S}v_i: v_i\in K_i\}$, and $tA=\{ta:a\in A\}$. The **support function** of a nonempty compact set $K$ is
--
--   $$h_K(x)=\sup_{z\in K}\langle x,z\rangle .$$
--
--   For a convex body $K$ and $\varepsilon>0$, the **$\varepsilon$-neighbourhood** and the **$\varepsilon$-interior** of Definition 1.1 are
--
--   $$K(\varepsilon)=K+\varepsilon B_2^n,\qquad K(-\varepsilon)=\mathbb{R}^n\setminus\big((\mathbb{R}^n\setminus K)+\varepsilon B_2^n\big).$$
--
--   These are the basic objects of the whole mission: every body is a convex body, every oracle answer is certified by membership in $K(\varepsilon)$ or non-membership in $K(-\varepsilon)$.
--
--   **Formalization Note.** `E n` is `EuclideanSpace ℝ (Fin n)`; `unitBall n` and `unitSphere n` are `Metric.closedBall 0 1` and `Metric.sphere 0 1`. `vol K` is `(volume K).toReal`. `supportFunction K x` is the real supremum `⨆ z : K, ⟪x, z⟫` (it is only used for nonempty compact `K`, where it is the true supremum). `minkowskiSum S K` is the Minkowski sum of a finite family (`{0}` for the empty family). `epsNbhd K ε` and `epsInterior K ε` are $K(\varepsilon)$ and $K(-\varepsilon)$ with pointwise set operations.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 2, Definition 1.1; p. 8, §2.1 (notation); p. 9 (convex geometry)

import Mathlib

open scoped Pointwise

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# Convex bodies, support functions and ε-neighbourhoods in ℝⁿ

Chen, Liu, *An FPRAS for Mixed Volumes*, STOC 2027 submission, p. 2 (Eq. (1), Definition 1.1),
p. 8 (notation) and p. 9 (convex geometry).

* `E n` is ℝⁿ with the Euclidean inner product and norm.
* `unitBall n` is the closed unit Euclidean ball `B₂ⁿ`; `unitSphere n` is `Sⁿ⁻¹`.
* A convex body is a compact convex set with nonempty interior.
* `vol K` is the Lebesgue volume `Volₙ(K)` (as a real number; finite on bounded sets).
* `supportFunction K x = sup_{z ∈ K} ⟨x, z⟩`, used for nonempty compact `K`.
* `minkowskiSum S K` is the Minkowski sum `∑_{i ∈ S} K i = {∑_{i∈S} v i : v i ∈ K i}`
  (the set `{0}` when `S = ∅`).
* `epsNbhd K ε = K + ε B₂ⁿ` is `K(ε)` and `epsInterior K ε = ℝⁿ \ ((ℝⁿ \ K) + ε B₂ⁿ)` is `K(−ε)`.
-/

/-- Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- The closed unit Euclidean ball `B₂ⁿ`. -/
def unitBall (n : ℕ) : Set (E n) := Metric.closedBall 0 1

/-- The unit Euclidean sphere `Sⁿ⁻¹`. -/
def unitSphere (n : ℕ) : Set (E n) := Metric.sphere 0 1

/-- A convex body: a compact convex set with nonempty interior (p. 9). -/
def IsConvexBody {n : ℕ} (K : Set (E n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- `Volₙ(K)`: Lebesgue measure on `ℝⁿ`, as a real number. -/
def vol {n : ℕ} (K : Set (E n)) : ℝ := (MeasureTheory.volume K).toReal

/-- The support function `h_K(x) = sup_{z ∈ K} ⟨x, z⟩` (p. 9). -/
def supportFunction {n : ℕ} (K : Set (E n)) (x : E n) : ℝ :=
  ⨆ z : K, inner ℝ x (z : E n)

/-- The Minkowski sum `∑_{i ∈ S} K i` of a finite family of sets. -/
def minkowskiSum {n : ℕ} {ι : Type} (S : Finset ι) (K : ι → Set (E n)) : Set (E n) :=
  {x | ∃ v : ι → E n, (∀ i ∈ S, v i ∈ K i) ∧ x = ∑ i ∈ S, v i}

/-- `K(ε) = K + ε B₂ⁿ` (Definition 1.1). -/
def epsNbhd {n : ℕ} (K : Set (E n)) (ε : ℝ) : Set (E n) := K + ε • unitBall n

/-- `K(−ε) = ℝⁿ \ ((ℝⁿ \ K) + ε B₂ⁿ)`, the ε-interior (Definition 1.1). -/
def epsInterior {n : ℕ} (K : Set (E n)) (ε : ℝ) : Set (E n) := (Kᶜ + ε • unitBall n)ᶜ

end MixedVolFPRAS.Main


