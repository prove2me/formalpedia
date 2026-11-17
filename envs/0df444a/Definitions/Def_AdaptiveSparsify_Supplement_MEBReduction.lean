-- Prove2me | Definitions.Def_AdaptiveSparsify_Supplement_MEBReduction
-- name    : AdaptiveSparsify_Supplement_MEBReduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:52:49.193532+00:00
-- url     : https://prove2.me/theorems/178b41ee-d483-46bc-88fc-e4ebfad1fafa
-- title:
--   Boxed LP feasibility, minimum enclosing ball radius, and the input and output streams of Theorem 4
-- statement:
--   The objects of Theorem 4.
--
--   1. **Input stream.** For $A\in\mathbb Z^{n\times d}$, $b\in\mathbb Z^n$, a bit bound $B$, $U$ and $\xi$: the integers $n,d,B,U,\xi$, then for $i=1,\dots,n$ the row $a_i$ followed by $b_i$.
--   2. **Output stream.** For points $p_1,\dots,p_m\in\mathbb Z^D$ and integers $\theta,\varrho$: the integers $m,D,\theta,\varrho$, then the coordinates of $p_1,\dots,p_m$.
--   3. **Boxed feasibility.** For $s\in\mathbb R$, the system $Ax\le b+s\mathbf 1$, $-U\mathbf 1\le x\le U\mathbf 1$ has a solution $x\in\mathbb R^d$. Case (i) of Theorem 4 is $s=0$, case (ii) is $s=\xi$.
--   4. **Minimum enclosing ball.** The radius of the minimum enclosing Euclidean ball of $p_1,\dots,p_m$ is
--   $$\operatorname{rad}(P)=\min_{c\in\mathbb R^D}\max_{\ell}\|p_\ell-c\|_2 .$$
--   "Radius at most $r$" means some ball of radius $r$ encloses all points, and "radius at least $r$" means every centre $c$ has a point at distance at least $r$.
--   5. **Bit bound.** $2^{C\,B\max(1,\log_2 n)}$: an integer below it in absolute value has at most $C\,B\max(1,\log_2 n)$ bits.
--
--   **Formalization Note** The header $n,d,B,U,\xi$ comes first, so a one-pass program knows $\Lambda=4d2^B$, $U$ and $\xi$ before the rows. The radius statements use centres and distances directly; since the minimum is attained, they are $\operatorname{rad}(P)\le r$ and $\operatorname{rad}(P)\ge r$ (for $m\ge1$), and no infimum junk value enters.
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Theorem 4, p.55 (also p.9); conventions p.55; Algorithm 3, p.60

import Mathlib
import Definitions.Def_AdaptiveSparsify_Supplement_IntRAM

namespace AdaptiveSparsify

/-!
# Boxed LP feasibility, minimum enclosing ball radii, and the streams of Theorem 4

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…),
Theorem 4, p.55 (also printed on p.9), with the conventions stated after it on p.55 and the
input/output of Algorithm 3, p.60.

**Formalization Note.**
* The input stream is `n, d, B, U, ξ`, then for `i = 1, …, n` the row `a_i` (entries `A_{i1}, …, A_{id}`)
  followed by `b_i`. The header comes first, so a one-pass program knows `Λ = 4d2^B`, `U` and `ξ`
  before the rows (reading).
* "An integer with `B` bits" is `|x| < 2^B`.
* `BoxFeasible A b U s` is `∃ x ∈ ℝ^d, A x ≤ b + s·1, −U ≤ x_j ≤ U`; case (i) of Theorem 4 is `s = 0`,
  case (ii) is `s = ξ`.
* The output stream is `m, D, θ, ϱ`, then the points `p_1, …, p_m ∈ ℤ^D`, coordinate by coordinate.
* The minimum enclosing ball radius of `P` is `rad(P) = min_c max_ℓ ‖p_ℓ − c‖₂` over real centres
  `c ∈ ℝ^D`; the minimum is attained. "Radius at most `r`" is `∃ c, ∀ ℓ, ‖p_ℓ − c‖₂ ≤ r` and "radius at
  least `r`" is `∀ c, ∃ ℓ, ‖p_ℓ − c‖₂ ≥ r`, which are `rad(P) ≤ r` and `rad(P) ≥ r` for `m ≥ 1`; no
  infimum is taken, so no junk value enters.
* `bitBound C B n = 2^{C · B · max(1, log₂ n)}`: an integer below it in absolute value has at most
  `C · B · max(1, log₂ n)` bits ("log n is interpreted as at least 1", p.55).
-/

namespace Supplement

/-- The input stream of Theorem 4: `n, d, B, U, ξ`, then each row `a_i` followed by `b_i`. -/
def lpStream {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℤ) (b : Fin n → ℤ) (B : ℕ) (U ξ : ℤ) :
    List ℤ :=
  [(n : ℤ), (d : ℤ), (B : ℤ), U, ξ] ++ (List.finRange n).flatMap (fun i => List.ofFn (A i) ++ [b i])

/-- The output stream of Theorem 4: `m, D, θ, ϱ`, then the points `p_1, …, p_m`. -/
def mebStream {m D : ℕ} (p : Fin m → Fin D → ℤ) (θ ϱ : ℤ) : List ℤ :=
  [(m : ℤ), (D : ℤ), θ, ϱ] ++ (List.finRange m).flatMap (fun l => List.ofFn (p l))

/-- The boxed system `A x ≤ b + s·1`, `−U ≤ x_j ≤ U` has a real solution. -/
def BoxFeasible {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℤ) (b : Fin n → ℤ) (U : ℤ) (s : ℝ) : Prop :=
  ∃ x : Fin d → ℝ, (∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ) + s) ∧
    ∀ j, -(U : ℝ) ≤ x j ∧ x j ≤ (U : ℝ)

/-- An integer point as a point of Euclidean space. -/
def toPoint {D : ℕ} (q : Fin D → ℤ) : EuclideanSpace ℝ (Fin D) :=
  WithLp.toLp 2 (fun k => (q k : ℝ))

/-- The minimum enclosing ball of `p_1, …, p_m` has radius at most `r`. -/
def MEBRadiusLE {m D : ℕ} (p : Fin m → Fin D → ℤ) (r : ℝ) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin D), ∀ l, dist (toPoint (p l)) c ≤ r

/-- The minimum enclosing ball of `p_1, …, p_m` has radius at least `r`. -/
def MEBRadiusGE {m D : ℕ} (p : Fin m → Fin D → ℤ) (r : ℝ) : Prop :=
  ∀ c : EuclideanSpace ℝ (Fin D), ∃ l, r ≤ dist (toPoint (p l)) c

/-- `2^{C · B · max(1, log₂ n)}`. -/
noncomputable def bitBound (C : ℝ) (B n : ℕ) : ℝ :=
  (2 : ℝ) ^ (C * B * max 1 (Real.logb 2 n))

end Supplement

end AdaptiveSparsify


