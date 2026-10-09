-- Prove2me | Definitions.Def_CurvatureSubmod_CSSP_Setting
-- name    : CurvatureSubmod_CSSP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:56:57.693754+00:00
-- url     : https://prove2.me/theorems/74a8440c-3400-476d-a485-985cc8034279
-- title:
--   (1.1), §2.1, §8 — marginal values, monotonicity, total curvature, column spans, projections proj_S, the CSSP objective f^A, and the condition number κ(A)
-- statement:
--   This file collects the objects of Sviridenko, Vondrák and Ward's application to column-subset selection (§8), together with the set-function vocabulary of §2.1.
--
--   Throughout, $X$ is a finite ground set and a set function is a map $f : 2^X \to \mathbb{R}$.
--
--   1. **Marginal value** (§2.1). For $A \subseteq X$ and $i \in X$, $f_A(i) = f(A + i) - f(A)$; it is $0$ when $i \in A$.
--   2. **Monotonicity** (§2.1). $f$ is *monotone increasing* if $f_A(i) \ge 0$ for all $i \in X$ and $A \subseteq X$, and *monotone decreasing* if $f_A(i) \le 0$ for all $i$ and $A$.
--   3. **Total curvature** ((1.1), p. 3) is not defined here: the goal uses the decreasing-case curvature $f_{X-j}(j) \le (1-c)\, f_\emptyset(j)$ of the series' shared setting.
--
--   Now let $A$ be a real $m \times n$ matrix with columns $c_1, \dots, c_n \in \mathbb{R}^m$, so that $Ax = \sum_i x_i c_i$ for $x \in \mathbb{R}^n$; $\|\cdot\|$ is the Euclidean norm.
--
--   4. **Column span and projection** (§8, p. 11). For $S \subseteq [n]$, $\mathrm{span}(S) = \mathrm{span}\{c_i : i \in S\}$, and
--   $$\mathrm{proj}_S(x) = \operatorname*{argmin}_{y \in \mathrm{span}(\{c_i : i \in S\})} \|x - y\|$$
--   is the orthogonal projection of $x$ onto that subspace ($\mathrm{span}(\emptyset) = \{0\}$).
--   5. **The CSSP objective** (§8, p. 11). $f^A : 2^{[n]} \to \mathbb{R}$,
--   $$f^A(S) = \sum_{i=1}^n \|c_i - \mathrm{proj}_S(c_i)\|^2 ,$$
--   the squared Frobenius distance from $A$ to the closest matrix whose columns lie in $\mathrm{span}(S)$.
--   6. **Condition number** (§8, p. 11). For $A$ with independent columns,
--   $$\kappa(A) = \frac{\sup_{\|x\|=1} \|Ax\|}{\inf_{\|x\|=1} \|Ax\|} .$$
--
--   These are the objects in which the paper relates the curvature of the column-subset selection objective to the conditioning of $A$.
--
--   **Formalization Note** Subsets of $[n]$ are `Finset (Fin n)`, $X - j$ is `Finset.univ.erase j`, $A + i$ is `insert i A`. Vectors live in `EuclideanSpace ℝ (Fin m)`; the columns are a family `c : Fin n → EuclideanSpace ℝ (Fin m)`, and $Ax$ is `applyA c x = ∑ j, x j • c j`. The projection is Mathlib's `Submodule.starProjection` onto `Submodule.span ℝ (c '' S)`, which is finite-dimensional, so the argmin exists and is unique. The supremum and infimum defining $\kappa$ are taken over the unit sphere of $\mathbb{R}^n$ (a bounded set, nonempty when $n \ge 1$); every result that uses $\kappa$ assumes linearly independent columns, under which the infimum is positive. The page's convention $\kappa = \infty$ for dependent columns is not encoded.
-- source:
--   Sviridenko, Vondrák, Ward, Optimal approximation for submodular and supermodular optimization with bounded curvature (SODA 2015 version, Oct. 9, 2014), (1.1) p. 3, §2.1 p. 4, §8 pp. 10–11

import Mathlib
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting

namespace CurvatureSubmod.CSSP

/-- §2.1, p. 4: the marginal value `f_A(i) = f(A + i) − f(A)`. -/
def marg {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (A : Finset X) (i : X) : ℝ :=
  f (insert i A) - f A

/-- §2.1, p. 4: `f` is non-decreasing (monotone increasing): `f_A(i) ≥ 0` for all `i`, `A`. -/
def MonoInc {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) : Prop :=
  ∀ (A : Finset X) (i : X), 0 ≤ marg f A i

/-- §2.1, p. 4: `f` is non-increasing (monotone decreasing): `f_A(i) ≤ 0` for all `i`, `A`. -/
def MonoDec {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) : Prop :=
  ∀ (A : Finset X) (i : X), marg f A i ≤ 0

/-- §8, p. 11: `span({c_i : i ∈ S})`, the subspace of `ℝ^m` spanned by the columns indexed by `S`. -/
noncomputable def colSpan {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  Submodule.span ℝ (c '' (↑S : Set (Fin n)))

/-- §8, p. 11: `proj_S(x) = argmin_{y ∈ span({c_i : i ∈ S})} ‖x − y‖`, the orthogonal projection
of `x` onto `colSpan c S` (finite-dimensional, so the projection exists). -/
noncomputable def proj {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  (colSpan c S).starProjection x

/-- §8, p. 11: `f^A(S) = Σ_{i=1}^n ‖c_i − proj_S(c_i)‖²`. -/
noncomputable def fA {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) (S : Finset (Fin n)) : ℝ :=
  ∑ i, ‖c i - proj c S (c i)‖ ^ 2

/-- §8, p. 10: `Ax = Σ_i x_i c_i`, the matrix with columns `c_1, …, c_n` applied to `x ∈ ℝ^n`. -/
noncomputable def applyA {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin m) :=
  ∑ j, x j • c j

/-- §8, p. 11: the condition number `κ(A) = sup_{‖x‖=1} ‖Ax‖ / inf_{‖x‖=1} ‖Ax‖`, the supremum
and infimum taken over the unit sphere of `ℝ^n`. Used only for `A` with independent columns. -/
noncomputable def condNum {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m)) : ℝ :=
  (⨆ x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}, ‖applyA c x.1‖) /
    (⨅ x : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}, ‖applyA c x.1‖)

end CurvatureSubmod.CSSP


