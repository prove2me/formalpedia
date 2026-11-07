-- Prove2me | Definitions.Def_ApproxDegComp_sqfreeFun
-- name    : ApproxDegComp_sqfreeFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:48.423196+00:00
-- url     : https://prove2.me/theorems/269317d0-8a18-48b1-99a4-855a330d7296
-- title:
--   Mixed partials $\partial_S R(0)$ and squarefree extraction $\mathcal S(R)$ of an analytic function
-- statement:
--   Let $R$ be a real function on $\mathbb R^n$ that is real analytic near $0$. For $S\subseteq[n]$ write $\partial_S=\prod_{i\in S}\partial_i$ for the mixed partial derivative taking one derivative in each coordinate of $S$. The **squarefree extraction** of $R$ is the multilinear polynomial
--
--   $$\mathcal S(R)(x)=\sum_{S\subseteq[n]}\partial_S R(0)\prod_{i\in S}x_i ,$$
--
--   i.e. the squarefree part of the Taylor expansion $\sum_\alpha\frac{\partial^\alpha R(0)}{\alpha!}x^\alpha$ of $R$ at $0$ (for squarefree $\alpha$, $\alpha!=1$).
--
--   **Formalization Note** $\partial_S R(0)$ is the $|S|$-th iterated Fréchet derivative of $R$ at $0$ applied to the coordinate vectors of $S$. For $R$ that is $C^{|S|}$ near $0$ (every function to which the mission applies it is analytic) this is the usual mixed partial in any order; for non-smooth $R$ Lean returns $0$, which is why the statements using it keep the source's analyticity or trigonometric-polynomial hypotheses.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Definition 20, p.14

import Mathlib

namespace ApproxDegComp

/-- **Mixed partial derivative** `∂_S R(0)` in distinct coordinates (Definition 20, p.14).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 20, p.14: "where ∂_S = Π_{i∈S} ∂ᵢ".

`mixedPartial R S` is the `|S|`-th iterated Fréchet derivative of `R` at `0`, applied to the
coordinate vectors `e_i`, `i ∈ S`, each once.

**Formalization Note** For `R` that is `C^{|S|}` near `0` (every `R` of the paper is
analytic there) the iterated derivative is symmetric, so this is `Π_{i∈S} ∂ᵢ R(0)` in any order;
for a non-smooth `R` the value is Mathlib's junk value `0`, which is why the statements that
use it keep the paper's analyticity (or trigonometric-polynomial) hypothesis. -/
noncomputable def mixedPartial {n : ℕ} (R : (Fin n → ℝ) → ℝ) (S : Finset (Fin n)) : ℝ :=
  iteratedFDeriv ℝ S.card R 0 (fun k => Pi.single (S.orderEmbOfFin rfl k) 1)

/-- **Squarefree extraction of a real-analytic function** `S(R)` (Definition 20, p.14).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 20, p.14: "The squarefree extraction of this is
S(R)(x) = Σ_{S⊆[n]} ∂_S R(0) Π_{i∈S} xᵢ, where ∂_S = Π_{i∈S} ∂ᵢ."

**Formalization Note** Built from `mixedPartial`; it is the multilinear polynomial whose
coefficient on `Π_{i∈S} xᵢ` is the Taylor coefficient `∂_S R(0)/α! = ∂_S R(0)` (`α! = 1` for a
squarefree `α`). -/
noncomputable def sqfreeFun {n : ℕ} (R : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), mixedPartial R S * ∏ i ∈ S, x i

end ApproxDegComp


