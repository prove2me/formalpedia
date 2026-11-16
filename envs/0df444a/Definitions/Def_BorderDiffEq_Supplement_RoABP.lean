-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_RoABP
-- name    : BorderDiffEq_Supplement_RoABP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:49:20.020905+00:00
-- url     : https://prove2.me/theorems/c6ab9fef-e16d-4221-9160-fef4a43684ea
-- title:
--   Read-once oblivious algebraic branching programs
-- statement:
--   A **read-once oblivious ABP** in $n$ variables over a ring $K$ is a layered directed graph with layers $V_0,\dots,V_n$, $V_0=\{s\}$ a single source and $V_n=\{t\}$ a single sink, in which every edge from $V_{\ell-1}$ to $V_\ell$ is labelled by a univariate polynomial in one variable $x_{\pi(\ell)}$, where $\pi$ is a permutation of $[n]$ (each variable is read in exactly one layer, in the order $x_{\pi(1)},\dots,x_{\pi(n)}$). It computes
--   $$
--   \sum_{\gamma:\,s\to t}\ \prod_{e\in\gamma} W(e),
--   $$
--   the sum over source–sink paths of the product of the edge labels. Equivalently it is a product $M_1(x_{\pi(1)})\cdots M_n(x_{\pi(n)})$ of matrices of univariate polynomials of sizes $1\times w_1,\dots,w_{n-1}\times1$. Its **width** is $\max_\ell|V_\ell|$ and its **individual degree** is the largest degree of a label.
--
--   **Formalization Note** Layer $\ell$ is `Fin (wd ℓ)` with `wd 0 = wd n = 1`; the edges between consecutive layers form a matrix of univariate polynomials, a zero entry being a missing edge. The order $\pi$ is supplied to `eval`, which substitutes $x_{\pi(\ell)}$ into the labels of layer $\ell$. With $n=0$ variables an roABP computes the constant $1$. This is a separate model from the published affine-label `BorderDiffEq.ABP`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Definition 4.11, pp.27–28; Definition 4.8, p.27

import Mathlib

namespace BorderDiffEq.Supplement

/-- **Read-once oblivious algebraic branching programs (roABPs)** (Bhat–Dutta–Kaplan–Shpilka–
Shringi, *Demystifying Border of Structured Algebraic Circuits via Differential Equations*,
manuscript (STOC 2027 submission), Definition 4.11, pp.27–28, with Definition 4.8, p.27): a layered
ABP with layers `V₀, …, Vₙ`, `V₀ = {s}`, `Vₙ = {t}`, in which every edge entering layer `ℓ` is
labelled by a univariate polynomial in one variable `x_{π(ℓ)}`, the variables `x_{π(1)}, …, x_{π(n)}`
being distinct (read once, in the order `π`). It computes the sum over all source–sink paths of the
product of the labels; its width is `maxᵢ |Vᵢ|` and its individual degree the maximal degree of a
label.

**Formalization Note.** Layer `i` is `Fin (wd i)` with `wd 0 = wd n = 1`; the edges between layers
`ℓ` and `ℓ+1` (0-indexed) form a matrix `M ℓ` of univariate polynomials, a zero entry being a
missing edge. The read order `π : Equiv.Perm (Fin n)` is not stored: `eval π A` substitutes
`x_{π(ℓ)}` into the labels of layer `ℓ`, so the same matrices read in order `π`. With `n = 0`
variables an roABP computes the constant `1`. -/
structure RoABP (K : Type) [Semiring K] (n : ℕ) where
  /-- the number of vertices in each layer -/
  wd : Fin (n + 1) → ℕ
  source_layer : wd 0 = 1
  sink_layer : wd (Fin.last n) = 1
  /-- the univariate edge labels between consecutive layers -/
  M : (ℓ : Fin n) → Matrix (Fin (wd ℓ.castSucc)) (Fin (wd ℓ.succ)) (Polynomial K)

namespace RoABP

variable {K : Type} {n : ℕ}

/-- The polynomial computed when layer `ℓ` reads `x_{π(ℓ)}`: the sum over all choices of one vertex
per layer (all source–sink paths) of the product of the labels, evaluated at `x_{π(ℓ)}`. -/
noncomputable def eval [CommRing K] (π : Equiv.Perm (Fin n)) (A : RoABP K n) :
    MvPolynomial (Fin n) K :=
  ∑ p : (i : Fin (n + 1)) → Fin (A.wd i),
    ∏ ℓ : Fin n, Polynomial.aeval (MvPolynomial.X (π ℓ)) (A.M ℓ (p ℓ.castSucc) (p ℓ.succ))

/-- The width `maxᵢ |Vᵢ|`. -/
def width [Semiring K] (A : RoABP K n) : ℕ := Finset.univ.sup A.wd

/-- The individual degree is at most `R`: every label has degree at most `R`. -/
def IndivDegLe [Semiring K] (A : RoABP K n) (R : ℕ) : Prop :=
  ∀ ℓ a b, (A.M ℓ a b).natDegree ≤ R

end RoABP

end BorderDiffEq.Supplement


