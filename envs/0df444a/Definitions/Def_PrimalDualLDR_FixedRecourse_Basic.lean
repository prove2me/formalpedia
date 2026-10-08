-- Prove2me | Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
-- name    : PrimalDualLDR_FixedRecourse_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:39.8952+00:00
-- url     : https://prove2.me/theorems/bf9b1aa4-d039-432d-a338-cb7bd09e3324
-- title:
--   Polyhedron $\{W\xi\ge h\}$, support of a measure, $e_1$ and the rule space $\mathcal L^2_{k,n}$ (Notation p. 3, (2.1a))
-- statement:
--   Four general objects used throughout §2 of Kuhn, Wiesemann and Georghiou.
--
--   1. For a matrix $W \in \mathbb R^{l\times k}$ and a vector $h \in \mathbb R^l$, the **polyhedron**
--   $$\Xi(W,h) = \{\xi \in \mathbb R^k : W\xi \ge h\},$$
--   where $W\xi \ge h$ is the componentwise order (Notation, p. 3).
--   2. A set $S \subseteq \mathbb R^k$ is the **support** of a measure $\mathbb P$ on $(\mathbb R^k, \mathfrak B(\mathbb R^k))$ if $S$ is closed, $\mathbb P(\mathbb R^k \setminus S) = 0$, and every open ball of positive radius centred at a point of $S$ has positive $\mathbb P$-measure. These three conditions say exactly that $S$ is the smallest closed set of probability one, which is the paper's definition of the support.
--   3. $e_1 \in \mathbb R^k$ is the basis vector whose first component is $1$ and all other components are $0$.
--   4. A function $x : \mathbb R^k \to \mathbb R^n$ belongs to $\mathcal L^2_{k,n} = L^2(\mathbb R^k, \mathfrak B(\mathbb R^k), \mathbb P; \mathbb R^n)$, the space of **decision rules**, if it is Borel measurable and $\mathbb E\|x(\xi)\|^2 < \infty$.
--
--   These are the building blocks of the fixed-recourse setting: the support of the uncertainty is a polyhedron $\Xi(W,h)$, and primal and dual decision rules range over $\mathcal L^2_{k,n}$.
--
--   **Formalization Note** Vectors in $\mathbb R^k$ are functions `Fin k → ℝ`; the paper's index $1$ is the Lean index `0`. The balls are those of the sup metric on `Fin k → ℝ`, which generate the same topology as the Euclidean balls, so the support characterization is unchanged. Square integrability is `MemLp x 2 P`, which is norm-independent on $\mathbb R^n$. Borel measurability is `Measurable x`: on `Fin k → ℝ` the product σ-algebra Mathlib uses is the Borel σ-algebra $\mathfrak B(\mathbb R^k)$. These four objects are shared by all three missions of the series (fixed recourse, random recourse, multistage), which is why they sit in the namespace of the first one.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, pp. 3–4, Notation, (2.1a)

import Mathlib

open MeasureTheory

namespace PrimalDualLDR.FixedRecourse

/-- The polyhedron `{ξ ∈ ℝ^k : Wξ ≥ h}` of (2.1a) in Kuhn, Wiesemann, Georghiou, *Primal and dual linear
decision rules in stochastic and robust optimization*, Optimization Online 2009/02/2218, p. 3. The order
`Wξ ≥ h` is componentwise (Notation, p. 3). -/
def polyhedron {k l : ℕ} (W : Matrix (Fin l) (Fin k) ℝ) (h : Fin l → ℝ) : Set (Fin k → ℝ) :=
  {ξ | ∀ i, h i ≤ (W.mulVec ξ) i}

/-- `S` is the support of the measure `P`, "the smallest closed subset of ℝ^k which has probability 1"
(Notation, p. 3): `S` is closed, `P(Sᶜ) = 0`, and every open ball centred at a point of `S` has positive
mass. These three conditions characterise the support (the smallest closed set of full measure). -/
def IsSupport {k : ℕ} (P : Measure (Fin k → ℝ)) (S : Set (Fin k → ℝ)) : Prop :=
  IsClosed S ∧ P Sᶜ = 0 ∧ ∀ ξ ∈ S, ∀ ε : ℝ, 0 < ε → 0 < P (Metric.ball ξ ε)

/-- The basis vector `e_1 ∈ ℝ^k` whose first component is `1` and all others `0` (p. 4). The paper's
index `1` is the `Fin` index `0`. -/
def e1 (k : ℕ) : Fin k → ℝ := fun j => if j.val = 0 then 1 else 0

/-- `x` belongs to `𝓛²_{k,n} = L²(ℝ^k, 𝔅(ℝ^k), P; ℝ^n)`, "the space of all Borel measurable,
square-integrable functions from ℝ^k to ℝ^n" (Notation, p. 3). -/
def IsL2Rule {k n : ℕ} (P : Measure (Fin k → ℝ)) (x : (Fin k → ℝ) → (Fin n → ℝ)) : Prop :=
  Measurable x ∧ MemLp x 2 P

end PrimalDualLDR.FixedRecourse


