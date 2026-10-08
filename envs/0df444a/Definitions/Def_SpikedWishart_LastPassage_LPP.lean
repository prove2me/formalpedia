-- Prove2me | Definitions.Def_SpikedWishart_LastPassage_LPP
-- name    : SpikedWishart_LastPassage_LPP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:35:50.376583+00:00
-- url     : https://prove2.me/theorems/3ca83230-3c91-45a0-b4dd-3014ae434fe8
-- title:
--   (306), p. 1692 — up/right paths, the last passage time L(N, M), and the exponential site law of rate π_iM
-- statement:
--   This file defines the last passage percolation model of §6.
--
--   Attach a real number $X(i,j)$ to every site $(i,j)$ of the grid $\{1,\ldots,N\}\times\{1,\ldots,M\}$. An **up/right path** from $(1,1)$ to $(a,b)$ is a sequence of sites $\pi = \{(i_k,j_k)\}_{k=1}^{a+b-1}$ with $(i_1,j_1) = (1,1)$, $(i_{a+b-1}, j_{a+b-1}) = (a,b)$, and each step $(i_{k+1},j_{k+1}) - (i_k,j_k)$ equal to $(1,0)$ or $(0,1)$. The **last passage time** to $(a,b)$ is
--   $$L(a,b) = \max_{\pi:(1,1)\nearrow(a,b)} \sum_{(i,j)\in\pi} X(i,j),$$
--   and $L(N,M)$, the last passage time to the opposite corner, is (306).
--
--   The random environment of Proposition 6.1: given positive numbers $\pi_1,\ldots,\pi_N$ and $M \ge 1$, the $X(i,j)$ are independent and $X(i,j)$ is exponential of mean $1/(\pi_i M)$, with density $\pi_i M e^{-\pi_i M x}$ on $x \ge 0$. All sites of row $i$ share the rate $\pi_i M$.
--
--   **Formalization Note** Sites are 0-based: the paper's $(1,1)$ and $(N,M)$ are $(0,0)$ and $(N-1,M-1)$, and $L$ requires $N, M \ge 1$. A path to $(a,b)$ is a function from $\{0,\ldots,a+b\}$ to sites; the maximum is a supremum over this finite, nonempty set of paths (nonemptiness is checked in a separate verification file). The site law is the product of Mathlib's exponential measures `expMeasure (π i * M)`, whose parameter is the rate.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1692, §6, (306) and the paragraph before (307)

import Mathlib

namespace SpikedWishart.LastPassage

open MeasureTheory ProbabilityTheory

/-- An up/right lattice path in the `N × M` grid (0-based sites `(i, j) : Fin N × Fin M`) from
`(0, 0)` to `(a, b)`: a sequence of `a + b + 1` sites starting at `(0, 0)`, ending at `(a, b)`, each
step adding exactly one of `(1, 0)` or `(0, 1)`. -/
def UpRightPath {N M : ℕ} (a : Fin N) (b : Fin M) : Type :=
  {p : Fin ((a : ℕ) + b + 1) → Fin N × Fin M //
    ((p 0).1 : ℕ) = 0 ∧ ((p 0).2 : ℕ) = 0 ∧ p (Fin.last _) = (a, b) ∧
    ∀ k : Fin ((a : ℕ) + b),
      (((p k.succ).1 : ℕ) = (p k.castSucc).1 + 1 ∧ (p k.succ).2 = (p k.castSucc).2) ∨
      ((p k.succ).1 = (p k.castSucc).1 ∧ ((p k.succ).2 : ℕ) = (p k.castSucc).2 + 1)}

instance UpRightPath.instFinite {N M : ℕ} (a : Fin N) (b : Fin M) : Finite (UpRightPath a b) := by
  unfold UpRightPath; infer_instance

/-- The last passage time (306) from `(0, 0)` to `(a, b)` (0-based) for the site weights `X`: the
maximum over up/right paths of the sum of the weights of the sites on the path. -/
noncomputable def lpp {N M : ℕ} (X : Fin N → Fin M → ℝ) (a : Fin N) (b : Fin M) : ℝ :=
  ⨆ p : UpRightPath a b, ∑ k, X (p.1 k).1 (p.1 k).2

/-- The last passage time `L(N, M)` of (306): from the corner `(0, 0)` to the opposite corner
`(N - 1, M - 1)` of the `N × M` grid (0-based; the paper's `(1, 1)` and `(N, M)`). -/
noncomputable def L {N M : ℕ} [NeZero N] [NeZero M] (X : Fin N → Fin M → ℝ) : ℝ :=
  lpp X ⟨N - 1, Nat.sub_one_lt (NeZero.ne N)⟩ ⟨M - 1, Nat.sub_one_lt (NeZero.ne M)⟩

/-- The law of the array `X(i, j)` of independent exponential random variables, `X(i, j)` with rate
`π_i M` (density `π_i M e^{-π_i M x}` on `x ≥ 0`, mean `1/(π_i M)`). -/
noncomputable def expLaw {N : ℕ} (π : Fin N → ℝ) (M : ℕ) : Measure (Fin N → Fin M → ℝ) :=
  Measure.pi fun i => Measure.pi fun _ => expMeasure (π i * M)

end SpikedWishart.LastPassage


