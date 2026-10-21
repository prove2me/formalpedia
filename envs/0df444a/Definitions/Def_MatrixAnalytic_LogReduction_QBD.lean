-- Prove2me | Definitions.Def_MatrixAnalytic_LogReduction_QBD
-- name    : MatrixAnalytic_LogReduction_QBD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:00.350446+00:00
-- url     : https://prove2.me/theorems/17c35a80-ba06-4d33-afdf-11a55fdd57b0
-- title:
--   The homogeneous QBD (8.1) and the logarithmic reduction recursion (8.40)–(8.44) for H^[k], L^[k], U^[k]
-- statement:
--   Let $\iota$ be a set of phases (finite or countably infinite, $m \le \infty$) and $B, A_0, A_1, A_2$ real matrices indexed by $\iota$. The **homogeneous QBD** (8.1) is the Markov chain on the states $(n,i)$, $n\ge0$ the level and $i\in\iota$ the phase, with transition matrix
--   $$P=\begin{bmatrix}B&A_0&0&0&\cdots\\A_2&A_1&A_0&0&\cdots\\0&A_2&A_1&A_0&\cdots\\\vdots&&\ddots&\ddots&\ddots\end{bmatrix}:$$
--   from level $0$ the chain stays in level $0$ with probabilities $B$ and moves to level $1$ with probabilities $A_0$; from a level $n\ge1$ it moves up with $A_0$, stays with $A_1$ and moves down with $A_2$. The level $\ell(n)$ is the set of states with first coordinate $n$.
--
--   Matrices with nonnegative entries are handled with entries in $[0,\infty]$, where products $(MM')_{ij}=\sum_k M_{ik}M'_{kj}$ and powers are always defined. Following the book's convention (p. 109), $(I-M)^{-1}$ denotes the series $\sum_{\nu\ge0}M^\nu$, computed entrywise in $[0,\infty]$.
--
--   The **logarithmic reduction recursion** of Theorem 8.4.1 defines, for $k\ge0$,
--   $$H^{[0]}=(I-A_1)^{-1}A_0,\quad L^{[0]}=(I-A_1)^{-1}A_2,\quad H^{[k+1]}=(I-U^{[k]})^{-1}(H^{[k]})^2,\quad L^{[k+1]}=(I-U^{[k]})^{-1}(L^{[k]})^2,$$
--   with $U^{[k]}=H^{[k]}L^{[k]}+L^{[k]}H^{[k]}$, and the ordered products $\prod_{0\le i\le k-1}H^{[i]}=H^{[0]}H^{[1]}\cdots H^{[k-1]}$, the empty product ($k=0$) being the identity. Finally, a **stationary probability vector** of a phase matrix $M$ is a vector $g\ge0$ with $\sum_ig_i=1$ and $\sum_ig_iM_{ij}=g_j$ for every $j$.
--
--   **Formalization Note** Every inverse in the recursion is the series $\sum_\nu M^\nu$ in $[0,\infty]$ (the book's convention, p. 109), so the recursion is always defined; an entry is $\infty$ exactly when its series diverges, and the theorems of the mission state that every such series is finite. The matrices $H^{[k]}, L^{[k]}, U^{[k]}$ are defined by the recursion, as in the book; their probabilistic meaning is a theorem.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 165, Eq. (8.1); p. 191, Eqs. (8.40)–(8.44); p. 109 (convention (I − M)⁻¹ = Σ M^ν)

import Mathlib

namespace MatrixAnalytic.LogReduction

noncomputable section

open scoped ENNReal

/-!
The homogeneous discrete-time QBD (8.1) of Latouche & Ramaswami (p. 165) and the logarithmic
reduction recursion (8.40)–(8.44) of §8.4 (p. 191). The phase set is an arbitrary type `ι` (the
book allows `m = ∞`); levels are counted from `0`.

Matrices with nonnegative entries indexed by phases are handled with values in `ℝ≥0∞`, where
every product and every series of nonnegative terms is defined: `matMulE`, `matPowE`, and the
book's convention `(I − M)⁻¹ := Σ_{ν ≥ 0} M^ν` (p. 109) as `seriesInvE`. An entry of
`seriesInvE M` is `⊤` exactly when its series diverges; whether it is finite is a statement to
prove, never an assumption.
-/

variable {ι : Type*}

/-- The transition matrix (8.1) of a homogeneous QBD with blocks `B, A₀, A₁, A₂`:
from level `0` the chain moves to level `0` with probabilities `B` and to level `1` with
probabilities `A₀`; from a level `n ≥ 1` it moves to level `n + 1` with probabilities `A₀`,
stays in level `n` with probabilities `A₁` and moves to level `n − 1` with probabilities `A₂`;
every other transition has probability `0`. -/
def qbdP (B A₀ A₁ A₂ : ι → ι → ℝ) : ℕ × ι → ℕ × ι → ℝ :=
  fun x y =>
    if x.1 = 0 then
      (if y.1 = 0 then B x.2 y.2 else if y.1 = 1 then A₀ x.2 y.2 else 0)
    else
      (if y.1 = x.1 + 1 then A₀ x.2 y.2
        else if y.1 = x.1 then A₁ x.2 y.2
        else if y.1 + 1 = x.1 then A₂ x.2 y.2
        else 0)

/-- The level `ℓ(n) = {(n, 1), …, (n, m)}`. -/
def level (n : ℕ) : Set (ℕ × ι) := {x | x.1 = n}

/-- A real matrix read entrywise in `ℝ≥0∞` (used for matrices with nonnegative entries). -/
def ennMat (A : ι → ι → ℝ) : ι → ι → ℝ≥0∞ := fun i j => ENNReal.ofReal (A i j)

/-- Matrix product in `ℝ≥0∞`: `(MM')_{ij} = Σ_k M_{ik} M'_{kj}`. -/
def matMulE (M M' : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' k, M i k * M' k j

/-- The identity matrix in `ℝ≥0∞`. -/
def matOneE [DecidableEq ι] : ι → ι → ℝ≥0∞ := fun i j => if i = j then 1 else 0

/-- Matrix powers in `ℝ≥0∞`: `M⁰ = I`, `M^{ν+1} = M^ν M`. -/
def matPowE [DecidableEq ι] (M : ι → ι → ℝ≥0∞) : ℕ → ι → ι → ℝ≥0∞
  | 0 => matOneE
  | ν + 1 => matMulE (matPowE M ν) M

/-- The book's convention (p. 109) `(I − M)⁻¹ := Σ_{ν ≥ 0} M^ν`, entrywise in `ℝ≥0∞`
(an entry is `⊤` exactly when its series diverges). -/
def seriesInvE [DecidableEq ι] (M : ι → ι → ℝ≥0∞) : ι → ι → ℝ≥0∞ :=
  fun i j => ∑' ν : ℕ, matPowE M ν i j

/-- The pair `(H^{[k]}, L^{[k]})` of the logarithmic reduction recursion (p. 191):
`H^{[0]} = (I − A₁)⁻¹A₀` (8.40), `L^{[0]} = (I − A₁)⁻¹A₂` (8.41), and for `k ≥ 0`
`H^{[k+1]} = (I − U^{[k]})⁻¹(H^{[k]})²` (8.42), `L^{[k+1]} = (I − U^{[k]})⁻¹(L^{[k]})²` (8.43)
with `U^{[k]} = H^{[k]}L^{[k]} + L^{[k]}H^{[k]}` (8.44). Every inverse is the series
`seriesInvE`. -/
def logHL [DecidableEq ι] (A₀ A₁ A₂ : ι → ι → ℝ) :
    ℕ → (ι → ι → ℝ≥0∞) × (ι → ι → ℝ≥0∞)
  | 0 => (matMulE (seriesInvE (ennMat A₁)) (ennMat A₀),
          matMulE (seriesInvE (ennMat A₁)) (ennMat A₂))
  | k + 1 =>
    let H := (logHL A₀ A₁ A₂ k).1
    let L := (logHL A₀ A₁ A₂ k).2
    let U := matMulE H L + matMulE L H
    (matMulE (seriesInvE U) (matMulE H H), matMulE (seriesInvE U) (matMulE L L))

/-- `H^{[k]}` of (8.40), (8.42). -/
def logH [DecidableEq ι] (A₀ A₁ A₂ : ι → ι → ℝ) (k : ℕ) : ι → ι → ℝ≥0∞ :=
  (logHL A₀ A₁ A₂ k).1

/-- `L^{[k]}` of (8.41), (8.43). -/
def logL [DecidableEq ι] (A₀ A₁ A₂ : ι → ι → ℝ) (k : ℕ) : ι → ι → ℝ≥0∞ :=
  (logHL A₀ A₁ A₂ k).2

/-- `U^{[k]} = H^{[k]}L^{[k]} + L^{[k]}H^{[k]}` (8.44). -/
def logU [DecidableEq ι] (A₀ A₁ A₂ : ι → ι → ℝ) (k : ℕ) : ι → ι → ℝ≥0∞ :=
  matMulE (logH A₀ A₁ A₂ k) (logL A₀ A₁ A₂ k) + matMulE (logL A₀ A₁ A₂ k) (logH A₀ A₁ A₂ k)

/-- The ordered product `Π_{0 ≤ i ≤ k−1} H^{[i]} = H^{[0]} H^{[1]} ⋯ H^{[k−1]}`; for `k = 0`
the empty product is the identity matrix (p. 190). -/
def prodH [DecidableEq ι] (A₀ A₁ A₂ : ι → ι → ℝ) : ℕ → ι → ι → ℝ≥0∞
  | 0 => matOneE
  | k + 1 => matMulE (prodH A₀ A₁ A₂ k) (logH A₀ A₁ A₂ k)

/-- A stationary probability vector of a phase matrix `M` with entries in `ℝ≥0∞` (used for `M`
stochastic, so every entry is finite): `g ≥ 0`, `g1 = 1` and `gM = g`. -/
def IsStationaryVec (M : ι → ι → ℝ≥0∞) (g : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ g i) ∧ HasSum g 1 ∧ ∀ j, HasSum (fun i => g i * (M i j).toReal) (g j)

end

end MatrixAnalytic.LogReduction


