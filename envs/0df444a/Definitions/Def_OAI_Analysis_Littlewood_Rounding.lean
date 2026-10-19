-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_Rounding
-- name    : OAI_Analysis_Littlewood_Rounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:57:09.583557+00:00
-- url     : https://prove2.me/theorems/8ced5910-6c21-4e19-8223-1cdbacdd9b8a
-- title:
--   Boolean signs, rotated Dirichlet kernels on a root-of-unity grid, and the defect mass of a vector
-- statement:
--   This file fixes three auxiliary objects used to round a real coefficient vector with entries in $[-1,1]$ to a vector of signs.
--
--   1. **Boolean sign.** For a Boolean value $b\in\{\mathrm{true},\mathrm{false}\}$,
--   $$
--   \sigma(b)=\begin{cases}1, & b=\mathrm{true},\\ -1, & b=\mathrm{false},\end{cases}
--   $$
--   so that $|\sigma(b)|=1$. A Boolean vector $x=(x_k)_k$ thus encodes the sign vector $(\sigma(x_k))_k$.
--
--   2. **Rotated Dirichlet kernel on the $M$-th roots of unity.** Let $M\ge1$ and write $\omega_j=e^{2\pi i j/M}$ for $j\in\mathbb{Z}/M\mathbb{Z}$. For $n\in\mathbb{N}$ and $z\in\mathbb{C}$,
--   $$
--   D_n(z;j)=\sum_{a=0}^{n-1}z^{a}\,\overline{\omega_j^{\,a}}=\sum_{a=0}^{n-1}z^{a}e^{-2\pi i a j/M}.
--   $$
--   For $|z|=1$ this is the Dirichlet kernel of length $n$ evaluated at the ratio $z\,\overline{\omega_j}$.
--
--   3. **Defect mass.** For $X=(X_0,\dots,X_{N-1})\in\mathbb{R}^N$,
--   $$
--   \mu(X)=\frac12\sum_{k=0}^{N-1}\bigl(1-|X_k|\bigr).
--   $$
--   If all $|X_k|\le1$, then $\mu(X)\ge0$, with equality exactly when every $X_k$ is a sign.
--
--   The Boolean sign encodes the colorings in the partial-coloring and discrepancy arguments, where an entropy count produces two widely separated signings with identical rounded row sums. The kernels $D_{2n}$ and $D_n$ reproduce monomials of degree less than $n$ on the grid of $M\ge2n$ roots of unity, which gives a bound without logarithmic loss: an analytic polynomial of degree less than $n$ that is bounded by $G$ at all $M$-th roots of unity is bounded by $2G$ on the whole unit circle. The defect mass is the quantity in which the final rounding error is measured: a vector $X$ with entries in $[-1,1]$ is replaced by a vector of signs whose Littlewood polynomial differs from that of $X$ on the unit circle by at most an absolute constant times $1+\sqrt{\mu(X)\log(80N/\mu(X))}$.
--
--   **Formalization Note** `boolSign`, `gridDirichlet` and `defectMass` are the three objects above, with the simp lemma `abs_boolSign`. In `gridDirichlet` the root of unity $\omega_j$ is `ZMod.stdAddChar j`, the standard additive character of `ZMod M` (this requires `NeZero M`), and the summation index $a$ runs over `Fin n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

/-- A Boolean encoding of a real sign. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem abs_boolSign (b : Bool) : |boolSign b| = 1 := by
  cases b <;> norm_num [boolSign]

open scoped ComplexConjugate
open Finset

/-- A rotated, finite Dirichlet kernel on the root grid. -/
def gridDirichlet {M : ℕ} [NeZero M] (n : ℕ) (z : ℂ) (j : ZMod M) : ℂ :=
  ∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))

def defectMass {N : ℕ} (X : Fin N → ℝ) : ℝ :=
  (∑ k : Fin N, (1 - |X k|)) / 2

end

end AsymptoticallyMinimalLittlewood

end OAI


