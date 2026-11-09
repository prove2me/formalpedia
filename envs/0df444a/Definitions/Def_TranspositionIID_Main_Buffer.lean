-- Prove2me | Definitions.Def_TranspositionIID_Main_Buffer
-- name    : TranspositionIID_Main_Buffer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:47.171297+00:00
-- url     : https://prove2.me/theorems/7ef567a9-5c7c-4c08-842f-147e29e46b9c
-- title:
--   Adaptive buffer, separated inversions and the fixed cost constant
-- statement:
--   Put $y_i=\log p_i$. For nonempty label sets, $r(x)$ is the infimum of the nonnegative radii for which $\sum_i(r-|x-y_i|)_+\ge1$. It is the unique positive root of the equality. Set
--   $$\theta(x)=\tfrac12\min\{1,r(x)\},\quad J_{a,b}(\sigma)=\#\{(i,j):y_j\le a,\ y_i>a+b,\ \sigma(j)<\sigma(i)\},\quad J_x=J_{x,\theta(x)}.$$
--   All pairs are counted. Define the exact constant
--   $$C_0=2+(1+\sqrt e)\left[\tfrac14+\tfrac{2\pi^2}{3}(1+8e)\right].$$
--   This shares the same buffer and inversion definitions across the analytic and comparison statements.
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). §2.2 equation (2.2), printed p.3 = PDF p.3; §2.3, printed p.4 = PDF p.4; equation (4.1), printed p.7 = PDF p.7

import Definitions.Def_TranspositionIID_Main_ListModel

noncomputable section

namespace TranspositionIID.Main

/-- The upper-level-set inverse defining the unique root in (2.2), p.3.
For n ≥ 1 the set is nonempty, bounded below, and its infimum is the unique positive root. -/
def bufferRoot {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ 1 ≤ ∑ i, max (r - |x - Real.log (p i)|) 0}

def buffer {n : ℕ} (p : Fin n → ℝ) (x : ℝ) : ℝ := (1 / 2) * min 1 (bufferRoot p x)

/-- All separated inverted pairs, not only adjacent pairs (§2.3, p.4). -/
def separatedInversions {n : ℕ} (p : Fin n → ℝ) (a b : ℝ) (σ : ListState n) : ℝ :=
  ((Finset.univ.filter (fun ij : Fin n × Fin n =>
    Real.log (p ij.2) ≤ a ∧ a + b < Real.log (p ij.1) ∧ σ ij.2 < σ ij.1)).card : ℝ)

def adaptiveInversions {n : ℕ} (p : Fin n → ℝ) (x : ℝ) (σ : ListState n) : ℝ :=
  separatedInversions p x (buffer p x) σ

/-- The exact constant (4.1), p.7. -/
def C0 : ℝ := 2 + (1 + Real.sqrt (Real.exp 1)) *
  (1 / 4 + (2 * Real.pi ^ 2 / 3) * (1 + 8 * Real.exp 1))

end TranspositionIID.Main


