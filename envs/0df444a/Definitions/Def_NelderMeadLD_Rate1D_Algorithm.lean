-- Prove2me | Definitions.Def_NelderMeadLD_Rate1D_Algorithm
-- name    : NelderMeadLD_Rate1D_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:10:40.348649+00:00
-- url     : https://prove2.me/theorems/3d9a7a3b-fd91-469c-9549-d304cab3a891
-- title:
--   §2.1, pp. 115–117, and §4.3, pp. 130–133 — Algorithm NM in dimension 1, move types, r*, N_NM = max(χ, 1/γ), j* and the bracketing index K
-- statement:
--   This file defines the one-dimensional Nelder–Mead method of Lagarias, Reeds, Wright and Wright (Algorithm NM, §2.1) and the auxiliary quantities of their §4.3 on linear convergence with reflection coefficient $\rho = 1$.
--
--   **Parameters.** The four coefficients of reflection $\rho$, expansion $\chi$, contraction $\gamma$ and shrinkage $\sigma$ satisfy (2.1):
--   $$\rho > 0,\quad \chi > 1,\quad \chi > \rho,\quad 0 < \gamma < 1,\quad 0 < \sigma < 1.$$
--
--   **State and trial points.** In dimension 1 a simplex is a pair of vertices $(x_1, x_2)$ ordered so that $f(x_1) \le f(x_2)$; $x_1$ is the best and $x_2$ the worst vertex, and the centroid of the $n = 1$ best vertices is $x_1$. The trial points (2.4)–(2.7) are
--   $$x_r = x_1 + \rho(x_1 - x_2),\quad x_e = x_1 + \rho\chi(x_1 - x_2),\quad x_c = x_1 + \rho\gamma(x_1 - x_2),\quad x_{cc} = x_1 - \gamma(x_1 - x_2),$$
--   and the shrink point is $v_2 = x_1 + \sigma(x_2 - x_1)$.
--
--   **One iteration.** Write $f_1 = f(x_1)$, $f_2 = f(x_2)$, $f_r = f(x_r)$ and so on.
--   1. If $f_r < f_1$: the iteration is an *expansion* (accepting $x_e$) if $f_e < f_r$, and otherwise a *reflection* (accepting $x_r$).
--   2. If $f_1 \le f_r < f_2$: the iteration is an *outside contraction* (accepting $x_c$) if $f_c \le f_r$, and otherwise a *shrink*.
--   3. If $f_r \ge f_2$: the iteration is an *inside contraction* (accepting $x_{cc}$) if $f_{cc} < f_2$, and otherwise a *shrink*.
--
--   The worst vertex $x_2$ is discarded and the new pair consists of $x_1$ and the accepted point $v$ (for a shrink, $v = v_2$). The new point becomes the best vertex if and only if $f(v) < f(x_1)$; on a tie it takes the second (highest) index. In dimension 1 this is both the paper's nonshrink insertion rule and its shrink ordering rule. The run $\Delta_0, \Delta_1, \dots$ is obtained by iterating this map from an initial pair $\Delta_0$ that is **nondegenerate** ($x_1 \ne x_2$) and ordered ($f(x_1) \le f(x_2)$). The **diameter** is $\operatorname{diam}(\Delta) = |x_1 - x_2|$.
--
--   **Objects of §4.3.** With $\rho = 1$:
--   1. The *move type* of iteration $k$ is the case (reflection, expansion, outside contraction, inside contraction, shrink) taken at $\Delta_k$. A *contraction* is an outside or an inside contraction; a shrink is not a contraction.
--   2. $r^* = \lceil \chi - 1 \rceil$ (Lemma 4.6).
--   3. $N_{NM} = \max(\chi, 1/\gamma)$ (Lemma 4.7; this is the constant (4.3) for $\rho = 1$).
--   4. $j^*$ is the largest integer $j \ge 0$ with
--   $$\chi + \chi^2 + \cdots + \chi^j < N_{NM},$$
--   where $j = 0$ gives the empty sum $0$. This covers both cases of Lemma 4.7: if $\chi = N_{NM}$ then already $j = 1$ fails, so $j^* = 0$.
--   5. The bracketing condition (4.2) at $\Delta$ is the up–down–up relation $f(x_2) \ge f(x_1)$ and $f(x_1) \le f(x_e)$ (along a run the first half always holds, so this is Corollary 4.1's $f_1^{(K)} \le f_e^{(K)}$), and the *bracketing index* $K$ of Lemma 4.2 is the first iteration at which it holds.
--
--   These are the objects in terms of which the paper proves that the Nelder–Mead interval shrinks M-step linearly once the minimizer is bracketed.
--
--   **Formalization Note.** The algorithm itself (parameters, trial points, move types, ordering rule, run, diameter and the bracketing predicate (4.2)) is imported from the shared module `NelderMeadLD.Conv1D.Algorithm`; this file adds only the §4.3 objects. The state is an ordered pair `p : ℝ × ℝ` with `p.1` $= x_1$ and `p.2` $= x_2$; the paper's 1-based vertex indices become the two components. `run f ρ χ γ σ p0 k` is $\Delta_k$; `moveAt f χ γ σ p0 k` is the move type of iteration $k$ with $\rho = 1$ substituted. The paper's ordering rule prints $j = \max\{\ell \mid f(v) < f(x_{\ell+1})\}$, which contradicts its own example on p. 118; the encoded rule is the insertion form ("highest possible index consistent with the ordering"), which in dimension 1 reads as stated above. `rStar` is the natural-number ceiling `⌈χ − 1⌉₊`, which equals the paper's $\lceil\chi - 1\rceil$ for $\chi > 1$. `jStar` is `Nat.findGreatest` over $0 \le j \le \lceil N_{NM}\rceil$; for $\chi > 1$ the sum $\chi + \cdots + \chi^j$ exceeds $j$, so every admissible $j$ is below $N_{NM}$ and the search bound loses nothing, and since the sum increases in $j$ the largest admissible $j$ is the paper's $j^*$.
-- source:
--   Lagarias, Reeds, Wright & Wright, Convergence properties of the Nelder–Mead simplex method in low dimensions, SIAM J. Optim. 9 (1998), pp. 115–117, §2.1, (2.1), (2.3)–(2.7); p. 124, (4.1); p. 125, (4.2); p. 131, Lemma 4.6 (r*); p. 132, Lemma 4.7 (N_NM, j*)

import Mathlib
import Definitions.Def_NelderMeadLD_Conv1D_Algorithm

namespace NelderMeadLD.Rate1D

open Classical
open NelderMeadLD.Conv1D

/-! The one-dimensional Algorithm NM (`ParamsOK`, `xr`, `xe`, `xc`, `xcc`, `Move`, `move`,
`place`, `step`, `run`, `IsStart`, `diam`, `Bracketed`) is the shared module
`NelderMeadLD.Conv1D.Algorithm`. The state is the ordered pair `p = (x₁, x₂)`: `p.1` is the
best vertex `x₁` and `p.2` the worst vertex `x₂`.

### Objects of §4.3 (reflection coefficient `ρ = 1`) -/

/-- The type of iteration `k` of the run with `ρ = 1`. -/
noncomputable def moveAt (f : ℝ → ℝ) (χ γ σ : ℝ) (p0 : ℝ × ℝ) (k : ℕ) : Move :=
  move f 1 χ γ (run f 1 χ γ σ p0 k)

/-- A contraction is an outside or an inside contraction (a shrink is not a contraction). -/
def IsContraction (m : Move) : Prop :=
  m = Move.outside ∨ m = Move.inside

/-- `r* = ⌈χ − 1⌉` of Lemma 4.6, as a natural number (equal to the paper's value for `χ > 1`). -/
noncomputable def rStar (χ : ℝ) : ℕ := ⌈χ - 1⌉₊

/-- `N_NM = max(χ, 1/γ)` of Lemma 4.7 (the constant (4.3) with `ρ = 1`). -/
noncomputable def NNM1 (χ γ : ℝ) : ℝ := max χ (1 / γ)

/-- `j*` of Lemma 4.7: the largest `j ≤ ⌈N_NM⌉` with `χ + χ² + ⋯ + χ^j < N_NM`
(`j = 0` has the empty sum `0`). -/
noncomputable def jStar (χ γ : ℝ) : ℕ :=
  Nat.findGreatest (fun j => ∑ i ∈ Finset.range j, χ ^ (i + 1) < NNM1 χ γ) ⌈NNM1 χ γ⌉₊

/-- `K` is the iteration index of Lemma 4.2 for `ρ = 1`: the first iteration at which the
up–down–up relation (4.2), `f₂^{(K)} ≥ f₁^{(K)}` and `f₁^{(K)} ≤ f_e^{(K)}`, holds. -/
def FirstBracket (f : ℝ → ℝ) (χ γ σ : ℝ) (p0 : ℝ × ℝ) (K : ℕ) : Prop :=
  Bracketed 1 χ f (run f 1 χ γ σ p0 K) ∧ ∀ j < K, ¬ Bracketed 1 χ f (run f 1 χ γ σ p0 j)

end NelderMeadLD.Rate1D


