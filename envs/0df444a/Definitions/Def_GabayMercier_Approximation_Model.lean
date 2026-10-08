-- Prove2me | Definitions.Def_GabayMercier_Approximation_Model
-- name    : GabayMercier_Approximation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:13.238067+00:00
-- url     : https://prove2.me/theorems/e1945f2f-e831-4e79-a14f-31f85e899e9c
-- title:
--   The continuous and discrete minimization problems and hypotheses (4.1)–(4.3)
-- statement:
--   Let $V$ and $Y$ be real Hilbert spaces, $A:V\to Y$ a continuous linear operator, $b\in V'$, and $f_2:Y\to(-\infty,+\infty]$ a proper, convex, lower semicontinuous function. Set $f_1(y)=\frac12\|y\|^2$. The continuous problem $({\cal P})$ minimizes
--   $$
--   \frac12\|Av\|^2+f_2(Av)-\langle b,v\rangle\quad(v\in V).
--   $$
--   A solution has finite objective value and is a global minimizer. For finite dimensional subspaces $V_k\subseteq V$ and continuous linear maps $A_k:V_k\to Y$, the discrete problem $({\cal P}_k)$ minimizes the same expression with $A_k$ in place of $A$ over $V_k$.
--
--   The approximation hypotheses require one constant $\alpha>0$ with $\alpha^2\|v\|^2\le\|Av\|^2$, a common $\alpha'>0$ and $M$ with $\alpha'\|w\|\le\|A_kw\|\le M\|w\|$, weak to weak and strong to strong consistency of $A_k$, vanishing $\|A_kw-Aw\|$ for every uniformly bounded family, and, for each $v\in V$, approximants $w_k\in V_k$ satisfying $w_k\to v$ and $f_2(A_kw_k)\to f_2(Av)$. These are (2.5), (4.1), and (4.3).
--
--   This model is shared by the convergence statement and its intermediate claims.
--
--   **Formalization Note** The paper's family indexed by $h\to0$ is a sequence $h_k\to0$: all its hypotheses and conclusions are sequential, and a family indexed by $h>0$ restricts to every such sequence, so $k\to\infty$ represents $h\to0$. Condition (4.1)(ii) is weak-to-weak and (4.1)(iii) norm-to-norm, both along sequences $w_k\in V_k$. Condition (4.1)(iv), printed "when $\|v_h\|\le C$ and $h\to0$", is read as: for every $C$ and every family $w_k\in V_k$ with $\|w_k\|\le C$ for all $k$, $\|A_kw_k-Aw_k\|\to0$. In (4.3) the convergence $f_2(A_kw_k)\to f_2(Av)$ is in the order topology of $[-\infty,+\infty]$, so it includes the case $f_2(Av)=+\infty$. The paper's internal-approximation property ($\forall v\,\exists v_h\to v$) is implied by (4.3) and is not stated separately. The printed cut-off space in (4.1)(ii)–(iii) is $Y$. The unused codomain subspace $Y_h$ is absorbed into $Y$. Extended values use `EReal`; finite objective value is required for a solution. The standing interior-domain condition (2.4) is retained. The paper's Proposition 2.1 proof also requires one feasible point $v$ with $f_2(Av)<+\infty$; this is stated explicitly. The paper's $V'$ remains the strong dual, while $Y'$ is identified with $Y$.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 8, 20–21, (2.2)–(2.5), (4.1)–(4.3)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The quadratic part of (4.2). -/
noncomputable def halfSq (y : Y) : ℝ := 1 / 2 * ‖y‖ ^ 2

/-- The objective of (𝒫ₕ), with the discrete operator `Aₕ`. -/
noncomputable def objectiveH {W : Submodule ℝ V} (Ah : W →L[ℝ] Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (w : W) : EReal :=
  ((halfSq (Ah w) - b w : ℝ) : EReal) + f₂ (Ah w)

/-- A finite-valued minimizer of (𝒫ₕ) over `W`. -/
def IsSolutionH {W : Submodule ℝ V} (Ah : W →L[ℝ] Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (w : W) : Prop :=
  objectiveH Ah f₂ b w ≠ ⊤ ∧ ∀ u, objectiveH Ah f₂ b w ≤ objectiveH Ah f₂ b u

/-- The standing assumptions (2.2), (2.4), (2.5), and the approximation assumptions
(4.1), (4.3). The quadratic term in (4.2) already satisfies (2.3). -/
structure ApproxHyp (A : V →L[ℝ] Y) (f₂ : Y → EReal) (α : ℝ)
    (Vh : ℕ → Submodule ℝ V) (Ah : (k : ℕ) → Vh k →L[ℝ] Y)
    (α' M : ℝ) : Prop where
  f₂_proper : IsProperFn f₂
  f₂_convex : IsConvexFn f₂
  f₂_lsc : LowerSemicontinuous f₂
  dom_interior : (interior {y : Y | f₂ y ≠ ⊤}).Nonempty
  feasible : ∃ v : V, f₂ (A v) ≠ ⊤
  α_pos : 0 < α
  bddBelow : ∀ v, α ^ 2 * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2
  α'_pos : 0 < α'
  i : ∀ k (w : Vh k), α' * ‖(w : V)‖ ≤ ‖Ah k w‖ ∧ ‖Ah k w‖ ≤ M * ‖(w : V)‖
  ii : ∀ (w : (k : ℕ) → Vh k) (x : V), WeakTendsto (fun k => (w k : V)) x →
    WeakTendsto (fun k => Ah k (w k)) (A x)
  iii : ∀ (w : (k : ℕ) → Vh k) (x : V), Tendsto (fun k => (w k : V)) atTop (𝓝 x) →
    Tendsto (fun k => Ah k (w k)) atTop (𝓝 (A x))
  iv : ∀ (C : ℝ) (w : (k : ℕ) → Vh k), (∀ k, ‖(w k : V)‖ ≤ C) →
    Tendsto (fun k => ‖Ah k (w k) - A (w k)‖) atTop (𝓝 0)
  h43 : ∀ x : V, ∃ w : (k : ℕ) → Vh k, Tendsto (fun k => (w k : V)) atTop (𝓝 x) ∧
    Tendsto (fun k => f₂ (Ah k (w k))) atTop (𝓝 (f₂ (A x)))

end GabayMercier.Approximation


