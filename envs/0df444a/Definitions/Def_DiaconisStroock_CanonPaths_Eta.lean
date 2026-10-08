-- Prove2me | Definitions.Def_DiaconisStroock_CanonPaths_Eta
-- name    : DiaconisStroock_CanonPaths_Eta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:06:42.727584+00:00
-- url     : https://prove2.me/theorems/87de8e9e-f406-442a-a834-a09e92c19782
-- title:
--   Canonical-path congestion η, equation (3.2)
-- statement:
--   Choose one walk $\gamma_{xy}$ from $x$ to $y$ for each distinct ordered pair of states. For every directed edge $e=(u,v)$ with positive stationary flow $Q(e)=\pi(u)P(u,v)$, sum the weights $\pi(x)\pi(y)$ of pairs whose chosen walk traverses $e$. The **congestion** is
--
--   $$
--   \eta=\max_{e:Q(e)>0}\frac{1}{Q(e)}\sum_{x\ne y:\,e\in\gamma_{xy}}\pi(x)\pi(y).
--   $$
--
--   This is the geometric quantity in Proposition 7. The module also defines the maximum number $b$ of selected ordered-pair walks traversing one directed pair, for the graph specialization (3.3).
--
--   **Formalization Note** Equal-endpoint pairs are excluded from both sums; they play no role in moving across a cut. A walk traversing the same directed edge more than once contributes its pair weight once. The maximum is over positive-flow directed edges and has Lean's default value zero if there are none; the theorem's irreducibility and two-state assumption rule out that case.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 54, §3B, (3.2); https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_lower
import Definitions.Def_DiaconisStroock_Poincare_Paths

namespace DiaconisStroock.CanonPaths

open MarkovMixing

/-- A selected walk for every distinct ordered pair of states (§3B, p. 54). -/
def IsWalkSystem {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ)
    (Γ : V → V → List V) : Prop :=
  ∀ x y : V, x ≠ y → DiaconisStroock.Poincare.IsWalk P π x y (Γ x y)

/-- The directed-edge canonical-path congestion η of (3.2), p. 54. The selected walks for
equal endpoints do not contribute. A walk contributes to an edge when it traverses that oriented
edge at least once. -/
noncomputable def eta {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ)
    (π : V → ℝ) (Γ : V → V → List V) : ℝ :=
  ⨆ e : {e : V × V // 0 < edgeMeasure P π e.1 e.2},
    (edgeMeasure P π e.1.1 e.1.2)⁻¹ *
      ∑ x : V, ∑ y : V,
        if x ≠ y ∧ e.1 ∈ DiaconisStroock.Poincare.pathEdges (Γ x y) then π x * π y else 0

/-- The largest number of selected walks through one oriented pair. -/
noncomputable def directedLoad {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : V → V → List V) : ℕ :=
  Finset.univ.sup fun e : V × V =>
    (Finset.univ.filter fun xy : V × V =>
      xy.1 ≠ xy.2 ∧ e ∈ DiaconisStroock.Poincare.pathEdges (Γ xy.1 xy.2)).card

end DiaconisStroock.CanonPaths


