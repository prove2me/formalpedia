-- Prove2me | Definitions.Def_DiaconisStroock_Poincare_Kappa
-- name    : DiaconisStroock_Poincare_Kappa
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:57.680585+00:00
-- url     : https://prove2.me/theorems/1c35bb01-5c4e-4179-b30a-a27c89c9b75c
-- title:
--   §1B, (1.5) and Proposition 1′ — path systems and directed-edge congestion
-- statement:
--   Let $\Gamma$ choose one edge-simple path $\gamma_{xy}$ for each ordered pair of distinct states $x,y$. With $Q(z,w)=\pi(z)P(z,w)$, define the directed-edge congestion from (1.5) by
--
--   $$
--   \kappa(\Gamma)=\max_{e}\sum_{\gamma_{xy}\ni e}|\gamma_{xy}|_Q\,\pi(x)\pi(y),
--   $$
--
--   where $e$ ranges over directed edges with $Q(e)>0$ and $\gamma_{xy}\ni e$ means that the path traverses $e$ in that direction. Proposition 1′ uses the alternative
--
--   $$
--   K(\Gamma)=\max_e Q(e)^{-1}\sum_{\gamma_{xy}\ni e}|\gamma_{xy}|\,\pi(x)\pi(y),
--   $$
--
--   with $|\gamma_{xy}|$ the number of edges. These are the two congestion parameters in the paper's eigenvalue bounds.
--
--   **Formalization Note** The choice of $\Gamma(x,x)$ is ignored. The real supremum over the finite positive-edge subtype equals the maximum when this subtype is nonempty; it has Lean's default value zero when empty. The mission's eigenvalue theorems assume irreducibility and at least two states, which exclude that case.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), pp. 37–38, (1.5), Proposition 1′, https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Paths

namespace DiaconisStroock.Poincare

open MarkovMixing
open scoped BigOperators

/-- A choice of one edge-simple path for every ordered pair of distinct states (§1B, p. 37). -/
def IsPathSystem {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ)
    (Γ : V → V → List V) : Prop :=
  ∀ x y : V, x ≠ y → IsPath P π x y (Γ x y)

/-- The directed-edge congestion κ(Γ) of (1.5), p. 37. -/
noncomputable def kappa {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ)
    (Γ : V → V → List V) : ℝ :=
  ⨆ e : {e : V × V // 0 < edgeMeasure P π e.1 e.2},
    ∑ x, ∑ y,
      if x ≠ y ∧ e.1 ∈ pathEdges (Γ x y) then qLength P π (Γ x y) * π x * π y else 0

/-- Sinclair's alternative directed-edge congestion K from Proposition 1′, p. 38. -/
noncomputable def sinclairK {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ)
    (π : V → ℝ) (Γ : V → V → List V) : ℝ :=
  ⨆ e : {e : V × V // 0 < edgeMeasure P π e.1 e.2},
    (edgeMeasure P π e.1.1 e.1.2)⁻¹ *
      ∑ x, ∑ y,
        if x ≠ y ∧ e.1 ∈ pathEdges (Γ x y) then
          ((pathEdges (Γ x y)).length : ℝ) * π x * π y else 0

end DiaconisStroock.Poincare


