-- Prove2me | Definitions.Def_PlatformCournot_rightDerivLinearization
-- name    : PlatformCournot_rightDerivLinearization
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:19.058651+00:00
-- url     : https://prove2.me/theorems/c995fc62-182f-4ee2-8024-5a832b9aa7dd
-- title:
--   Lemma 2's linearized profile $\bar C_i(s)=(\partial^+C_i(s_i)\,s)^+$
-- statement:
--   Given a cost profile $C$ and a supply profile $q$ with outputs $s_i=\sum_j q_{ij}$, the **linearized cost profile** of Lemma 2 is
--
--   $$\bar C_i(s)=\bigl(\partial^+C_i(s_i)\cdot s\bigr)^+,\qquad i=1,\dots,n,$$
--
--   where $\partial^+C_i$ is the right derivative of $C_i$. Lemma 2 applies it at the Nash equilibrium of the open access game.
--
--   **Formalization Note** The right derivative $\partial^+C_i(x)$ is the derivative within $[x,\infty)$ at $x$ (`derivWithin (C i) (Set.Ici x) x`); for a convex function on $\mathbb R$ it exists everywhere, including at $x=0$.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Lemma 2, p.17

import Mathlib
import Definitions.Def_PlatformCournot_linearCost
import Definitions.Def_PlatformCournot_supply

namespace PlatformCournot

/-- **The piecewise linear cost profile `C̄` of Lemma 2.**
Pang et al., arXiv:1903.04574v3, Lemma 2, p.17: "define the piecewise linear cost function profile
C̄ = (C̄1,...,C̄n) according to C̄i(si) := (∂+Ci(Σ_{j=1}^m qNE_ij(F × M)) · si)^+ for i = 1,...,n,
where ∂+Ci denotes the right-derivative of the function Ci."

`rightDerivLinearization C q i s = (∂⁺Cᵢ(sᵢ) · s)⁺` where `sᵢ` is firm `i`'s output under `q`.

**Formalization Note** The right derivative `∂⁺Cᵢ(x)` is `derivWithin (C i) (Set.Ici x) x`; for a
convex `Cᵢ` on `ℝ` it exists everywhere, including at `x = 0`. The profile `q` is a parameter; Lemma
2 applies it at a Nash equilibrium of the open access game. -/
noncomputable def rightDerivLinearization {n m : ℕ} (C : Fin n → ℝ → ℝ)
    (q : Fin n → Fin m → ℝ) (i : Fin n) : ℝ → ℝ :=
  linearCost (derivWithin (C i) (Set.Ici (supply q i)) (supply q i))

end PlatformCournot


