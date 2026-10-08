-- Prove2me | Definitions.Def_HomeomorphAction
-- name    : HomeomorphAction
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-06T10:43:45.064788+00:00
-- url     : https://prove2.me/theorems/6b1b59b6-feec-409b-ae29-db476c157c19
-- title:
--   Homeomorphism groups act on their spaces — f • x = f x
-- statement:
--   `HomeomorphAction.applyMulAction` makes the group of homeomorphisms of a topological space $X$ (`X ≃ₜ X`, with composition as multiplication) act on $X$ by evaluation: $f \cdot x = f(x)$.
--
--   Every subgroup of `OnePoint ℝ ≃ₜ OnePoint ℝ`, the homeomorphisms of the projective line $\mathbf P^1 = \mathbb R \cup \{\infty\}$, then acts on $\mathbf P^1$ by restricting this action. This is how the statements of the package act with Monod's groups $H$ (`Monod.Hpp`) and $H(\mathbb Z)$ (`Monod.H ⊥`) and their subgroups, as in Juschenko, Matte Bon, Monod and de la Salle (§6, p. 22), where these groups act on the line by evaluation.
-- source:
--   Standalone definition: the action of the homeomorphism group of a space on the space, f • x = f x, used for the action of subgroups of Monod's groups on P¹ in Juschenko, K., Matte Bon, N., Monod, N. and de la Salle, M., Extensive amenability and an application to interval exchanges, Ergodic Theory Dynam. Systems 38 (2018) 195–219, https://doi.org/10.1017/etds.2016.32 (arXiv:1503.04977v1, whose page numbers are used), p. 22, §6

import Mathlib

/-!
# The action of homeomorphisms on their space

The homeomorphism group of a topological space acts on the space by evaluation.
-/

/-- The action of the homeomorphism group of a topological space `X` on `X`: `f • x = f x`. -/
instance HomeomorphAction.applyMulAction {X : Type*} [TopologicalSpace X] :
    MulAction (X ≃ₜ X) X where
  smul f x := f x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl


