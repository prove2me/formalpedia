-- Prove2me | Definitions.Def_ChanPangGQVI_Existence_IsContractibleSet
-- name    : ChanPangGQVI_Existence_IsContractibleSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:36:30.957375+00:00
-- url     : https://prove2.me/theorems/297e7c32-e521-4ba0-af0b-a4d842ef284e
-- title:
--   Contractible subset of $\mathbb R^n$
-- statement:
--   A subset $S$ of $\mathbb R^n$ is **contractible** if there are a point $x\in S$ and a continuous function $g : S\times[0,1]\to S$ such that
--
--   $$
--   g(x',0)=x' \quad\text{and}\quad g(x',1)=x \qquad\text{for all } x'\in S.
--   $$
--
--   A contractible set is in particular nonempty, and every nonempty convex set is contractible (take $g(x',t)=(1-t)x'+tx$). Contractible compact values are the hypothesis under which the Eilenberg–Montgomery fixed point theorem applies to upper semicontinuous point-to-set mappings; they generalise the convex values of Kakutani's theorem.
--
--   **Formalization Note** The homotopy is a function $g:\mathbb R^n\times\mathbb R\to\mathbb R^n$ that is continuous on $S\times[0,1]$ and maps $S\times[0,1]$ into $S$; its values elsewhere play no role.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 214, Section 3 (definition of a contractible set)

import Mathlib

namespace ChanPangGQVI.Existence

/-- Chan and Pang 1982, p. 214, §3: a subset `S` of `ℝⁿ` is contractible if there is a point
`x ∈ S` and a continuous function `g : S × [0, 1] → S` such that `g(x', 0) = x'` and
`g(x', 1) = x` for all `x' ∈ S`. The function is represented by `g : ℝⁿ × ℝ → ℝⁿ`, continuous on
`S × [0, 1]` and mapping it into `S`; its values off `S × [0, 1]` are irrelevant. In particular a
contractible set is nonempty. -/
def IsContractibleSet {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ x ∈ S, ∃ g : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n),
    ContinuousOn g (S ×ˢ Set.Icc (0 : ℝ) 1) ∧ Set.MapsTo g (S ×ˢ Set.Icc (0 : ℝ) 1) S ∧
      ∀ x' ∈ S, g (x', 0) = x' ∧ g (x', 1) = x

end ChanPangGQVI.Existence


