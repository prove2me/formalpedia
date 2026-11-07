-- Prove2me | Definitions.Def_PRUPermLayer_friedrichsCos
-- name    : PRUPermLayer_friedrichsCos
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:52.51725+00:00
-- url     : https://prove2.me/theorems/33eaa747-31f2-40cf-a909-8728df71f79a
-- title:
--   Friedrichs cosine $c(A,B) = \|\Pi_A\Pi_B - \Pi_{A\cap B}\|$
-- statement:
--   For subspaces $A, B$ with projectors $\Pi_A, \Pi_B$ and intersection projector $\Pi_{A \cap B}$, the **Friedrichs cosine** is
--   $$
--   c(A, B) = \big\|\Pi_A \Pi_B - \Pi_{A\cap B}\big\|,
--   $$
--   with $\|\cdot\|$ the operator norm. It is $0$ when the parts of $A$ and $B$ orthogonal to $A\cap B$ are orthogonal to each other.
--
--   **Formalization Note** $\|\cdot\|$ is the published spectral norm (largest singular value).
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_PRUPermLayer_projMat

namespace PRUPermLayer

/-- The Friedrichs cosine `c(A, B) = ‖Π_A Π_B − Π_{A∩B}‖` of two subspaces, an operator norm
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.3, p.10 (PDF p.12), citing [KW89]).

**Formalization Note** `‖·‖` is the operator norm (`QAlgorithms.specNorm`, the largest singular
value), as fixed on p.8. -/
noncomputable def friedrichsCos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K₁ K₂ : Submodule ℂ (EuclideanSpace ℂ ι)) : ℝ :=
  QAlgorithms.specNorm (projMat K₁ * projMat K₂ - projMat (K₁ ⊓ K₂))

end PRUPermLayer


