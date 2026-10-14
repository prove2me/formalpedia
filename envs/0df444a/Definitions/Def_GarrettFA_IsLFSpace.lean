-- Prove2me | Definitions.Def_GarrettFA_IsLFSpace
-- name    : GarrettFA_IsLFSpace
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T19:27:33.459603+00:00
-- url     : https://prove2.me/theorems/16280af1-55bd-493b-896d-64acf81c1044
-- title:
--   LF-space (strict colimit of Fréchet spaces)
-- statement:
--   A topological vector space $V$ over $\mathbb K=\mathbb R$ or $\mathbb C$ is an **LF-space** if there is a chain of subspaces $V_0\subsetneq V_1\subsetneq\cdots$ such that $V$ is the strict colimit of the $V_n$ and every $V_n$, with the subspace topology, is a Fréchet space, i.e. metrizable and complete. Each $V_n$ is locally convex automatically, as a subspace of the locally convex space $V$.
--
--   Examples are the spaces of test functions $C_c^\infty(\mathbb R^n)$ and $C_c^o(\mathbb R^n)$, and $\mathbb C^\infty$.
--
--   **Formalization Note** Completeness of $V_n$ is completeness of $V_n$ as a subset of $V$ for the uniform structure of $V$.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 1 and p. 2, §1.3 ("A strict colimit of Fréchet spaces is an LF-space")

import Definitions.Def_GarrettFA_IsStrictColimit

namespace GarrettFA

/-- Garrett, *Completeness and quasi-completeness*, §1.3: an LF-space is a strict colimit of a
countable chain of Fréchet spaces. Here `V` is the strict colimit of the chain `F` and each
`F n`, with the subspace topology and uniformity from `V`, is metrizable and complete
(it is automatically locally convex, being a subspace of a locally convex space). -/
def IsLFSpace (𝕜 : Type*) (V : Type*) [RCLike 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [Module ℝ V] [IsScalarTower ℝ 𝕜 V] [UniformSpace V] : Prop :=
  ∃ F : ℕ → Submodule 𝕜 V, IsStrictColimit 𝕜 F ∧
    ∀ n, TopologicalSpace.MetrizableSpace (F n) ∧ IsComplete (F n : Set V)

end GarrettFA


