-- Prove2me | Definitions.Def_AronszajnRK_Sum_IsReproducingKernelOn
-- name    : AronszajnRK_Sum_IsReproducingKernelOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:30:59.082832+00:00
-- url     : https://prove2.me/theorems/d601963a-8839-49d0-91ac-654824b1a759
-- title:
--   Reproducing kernel of a linear subspace of an RKHS
-- statement:
--   Let $F$ be a complex Hilbert space of functions on a set $E$ with continuous point evaluations, and let $S\subseteq F$ be a linear subspace. A family $(k_y)_{y\in E}$ of elements of $F$ is a **reproducing kernel of $S$** if
--
--   1. $k_y\in S$ for every $y\in E$;
--   2. for every $y\in E$ and every $f\in S$,
--   $$f(y)=(f,\,k_y).$$
--
--   The corresponding scalar kernel of $S$ is $K_S(x,y)=k_y(x)$. This is the definition of a reproducing kernel applied to $S$ with the norm inherited from $F$; it is used to state that closed subspaces have reproducing kernels and that the kernels of complementary subspaces add up.
--
--   **Formalization Note** The paper's scalar product $(f,g)$ is linear in $f$; Mathlib's `⟪g, f⟫_ℂ` is linear in $f$, so condition 2 is written `⟪k y, f⟫_ℂ = f y`.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 343, §1, Definition; applied to subspaces in p. 345, §2 (7)

import Mathlib

open scoped InnerProductSpace

namespace AronszajnRK.Sum

/-- `k` is a reproducing kernel of the linear subspace `S` of the complex Hilbert space `H` of
functions on `X` (Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950),
§1, Definition, conditions 1 and 2, p. 343 (PDF 7), applied to a subspace as in §2 (7),
p. 345 (PDF 9)):
1. for every `y`, the function `K(·, y)`, here the element `k y`, belongs to `S`;
2. the reproducing property: for every `y` and every `f ∈ S`, `f(y) = (f, K(·, y))`.

Aronszajn's scalar product `(f, g)` is linear in `f`; Mathlib's `⟪g, f⟫_ℂ` is linear in its
second argument, so Aronszajn's `(f, k y)` is `⟪k y, f⟫_ℂ`. -/
def IsReproducingKernelOn {X : Type*} {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [RKHS ℂ H X ℂ] (S : Submodule ℂ H) (k : X → H) : Prop :=
  (∀ y, k y ∈ S) ∧ ∀ y, ∀ f ∈ S, ⟪k y, f⟫_ℂ = f y

end AronszajnRK.Sum


