-- Prove2me | Definitions.Def_AronszajnRK_Product_IsFunctionalCompletion
-- name    : AronszajnRK_Product_IsFunctionalCompletion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:34:07.695779+00:00
-- url     : https://prove2.me/theorems/dcbbf046-1611-48bb-a6eb-fcff14f12af4
-- title:
--   Functional completion of a class of functions forming an incomplete Hilbert space
-- statement:
--   Let $F$ be a linear class of complex-valued functions on a set $X$ carrying a scalar product that satisfies all the axioms of a Hilbert space except possibly completeness. We present $F$ as an inner product space $G$ together with an injective linear map $\iota : G \to \mathbb{C}^X$ assigning to each element the function it is.
--
--   A complex Hilbert space $H$ of functions on $X$ in which every point evaluation is continuous is a **functional completion** of $F$ if there is a linear isometry $j : G \to H$ with dense range such that
--
--   $$
--   j(g) = \iota(g) \quad \text{as functions on } X, \qquad g \in G.
--   $$
--
--   In words: the completed class is obtained by adjoining functions to $F$, contains $F$ with its norm as a dense subset, and the value of a function of the completed class at a given point depends continuously on the function.
--
--   This is the notion of completion under which §4 of the paper proves existence criteria and uniqueness, and by which the direct product $F_1 \otimes F_2$ of §8 is constructed.
--
--   **Formalization Note** Continuity of point evaluations is the `RKHS ℂ H X ℂ` structure on $H$. Isometry plus linearity gives that the scalar product of $F$ is preserved.
-- source:
--   Aronszajn, Theory of Reproducing Kernels, Trans. Amer. Math. Soc. 68 (1950), p. 347, §4

import Mathlib

namespace AronszajnRK.Product

/-- **Functional completion** (N. Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math.
Soc. 68 (1950), §4, p. 347, PDF p. 11). The class of functions `F` is presented as a complex
inner product space `G` (not assumed complete) together with a linear map `ι : G → (X → ℂ)`
sending each element to the function it is. A complex Hilbert space `H` of functions on `X`
with continuous point evaluations (an `RKHS`) is a functional completion of `F` when there is
a linear isometry `j : G → H` with dense range such that `j g` is the same function as `ι g`:
the completed class contains `F` with its norm as a dense subset, and the value of an element
at each point depends continuously on the element. -/
def IsFunctionalCompletion {X G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (ι : G →ₗ[ℂ] (X → ℂ)) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] : Prop :=
  ∃ j : G →ₗᵢ[ℂ] H, DenseRange j ∧ ∀ g : G, ⇑(j g) = ι g

end AronszajnRK.Product


