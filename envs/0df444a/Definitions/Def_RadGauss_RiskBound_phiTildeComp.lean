-- Prove2me | Definitions.Def_RadGauss_RiskBound_phiTildeComp
-- name    : RadGauss_RiskBound_phiTildeComp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:01:39.273138+00:00
-- url     : https://prove2.me/theorems/fb1debb7-ca2c-4629-9e96-1fefd54c85f4
-- title:
--   The centred cost class $\tilde\phi\circ F = \{(x,y)\mapsto \phi(y,f(x))-\phi(y,0)\}$
-- statement:
--   Let $\mathcal X$ be an input space, $\mathcal Y$ an output space and $\mathcal A$ an action space with a distinguished action $0 \in \mathcal A$. For a cost function $\phi : \mathcal Y \times \mathcal A \to \mathbb R$ and a class $F$ of maps $\mathcal X \to \mathcal A$, define the class of functions on $\mathcal X \times \mathcal Y$
--
--   $$\tilde\phi \circ F = \bigl\{(x, y) \mapsto \phi(y, f(x)) - \phi(y, 0) \;:\; f \in F\bigr\}.$$
--
--   Subtracting the cost of the fixed action $0$ centres the class; the risk bound of Theorem 8 is stated with the Rademacher complexity of this centred class, which can be much smaller than that of $\phi \circ F$ when the absolute value is inside the supremum.
--
--   **Formalization Note** The cost is curried, $\phi : \mathcal Y \to \mathcal A \to \mathbb R$, and the distinguished action is the `0` of a `[Zero A]` instance: the paper writes $\phi(y, 0)$ without saying that $\mathcal A$ contains $0$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 467 (PDF p. 5), Theorem 8 (definition of φ̃∘F)

import Mathlib

namespace RadGauss.RiskBound

/-- The class `φ̃ ∘ F = {(x, y) ↦ φ(y, f(x)) − φ(y, 0) : f ∈ F}` of Theorem 8 (p. 467), for a cost
function `φ : 𝒴 × 𝒜 → ℝ` (curried) and a class `F` of maps `𝒳 → 𝒜`; `0` is the distinguished
action `0 ∈ 𝒜`. Its members are functions on `𝒳 × 𝒴`. -/
def phiTildeComp {X Y A : Type*} [Zero A] (φ : Y → A → ℝ) (F : Set (X → A)) :
    Set (X × Y → ℝ) :=
  {h | ∃ f ∈ F, h = fun z => φ z.2 (f z.1) - φ z.2 0}

end RadGauss.RiskBound


