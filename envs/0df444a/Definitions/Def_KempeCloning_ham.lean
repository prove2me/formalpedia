-- Prove2me | Definitions.Def_KempeCloning_ham
-- name    : KempeCloning_ham
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:24:09.180318+00:00
-- url     : https://prove2.me/theorems/b33cf34b-a70f-4e28-9923-04961a1bbf06
-- title:
--   The Hamiltonian $\mathcal H = \gamma(a_1b_2 - a_2b_1)c^\dagger + \mathrm{h.c.}$ (14)
-- statement:
--   For a real coupling constant $\gamma$, the Hamiltonian of Eq. (14) is
--
--   $$\mathcal H = \gamma\,(a_1 b_2 - a_2 b_1)\,c^\dagger + \mathrm{h.c.} = \gamma\,(a_1 b_2 c^\dagger - a_2 b_1 c^\dagger) + \gamma\,(c\, b_2^\dagger a_1^\dagger - c\, b_1^\dagger a_2^\dagger).$$
--
--   It describes $N$ $\Lambda$-atoms (in the Schwinger representation, modes $b_1, b_2, c$) coupled to two photon modes $a_1, a_2$: the term $c\,b_2^\dagger a_1^\dagger$ de-excites an atom from $e$ to $g_2$ while emitting a photon into $a_1$. It is the Hamiltonian the paper uses from Sec. II B on.
--
--   **Formalization Note** $\gamma$ is real: the paper notes that a phase in either mode can be absorbed into $\gamma$, and the recursion (21) is for real $\gamma$. The Hermitian conjugate is written out with the order of factors reversed. Operator products are compositions of linear maps on finite superpositions of number states.
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, (14), p.4

import Definitions.Def_KempeCloning_ann
import Definitions.Def_KempeCloning_cre

namespace KempeCloning

open Mode

/-- **The Hamiltonian (14): `H = γ(a₁b₂ − a₂b₁)c† + h.c.`**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, (14), p.4: "it is slightly more
convenient for our purposes to use the following Hamiltonian instead of (12):
H = γ(a1b2 − a2b1)c† + h.c., (14) […] This is the Hamiltonian that is going to be used in the
rest of this paper."

For a real coupling constant `γ`,
`H = γ (a₁ b₂ c† − a₂ b₁ c†) + γ (c b₂† a₁† − c b₁† a₂†)`,
the second bracket being the Hermitian conjugate of the first.

**Formalization Note.** `γ` is real: the paper notes that "a phase transformation in either mode
can be absorbed into γ" (p.4), and the recursion (21) is stated for real `γ`. The Hermitian
conjugate is written out: `(a₁b₂c†)† = c b₂† a₁†`, with the operator product read right to left as
composition (`ann c ∘ₗ cre b2 ∘ₗ cre a1` applies `a₁†` first). Operators on distinct modes commute,
so the order inside each term does not matter. -/
noncomputable def ham (γ : ℝ) : FockVec →ₗ[ℂ] FockVec :=
  (γ : ℂ) • (ann a1 ∘ₗ ann b2 ∘ₗ cre c - ann a2 ∘ₗ ann b1 ∘ₗ cre c) +
    (γ : ℂ) • (ann c ∘ₗ cre b2 ∘ₗ cre a1 - ann c ∘ₗ cre b1 ∘ₗ cre a2)

end KempeCloning


