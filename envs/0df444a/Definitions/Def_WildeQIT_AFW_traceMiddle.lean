-- Prove2me | Definitions.Def_WildeQIT_AFW_traceMiddle
-- name    : WildeQIT_AFW_traceMiddle
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:59.733224+00:00
-- url     : https://prove2.me/theorems/d4f2bf5f-9f26-463f-8b64-2e003fb12769
-- title:
--   Partial trace over the middle factor, $\rho_{AC} = \mathrm{Tr}_B\,\rho_{ABC}$
-- statement:
--   Let $\rho_{ABC}$ be an operator on $\mathcal H_A \otimes \mathcal H_B \otimes \mathcal H_C$ with standard bases $\{|a\rangle\}$, $\{|b\rangle\}$, $\{|c\rangle\}$. Its partial trace over the middle system $B$ is the operator on $\mathcal H_A \otimes \mathcal H_C$ with matrix entries
--
--   $$
--   \bigl(\mathrm{Tr}_B\,\rho_{ABC}\bigr)_{(a,c),(a',c')} = \sum_b \bigl(\rho_{ABC}\bigr)_{(a,b,c),(a',b,c')} .
--   $$
--
--   This is the book's partial trace (Definition 4.3.4) applied to the middle factor; it gives the marginal $\rho_{AC}$ that enters the conditional mutual information $I(A;B|C)$.
--
--   **Formalization Note** The tripartite system is the index type `A × (B × C)`, so an index is `(a, (b, c))`. The published `WildeQIT.partialTraceLeft` / `partialTraceRight` trace out an outer factor; this definition handles the middle one.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 4.3.4, p. 142 (partial trace), used for ρAC in (11.88), p. 337

import Mathlib

namespace WildeQIT.AFW

/-- The marginal `ρ_AC = Tr_B ρ_ABC` of a tripartite operator on `A × (B × C)`:
`(Tr_B ρ)_{(a,c),(a',c')} = Σ_b ρ_{(a,(b,c)),(a',(b,c'))}` (Wilde, arXiv:1106.1445v8,
Definition 4.3.4, partial trace over the middle factor). -/
def traceMiddle {A B C : Type} [Fintype B] (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    Matrix (A × C) (A × C) ℂ :=
  Matrix.of fun ac ac' => ∑ b, ρ (ac.1, (b, ac.2)) (ac'.1, (b, ac'.2))

end WildeQIT.AFW


