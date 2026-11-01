-- Prove2me | Definitions.Def_WildeQIT_EADamping_idTensorApply
-- name    : WildeQIT_EADamping_idTensorApply
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:52.159816+00:00
-- url     : https://prove2.me/theorems/f1883dd0-8a7b-4d75-ade2-f4310fb84ec8
-- title:
--   A channel acting on one share of a bipartite operator, $(\mathrm{id}_A\otimes\mathcal N_{A'\to B})(X_{AA'})$
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel with Kraus operators $\{K_i\}$, and let $X_{AA'}$ be an operator on $A\otimes A'$, where $A$ is a reference system with a finite basis. The channel acting on the $A'$ share is
--
--   $$
--   (\mathrm{id}_A\otimes\mathcal N_{A'\to B})(X_{AA'})=\sum_i (I_A\otimes K_i)\,X_{AA'}\,(I_A\otimes K_i)^\dagger ,
--   $$
--
--   an operator on $A\otimes B$. The book writes it $\mathcal N_{A'\to B}(X_{AA'})$; it produces the state $\rho_{AB}=\mathcal N_{A'\to B}(\varphi_{AA'})$ whose mutual information enters $I(\mathcal N)$.
--
--   **Formalization Note** Operators on $A\otimes A'$ are matrices indexed by the product type `r × a` (Kronecker convention), with the reference on the left.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §13.4, p. 406, (13.120); Theorem 21.3.1, p. 593

import Definitions.Def_WildeQIT_QChannel
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §13.4, p. 406, (13.120), and
§21.3, p. 593 (`σ_{AB} ≡ N_{A′→B}(Φ_{AA′})`): the channel acts on the `A′` share of a bipartite state.
-/

open Matrix
open scoped Kronecker

namespace WildeQIT.EADamping

/-- **The channel acting on one share of a bipartite operator**, `(id_A ⊗ N_{A′→B})(X_{AA′})`
(Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 406, (13.120); p. 593):
with Kraus operators `Kᵢ` of `N`, `(id ⊗ N)(X) = ∑ᵢ (I ⊗ Kᵢ) X (I ⊗ Kᵢ)†`. The book writes it
`N_{A′→B}(φ_{AA′})`.

**Formalization Note.** The reference system (the book's `A`) is the left factor of the product
index type `r × a`; the channel input `A′` is the right factor. -/
def idTensorApply {r a b : Type} [Fintype r] [DecidableEq r] [Fintype a] [Fintype b]
    [DecidableEq a] (N : QChannel a b) (X : Matrix (r × a) (r × a) ℂ) : Matrix (r × b) (r × b) ℂ :=
  ∑ i, ((1 : Matrix r r ℂ) ⊗ₖ N.K i) * X * ((1 : Matrix r r ℂ) ⊗ₖ N.K i)ᴴ

end WildeQIT.EADamping


