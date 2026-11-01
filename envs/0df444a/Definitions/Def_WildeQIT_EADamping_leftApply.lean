-- Prove2me | Definitions.Def_WildeQIT_EADamping_leftApply
-- name    : WildeQIT_EADamping_leftApply
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:51.304931+00:00
-- url     : https://prove2.me/theorems/ec883273-bf9c-402e-a169-6cfd9049f90c
-- title:
--   A Kraus family acting on Alice's share, $(\mathcal E\otimes\mathrm{id}_{T_B})(X)$
-- statement:
--   Let $\{K_i\}$ be a finite family of operators from a system $S$ to a system $S'$, and let $X$ be an operator on $S\otimes T_B$, where $T_B$ is a system with a finite basis that is left untouched. Then
--
--   $$
--   (\mathcal E\otimes\mathrm{id}_{T_B})(X)=\sum_i (K_i\otimes I_{T_B})\,X\,(K_i\otimes I_{T_B})^\dagger .
--   $$
--
--   In entanglement-assisted coding this is how Alice's encoder $\mathcal E^m_{T_A\to A'^n}$ and the $n$ channel uses $\mathcal N_{A'^n\to B^n}$ act on the global state, while Bob's share $T_B$ of the entanglement is not touched.
--
--   **Formalization Note** The acted-on system is the left factor of the product index type, the untouched system the right factor. No completeness relation is imposed here; every use passes the Kraus family of a channel.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §21.1, p. 589, (21.4)–(21.5)

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.1, p. 589, (21.4)–(21.5)
(an encoding channel `E^m_{T_A→A′ⁿ}` and the channel uses `N_{A′ⁿ→Bⁿ}` act on Alice's share of a
bipartite state, leaving Bob's share `T_B` alone).
-/

open Matrix
open scoped Kronecker

namespace WildeQIT.EADamping

/-- **A Kraus family acting on the left share of a bipartite operator**, `(E ⊗ id_{T_B})(X)`
(Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.1, p. 589, (21.4)–(21.5)):
for Kraus operators `Kᵢ : a → b`, `(E ⊗ id)(X) = ∑ᵢ (Kᵢ ⊗ I) X (Kᵢ ⊗ I)†`.

**Formalization Note.** The acted-on system is the left factor of `a × r`; the untouched system
(Bob's share `T_B` of the entanglement) is the right factor `r`. No completeness relation is
required here; every use passes the Kraus family of a channel. -/
def leftApply {ι a b r : Type} [Fintype ι] [Fintype a] [Fintype r] [DecidableEq r]
    (K : ι → Matrix b a ℂ) (X : Matrix (a × r) (a × r) ℂ) : Matrix (b × r) (b × r) ℂ :=
  ∑ i, (K i ⊗ₖ (1 : Matrix r r ℂ)) * X * (K i ⊗ₖ (1 : Matrix r r ℂ))ᴴ

end WildeQIT.EADamping


