-- Prove2me | Definitions.Def_ZeroOneExpansion_Sn
-- name    : ZeroOneExpansion_Sn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:10.702331+00:00
-- url     : https://prove2.me/theorems/3a4d23d7-f311-4765-afc6-40d51090090f
-- title:
--   Profile counts $A_{k,\ell}$ and the cut $S_n=\{u: |I(u)|<|J(u)|\}$
-- statement:
--   For $0\le k,\ell\le n$,
--   $$A_{k,\ell}=\binom nk\binom n\ell 3^k2^\ell,$$
--   the number of lower-layer vertices of $P_n$ with active-block profile $(|I(u)|,|J(u)|)=(k,\ell)$. The cut is
--   $$S_n=\{u\in V_n: |I(u)|<|J(u)|\}.$$
--
--   $S_n$ is the admissible set whose boundary ratio bounds $h(G_n)$ in Theorem 14.
--
--   **Formalization Note** $S_n$ is a set of vertices of $G_n$.
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), §4, p.7, A_{k,ℓ} and display (1)

import Mathlib
import Definitions.Def_ZeroOneExpansion_Pn

set_option autoImplicit false

namespace ZeroOneExpansion

/-- `A_{k,ℓ} := C(n, k) C(n, ℓ) 3^k 2^ℓ` (arXiv:2608.01870, §4, p.7), the number of lower-layer
vertices of `Pn` with active-block profile `(k, ℓ)`. -/
def Acount (n k l : ℕ) : ℕ := n.choose k * n.choose l * 3 ^ k * 2 ^ l

/-- The cut `Sn := {u ∈ Vn : |I(u)| < |J(u)|}` (arXiv:2608.01870, §4, display (1), p.7), as a set of
vertices of `Gn`. -/
def Sn (n : ℕ) : Set (Grunbaum2003.PolytopeVertex (Pn n)) :=
  {u | (Iset n u.val).card < (Jset n u.val).card}

end ZeroOneExpansion


