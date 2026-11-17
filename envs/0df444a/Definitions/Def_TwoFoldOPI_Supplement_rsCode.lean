-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_rsCode
-- name    : TwoFoldOPI_Supplement_rsCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:53:18.852379+00:00
-- url     : https://prove2.me/theorems/fa51042a-5413-4d03-9079-65e84854a8ce
-- title:
--   The Reed–Solomon code $\mathrm{RS}_{\mathbb F_q,\gamma,k}$
-- statement:
--   For a finite field $\mathbb F_q$, an element $\gamma$ and $k\ge0$,
--   $$\mathrm{RS}_{\mathbb F_q,\gamma,k}=\{(f(\gamma),f(\gamma^2),\dots,f(\gamma^{q-1})): f\in\mathbb F_q[X],\ \deg f\le k-1\}\subseteq\mathbb F_q^{q-1}.$$
--
--   With $\gamma$ a generator of $\mathbb F_q^*$ this is the code $C_\lambda$ of Definition 11.1 and $C_q$ of Definition 12.1.
--
--   **Formalization Note** Coordinate $j\in\{0,\dots,q-2\}$ is the evaluation at $\gamma^{j+1}$. Statements require $\gamma$ to have order $q-1$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.3, p. 21

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **The Reed–Solomon code `RS_{F_q,γ,k}`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.3, p.21: "Let F_q be a field, k ∈ [1, q − 1] an integer, γ a generator
of F_q^*, and v ∈ F_q^{q−1} some vector of nonzero elements. Then the generalized Reed–Solomon
code GRS_{F_q,γ,k,v} is defined as: {(v_1 f(γ), v_2 f(γ^2), …, v_{q−1} f(γ^{q−1})) : f ∈ F_q[X],
deg f ≤ k − 1}. … When v is the all 1's vector, we simply refer to this as the Reed–Solomon code
RS_{F_q,γ,k}."

`rsCode γ k = {(f(γ^1), f(γ^2), …, f(γ^{q−1})) : deg f ≤ k − 1} ⊆ K^{q−1}`, `q = |K|`; coordinate
`j ∈ {0, …, q−2}` is the evaluation at `γ^{j+1}`.

**Formalization Note.** `deg f ≤ k − 1` is `f ∈ K[X]_{<k}` (`Polynomial.degreeLT K k`). The code is
the image of that space under the evaluation map, so it is `K`-linear. Statements supply `γ` with
`orderOf γ = q − 1` (a generator of `K^*`). -/
noncomputable def rsCode {K : Type*} [Field K] [Fintype K] (γ : K) (k : ℕ) :
    Submodule K (Fin (Fintype.card K - 1) → K) :=
  (Polynomial.degreeLT K k).map
    (LinearMap.pi fun j : Fin (Fintype.card K - 1) => Polynomial.leval (γ ^ (j.val + 1)))

end Supplement

end TwoFoldOPI


