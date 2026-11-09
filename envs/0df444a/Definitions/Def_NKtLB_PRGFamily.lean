-- Prove2me | Definitions.Def_NKtLB_PRGFamily
-- name    : NKtLB_PRGFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:56:31.166358+00:00
-- url     : https://prove2.me/theorems/e5edaa8f-399c-4add-952f-152a8563abf9
-- title:
--   Families of generator triples $(G,A,R^{(-)})$
-- statement:
--   A family of triples indexed by $(n,m,k)$, with $\varepsilon=1/k$: a seed length $d(n,m,k)$, a reconstruction-randomness length $r(n,m,k)$, maps
--   $$
--   G,A:\{0,1\}^n\times\{0,1\}^d\to\{0,1\}^m,
--   $$
--   and a non-adaptive oracle procedure $R^{(-)}:\{0,1\}^m\times\{0,1\}^d\times\{0,1\}^r\to\{0,1\}^n$. The procedure $R$ is given as a query map, which lists the queries $q_1,\dots,q_j$ asked of the oracle $D$, and an answer map, which computes the output from the answer bits $D(q_1),\dots,D(q_j)$. This is the shape of the generator of Lemma 31.
--
--   **Formalization Note** All maps are total on bit strings; their values outside the stated domains are irrelevant.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Lemma 31, pp.26–27

import Mathlib

namespace NKtLB

/-- **A family of generator triples `(G, A, R^{(-)})`** indexed by `(n, m, k)`, the shape of
Lemma 31 (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), pp.26–27): `G, A : {0,1}^n × {0,1}^d → {0,1}^m` and
`R^{(-)} : {0,1}^m × {0,1}^d × {0,1}^r → {0,1}^n`, with `ε = 1/k`, seed length `d(n,m,k)` and
reconstruction randomness `r(n,m,k)`. The non-adaptive oracle procedure `R` is a query map `Rq`
(the list of queries it asks `D`) and an answer map `Ra` (the output from the answer bits).

**Formalization Note.** All maps are total on `List Bool`; their values off the stated domains are
irrelevant. `PRGFamily.R F n m k D a z w = Ra a z w (D(q₁), …, D(q_j))` with `(q₁, …, q_j) =
Rq a z w`. -/
structure PRGFamily where
  d : ℕ → ℕ → ℕ → ℕ
  r : ℕ → ℕ → ℕ → ℕ
  G : ℕ → ℕ → ℕ → List Bool → List Bool → List Bool
  A : ℕ → ℕ → ℕ → List Bool → List Bool → List Bool
  Rq : ℕ → ℕ → ℕ → List Bool → List Bool → List Bool → List (List Bool)
  Ra : ℕ → ℕ → ℕ → List Bool → List Bool → List Bool → List Bool → List Bool

/-- The reconstruction `R^D(a, z, w)` with non-adaptive oracle access to `D`. -/
def PRGFamily.R (F : PRGFamily) (n m k : ℕ) (D : List Bool → Bool) (a z w : List Bool) :
    List Bool :=
  F.Ra n m k a z w ((F.Rq n m k a z w).map D)

end NKtLB


