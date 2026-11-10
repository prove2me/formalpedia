-- Prove2me | Definitions.Def_SetDefinedGraphs_realisation
-- name    : SetDefinedGraphs_realisation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:29.19389+00:00
-- url     : https://prove2.me/theorems/005e8bca-19ac-4364-a874-4ebcd6c08adc
-- title:
--   Realisation of a Boolean function $f$ over a set of vectors $V\subseteq\mathbb N^d$
-- statement:
--   Fix $d\in\mathbb N$ and a Boolean function $f:\{0,1\}^{d^2}\to\{0,1\}$ of the variables $q_{i,j}$, $i,j\in[d]$. For vectors $u,w\in\mathbb N^d$ the **equality pattern** is
--   $$Q_{u,w}(i,j)=\begin{cases}1,&u_i=w_j,\\0,&u_i\ne w_j.\end{cases}$$
--   For a set $V\subseteq\mathbb N^d$, the **realisation of $f$ over $V$** is the digraph with vertex set $V$ and an arc from $u$ to $w$ if and only if
--   $$f\bigl(Q_{u,w}(1,1),Q_{u,w}(1,2),\dots,Q_{u,w}(d,d)\bigr)=1 .$$
--   So adjacency depends only on which coordinates of the two vectors are equal. The module states this for vectors indexed by an arbitrary coordinate type, so that restricted vectors $v|_I\in\mathbb N^I$ use the same notion.
--
--   **Formalization Note** $f$ is a map from $d\times d$ Boolean matrices to Booleans (paper coordinate $i$ is index $i-1$). The paper's digraphs are loopless (p.2, p.14), so an arc additionally requires $u\ne w$.
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.2 (PDF p.4) and §3.1 p.14 (PDF p.16): realisation of f over V

import Mathlib

set_option autoImplicit false

namespace SetDefinedGraphs

/-- The **equality pattern** `Q_{u,w}` of two vectors `u, w ∈ ℕ^ι` (arXiv:2607.23754, §1.1 p.2 and §3.1 p.14):
`Q_{u,w}(i, j) = 1` if `u_i = w_j` and `Q_{u,w}(i, j) = 0` otherwise. It is the assignment of the variables `q_{i,j}`
of a Boolean function at the ordered pair `(u, w)`. -/
def eqPattern {ι : Type} (u w : ι → ℕ) : ι → ι → Bool :=
  fun i j => decide (u i = w j)

/-- The **realisation** of a Boolean function `f : {0,1}^{ι × ι} → {0,1}` over a set `V ⊆ ℕ^ι`
(Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev, *Set-defined graph classes: χ-boundedness meets tropical algebra*,
arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.2 and §3.1 p.14): the digraph with vertex set `V` and an arc
from `u` to `w` if and only if `f(Q_{u,w}) = 1`. For `ι = Fin d` this is the paper's `d`-dimensional realisation.

**Formalization Note** A Boolean function on the `d²` variables `q_{i,j}` is a map `(Fin d → Fin d → Bool) → Bool`
(the argument is the matrix of variable values; paper coordinate `i` is index `i − 1`). The paper's digraphs are
loopless (p.2: "Our digraphs are assumed to be without loops"; p.14), so an arc also requires `u ≠ w`. -/
def realisation {ι : Type} (f : (ι → ι → Bool) → Bool) (V : Set (ι → ℕ)) : Digraph V where
  Adj u w := u ≠ w ∧ f (eqPattern u.1 w.1) = true

end SetDefinedGraphs


