-- Prove2me | Definitions.Def_KnapsackFacets_EvcToCss
-- name    : KnapsackFacets_EvcToCss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:43.029755+00:00
-- url     : https://prove2.me/theorems/fa8c77ca-d8f2-4c21-8e97-bcbdee8bc6da
-- title:
--   The EVC instance on an edge list and the EVC → CSS construction
-- statement:
--   Let $V=\{v_1,\dots,v_n\}$ and let $E=\{e_1,\dots,e_m\}$ be the edges of a graph. The EVC instance $(V,E,k)$ has answer “yes” when some $V'\subseteq V$ of size $k$ meets every edge and no $V'$ of size $k-1$ does.
--
--   The construction in the proof of Theorem 2 maps $(V,E,k)$ to the CSS instance $(w,t)$ with
--   $$
--   w_i=1+\sum_{j=1}^m (n+1)^j\,\mathbb 1(v_i\in e_j)\quad(i=1,\dots,n),\qquad w_{n+j}=(n+1)^j\quad(j=1,\dots,m),
--   $$
--   $$
--   t=n-k+1+\sum_{j=1}^m(n+1)^j .
--   $$
--
--   This is the base-$(n+1)$ digit construction behind the reduction from EVC to CSS.
--
--   **Formalization Note** $V$ is `Fin n` and the edges are a family $e:\{0,\dots,m-1\}\to$ `Sym2 (Fin n)`; the paper's $e_j$ is $e(j-1)$ and its exponent $j$ is `j.val + 1`. The weight vector has the $n$ vertex weights first and the $m$ edge weights after them; $t$ is an integer.
-- source:
--   Chen & Zhu, The Complexity of Recognizing Facets for the Knapsack Polytope, arXiv:2211.03311v3, §2, p.3 (EVC) and Theorem 2, proof, p.4 (definition of w and t)

import Mathlib

set_option autoImplicit false

namespace KnapsackFacets

/-- **Vertex cover of an edge list.** For vertices `V = Fin n` and edges `e₁, …, e_m`
(`e : Fin m → Sym2 (Fin n)`), `C` meets every edge. Chen & Zhu, arXiv:2211.03311v3, §2, p.3
("V′ ∩ e ≠ ∅ for all e ∈ E") and p.4 ("Assume V = {v1, . . . , vn} and E = {e1, . . . , em}").

**Formalization Note.** Vertex `vᵢ` is `i - 1 : Fin n`, edge `e_j` is `e (j - 1)`. -/
def IsEdgeCover {n m : ℕ} (e : Fin m → Sym2 (Fin n)) (C : Finset (Fin n)) : Prop :=
  ∀ j : Fin m, ∃ v ∈ C, v ∈ e j

/-- **A “yes” instance `(V, E, k)` of exact vertex cover**, for `V = Fin n` and
`E = {e₁, …, e_m}`: there is a vertex cover of size `k` and none of size `k − 1`.
Chen & Zhu, arXiv:2211.03311v3, §2, p.3 (definition of EVC). -/
def EVCYesEdges {n m : ℕ} (e : Fin m → Sym2 (Fin n)) (k : ℕ) : Prop :=
  (∃ C : Finset (Fin n), C.card = k ∧ IsEdgeCover e C) ∧
    ¬ ∃ C : Finset (Fin n), C.card = k - 1 ∧ IsEdgeCover e C

/-- **The weights of the EVC → CSS reduction.** Chen & Zhu, arXiv:2211.03311v3, proof of
Theorem 2, p.4: "For i = 1, . . . , n, define wᵢ := 1 + Σ_{j=1}^m (n + 1)ʲ 𝟙(vᵢ ∈ eⱼ). For
j = 1, . . . , m, define w_{n+j} := (n + 1)ʲ."

**Formalization Note.** The weight vector is `Fin (n + m) → ℕ`, the first `n` entries for the
vertices, the last `m` for the edges (`Fin.append`); the paper's index `j ∈ {1, …, m}` is
`j.val + 1` for `j : Fin m`. -/
def evcCssWeights {n m : ℕ} (e : Fin m → Sym2 (Fin n)) : Fin (n + m) → ℕ :=
  Fin.append
    (fun i : Fin n => 1 + ∑ j : Fin m, if i ∈ e j then (n + 1) ^ (j.val + 1) else 0)
    (fun j : Fin m => (n + 1) ^ (j.val + 1))

/-- **The target of the EVC → CSS reduction.** Chen & Zhu, arXiv:2211.03311v3, proof of
Theorem 2, p.4: "Define t := n − k + 1 + Σ_{j=1}^m (n + 1)ʲ."

**Formalization Note.** `t` is an integer (`n − k` is integer subtraction). -/
def evcCssTarget {n m : ℕ} (_e : Fin m → Sym2 (Fin n)) (k : ℕ) : ℤ :=
  (n : ℤ) - k + 1 + ∑ j : Fin m, ((n : ℤ) + 1) ^ (j.val + 1)

end KnapsackFacets


