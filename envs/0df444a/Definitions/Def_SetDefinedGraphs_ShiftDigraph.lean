-- Prove2me | Definitions.Def_SetDefinedGraphs_ShiftDigraph
-- name    : SetDefinedGraphs_ShiftDigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:41.36099+00:00
-- url     : https://prove2.me/theorems/8f3d1247-cb68-495d-ad93-c762aa4658d2
-- title:
--   Canonical shift digraphs $\vec S(n,d)$, $d$-dimensional shift digraphs, shift-colorability, unions of shift-colorable digraphs
-- statement:
--   For integers $n,d$ with $d\ge2$, the **canonical $d$-dimensional shift digraph** $\vec S(n,d)$ has vertex set $\{(u_1,\dots,u_d)\in[n]^d:u_1<\dots<u_d\}$ and an arc from $(u_1,\dots,u_d)$ to $(w_1,\dots,w_d)$ if and only if
--   $$u_k=w_{k-1}\quad\text{for every }k\in\{2,\dots,d\}.$$
--   A **$d$-dimensional shift digraph** is (isomorphic to) an induced subdigraph of some $\vec S(n,d)$; their class is $\vec{\mathcal S}_d$. A **shift digraph** means dimension $2$. A digraph is **shift-colorable** if there is a homomorphism from it to a shift digraph. A digraph $G$ is the **union of at most $c$ shift-colorable digraphs** if there are $k\le c$ shift-colorable digraphs $H_1,\dots,H_k$ on $V(G)$ with
--   $$G(a,b)=H_1(a,b)\vee\dots\vee H_k(a,b)\qquad\text{for all distinct }a,b\in V(G).$$
--
--   **Formalization Note** $[n]$ is $\{0,\dots,n-1\}$, an order isomorphism. A homomorphism into an induced subdigraph of $\vec S(n,2)$ is one into $\vec S(n,2)$, and $\vec S(n,2)$ is a shift digraph, so shift-colorability asks for a homomorphism into $\vec S(n,2)$ for some $n$.
-- source:
--   Adenwalla, Braunfeld, Hons, Sylvester, Zamaraev, Set-defined graph classes: χ-boundedness meets tropical algebra, arXiv:2607.23754 (held version, sha256 642c0d70…), §1.1 p.2 (PDF p.4): canonical shift digraph, shift (di)graph, shift-colorable; §3.2 p.15 (S⃗_d); §3.4 p.17 (union of digraphs)

import Mathlib
import Definitions.Def_FASTournament_induce
import Definitions.Def_FASTournament_Isomorphic
import Definitions.Def_SetDefinedGraphs_DigraphBasics

set_option autoImplicit false

namespace SetDefinedGraphs

/-- The vertices of the canonical shift digraph `S⃗(n, d)`: strictly increasing tuples `(u₁ < ⋯ < u_d)` in `[n]^d`
(arXiv:2607.23754, §1.1 p.2).

**Formalization Note** `[n]` is `Fin n` (`{0, …, n−1}` instead of `{1, …, n}`, an order isomorphism) and paper
coordinate `k` is index `k − 1`. -/
abbrev ShiftVertex (n d : ℕ) : Type := {u : Fin d → Fin n // StrictMono u}

/-- The **canonical `d`-dimensional shift digraph** `S⃗(n, d)` (Adenwalla–Braunfeld–Hons–Sylvester–Zamaraev,
*Set-defined graph classes: χ-boundedness meets tropical algebra*, arXiv:2607.23754 (held version, sha256 642c0d70…),
§1.1 p.2): vertex set `{(u₁, …, u_d) ∈ [n]^d : u₁ < ⋯ < u_d}`, with an arc from `u` to `w` iff `u_k = w_{k−1}` for every
`k ∈ {2, …, d}`. The paper defines it for `d ≥ 2`; every statement using it with a general `d` assumes `2 ≤ d`. -/
def shiftDigraph (n d : ℕ) : Digraph (ShiftVertex n d) where
  Adj u w := ∀ i j : Fin d, j.val = i.val + 1 → u.1 j = w.1 i

/-- `G` is a **`d`-dimensional shift digraph** (`G ∈ S⃗_d`): it is isomorphic to an induced subdigraph of `S⃗(n, d)` for
some `n` (arXiv:2607.23754, p.2 and p.15). -/
def IsShiftDigraphDim (d : ℕ) {W : Type} (G : Digraph W) : Prop :=
  ∃ n : ℕ, ∃ S : Set (ShiftVertex n d), FASTournament.Isomorphic G (FASTournament.induce (shiftDigraph n d) S)

/-- A digraph is **shift-colorable** if there is a homomorphism from it to a shift digraph (arXiv:2607.23754, p.2),
where a shift digraph (dimension `2`) is an induced subdigraph of `S⃗(n, 2)` for some `n`.

**Formalization Note** A homomorphism into an induced subdigraph of `S⃗(n, 2)` is a homomorphism into `S⃗(n, 2)`, and
`S⃗(n, 2)` is itself a shift digraph, so the definition asks for a homomorphism into `S⃗(n, 2)` for some `n`. -/
def IsShiftColorable {W : Type} (G : Digraph W) : Prop :=
  ∃ n : ℕ, Homomorphic G (shiftDigraph n 2)

/-- `G` is the **union of at most `c` shift-colorable digraphs** (arXiv:2607.23754, §3.4 p.17, and Theorem 1.2): there
are `k ≤ c` shift-colorable digraphs `H₁, …, H_k` on the vertex set of `G` with `G(a, b) = H₁(a, b) ∨ ⋯ ∨ H_k(a, b)`
for all distinct vertices `a, b`. -/
def IsUnionOfShiftColorable (c : ℕ) {W : Type} (G : Digraph W) : Prop :=
  ∃ k : ℕ, k ≤ c ∧ ∃ H : Fin k → Digraph W, (∀ j, IsShiftColorable (H j)) ∧
    ∀ a b, a ≠ b → (G.Adj a b ↔ ∃ j, (H j).Adj a b)

end SetDefinedGraphs


