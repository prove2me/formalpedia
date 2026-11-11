-- Prove2me | Definitions.Def_DetConnSketch_Main_TwoLift
-- name    : DetConnSketch_Main_TwoLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:41:25.211248+00:00
-- url     : https://prove2.me/theorems/1a9e7785-7508-42d8-ad2a-4dab8f075a69
-- title:
--   Two-lifts $L_x$ of $K_{k,k}$ on $4k$ vertices and the binary cut space $B$ (§8.2.1–8.2.2)
-- statement:
--   Let $H = K_{k,k}$ have left vertices $u_1,\dots,u_k$, right vertices $v_1,\dots,v_k$ and the $m = k^2$ edges $u_iv_j$. A vector $x \in \mathbb F_2^m$ has one bit $x_{ij}$ per edge.
--
--   The **two-lift** $L_x$ is the simple graph on the $4k$ vertices $(w, t)$, $w \in V(H)$, $t \in \mathbb F_2$, with the edges
--   $$\{(u_i, t),\ (v_j, t + x_{ij})\}, \qquad 1 \le i, j \le k,\ t \in \mathbb F_2 .$$
--   The **binary cut space** is
--   $$B = \{\, (a_{u_i} + a_{v_j})_{i,j} : a \in \mathbb F_2^{V(H)} \,\} \subseteq \mathbb F_2^m .$$
--
--   **Formalization Note.** `EdgeLabel k = Fin k → Fin k → ZMod 2` is $\mathbb F_2^m$; `LiftVertex k = (Fin k ⊕ Fin k) × ZMod 2`, with `Sum.inl i` for $u_i$ and `Sum.inr j` for $v_j$; `lift x` is $L_x$ and `cutSpace k` is $B$. Indices are $0$-based.
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), pp. 49–50 (PDF 53–54), §8.2.1–8.2.2

import Mathlib

namespace DetConnSketch.Main

/-!
# Two-lifts `L_x` of `K_{k,k}` and the binary cut space `B` (§8.2.1–8.2.2)

Khanna, Putterman, Sudan, *Deterministic Connectivity Sketches Under Edge Deletions*,
arXiv:2611.06626 (copy sha256 fff87f5b…), pp. 49–50.

* `H = K_{k,k}` has left vertices `u_i = Sum.inl i` and right vertices `v_j = Sum.inr j`
  (`i, j : Fin k`) and the `m = k²` edges `u_i v_j`.
* `EdgeLabel k = F_2^m`: one bit `x i j : ZMod 2` per edge `u_i v_j`.
* `LiftVertex k`: the `4k` lifted vertices `(w, t)`, `w ∈ V(H)`, `t ∈ F_2`.
* `lift x = L_x`: the simple graph on `LiftVertex k` with the edges
  `{(u_i, t), (v_j, t + x_ij)}` for all `i, j` and `t ∈ F_2`.
* `cutSpace k = B = {(a_{u_i} + a_{v_j})_{i,j} : a ∈ F_2^{V(H)}}`.
-/

/-- Edge labels of `K_{k,k}`: `F_2^m` with `m = k²`, coordinate `x i j` on the edge `u_i v_j`. -/
abbrev EdgeLabel (k : ℕ) := Fin k → Fin k → ZMod 2

/-- The `4k` vertices `(w, t)` of a two-lift of `K_{k,k}`: `w = Sum.inl i` is `u_i`,
`w = Sum.inr j` is `v_j`, and `t ∈ F_2`. -/
abbrev LiftVertex (k : ℕ) := (Fin k ⊕ Fin k) × ZMod 2

/-- The two-lift `L_x`: edges `{(u_i, t), (v_j, t + x_ij)}` for all `i, j : Fin k`, `t ∈ F_2`. -/
def lift {k : ℕ} (x : EdgeLabel k) : SimpleGraph (LiftVertex k) :=
  SimpleGraph.fromRel fun p q =>
    ∃ i j : Fin k, ∃ t : ZMod 2, p = (Sum.inl i, t) ∧ q = (Sum.inr j, t + x i j)

/-- The binary cut space `B ⊆ F_2^m` of `K_{k,k}`: all `(a_{u_i} + a_{v_j})_{i,j}` for vertex
bits `a ∈ F_2^{V(H)}`. -/
def cutSpace (k : ℕ) : Set (EdgeLabel k) :=
  {b | ∃ a : Fin k ⊕ Fin k → ZMod 2, ∀ i j, b i j = a (Sum.inl i) + a (Sum.inr j)}

end DetConnSketch.Main


