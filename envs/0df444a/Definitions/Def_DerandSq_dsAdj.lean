-- Prove2me | Definitions.Def_DerandSq_dsAdj
-- name    : DerandSq_dsAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:01.761619+00:00
-- url     : https://prove2.me/theorems/00b7315a-14fb-4a18-9d30-b1e9a509a9f7
-- title:
--   Adjacency matrix $A_S$ of the derandomized square $S = G \circledS H$
-- statement:
--   Let $\pi_1, \dots, \pi_d$ be permutations of $[N]$ and let $G$ be the $d$-regular graph on $[N]$ with adjacency matrix $\sum_j \lambda(\pi_j)$ and the canonical out-labelling $\mathrm{Out}_G(v, j) = \pi_j(v)$ of (4.1). Let $H$ be a graph on the label set $[d]$ with out-labelling $\mathrm{Out}_H(a, \cdot)$ enumerating the neighbours of $a$. The **derandomized square** $S = G \circledS H$ (Rozenman–Vadhan) is the graph on $[N]$ with out-labelling
--   $$
--   \mathrm{Out}_S(v, (a, b)) = \mathrm{Out}_G(\mathrm{Out}_G(v, a), \mathrm{Out}_H(a, b)),
--   $$
--   so from $v$ there is one edge to $\pi_b(\pi_a(v))$ for every label $a \in [d]$ and every $H$-neighbour $b$ of $a$. Its adjacency matrix counts these labels:
--   $$
--   (A_S)_{w,v} = \bigl|\{(a, b) \in [d]^2 : \{a, b\} \in E(H),\ \pi_b(\pi_a(v)) = w\}\bigr|.
--   $$
--   When $H$ is $k$-regular, $S$ is $dk$-regular.
--
--   **Formalization Note** Labels are `Fin d`. The $k$ labels $\mathrm{Out}_H(a, \cdot)$ are encoded by the neighbour set of $a$ itself; any bijection between the neighbours of $a$ and $[k]$ gives the same counts. Columns are tails ($A_S e_v = \sum_{\text{labels}} e_{\mathrm{Out}_S(v, \cdot)}$), matching the orientation of $\lambda(\pi)$.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §4, p.18 (Rozenman–Vadhan derandomized square)

import Mathlib

namespace DerandSq

/-- The adjacency matrix `A_S` of the derandomized square `S = G Ⓢ H` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §4, p.18), where
`G` is the `d`-regular graph on `[N]` with the canonical labelling `Out_G(v, j) = π_j(v)` of (4.1)
and `H` is a graph on the label set `[d]`. The out-labelling of `S` is
`Out_S(v, (a, b)) = Out_G(Out_G(v, a), Out_H(a, b))`, so from `v` there is one edge to
`π_b(π_a(v))` for every label `a` and every `H`-neighbour `b` of `a`. The entry in row `w`,
column `v` is the number of labels `(a, b)` with `H.Adj a b` and `π_b(π_a(v)) = w`.

**Formalization Note** Labels are `Fin d` (0-based). The `k` labels `Out_H(a, ·)` of the
neighbours of `a` are encoded by the neighbour set of `a` itself (any bijection `N_H(a) ≃ [k]`
gives the same counts). Columns are tails: `A_S e_v = ∑ e_{Out_S(v, ·)}`, the orientation of
`λ(π) δ_v = δ_{π v}`. -/
noncomputable def dsAdj {N d : ℕ} (π : Fin d → Equiv.Perm (Fin N)) (H : SimpleGraph (Fin d)) :
    Matrix (Fin N) (Fin N) ℝ := by
  classical exact Matrix.of fun w v =>
    ((Finset.univ.filter (fun ab : Fin d × Fin d => H.Adj ab.1 ab.2 ∧ π ab.2 (π ab.1 v) = w)).card : ℝ)

end DerandSq


