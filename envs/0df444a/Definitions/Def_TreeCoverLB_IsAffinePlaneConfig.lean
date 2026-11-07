-- Prove2me | Definitions.Def_TreeCoverLB_IsAffinePlaneConfig
-- name    : TreeCoverLB_IsAffinePlaneConfig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:02.943211+00:00
-- url     : https://prove2.me/theorems/1554038a-0a93-4e65-a284-010ccab5b875
-- title:
--   Affine-plane configuration in $\mathbb Z_p^k$
-- statement:
--   For $C\subseteq\mathbb Z_p^k$ and $i\in[k]$ let $A_i(C)=\{x_i:x\in C\}$. $C$ is an **affine-plane configuration** if
--   $$
--   |C|=(k-1)^2,\qquad |A_i(C)|=k-1\quad(i\in[k]),
--   $$
--   and every two distinct words $x,y\in C$ agree in exactly one coordinate: $|\{i\in[k]: x_i=y_i\}|=1$.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Definition 5.7, p.21 (PDF p.23)

import Mathlib

namespace TreeCoverLB

/-- **Affine-plane configuration** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Definition 5.7, p.21 (PDF p.23)): a set `C ⊆ ℤ_p^k` with
`|C| = (k − 1)²`, `|A_i(C)| = k − 1` for every `i ∈ [k]`, where `A_i(C) = {x_i : x ∈ C}`, and such
that every two distinct words `x, y ∈ C` agree in exactly one coordinate:
`|{i ∈ [k] : x_i = y_i}| = 1`. -/
def IsAffinePlaneConfig {p k : ℕ} (C : Finset (Fin k → ZMod p)) : Prop :=
  C.card = (k - 1) ^ 2 ∧ (∀ i : Fin k, (C.image fun x => x i).card = k - 1) ∧
    ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (Finset.univ.filter fun i : Fin k => x i = y i).card = 1

end TreeCoverLB


