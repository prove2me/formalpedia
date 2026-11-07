-- Prove2me | Definitions.Def_TreeCoverLB_agreementComplex
-- name    : TreeCoverLB_agreementComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:00.159007+00:00
-- url     : https://prove2.me/theorems/74562a7c-27d8-4070-afe2-c6651c2133a5
-- title:
--   Agreement complex $I_{p,k}$ and the diagonal $\mathbb Z_p$-action
-- statement:
--   Two words $x,y\in\mathbb Z_p^k$ **agree** if $x_i=y_i$ for some $i\in[k]$. The **agreement complex** $I_{p,k}$ is the simplicial complex on $\mathbb Z_p^k$ whose faces are the pairwise agreeing families of words:
--   $$
--   I_{p,k}=\{\sigma\subseteq\mathbb Z_p^k:\ \forall x,y\in\sigma\ \exists i\in[k],\ x_i=y_i\}.
--   $$
--   $\mathbb Z_p$ acts diagonally on words, $g(x_1,\dots,x_k)=(x_1+g,\dots,x_k+g)$, and hence on $|I_{p,k}|$ by $(g\cdot\mu)(x)=\mu(x-g)$.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Definition 4.1 and the diagonal action, p.11 (PDF p.13)

import Mathlib

namespace TreeCoverLB

/-- The **agreement complex** `I_{p,k}` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Definition 4.1, p.11 (PDF p.13)): the faces are the
families `σ` of words `x ∈ ℤ_p^k` that pairwise agree, i.e. any two words `x, y ∈ σ` satisfy
`x_i = y_i` for some coordinate `i`.

**Formalization Note** Words are `Fin k → ZMod p`; only the alphabet `ℤ_p` (`I_{p,k} = I_{ℤ_p,k}`)
is used in the paper's arguments. -/
def agreementComplex (p k : ℕ) : Set (Finset (Fin k → ZMod p)) :=
  {σ | ∀ x ∈ σ, ∀ y ∈ σ, ∃ i, x i = y i}

/-- The diagonal action of `ℤ_p` on `|I_{p,k}|` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4, p.11 (PDF p.13)): on words
`g(x_1, …, x_k) = (x_1 + g, …, x_k + g)`, extended to points by `(g · µ)(x) = µ(x − g)` (the
linear extension `Σ µ_x e_{x + g}`). -/
def wordAct {p k : ℕ} (g : ZMod p) (μ : (Fin k → ZMod p) → ℝ) : (Fin k → ZMod p) → ℝ :=
  fun x => μ (fun i => x i - g)

end TreeCoverLB


