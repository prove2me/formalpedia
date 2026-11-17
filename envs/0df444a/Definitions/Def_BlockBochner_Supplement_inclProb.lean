-- Prove2me | Definitions.Def_BlockBochner_Supplement_inclProb
-- name    : BlockBochner_Supplement_inclProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:30:49.724257+00:00
-- url     : https://prove2.me/theorems/987c8762-8cae-4355-ba69-10ff29da379c
-- title:
--   Inclusion probabilities $p_i$, $p_{ij}$
-- statement:
--   For $X\sim\mu$ (the fugacity measure) and a finite set $A$ of ground elements, $\Pr_\mu[A\subseteq X]=\sum_{S\supseteq A}\mu(S)$. With $X_i=\mathbf 1\{i\in X\}$,
--   $$
--   p_i=\mathbb E_\mu X_i=\Pr_\mu[i\in X],\qquad p_{ij}=\mathbb E_\mu[X_iX_j]=\Pr_\mu[i,j\in X],
--   $$
--   and $p_{ii}=p_i$.
--
--   **Formalization Note** `inclProb I lam A` is $\Pr_\mu[A\subseteq X]$; $p_i$ is the case $A=\{i\}$ and $p_{ij}$ the case $A=\{i,j\}$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 5, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_BlockBochner_Supplement_fugacityProb

namespace BlockBochner.Supplement

open Classical in
/-- **Inclusion probabilities `p_i`, `p_ij`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 5, p.30: for
`X ∼ µ` and `X_i = 1{i∈X}`, `p_i = E_µ X_i` and `p_ij = E_µ[X_i X_j]`. `inclProb I lam A` is
`Pr_µ[A ⊆ X]`, so `p_i = inclProb I lam {i}` and `p_ij = inclProb I lam {i, j}` (`p_ii = p_i`).

**Formalization Note** The sum of `µ(S)` over all finite subsets `S ⊇ A` (sets outside `I` have
`µ(S) = 0`). -/
noncomputable def inclProb {α : Type*} [Fintype α] (I : Finset α → Prop) (lam : α → ℝ)
    (A : Finset α) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S => A ⊆ S), fugacityProb I lam S

end BlockBochner.Supplement


