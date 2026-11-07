-- Prove2me | Definitions.Def_CodeSW_evenCover
-- name    : CodeSW_evenCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:58.643192+00:00
-- url     : https://prove2.me/theorems/e7f9a824-6039-436c-8de7-41cd8c442087
-- title:
--   The even cover model $\xi(A)\propto r^{|A|}\mathbf 1(1_A\in L)$
-- statement:
--   The **even cover model** with cover space $L\subseteq\{0,1\}^c$ and weight ratio $r$ is the distribution on subsets of checks
--   $$\xi(A)=\frac{r^{|A|}\mathbf 1(1_A\in L)}{\sum_{B}r^{|B|}\mathbf 1(1_B\in L)}.$$
--   The paper's model $\xi_{h,q}(A)\propto(q/(1-q))^{|A|}\mathbf 1(1_A\in\ker(h^T))$ is the case $L=\ker(h^T)$, $r=q/(1-q)$. The model $\xi_{h^\perp,q}$ is the case $L=\mathrm{col}(h)$, because $\ker((h^\perp)^T)=\mathrm{col}(h)$ for any column generator $h^\perp$ of $\mathrm{col}(h)^\perp$.
--
--   This model generalizes the even subgraph model, and it is coupled to the random cluster model in Lemma 18.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), §3.3.2, p.20; p.22

import Definitions.Def_CodeSW_kerA
open Matrix
noncomputable section

namespace CodeSW

open Classical in
/-- The **even cover model** with weight ratio `r` and cover space `L ⊆ F₂^c`:
`ξ(A) ∝ r^{|A|} 1(1_A ∈ L)` on subsets `A ⊆ E = [c]`, normalized
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, §3.3.2, p.20: `ξ_{h,p}(A) ∝ (p/(1−p))^{|A|} 1(1_A ∈ ker(hᵀ))`; p.22: `Ω↑ = ker(hᵀ)`,
`Ω↓ = col(h)`).

**Formalization Note** The page's `ξ_{h,q}` is `evenCover (ker hᵀ) (q/(1−q))`; the dual model
`ξ_{h^⊥,q}` is `evenCover (col h) (q/(1−q))`, since `ker((h^⊥)ᵀ) = col(h)` for any column generator
`h^⊥` of `col(h)^⊥`. -/
def evenCover {c : ℕ} (L : Submodule (ZMod 2) (Fin c → ZMod 2)) (r : ℝ) (A : Finset (Fin c)) :
    ℝ :=
  (r ^ A.card * (if ind A ∈ L then 1 else 0)) /
    ∑ B : Finset (Fin c), r ^ B.card * (if ind B ∈ L then 1 else 0)

end CodeSW


