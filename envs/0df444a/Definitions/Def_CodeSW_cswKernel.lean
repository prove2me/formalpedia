-- Prove2me | Definitions.Def_CodeSW_cswKernel
-- name    : CodeSW_cswKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:32.442193+00:00
-- url     : https://prove2.me/theorems/b10a6a9d-76de-4c67-a668-c50798ccd1a8
-- title:
--   The Code Swendsen-Wang chain (Algorithm 2) as a transition matrix on $\{0,1\}^n$
-- statement:
--   One step of the **Code Swendsen-Wang chain** from $x\in\{0,1\}^n$ has two stages. In the cluster formation stage, each satisfied check $e\in E(x)$ is kept independently with probability $p$, giving a set $A\subseteq E(x)$. In the cluster update stage, the new configuration $y$ is drawn uniformly from $\ker(h_A)$. The transition matrix is therefore
--   $$P(x,y)=\sum_{A\subseteq E(x)}p^{|A|}(1-p)^{|E(x)|-|A|}\,\frac{\mathbf 1(y\in\ker h_A)}{2^{k(A)}}.$$
--   The chain at inverse temperature $\beta$ is this matrix at $p=1-e^{-2\beta}$.
--
--   This is the chain whose mixing time the mission's goal theorem bounds. It generalizes the Swendsen-Wang dynamics of the Ising model, which is the case where $h$ is the edge-vertex incidence matrix of the interaction graph.
--
--   **Formalization Note** The bond probability is a parameter of the auxiliary matrix `cswKernelP`, so that the zero-temperature chain ($p=1$, every satisfied check is kept) treated in the proof of Lemma 7 is the same object. `cswKernel h β` is `cswKernelP h (bondProb β)`.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Algorithm 2, p.16

import Definitions.Def_CodeSW_gibbs
open Matrix
noncomputable section

namespace CodeSW

open Classical in
/-- One step of the **Code Swendsen-Wang chain** with bond probability `p`, as a transition
matrix on `X = {0,1}^n` (Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*,
arXiv:2510.08446, manuscript sha256 4e4abb5e…, Algorithm 2, p.16). From `x`: (i) cluster
formation keeps each satisfied check `e ∈ E(x)` independently with probability `p`, giving `A`;
(ii) cluster update draws `y` uniformly from `ker(h_A)`. Hence
`P(x,y) = ∑_{A ⊆ E(x)} p^{|A|} (1−p)^{|E(x)|−|A|} · 1(y ∈ ker h_A) / 2^{k(A)}`.

**Formalization Note** `|ker h_A| = 2^{k(A)}`. The bond probability is a parameter so that the
zero-temperature chain (`p = 1`, keep every satisfied check, Lemma 7's proof, p.17) is the same
object; `cswKernel h β` is the chain at `p = 1 − e^{−2β}`. The exponent `|E(x)| − |A|` is natural
subtraction with `A ⊆ E(x)`, so it is exact. -/
def cswKernelP {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ :=
  fun x y => ∑ A ∈ (satChecks h x).powerset,
    p ^ A.card * (1 - p) ^ ((satChecks h x).card - A.card) *
      (if y ∈ kerA h A then ((2 : ℝ) ^ kDim h A)⁻¹ else 0)

/-- The **Code SW chain** of Algorithm 2 at inverse temperature `β`: `cswKernelP h p` with
`p = 1 − e^{−2β}` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, Algorithm 2, p.16). -/
def cswKernel {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (β : ℝ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℝ :=
  cswKernelP h (bondProb β)

end CodeSW


