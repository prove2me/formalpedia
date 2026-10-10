-- Prove2me | Definitions.Def_HomogLCP_Embed_Setting
-- name    : HomogLCP_Embed_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:42:10.407052+00:00
-- url     : https://prove2.me/theorems/4361bde7-0f7d-4235-94f1-1d2807a88042
-- title:
--   (4.1) p. 7, (4.7) p. 9, §4.4 p. 10 — the embedding operators F, I and Q = F ∪ I of LCP(M, q, C)
-- statement:
--   Fix a matrix $M\in\mathbb R^{d\times d}$ and a vector $q\in\mathbb R^d$. Points of $\mathbb R^{d+1}=\mathbb R^d\times\mathbb R$ are written $(z,\tau)$.
--
--   1. **The feasibility embedding $\mathcal F$, (4.1).** The single-valued operator $\mathcal F:\mathbb R^d\times\mathbb R_{++}\to\mathbb R^{d+1}$ is
--   $$\mathcal F(z,\tau)=\begin{bmatrix} Mz+q\tau\\ -z^\top Mz/\tau-z^\top q\end{bmatrix},\qquad \operatorname{dom}\mathcal F=\{(z,\tau)\mid \tau>0\}.$$
--   2. **The infeasibility embedding $\mathcal I$, (4.7).** The set-valued operator
--   $$\mathcal I(z,\tau)=\left\{\begin{bmatrix} Mz\\ \kappa\end{bmatrix}\ \middle|\ \kappa\le -z^\top q\right\},\qquad \operatorname{dom}\mathcal I=\{(z,0)\mid z^\top Mz=0\}.$$
--   3. **The final embedding $\mathcal Q$ (§4.4).** $\mathcal Q=\mathcal F\cup\mathcal I$, with $\operatorname{dom}\mathcal Q=\operatorname{dom}\mathcal F\cup\operatorname{dom}\mathcal I$.
--
--   $\mathcal F$ encodes feasibility and $\mathcal I$ infeasibility of the linear complementarity problem $\mathrm{LCP}(M,q,\mathcal C)$; their union is the operator whose maximal monotonicity justifies applying Douglas–Rachford splitting to the homogeneous embedding.
--
--   **Formalization Note** All three operators are graphs (sets of (point, value) pairs) on `(Fin d → ℝ) × ℝ`. The domain condition $\tau>0$ is part of the graph of $\mathcal F$, so the Lean value of $z^\top Mz/0$ never enters. The graph of $\mathcal I$ contains exactly the pairs $((z,0),(Mz,\kappa))$ with $z^\top Mz=0$ and $\kappa\le -z^\top q$. No hypothesis on $M$ is part of the definitions; monotonicity of $M$ is a hypothesis of the theorems.
-- source:
--   O'Donoghue, Operator splitting for a homogeneous embedding of the linear complementarity problem, arXiv:2004.02177v4, p. 7, (4.1); p. 9, (4.7); p. 10, §4.4 (Q = F ∪ I)

import Mathlib
import Definitions.Def_HomogLCP_Embed_MonotoneOp

namespace HomogLCP.Embed

open Matrix

/-- The Andersen–Ye embedding operator `ℱ` of (4.1), p. 7, as a graph on `ℝ^d × ℝ`. Its domain
is `ℝ^d × ℝ₊₊` (`τ > 0`), and on it
`ℱ(z, τ) = (Mz + qτ, -zᵀMz/τ - zᵀq)`. -/
def embF {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ) : Op d :=
  {a | 0 < a.1.2 ∧
    a.2 = (M *ᵥ a.1.1 + a.1.2 • q, -(a.1.1 ⬝ᵥ (M *ᵥ a.1.1)) / a.1.2 - a.1.1 ⬝ᵥ q)}

/-- The infeasibility operator `ℐ` of (4.7), p. 9:
`ℐ(z, τ) = {(Mz, κ) | κ ≤ -zᵀq}` with `dom ℐ = {(z, 0) | zᵀMz = 0}`. -/
def embI {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ) : Op d :=
  {a | a.1.2 = 0 ∧ a.1.1 ⬝ᵥ (M *ᵥ a.1.1) = 0 ∧ a.2.1 = M *ᵥ a.1.1 ∧ a.2.2 ≤ -(a.1.1 ⬝ᵥ q)}

/-- The final embedding operator `𝒬 = ℱ ∪ ℐ` of §4.4, p. 10 (union of graphs). -/
def embQ {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ) : Op d :=
  embF M q ∪ embI M q

end HomogLCP.Embed


