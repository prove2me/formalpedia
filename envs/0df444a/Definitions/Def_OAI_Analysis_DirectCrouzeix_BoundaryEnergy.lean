-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
-- name    : OAI_Analysis_DirectCrouzeix_BoundaryEnergy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:31:56.980829+00:00
-- url     : https://prove2.me/theorems/0f15dfa2-18ff-4be5-baf8-786fbd0d287d
-- title:
--   Coefficient weights $w_0=1$ and $w_k=2$ for $k\ge1$ in Faber energy bounds
-- statement:
--   The module introduces the weight sequence
--
--   $$
--   w_k=\begin{cases}1,&k=0,\\ 2,&k\ge1,\end{cases}\qquad k\in\mathbb{N},
--   $$
--
--   as real numbers, and records the simplification rule $\|0\|_{\mathrm{HS}}^{2}=0$ for the zero matrix of any shape, where $\|M\|_{\mathrm{HS}}^{2}=\operatorname{Re}\operatorname{tr}(M^{*}M)=\sum_{i,j}|M_{ij}|^{2}$ is the squared Hilbert–Schmidt norm and $M^{*}$ the conjugate transpose.
--
--   The weights describe how the boundary energy of a Faber expansion is controlled by its coefficients. For coefficients $C_0,\dots,C_{N-1}$ in a Hilbert space and the Faber polynomials $F_k$ of a suitable convex boundary curve $t\mapsto\Gamma(t)$, $t\in\mathbb{R}/\mathbb{Z}$, the development proves (under its analyticity and kernel-positivity hypotheses) the two-sided estimate $\sum_k\|C_k\|^{2}\le\int_0^1\big\|\sum_kF_k(\Gamma(t))C_k\big\|^{2}dt\le\sum_k w_k\|C_k\|^{2}$. Dually, if matrices $P_0,P_1,\dots$ and a real $b\ge0$ satisfy $\big|\sum_{k<N}[P_k,C_k]\big|^{2}\le b\sum_{k<N}w_k\|C_k\|_{\mathrm{HS}}^{2}$ for every $N$ and all matrices $C_0,\dots,C_{N-1}$ of the same shape, where $[M,C]=\sum_{i,j}M_{ij}C_{ij}$ is the bilinear entrywise pairing, then $\|P_0\|_{\mathrm{HS}}^{2}+\tfrac12\sum_{k\ge1}\|P_k\|_{\mathrm{HS}}^{2}\le b$. Both facts are proved separately.
--
--   **Formalization Note** `faberWeight k` is `if k = 0 then 1 else 2` as a real number, and `hsSq_zero` is the simplification lemma `hsSq 0 = 0` for matrices indexed by arbitrary finite types.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/BoundaryEnergy.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/BoundaryEnergy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier

namespace OAI

universe u_73 u_74 u_75 u_76 u_77 u_78 u_79 u_80 u_81 u_82 u_83 u_84 u_85 u_86

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

open MeasureTheory

@[simp] theorem hsSq_zero {ι : Type u_75} {κ : Type u_76} [Fintype ι] [Fintype κ] :
    hsSq (0 : Matrix ι κ ℂ) = 0 := by simp [hsSq_eq_sum_norm_sq]

def faberWeight (k : ℕ) : ℝ := if k = 0 then 1 else 2

end DirectCrouzeix

end

end OAI


