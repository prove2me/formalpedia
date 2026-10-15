-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:07:46.979005+00:00
-- url     : https://prove2.me/theorems/15d30f45-aab5-4f5a-9322-ba514f9d7ad3
-- title:
--   Stage spaces $\ell^2(G;\mathbb{C}^{k_j})$, their Hilbert direct sum over $j\in\mathbb{N}$, and its double
-- statement:
--   Let $G$ be a set (a group in the application) and $k:\mathbb{N}\to\mathbb{N}$ a sequence of fibre dimensions. The file names three Hilbert spaces.
--
--   1. **Stage spaces.** For $j\in\mathbb{N}$,
--   $$\mathcal H_j=\ell^2\bigl(G;\mathbb{C}^{k_j}\bigr)=\Bigl\{\xi:G\to\mathbb{C}^{k_j}:\ \sum_{x\in G}\|\xi(x)\|^2<\infty\Bigr\},$$
--   with $\mathbb{C}^{k_j}$ Euclidean and $\|\xi\|^2=\sum_{x\in G}\|\xi(x)\|^2$.
--   2. **Total space.** $\mathcal H=\bigoplus_{j\in\mathbb{N}}\mathcal H_j$, the $\ell^2$ direct sum: sequences $(\xi_j)_{j\in\mathbb{N}}$ with $\xi_j\in\mathcal H_j$ and $\sum_j\|\xi_j\|^2<\infty$.
--   3. **Carrier.** $\mathcal H\oplus_2\mathcal H$, the pairs $(\xi,\eta)$ of elements of $\mathcal H$ with $\|(\xi,\eta)\|^2=\|\xi\|^2+\|\eta\|^2$.
--
--   These are the spaces of the direct-sum obstruction. Each stage carries the left translation representation $(\lambda(g)\xi)(x)=\xi(g^{-1}x)$, and the total space carries their direct sum. Suppose all $k_j>0$, and take stage operators $A_j$ commuting with all translations and $T_j$, with no uniform bound on their norms, such that the row of $T_j$ at $1$, the column of $A_j-T_j$ at $1$ and the coboundaries $T_j-\lambda(g)T_j\lambda(g^{-1})$ are all bounded in norm by some $\kappa\ge0$, while the kernel energies satisfy $\mathcal E(A_j)/k_j\to\infty$. Then, for every $t>0$, the development builds a representation $\pi$ of $G$ on the carrier with $\|\pi(g)\|\le1+t\kappa$ for all $g$ that is not similar to a unitary representation. The carrier is the Hilbert double on which triangular representations act.
--
--   **Formalization Note** These are abbreviations: `Stage G k j` is `KernelObstruction.Space G (Fin (k j))`, `Total G k` is `HilbertSum.Space (Stage G k)` (an `lp` space with exponent 2 over $\mathbb{N}$) and `Carrier G k` is `Triangular.Double (Total G k)`. All Hilbert-space structure is inherited from these constructions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SumObstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SumObstruction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete

namespace OAI

/-! The operator-theoretic direct-sum obstruction, constructed from stage operators
without any uniform bound on their norms. -/
noncomputable section
namespace Dixmier
namespace DirectSumObstruction
open Filter
open scoped Topology
variable {G : Type*} [Group G]

abbrev Stage (G : Type*) (k : ℕ → ℕ) (j : ℕ) : Type _ := KernelObstruction.Space G (Fin (k j))
abbrev Total (G : Type*) (k : ℕ → ℕ) : Type _ := HilbertSum.Space (Stage G k)
abbrev Carrier (G : Type*) (k : ℕ → ℕ) := Triangular.Double (Total G k)

end DirectSumObstruction
end Dixmier

end

end OAI


