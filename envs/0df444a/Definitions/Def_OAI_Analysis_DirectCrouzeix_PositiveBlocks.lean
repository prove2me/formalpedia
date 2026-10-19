-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
-- name    : OAI_Analysis_DirectCrouzeix_PositiveBlocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:23:01.765449+00:00
-- url     : https://prove2.me/theorems/52ec3c5c-bd34-4c3d-ae04-b48ae1cad236
-- title:
--   Squared Hilbert–Schmidt (Frobenius) norm of a complex matrix
-- statement:
--   Let $I$ and $J$ be finite index sets and let $M=(M_{ij})_{i\in I,\,j\in J}$ be a complex matrix whose rows are indexed by $I$ and whose columns are indexed by $J$. Write $M^{*}$ for the conjugate transpose of $M$ (a $J\times I$ matrix), so that $M^{*}M$ is a square matrix indexed by $J$. The module defines the squared Hilbert–Schmidt norm
--
--   $$
--   \|M\|_{\mathrm{HS}}^{2}=\operatorname{Re}\,\operatorname{tr}\big(M^{*}M\big)\in\mathbb{R}.
--   $$
--
--   Since $\operatorname{tr}(M^{*}M)=\sum_{i\in I}\sum_{j\in J}|M_{ij}|^{2}$ is already a nonnegative real number, taking the real part only records this value as a real number. Thus $\|M\|_{\mathrm{HS}}^{2}$ is the squared Frobenius norm of $M$, the squared Euclidean length of the array of its entries; the matrix need not be square.
--
--   This is the basic quadratic energy of the development. It is used, for instance, in the estimate $2\|Z\|_{\mathrm{HS}}^{2}\le\|U\|_{\mathrm{HS}}^{2}+\|V\|_{\mathrm{HS}}^{2}$ for square matrices $U,V,Z$ such that the block matrix $\begin{pmatrix}U&Z^{*}\\ Z&V\end{pmatrix}$ is positive semidefinite, and in Parseval-type identities for matrix-valued functions on the circle (both proved separately).
--
--   **Formalization Note** The definition is `hsSq M := (Matrix.trace (Mᴴ * M)).re` for `M : Matrix ι κ ℂ` with `[Fintype ι] [Fintype κ]`; the index types are arbitrary finite types, not necessarily of the form `Fin n`. The identity with the sum of squared moduli of the entries is proved in a later module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/PositiveBlocks.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PositiveBlocks.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def hsSq {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) : ℝ :=
  (Matrix.trace (Mᴴ * M)).re

end DirectCrouzeix

end

end OAI


