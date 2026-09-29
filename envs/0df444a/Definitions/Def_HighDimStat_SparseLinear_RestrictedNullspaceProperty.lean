-- Prove2me | Definitions.Def_HighDimStat_SparseLinear_RestrictedNullspaceProperty
-- name    : HighDimStat_SparseLinear_RestrictedNullspaceProperty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:06:34.289972+00:00
-- url     : https://prove2.me/theorems/d5a03685-87df-4d1f-ba74-f2af747b19b7
-- title:
--   The restricted nullspace property (Definition 7.7)
-- statement:
--   **Definition 7.7.** The matrix $X$ satisfies the **restricted nullspace property** with
--   respect to $S$ if the cone $C(S) = C_1(S)$ meets the nullspace of $X$ only at the origin.
--
--   For $X \in \mathbb R^{n\times d}$ and $S \subseteq \{1,\dots,d\}$,
--
--   $$
--   \mathrm{RNP}(X, S) \;:\Longleftrightarrow\; C(S) \cap \mathrm{null}(X) \;=\; \{0\},
--   $$
--
--   where $C(S) = \{\Delta \mid \|\Delta_{S^c}\|_1 \le \|\Delta_S\|_1\}$ and $\mathrm{null}(X)
--   = \{\Delta \mid X\Delta = 0\}$. This is the condition Theorem 7.8 shows is equivalent to
--   the basis pursuit linear program exactly recovering every $S$-sparse vector.
--
--   **Formalization Note** Written pointwise, as "every $\Delta$ in the cone $C_1(S)$ with
--   $X\Delta = 0$ is the zero vector," rather than as a set-equality `C(S) ∩ null(X) = {0}`,
--   the two are equivalent since $0$ always lies in both sets.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 202 (PDF p. 222), Definition 7.7

import Mathlib
import Definitions.Def_HighDimStat_SparseLinear_ConeSet

namespace HighDimStat.SparseLinear

/-- **Definition 7.7.** The matrix `X` satisfies the restricted nullspace property with respect
to `S` if `C(S) ∩ null(X) = {0}`, Wainwright, *High-Dimensional Statistics* (2019), p. 202.
Here `C(S) = ConeSet S 1` and `null(X) = {Δ | X.mulVec Δ = 0}`. -/
def RestrictedNullspaceProperty {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Prop :=
  ∀ Δ : Fin d → ℝ, ConeSet S 1 Δ → X.mulVec Δ = 0 → Δ = 0

end HighDimStat.SparseLinear


