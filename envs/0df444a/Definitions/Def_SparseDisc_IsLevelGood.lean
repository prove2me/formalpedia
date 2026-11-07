-- Prove2me | Definitions.Def_SparseDisc_IsLevelGood
-- name    : SparseDisc_IsLevelGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:54:46.200198+00:00
-- url     : https://prove2.me/theorems/5f04fb28-de9c-4ec9-be65-bad74af56c30
-- title:
--   Good leveled graph $(G, \ell)$
-- statement:
--   A **leveled graph** $(G, \ell)$ is a simple graph $G$ on $V$ with levels $\ell : V \to \{1, 2, \dots\}$. A leveled constraint system on it is a 2-sparse constraint system with graph $H \subseteq G$ in which $Z_v$ is $\ell_v$-coarse, and $(G, \ell)$ is **good** if every such system has a solution. Thus $G$ is $c$-good iff $(G, c)$ is good.
--
--   **Formalization Note** Levels are natural numbers; the requirement $\ell_v \ge 1$ is stated as a hypothesis in every result that uses leveled graphs. Constraint systems are as in `SparseDisc.IsCGood`.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Section 8.6, p.37

import Mathlib
import Definitions.Def_SparseDisc_IsCoarse
import Definitions.Def_SparseDisc_IsTwoSparseSupp
import Definitions.Def_SparseDisc_instGraph
import Definitions.Def_SparseDisc_restrictTo

namespace SparseDisc

/-- `IsLevelGood G ℓ`: the leveled graph `(G, ℓ)` is **good** — every leveled constraint system on
it (a 2-sparse constraint system with graph `H ⊆ G` in which `Z_v` is `ℓ_v`-coarse) has a solution
(Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027 submission
manuscript (sha256 0f09ec60…25b81), Section 8.6, p.37).

**Formalization Note** Levels are natural numbers; the paper's `ℓ : V → {1, 2, …}` is the
hypothesis `∀ v, 1 ≤ ℓ v`, stated in every result that uses leveled graphs. Constraint systems are
as in `IsCGood`. -/
def IsLevelGood {V : Type} [Fintype V] (G : SimpleGraph V) (ℓ : V → ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : V → Finset ι) (Z : (v : V) → Set (Cube (U v))),
    IsTwoSparseSupp U → instGraph U ≤ G → (∀ v, IsCoarse (ℓ v : ℝ) (Z v)) →
      ∃ x : Cube ι, ∀ v, restrictTo (U v) x ∈ Z v

end SparseDisc


