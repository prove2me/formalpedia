-- Prove2me | Definitions.Def_PolyContract_IsRankFunction
-- name    : PolyContract_IsRankFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:40:40.190205+00:00
-- url     : https://prove2.me/theorems/7a5f866b-c456-4d69-9f52-f36c14a68cea
-- title:
--   Polymatroid rank function $f$ and independence polyhedron $P^{(+)}(f)$
-- statement:
--   Let $E$ be a finite ground set. For $x\in\mathbb R^E$ and $S\subseteq E$ write $x(S):=\sum_{e\in S}x_e$. A set function $f:2^E\to\mathbb R$ is a **rank function** if it is
--
--   1. submodular: $f(X)+f(Y)\ge f(X\cup Y)+f(X\cap Y)$ for all $X,Y\subseteq E$;
--   2. normalized: $f(\emptyset)=0$;
--   3. monotone: $f(X)\le f(Y)$ whenever $X\subseteq Y$.
--
--   Then $(E,f)$ is a polymatroid, with **independence polyhedron**
--   $$P^{(+)}(f):=\{x\in\mathbb R^E_{\ge 0}: x(S)\le f(S)\text{ for all }S\subseteq E\}.$$
--
--   These are the feasible effort allocations of the agent in every contract instance of the mission.
--
--   **Formalization Note** The ground set is a finite type and subsets are finite sets of it. Submodularity is the published predicate `NonmonotoneSubmod.Shared.Submodular`, which is exactly inequality 1.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), §2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

set_option autoImplicit false

namespace PolyContract

/-- `x(S) := Σ_{e ∈ S} x_e` for a vector `x ∈ ℝ^E` and a set `S ⊆ E` (Klimm, Lippke, Warode,
*The Complexity of Continuous Contract Design over Polymatroids*, arXiv:2611.04934, version of
November 3, 2026, sha256 18cfc0a5…, §2, p.5). -/
def setSum {ι : Type} (x : ι → ℝ) (S : Finset ι) : ℝ := ∑ e ∈ S, x e

/-- A **rank function** (arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…, §2,
p.5): a set function `f : 2^E → ℝ` that is submodular, `f(X) + f(Y) ≥ f(X ∪ Y) + f(X ∩ Y)`,
normalized, `f(∅) = 0`, and monotone, `f(X) ≤ f(Y)` for `X ⊆ Y`. Then `(E, f)` is a polymatroid.

**Formalization Note** The ground set `E` is the finite type `ι`, and subsets are `Finset ι`.
Submodularity is the published `NonmonotoneSubmod.Shared.Submodular`, which is exactly the
inequality above and bundles nothing else. -/
def IsRankFunction {ι : Type} [Fintype ι] [DecidableEq ι] (f : Finset ι → ℝ) : Prop :=
  NonmonotoneSubmod.Shared.Submodular f ∧ f ∅ = 0 ∧ ∀ X Y : Finset ι, X ⊆ Y → f X ≤ f Y

/-- The **independence polyhedron** `P(+)(f) := {x ∈ ℝ^E_{≥0} : x(S) ≤ f(S) for all S ⊆ E}`
(arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…, §2, p.5). -/
def indepPoly {ι : Type} (f : Finset ι → ℝ) : Set (ι → ℝ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ S : Finset ι, setSum x S ≤ f S}

end PolyContract


