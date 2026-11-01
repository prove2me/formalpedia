-- Prove2me | Definitions.Def_MaxEntCont_IsLowerSemicontinuousFaceFunction
-- name    : MaxEntCont_IsLowerSemicontinuousFaceFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:40.294178+00:00
-- url     : https://prove2.me/theorems/55389b8e-e6e1-412e-9658-3af89e185b55
-- title:
--   Lower semicontinuity of the face function $x\mapsto F(x)$
-- statement:
--   Let $C$ be a convex subset of a real normed space, with the subspace topology, and let $F(x)$ be the face of $C$ containing $x$ in its relative interior. The **face function** of $C$ is the set-valued map
--   $$
--   C\to C,\qquad x\mapsto F(x).
--   $$
--   A set-valued map $\Gamma:\widetilde X\to\widetilde Y$ between topological spaces is lower semicontinuous at $x\in\widetilde X$ if for each open set $G$ meeting $\Gamma(x)$ there is a neighbourhood $N$ of $x$ such that $G\cap\Gamma(x')\neq\emptyset$ for all $x'\in N$; it is lower semicontinuous if it is so at every point.
--
--   The face function of $C$ is **lower semicontinuous** when, for every $x\in C$ and every open set $G$ meeting $F(x)$, there is a neighbourhood $N$ of $x$ in $C$ such that $G$ meets $F(x')$ for every $x'\in N$.
--
--   **Formalization Note** $F(x)$ is `OAI.CanonicalFace198.minFace C x` (see Fact 5.3). Open subsets of $C$ are traces $G\cap C$ of open subsets $G$ of the ambient space; since $F(x')\subseteq C$, $(G\cap C)\cap F(x')=G\cap F(x')$, so $G$ ranges over the open sets of the ambient space. Neighbourhoods of $x$ in $C$ are the sets of the filter `𝓝[C] x`.
-- source:
--   Rodman, Spitkovsky, Szkoła, Weis, Continuity of the maximum-entropy inference, arXiv:1502.02018v1, p. 13, definitions of the face function and of lower semi-continuity (in text)

import Mathlib
import Definitions.Def_TriangleFace

namespace MaxEntCont

open OAI.CanonicalFace198 Topology Filter

/-- **Lower semicontinuous face function** (Rodman, Spitkovsky, Szkoła, Weis, *Continuity of the maximum-entropy inference*, arXiv:1502.02018v1, p. 13). The face function of a convex set
`C` is the set-valued map `C → C, x ↦ F(x)`; a set-valued map `Γ` is lower semicontinuous at `x`
"if for each open set `G` meeting `Γ(x)` there exists a neighborhood `N` of `x` such that for
all `x′ ∈ N` we have `G ∩ Γ(x′) ≠ ∅`", and lower semicontinuous if it is so at every point.

`IsLowerSemicontinuousFaceFunction C` says: for every `x ∈ C` and every open `G` of the ambient
space meeting `F(x)`, for all `x′ ∈ C` near `x`, `G` meets `F(x′)`.

**Formalization Note** `F(x)` is `OAI.CanonicalFace198.minFace C x` (identified with the paper's
face function by `MaxEntCont.fact_5_3`). Open sets of `C` (subspace topology) are traces `G ∩ C`
of open sets `G` of the ambient space; since `F(x′) ⊆ C`, `(G ∩ C) ∩ F(x′) = G ∩ F(x′)`.
Neighbourhoods of `x` in `C` are the sets of the filter `𝓝[C] x`. -/
def IsLowerSemicontinuousFaceFunction {X : Type*} [AddCommGroup X] [Module ℝ X]
    [TopologicalSpace X] (C : Set X) : Prop :=
  ∀ x ∈ C, ∀ G : Set X, IsOpen G → (G ∩ minFace C x).Nonempty →
    ∀ᶠ x' in 𝓝[C] x, (G ∩ minFace C x').Nonempty

end MaxEntCont


