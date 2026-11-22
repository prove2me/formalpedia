-- Prove2me | Definitions.Def_VectorValuedHolomorphy_CompactlySupportedInductiveLimit
-- name    : VectorValuedHolomorphy_CompactlySupportedInductiveLimit
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T15:22:13.896799+00:00
-- url     : https://prove2.me/theorems/0399f99e-a011-4c75-8f4d-aba34dd5694f
-- title:
--   The locally convex inductive limit topology on the space $C_c(X,E)$ of continuous compactly supported vector-valued functions
-- statement:
--   This file defines the **locally convex inductive limit topology on $C_c(X,E)$**, the space of continuous compactly supported functions with values in a topological vector space.
--
--   Let $\mathbb k$ be $\mathbb R$ or $\mathbb C$, let $X$ be a topological space (in the source: locally compact Hausdorff) and $E$ a topological vector space over $\mathbb k$ (in the source: a Hausdorff locally convex space). Let $C_c(X,E)$ be the vector space of continuous functions $f\colon X\to E$ with compact support $\operatorname{supp}(f)=\overline{\{x: f(x)\neq 0\}}$, and for a compact $K\subset X$ let $C(X,K;E)\subset C_c(X,E)$ be the subspace of the functions with support in $K$, with the *topology of uniform convergence* (defined by the seminorms $f\mapsto\sup_{x}\nu(f(x))$, $\nu$ a continuous seminorm on $E$, when $E$ is locally convex).
--
--   The *locally convex inductive limit topology* on $C_c(X,E)$ is the finest locally convex topology for which all the inclusions
--   $$C(X,K;E)\hookrightarrow C_c(X,E),\qquad K\subset X\ \text{compact},$$
--   are continuous. Equivalently, it is the topology defined by the family of **all** seminorms $p$ on $C_c(X,E)$ such that the restriction of $p$ to $C(X,K;E)$ is continuous for every compact $K$; this is the form taken as the definition:
--
--   1. `VectorValuedHolomorphy.ContinuousOnSupportedIn 𝕜 X E p`: the seminorm $p$ on $C_c(X,E)$ is continuous on every $C(X,K;E)$.
--   2. `VectorValuedHolomorphy.compactlySupportedSeminormFamily 𝕜 X E`: the family of all such seminorms.
--   3. `VectorValuedHolomorphy.compactlySupportedTopology 𝕜 X E`: the topology on $C_c(X,E)$ defined by this family.
--   4. `VectorValuedHolomorphy.compactlySupportedUniformSpace 𝕜 X E`: the uniform structure of the topological vector space so obtained (needed to speak of completeness and quasi-completeness).
--
--   This is the topology of Bourbaki's space $\mathscr K(X;E)$; for $E=\mathbb k$ its continuous linear forms are the Radon measures on $X$. It is in general strictly finer than the topology of uniform convergence on compact subsets induced from $C(X,E)$. The paper uses it throughout for spaces of vector-valued test functions (Definition C.5.1.1, Lemma C.5.1.3).
--
--   **Formalization Note.** $C_c(X,E)$ is Mathlib's `CompactlySupportedContinuousMap X E` (notation `C_c(X, E)`), which carries no topology in Mathlib at the pinned revision; the topology and the uniform structure are therefore plain definitions (`abbrev`s), not instances, and statements about them pass them explicitly. $C(X,K;E)$ is the subtype `{f : C_c(X, E) // tsupport f ⊆ K}`, and its topology of uniform convergence is the topology induced by the inclusion into `C(X, E)` with the compact-open topology (for functions supported in the compact set $K$, uniform convergence on compact sets is uniform convergence on $X$). The topology is `(compactlySupportedSeminormFamily 𝕜 X E).moduleFilterBasis.topology`, so that `WithSeminorms` holds by definition; a locally convex topology is defined by its continuous seminorms, and the continuous seminorms of the inductive limit topology are exactly the seminorms continuous on each step, which is why this agrees with the usual definition as a finest locally convex topology. The definitions are stated for `[NontriviallyNormedField 𝕜]` and a topological additive group `E` with `[ContinuousConstSMul 𝕜 E]`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 721, Definition C.5.1.1 and Remark C.5.1.2; classical reference: N. Bourbaki, Elements of Mathematics, Integration I, Springer, Ch. III, §1.1, Def. 1 (as cited by the paper)

import Mathlib

/-!
# The locally convex inductive limit topology on `C_c(X, E)`

Let `𝕜` be a nontrivially normed field (in the applications `ℝ` or `ℂ`), `X` a topological space
(in the applications locally compact Hausdorff) and `E` a topological vector space over `𝕜` (in
the applications a Hausdorff locally convex space). Mathlib's `C_c(X, E)`
(`CompactlySupportedContinuousMap`) is the vector space of continuous compactly supported functions
`X → E`. For a compact `K ⊆ X`, the subspace `C(X, K; E)` of the functions with support in `K` is
the subtype `{f : C_c(X, E) // tsupport f ⊆ K}`; its *topology of uniform convergence* is the
topology induced by the inclusion into `C(X, E)` with the compact-open topology (for functions
supported in the compact set `K`, uniform convergence on compact sets is uniform convergence on
`X`).

The *locally convex inductive limit topology* on `C_c(X, E)` is the finest locally convex topology
for which all the inclusions `C(X, K; E) → C_c(X, E)` are continuous. It is the topology defined
by the family of all seminorms on `C_c(X, E)` whose restriction to every `C(X, K; E)` is
continuous, and this is how it is defined here.

Source: A. M. Masullo, *The Music of the Primes*, draft of 20 November 2026, Definition C.5.1.1
(p. 721); N. Bourbaki, *Integration I*, Ch. III, §1, no. 1.
-/

open scoped CompactlySupported

namespace VectorValuedHolomorphy

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] (X : Type*) [TopologicalSpace X] (E : Type*)
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousConstSMul 𝕜 E]

/-- A seminorm `p` on `C_c(X, E)` is *continuous on every* `C(X, K; E)`: for every compact
`K ⊆ X`, the restriction of `p` to the functions with support in `K` is continuous for the
topology of uniform convergence (the topology induced from `C(X, E)` with the compact-open
topology). -/
def ContinuousOnSupportedIn (p : Seminorm 𝕜 C_c(X, E)) : Prop :=
  ∀ K : Set X, IsCompact K →
    @Continuous {f : C_c(X, E) // tsupport f ⊆ K} ℝ
      (TopologicalSpace.induced (fun f => (f.1 : C(X, E))) ContinuousMap.compactOpen) _
      (fun f => p f.1)

/-- The family of all seminorms on `C_c(X, E)` that are continuous on every `C(X, K; E)`, `K`
compact. -/
def compactlySupportedSeminormFamily :
    SeminormFamily 𝕜 C_c(X, E)
      {p : Seminorm 𝕜 C_c(X, E) // ContinuousOnSupportedIn 𝕜 X E p} :=
  fun p => p.1

/-- The *locally convex inductive limit topology* on `C_c(X, E)`: the topology defined by the
family of all seminorms whose restriction to every `C(X, K; E)`, `K` compact, is continuous for
the topology of uniform convergence. -/
abbrev compactlySupportedTopology : TopologicalSpace C_c(X, E) :=
  (compactlySupportedSeminormFamily 𝕜 X E).moduleFilterBasis.topology

/-- The uniform structure of the topological additive group `C_c(X, E)` with the locally convex
inductive limit topology (its topology is `compactlySupportedTopology 𝕜 X E`). -/
abbrev compactlySupportedUniformSpace : UniformSpace C_c(X, E) :=
  (compactlySupportedSeminormFamily 𝕜 X E).moduleFilterBasis.toAddGroupFilterBasis.uniformSpace

theorem compactlySupportedUniformSpace_toTopologicalSpace :
    (compactlySupportedUniformSpace 𝕜 X E).toTopologicalSpace =
      compactlySupportedTopology 𝕜 X E := rfl

end VectorValuedHolomorphy


