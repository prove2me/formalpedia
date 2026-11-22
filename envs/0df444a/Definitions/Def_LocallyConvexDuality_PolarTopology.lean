-- Prove2me | Definitions.Def_LocallyConvexDuality_PolarTopology
-- name    : LocallyConvexDuality_PolarTopology
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T09:20:25.845438+00:00
-- url     : https://prove2.me/theorems/647d15c4-ea5b-446e-8ee5-b7f7aee8055d
-- title:
--   Topologies of a dual pair: polar ($\mathfrak S$-)topologies, the Mackey topology $\tau(E,F)$, the strong topology $\beta(E,F)$, compatible topologies
-- statement:
--   **Polar topologies of a bilinear pairing, the Mackey topology, the strong topology, and compatible topologies.**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E$ and $F$ be $\mathbb K$-vector spaces and let $\langle\cdot,\cdot\rangle : E\times F\to\mathbb K$ be a bilinear pairing. Recall the weak topology $\sigma(E,F)$ on $E$ (the coarsest topology making every functional $\langle\cdot,y\rangle$, $y\in F$, continuous) and, symmetrically, $\sigma(F,E)$ on $F$. The following four notions are defined.
--
--   1. **Polar topology ($\mathfrak S$-topology).** For a family $\mathfrak S$ of subsets of $F$, the $\mathfrak S$-topology on $E$ is the topology of uniform convergence on the members of $\mathfrak S$, an element $x\in E$ being regarded as the function $y\mapsto\langle x,y\rangle$ on $F$. Thus a net $(x_\alpha)$ converges to $x$ if and only if
--   $$\sup_{y\in A}\,\bigl|\langle x_\alpha-x,\,y\rangle\bigr|\longrightarrow 0\qquad\text{for every }A\in\mathfrak S .$$
--   When every member of $\mathfrak S$ is $\sigma(F,E)$-bounded this is the locally convex topology defined by the seminorms
--   $$p_A(x)=\sup_{y\in A}|\langle x,y\rangle|,\qquad A\in\mathfrak S,$$
--   whose closed unit balls are the polars $A^\circ=\{x\in E:\ |\langle x,y\rangle|\le 1\ \text{for all }y\in A\}$.
--
--   2. **Mackey topology $\tau(E,F)$.** The $\mathfrak S$-topology on $E$ for $\mathfrak S$ the family of all subsets of $F$ that are convex, circled and $\sigma(F,E)$-compact.
--
--   3. **Strong topology $\beta(E,F)$.** The $\mathfrak S$-topology on $E$ for $\mathfrak S$ the family of all $\sigma(F,E)$-bounded subsets of $F$.
--
--   4. **Compatible (consistent) topology.** A topology $\mathfrak T$ on $E$ is *compatible* (the paper says *consistent*) with the pairing if the $\mathfrak T$-continuous linear functionals on $E$ are exactly the functionals $\langle\cdot,y\rangle$ with $y\in F$:
--   $$\ell : E\to\mathbb K\ \text{linear is }\mathfrak T\text{-continuous}\iff \exists\,y\in F,\ \ \ell=\langle\cdot,y\rangle .$$
--   In other words, the dual of $(E,\mathfrak T)$ is $F$.
--
--   These are the standard topologies of a dual system. The paper recalls them in §C.2.2.1–C.2.2.2 in order to describe, via the Mackey–Arens theorem, all locally convex topologies on $E$ having $F$ as dual, and to compare them with the strong topology; Mathlib has the weak topology and the absolute polar of a pairing, but neither the polar topologies of a general pairing, nor the Mackey topology, nor the notion of a compatible topology.
--
--   **Formalization Note.** The pairing is a bilinear map `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` with `[RCLike 𝕜]`; no separation hypothesis is built into the definitions. `polarTopology B 𝔖` is the topology induced on `E` by the map `x ↦ (y ↦ B x y)` into Mathlib's space `UniformOnFun F 𝕜 𝔖` of functions `F → 𝕜` with the topology of uniform convergence on the members of `𝔖`; the family `𝔖 : Set (Set F)` is arbitrary (it need not be directed or consist of bounded sets), which agrees with the classical definition for the saturated families considered in the literature. In `mackeyTopology B` and `strongTopology B`, compactness and von Neumann boundedness of subsets of `F` are taken in Mathlib's weak space `WeakBilin B.flip` (that is, for $\sigma(F,E)$), and "convex and circled" is `AbsConvex 𝕜` (balanced, and convex with respect to the `ComplexOrder` order on `𝕜`, i.e. for real convex combinations). `IsCompatibleTopology B t` says `∀ l : E →ₗ[𝕜] 𝕜, Continuous l ↔ l ∈ Set.range B.flip`, continuity being for the topology `t` on `E`. All three topologies are terms of type `TopologicalSpace E`; in Mathlib's order on topologies `t₁ ≤ t₂` means that `t₁` is finer than `t₂`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 673-674, §C.2.2.1-§C.2.2.2 (unnumbered definitions of polar topologies, consistent topologies, the Mackey topology and the strong topology); classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. IV, §1 and 3.2-3.3 (as cited by the paper at this place)

import Mathlib

/-!
# Topologies of a dual pair: polar topologies, the Mackey topology, the strong topology

Let `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` be a bilinear pairing of vector spaces over `𝕜 = ℝ` or `ℂ`
(written `⟨x, y⟩ = B x y`). Mathlib provides the weak topology `σ(E, F)` as the topology of the
type synonym `WeakBilin B` (and `σ(F, E)` as that of `WeakBilin B.flip`), and the absolute polar
`LinearMap.polar`. This file adds the other classical topologies of the pairing:

* `LocallyConvexDuality.polarTopology B 𝔖` : the `𝔖`-topology on `E`, i.e. the topology of uniform
  convergence on the members of a family `𝔖` of subsets of `F`;
* `LocallyConvexDuality.mackeyTopology B` : the Mackey topology `τ(E, F)`;
* `LocallyConvexDuality.strongTopology B` : the strong topology `β(E, F)`;
* `LocallyConvexDuality.IsCompatibleTopology B t` : the topology `t` on `E` is compatible
  (consistent) with the pairing, i.e. the dual of `(E, t)` is `F`.

Reference: H. H. Schaefer, M. P. Wolff, *Topological Vector Spaces*, 2nd ed., Chapter IV, §§1–3.
-/

open scoped ComplexOrder

namespace LocallyConvexDuality

variable {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- The **polar topology** (`𝔖`-topology) on `E` attached to a pairing `B : E × F → 𝕜` and a family
`𝔖` of subsets of `F`: the topology of uniform convergence on the members of `𝔖`, where `x : E` is
regarded as the function `y ↦ B x y` on `F`. A net `x_α` converges to `x` for this topology iff
`sup_{y ∈ A} ‖B (x_α - x) y‖ → 0` for every `A ∈ 𝔖`. When the members of `𝔖` are
`σ(F, E)`-bounded this is the locally convex topology defined by the seminorms
`p_A(x) = sup_{y ∈ A} ‖B x y‖`, `A ∈ 𝔖`, whose closed unit balls are the polars `A°`. -/
@[instance_reducible]
def polarTopology (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (𝔖 : Set (Set F)) : TopologicalSpace E :=
  TopologicalSpace.induced (fun x : E => UniformOnFun.ofFun 𝔖 (fun y : F => B x y))
    (UniformOnFun.topologicalSpace F 𝕜 𝔖)

/-- The **Mackey topology** `τ(E, F)` of a pairing `B : E × F → 𝕜`: the topology on `E` of uniform
convergence on all absolutely convex (convex and circled) subsets of `F` that are compact for the
weak topology `σ(F, E)`. -/
@[instance_reducible]
def mackeyTopology (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : TopologicalSpace E :=
  polarTopology B {A : Set F | AbsConvex 𝕜 A ∧ IsCompact (X := WeakBilin B.flip) A}

/-- The **strong topology** `β(E, F)` of a pairing `B : E × F → 𝕜`: the topology on `E` of uniform
convergence on all subsets of `F` that are (von Neumann) bounded for the weak topology
`σ(F, E)`. -/
@[instance_reducible]
def strongTopology (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : TopologicalSpace E :=
  polarTopology B {A : Set F | Bornology.IsVonNBounded (E := WeakBilin B.flip) 𝕜 A}

/-- A topology `t` on `E` is **compatible** (or **consistent**) with the pairing
`B : E × F → 𝕜` if the `t`-continuous linear functionals on `E` are exactly the functionals
`x ↦ B x y`, `y ∈ F`; in other words, the dual of `(E, t)` is `F`. -/
def IsCompatibleTopology (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (t : TopologicalSpace E) : Prop :=
  ∀ l : E →ₗ[𝕜] 𝕜, @Continuous E 𝕜 t inferInstance l ↔ l ∈ Set.range B.flip

end LocallyConvexDuality


