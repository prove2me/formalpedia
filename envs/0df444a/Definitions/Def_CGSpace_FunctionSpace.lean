-- Prove2me | Definitions.Def_CGSpace_FunctionSpace
-- name    : CGSpace_FunctionSpace
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T09:20:25.401906+00:00
-- url     : https://prove2.me/theorems/0874f44e-04f9-4570-aea9-bba20986d8f1
-- title:
--   $k$-ification $k(X)$, compact-open topology by test maps, and the compactly generated function space $\mathscr{C}ont_k(X,Y)=k(\mathrm{C}(X,Y))$
-- statement:
--   Definitions of the $k$-ification of a topological space, of the compact-open topology defined by test maps from compact Hausdorff spaces, and of the compactly generated function space $\mathscr{C}ont_k(X,Y)$.
--
--   Throughout, a *test map* into a topological space $X$ is a continuous map $g:S\to X$ whose source $S$ is a compact Hausdorff space. No separation axiom is imposed on the spaces $X$, $Y$ themselves.
--
--   1. **$k$-ification** (`CGSpace.KSpace X`, with the identity bijection `CGSpace.KSpace.mk : X ≃ CGSpace.KSpace X`). For a topological space $X$, the space $k(X)$ has the same underlying set as $X$, and a subset $Z\subseteq X$ is closed in $k(X)$ if and only if it is *$k$-closed*, i.e. $g^{-1}(Z)$ is closed in $S$ for every test map $g:S\to X$. Equivalently, the topology of $k(X)$ is the finest topology on the set $X$ for which all test maps into $X$ remain continuous. It is finer than the topology of $X$, and $X$ is *compactly generated* exactly when $k(X)=X$. For compactly generated spaces $X,Y$ the product in the category $\mathbf{CG}$ of compactly generated spaces is
--   $$X\times Y:=k(X\times_0 Y),$$
--   where $X\times_0 Y$ denotes the cartesian product with the product topology; in Lean it is `CGSpace.KSpace (X × Y)`.
--
--   2. **Compact-open topology defined by test maps** (`CGSpace.probeCompactOpen X Y`). For topological spaces $X,Y$, a test map $g:S\to X$ and an open subset $U\subseteq Y$ put
--   $$N(g,S,U)=\{\,f\in \mathrm{C}(X,Y)\;:\;(f\circ g)(S)\subseteq U\,\}.$$
--   The topology on the set $\mathrm{C}(X,Y)$ of continuous maps $X\to Y$ is the one admitting the family of all the sets $N(g,S,U)$ as a sub-base.
--
--   3. **Compactly generated function space** (`CGSpace.ContK X Y`, with the identity bijection `CGSpace.ContK.toContinuousMap : CGSpace.ContK X Y ≃ C(X, Y)`):
--   $$\mathscr{C}ont_k(X,Y):=k\big(\mathrm{C}(X,Y)\big),$$
--   the $k$-ification of $\mathrm{C}(X,Y)$ endowed with the topology of item 2.
--
--   These are the objects in terms of which the category of compactly generated spaces is cartesian closed (exponential law $\mathscr{C}ont_k(X\times Y,Z)\cong\mathscr{C}ont_k(X,\mathscr{C}ont_k(Y,Z))$, with $\mathscr{C}ont_k$ as internal hom). The paper recalls them in Appendix E.1 as the foundation of the convenient categories of spaces underlying its topological stacks.
--
--   **Formalization Note.** The definitions are made for arbitrary topological spaces `X Y : Type u` (the source states Definition E.1.2.6 and Construction E.1.2.9 for compactly generated $X$, $Y$). Test spaces range over `CompHaus.{u}`, the compact Hausdorff spaces in the universe of the spaces, exactly as in Mathlib's `TopologicalSpace.compactlyGenerated` and `CompactlyGeneratedSpace`. `KSpace X` is a type synonym of `X` carrying `TopologicalSpace.compactlyGenerated X`, and `ContK X Y` is a type synonym of `C(X, Y)`, so that it does not inherit Mathlib's instance `ContinuousMap.compactOpen`. Since the condition $(f\circ g)(S)\subseteq U$ only depends on the compact set $g(S)\subseteq X$, the sub-base of item 2 is a subfamily of the usual sub-base $\{f:f(C)\subseteq U\}$ ($C\subseteq X$ compact, $U\subseteq Y$ open); hence `probeCompactOpen X Y` is coarser than or equal to Mathlib's compact-open topology, with equality when $X$ is Hausdorff. (Remark E.1.2.7 of the source describes the comparison of the two topologies the other way round.) `CGSpace.KSpace X` coincides with the type synonym `QAlgorithms.Papers.Independent.Intakethird100.P07.KSpace` of the existing platform definition file `QAlgorithms_Papers_Independent_Intakethird100_P07` (same carrier, same topology), and it is the special case, for the family of all compact Hausdorff spaces of `Type u`, of Mathlib's `Topology.WithGeneratedByTopology` (`Mathlib.Topology.Convenient.GeneratedBy`): `TopologicalSpace.compactlyGenerated.{u} X = TopologicalSpace.generatedBy (fun S : CompHaus.{u} => S)`. Likewise `probeCompactOpen X Y` is the topology induced on `C(X, Y)` by the topology that `Mathlib.Topology.Convenient.HomSpace` puts on `Topology.ContinuousMapGeneratedBy` for that family (the two topologies have the same sub-basic sets, and for compactly generated $X$ every element of `Topology.ContinuousMapGeneratedBy` is a continuous map, so the two function spaces coincide). The definitions are restated here on the type `C(X, Y)` and with Mathlib's `CompactlyGeneratedSpace` because Mathlib has not yet connected `CompactlyGeneratedSpace` to that framework.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 828 and 834-836, Definition E.1.1.1, Remark E.1.2.5(2), Definition E.1.2.6 and Construction E.1.2.9; classical reference (as cited by the paper in Remark E.1.2.11): L. G. Lewis, Jr., The stable category and generalized Thom spectra, Ph.D. thesis, University of Chicago, 1978, §5, p. 160; N. Strickland, The category of CGWH spaces (available online), Def. 2.8

import Mathlib

/-!
# Compactly generated function spaces

Definitions for the cartesian closed structure on compactly generated spaces
(`CompactlyGeneratedSpace` of Mathlib: the topology is coinduced by all continuous maps from
compact Hausdorff spaces of the same universe; no separation axiom).

* `CGSpace.KSpace X` : the `k`-ification `k(X)` of a topological space, i.e. the type `X` with the
  topology `TopologicalSpace.compactlyGenerated X`. The product of two compactly generated
  spaces `X`, `Y` in the category of compactly generated spaces is `CGSpace.KSpace (X × Y)`.
* `CGSpace.probeCompactOpen X Y` : the compact-open topology on `C(X, Y)` defined by test maps
  from compact Hausdorff spaces (sub-base `N(g, U) = {f | f (g (S)) ⊆ U}` for `g : S → X` continuous
  with `S` compact Hausdorff and `U ⊆ Y` open).
* `CGSpace.ContK X Y` : the compactly generated function space `k(C(X, Y))`.

Source: A. M. Masullo, *The Music of the Primes*, Definition E.1.1.1, Definition E.1.2.6 and
Construction E.1.2.9 (following Lewis and Strickland).
-/

universe u

namespace CGSpace

/-- The `k`-ification `k(X)` of a topological space `X`: a copy of the type `X`, which is given
the compactly generated topology `TopologicalSpace.compactlyGenerated X`, the finest topology for
which every continuous map `S → X` from a compact Hausdorff space `S : Type u` is continuous. -/
def KSpace (X : Type u) : Type u := X

namespace KSpace

/-- The identity bijection `X ≃ k(X)`. -/
def mk {X : Type u} : X ≃ KSpace X := Equiv.refl X

/-- `k(X)` carries the compactly generated topology of `X` (test spaces: compact Hausdorff spaces
in the universe of `X`). -/
instance instTopologicalSpace (X : Type u) [TopologicalSpace X] : TopologicalSpace (KSpace X) :=
  TopologicalSpace.compactlyGenerated.{u} X

end KSpace

/-- The compact-open topology on `C(X, Y)` *defined by test maps*: the topology generated by the
sets `N(g, U) = {f | ∀ t, f (g t) ∈ U}`, where `S` is a compact Hausdorff space, `g : S → X` is
continuous and `U ⊆ Y` is open. It is coarser than (or equal to) Mathlib's compact-open topology
`ContinuousMap.compactOpen`, whose sub-base uses all compact subsets of `X`. -/
@[instance_reducible]
def probeCompactOpen (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace C(X, Y) :=
  TopologicalSpace.generateFrom
    {N : Set C(X, Y) | ∃ (S : CompHaus.{u}) (g : C(S, X)) (U : Set Y),
      IsOpen U ∧ N = {f : C(X, Y) | ∀ t : S, f (g t) ∈ U}}

/-- The compactly generated function space `Cont_k(X, Y) = k(C(X, Y))`: a copy of the type
`C(X, Y)` of continuous maps, which is given the `k`-ification of the topology
`CGSpace.probeCompactOpen X Y`. -/
def ContK (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] : Type u := C(X, Y)

namespace ContK

/-- The identity bijection between `Cont_k(X, Y)` and the type `C(X, Y)` of continuous maps. -/
def toContinuousMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] :
    ContK X Y ≃ C(X, Y) := Equiv.refl _

/-- `Cont_k(X, Y)` carries the `k`-ification of the compact-open topology defined by test maps. -/
instance instTopologicalSpace (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace (ContK X Y) :=
  @TopologicalSpace.compactlyGenerated.{u} C(X, Y) (probeCompactOpen X Y)

end ContK

end CGSpace


