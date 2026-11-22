-- Prove2me | Definitions.Def_CGWH_WeakHausdorff
-- name    : CGWH_WeakHausdorff
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T10:48:44.885832+00:00
-- url     : https://prove2.me/theorems/872be703-f288-44e1-af31-5e26f6e07dc1
-- title:
--   Weakly Hausdorff spaces, the weak Hausdorffification $h(X)=X/R_X$, and the category $\mathbf{CGWH}$
-- statement:
--   Definitions of the weak Hausdorff separation axiom, of the weak Hausdorffification of a topological space, and of the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces.
--
--   Throughout, a *test map* into a topological space $X$ is a continuous map $g:K\to X$ whose source $K$ is a compact Hausdorff space. A subset $Z\subseteq X$ is *$k$-closed* if $g^{-1}(Z)$ is closed in $K$ for every test map $g:K\to X$; the $k$-ification $k(X)$ is the set $X$ with the topology whose closed sets are the $k$-closed subsets, and $X$ is *compactly generated* if $k(X)=X$ (no separation axiom is imposed). For spaces $X,Y$, $X\times_0Y$ is the cartesian product with the product topology and $X\times Y:=k(X\times_0Y)$.
--
--   1. **Weakly Hausdorff space** (`CGWH.WeaklyHausdorffSpace X`). A topological space $X$ is *weakly Hausdorff* if for every compact Hausdorff space $K$ and every continuous map $f:K\to X$ the image $f(K)$ is a closed subset of $X$.
--
--   2. **Smallest closed equivalence relation** (`CGWH.whSetoid X`). For a topological space $X$,
--   $$R_X:=\bigcap\big\{\,R\subseteq X\times X\;:\;R\text{ is an equivalence relation on the set }X\text{ and }R\text{ is closed in }X\times X=k(X\times_0X)\,\big\}.$$
--   Being an intersection of equivalence relations that are closed in $k(X\times_0X)$ (the total relation is one of them), $R_X$ is itself an equivalence relation closed in $k(X\times_0X)$, the smallest one.
--
--   3. **Weak Hausdorffification** (`CGWH.WeakHausdorffification X`, with the quotient map `CGWH.WeakHausdorffification.mk`). The quotient space
--   $$h(X):=X/R_X,\qquad q_X:X\to h(X),$$
--   endowed with the quotient topology.
--
--   4. **The category $\mathbf{CGWH}$** (`CGWH.CGWHCat`, with the inclusion functor `CGWH.forgetToCG`). The category whose objects are the compactly generated weakly Hausdorff topological spaces and whose morphisms are the continuous maps; it is the full subcategory of the category $\mathbf{CG}$ of compactly generated spaces on the weakly Hausdorff objects, and $u_{\mathrm{wh}}:\mathbf{CGWH}\to\mathbf{CG}$ is the inclusion.
--
--   The weak Hausdorff axiom lies between $T_1$ and Hausdorff, and for a compactly generated space $X$ it is equivalent to the diagonal being closed in $X\times X$. The category $\mathbf{CGWH}$ (McCord, Lewis, Strickland) is the standard "convenient category of spaces": it is complete, cocomplete and cartesian closed, quotient maps are stable under pullback in it, and $X\mapsto h(X)$ is the left adjoint of the inclusion $\mathbf{CGWH}\subset\mathbf{CG}$. The paper recalls these notions in Appendix E.2 as the category of spaces underlying its topological stacks.
--
--   **Formalization Note.** In `CGWH.WeaklyHausdorffSpace X`, for `X : Type u`, the test spaces range over the compact Hausdorff spaces `K : Type u` of the universe of `X`, exactly as in Mathlib's `CompactlyGeneratedSpace` (test spaces `CompHaus.{u}`). This loses no generality: if $f:K\to X$ is continuous with $K$ compact Hausdorff in any universe and $S\subseteq K$ contains one point of each non-empty fibre of $f$, then $f(K)=f(\overline S)$, and the compact Hausdorff space $\overline S$ has a dense subset of cardinality at most $|X|$, hence cardinality at most $2^{2^{|X|}}$. `CGWH.whSetoid X` is the infimum, in the complete lattice `Setoid X`, of the set of setoids `S` whose graph `{p : X × X | S p.1 p.2}` is closed for the topology `TopologicalSpace.compactlyGenerated (X × X)` (the $k$-ification of the product topology); it is defined for an arbitrary topological space, whereas the source defines $R_X$ and $h(X)$ for compactly generated $X$ only. `CGWH.WeakHausdorffification X` is a type synonym of `Quotient (CGWH.whSetoid X)` carrying the quotient topology. `CGWH.CGWHCat.{u}` is the `ObjectProperty.FullSubcategory` of Mathlib's category `CompactlyGenerated.{u, u}` (compactly generated spaces in `Type u`, tested by `CompHaus.{u}`) defined by the object property `CGWH.weaklyHausdorff`; an object `X` has underlying compactly generated space `X.obj`, and a morphism `f : X ⟶ Y` has underlying continuous map `ConcreteCategory.hom f.hom : C(X.obj, Y.obj)`. The file contains definitions only. Mathlib (at the pinned revision) has no weak Hausdorff notion. On the platform, the paper-specific bundles `QAlgorithms_Papers_Independent_Intakethird100_P73` (`IsWeaklyHausdorff`, a predicate on its own bundled structure `KSpace`) and `QAlgorithms_Papers_Independent_Intake100_P03` (`IsKSpace`, the conjunction "compactly generated and weakly Hausdorff") use the same condition (closed images of all probes from `CompHaus.{u}`); it is restated here as an unbundled type class in a neutral namespace so that these bundles need not be imported.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 846 and 851, Definition E.2.1.1, Definition E.2.2.1 and Definition E.2.2.2; classical references (the sources named by the paper for Section E.2, p. 846, and for the construction of $h$, p. 851): L. G. Lewis, Jr., The stable category and generalized Thom spectra, Ph.D. thesis, University of Chicago, 1978, §3; M. C. McCord, Classifying spaces and infinite symmetric products, Transactions of the American Mathematical Society 146 (1969), 273-298, §2; C. Rezk, Compactly generated spaces (available online), §4; N. Strickland, The category of CGWH spaces (available online), §1 and Prop. 2.22

import Mathlib

/-!
# Weakly Hausdorff spaces, the weak Hausdorffification and the category `CGWH`

Definitions for the theory of compactly generated weakly Hausdorff spaces (McCord, Lewis,
Strickland). "Compactly generated" is Mathlib's `CompactlyGeneratedSpace`: the topology is coinduced
by all continuous maps from compact Hausdorff spaces of the same universe, with no separation axiom.

* `CGWH.WeaklyHausdorffSpace X` : the space `X` is *weakly Hausdorff*, i.e. the image of every
  continuous map from a compact Hausdorff space to `X` is closed in `X`.
* `CGWH.whSetoid X` : the smallest equivalence relation on `X` whose graph is closed in the
  `k`-ification `k(X × X)` of the product topology.
* `CGWH.WeakHausdorffification X` : the quotient space `h(X) = X / R_X` of `X` by `CGWH.whSetoid X`,
  with the quotient map `CGWH.WeakHausdorffification.mk : X → h(X)`.
* `CGWH.CGWHCat` : the category of compactly generated weakly Hausdorff spaces, defined as the full
  subcategory of Mathlib's category `CompactlyGenerated` of compactly generated spaces, with the
  inclusion functor `CGWH.forgetToCG`.

Source: A. M. Masullo, *The Music of the Primes*, Definition E.2.1.1, Definition E.2.2.1 and
Definition E.2.2.2 (following McCord, Lewis and Strickland).
-/

universe u

open CategoryTheory Topology

namespace CGWH

/-- A topological space `X` is *weakly Hausdorff* if for every compact Hausdorff space `K` and every
continuous map `f : K → X` the image `f(K)` is closed in `X`. The test spaces `K` range over the
compact Hausdorff spaces in the universe of `X`, as for Mathlib's `CompactlyGeneratedSpace`. -/
class WeaklyHausdorffSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- The image of a continuous map from a compact Hausdorff space is closed. -/
  isClosed_range : ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K] (f : K → X),
    Continuous f → IsClosed (Set.range f)

/-- The smallest *closed* equivalence relation `R_X` on a topological space `X`: the intersection of
all equivalence relations on `X` whose graph `{(x, y) | x ∼ y}` is closed in the `k`-ification
`k(X × X)` of the product topology (the product of `X` with itself in the category of compactly
generated spaces, when `X` is compactly generated). -/
def whSetoid (X : Type u) [TopologicalSpace X] : Setoid X :=
  sInf {S : Setoid X |
    IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] {p : X × X | S p.1 p.2}}

/-- The *weak Hausdorffification* `h(X) = X / R_X` of a topological space `X`: the quotient of `X`
by the smallest closed equivalence relation `CGWH.whSetoid X`, with the quotient topology. It is
meant to be used for compactly generated `X`. -/
def WeakHausdorffification (X : Type u) [TopologicalSpace X] : Type u :=
  Quotient (whSetoid X)

namespace WeakHausdorffification

/-- `h(X)` carries the quotient topology of `X`. -/
instance instTopologicalSpace (X : Type u) [TopologicalSpace X] :
    TopologicalSpace (WeakHausdorffification X) :=
  inferInstanceAs (TopologicalSpace (Quotient (whSetoid X)))

/-- The quotient map `q_X : X → h(X)`. -/
def mk {X : Type u} [TopologicalSpace X] (x : X) : WeakHausdorffification X :=
  Quotient.mk (whSetoid X) x

end WeakHausdorffification

/-- The property of a compactly generated space of being weakly Hausdorff. -/
def weaklyHausdorff : ObjectProperty CompactlyGenerated.{u, u} :=
  fun X => WeaklyHausdorffSpace X

/-- The category `CGWH` of compactly generated weakly Hausdorff spaces and continuous maps: the full
subcategory of the category `CompactlyGenerated` of compactly generated spaces on the weakly
Hausdorff ones. -/
abbrev CGWHCat : Type (u + 1) := (weaklyHausdorff.{u}).FullSubcategory

/-- The inclusion (forgetful) functor `u_wh : CGWH ⥤ CG`. -/
abbrev forgetToCG : CGWHCat.{u} ⥤ CompactlyGenerated.{u, u} := (weaklyHausdorff.{u}).ι

end CGWH


