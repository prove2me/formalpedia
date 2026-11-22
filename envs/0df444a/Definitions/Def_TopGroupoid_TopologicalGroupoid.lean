-- Prove2me | Definitions.Def_TopGroupoid_TopologicalGroupoid
-- name    : TopGroupoid_TopologicalGroupoid
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T15:31:30.222783+00:00
-- url     : https://prove2.me/theorems/c43b3417-7e18-4650-9eaa-691b1cff8726
-- title:
--   Groupoids in sets $(X,R,s,t,c,e,i)$, their morphisms and isotropy sets, and topological groupoids (groupoids internal to $\mathbf{CGWH}$)
-- statement:
--   Definition of groupoids presented by their structure maps, of their morphisms and isotropy sets, and of *topological groupoids*, i.e. groupoids internal to the category $\mathbf{CGWH}$ of compactly generated weakly Hausdorff spaces.
--
--   **Groupoids in sets** (`TopGroupoid.SetGroupoid X R`). A *groupoid in sets* is a datum $(X,R,s,t,c,e,i)$ consisting of
--
--   - a set $X$, the *set of objects*, and a set $R$, the *set of morphisms*;
--   - maps $s,t:R\to X$, the *source* and the *target*;
--   - a map $c:R\times_{s,X,t}R\to R$, the *composition law*, defined on the set $R\times_{s,X,t}R=\{(g,h)\in R\times R:\ s(g)=t(h)\}$ of composable pairs;
--   - a map $e:X\to R$, the *unit section*, and a map $i:R\to R$, the *inversion*;
--
--   subject to the following axioms.
--
--   1. *Associativity.* For every composable pair $(g,h)$, $$t(c(g,h))=t(g),\qquad s(c(g,h))=s(h),$$ and $c(g,c(h,k))=c(c(g,h),k)$ whenever $s(g)=t(h)$ and $s(h)=t(k)$.
--   2. *Identity.* $s(e(x))=t(e(x))=x$ for all $x\in X$, and $c(g,e(s(g)))=g=c(e(t(g)),g)$ for all $g\in R$.
--   3. *Inverse.* For all $g\in R$: $s(i(g))=t(g)$, $t(i(g))=s(g)$, $c(g,i(g))=e(t(g))$ and $c(i(g),g)=e(s(g))$.
--
--   So $g\in R$ is a morphism from $s(g)$ to $t(g)$ and $c(g,h)$ is the composite of $h$ followed by $g$.
--
--   **Isotropy** (`TopGroupoid.SetGroupoid.isotropy G x`). For an object $x\in X$, the isotropy set is $$R_x:=s^{-1}(x)\cap t^{-1}(x)=\{g\in R:\ s(g)=x,\ t(g)=x\}.$$
--
--   **Morphisms of groupoids** (`TopGroupoid.SetGroupoid.IsHom G G' f₁ f₂`). A morphism from $(X,R,s,t,c,e,i)$ to $(X',R',s',t',c',e',i')$ is a pair of maps $f_1:X\to X'$, $f_2:R\to R'$ compatible with the structure maps: $$s'\circ f_2=f_1\circ s,\quad t'\circ f_2=f_1\circ t,\quad f_2(c(g,h))=c'(f_2(g),f_2(h)),\quad f_2\circ e=e'\circ f_1,\quad f_2\circ i=i'\circ f_2,$$ the third identity for all composable pairs $(g,h)$ (the pair $(f_2(g),f_2(h))$ is then composable by the first two).
--
--   **Topological groupoids** (`TopGroupoid.TopologicalGroupoid X R`). A topological space is *compactly generated* if its topology is coinduced by all continuous maps from compact Hausdorff spaces, and *weakly Hausdorff* if the image of every such map is closed. A *topological groupoid* is a groupoid internal to $\mathbf{CGWH}$: a groupoid in sets $(X,R,s,t,c,e,i)$ in which $X$ and $R$ are compactly generated weakly Hausdorff topological spaces and all the structure maps $s,t,c,e,i$ are continuous. Here $R\times_{s,X,t}R$ carries the topology of the fibre product in $\mathbf{CGWH}$: the $k$-ification of the subspace topology induced by the product topology of $R\times R$ (the $k$-ification of a topology is the topology coinduced by all continuous maps from compact Hausdorff spaces). A *map of topological groupoids* (`TopGroupoid.TopologicalGroupoid.IsHom G G' f₁ f₂`) is a morphism $(f_1,f_2)$ of the underlying groupoids in sets such that $f_1$ and $f_2$ are continuous.
--
--   The stacks of the paper's Appendix E are quotient stacks associated to explicit topological groupoids: the basic example is the action groupoid $G\times X\rightrightarrows X$ of a continuous group action, and a topological groupoid generalizes a topological equivalence relation on $X$ (the image of $(t,s):R\to X\times X$). The presentation by structure maps, rather than by a family of sets of morphisms indexed by pairs of objects, is what allows one to put a topology on the set of all morphisms.
--
--   **Formalization Note.** `SetGroupoid X R` is a structure on two types `X : Type u`, `R : Type v` with fields `src`, `tgt`, `comp`, `unit`, `inv` and the axioms; `comp` takes an element of the subtype `{p : R × R // src p.1 = tgt p.2}`. `SetGroupoid.IsHom` and `TopologicalGroupoid.IsHom` are `Prop`-valued structures. `TopologicalGroupoid X R` (for `X R : Type u` carrying topologies) extends `SetGroupoid X R`; the conditions that `X` and `R` are compactly generated (Mathlib's `CompactlyGeneratedSpace`) and weakly Hausdorff (`CGWH.WeaklyHausdorffSpace`, definition file `CGWH_WeakHausdorff`) are fields of the structure, and the continuity of the composition is `Continuous[TopologicalSpace.compactlyGenerated.{u} {p : R × R // src p.1 = tgt p.2}, _] comp`. The paper defines groupoids internal to an arbitrary category with fibre products (Definition E.4.2.1); only the case of $\mathbf{CGWH}$ is formalized, in the concrete form the paper describes after Definition E.4.2.3, using that the fibre product of $\mathbf{CGWH}$ is the $k$-ification of the topological fibre product. Mathlib's `CategoryTheory.Groupoid` is the other standard presentation of a groupoid (a category in which every morphism is invertible).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 883-884, Definition E.4.1.1; p. 886, Definition E.4.2.1 and Definition E.4.2.3; p. 887, (E.4.2.1); classical references given by the paper at the beginning of Section E.4.1: P. J. Higgins, Notes on categories and groupoids, Van Nostrand Reinhold, London, 1971; A. Cannas da Silva, A. Weinstein, Geometric Models for Noncommutative Algebras, Berkeley Mathematics Lecture Notes 10 (1999), Part VI; B. Noohi, Foundations of topological stacks, I, arXiv:math/0503247, Section 3.2; notation of the Stacks Project, Tag 022L

import Definitions.Def_CGWH_WeakHausdorff

/-!
# Groupoids in sets and topological groupoids

A groupoid is presented by its *structure maps*: a set `X` of objects, a set `R` of morphisms
(arrows), source and target maps `s, t : R → X`, a composition law `c` defined on the fibre product
`R ×_{s,X,t} R = {(g, h) | s g = t h}`, a unit section `e : X → R` and an inversion `i : R → R`.
The composition `c (g, h)` is the composite "`g` after `h`": it is defined when the source of `g` is
the target of `h`, and it goes from the source of `h` to the target of `g`.

* `TopGroupoid.SetGroupoid X R` : a *groupoid in sets* with set of objects `X` and set of morphisms
  `R`.
* `TopGroupoid.SetGroupoid.isotropy G x` : the isotropy set `R_x = s⁻¹(x) ∩ t⁻¹(x)` of the morphisms
  from an object `x` to itself.
* `TopGroupoid.SetGroupoid.IsHom G G' f₁ f₂` : the pair `(f₁ : X → X', f₂ : R → R')` is a *morphism
  of groupoids*, i.e. it is compatible with all the structure maps.
* `TopGroupoid.TopologicalGroupoid X R` : a *topological groupoid*, i.e. a groupoid internal to the
  category `CGWH` of compactly generated weakly Hausdorff spaces: `X` and `R` are compactly
  generated weakly Hausdorff spaces, `s`, `t`, `e`, `i` are continuous, and `c` is continuous on the
  fibre product of `CGWH`, which is the set `{(g, h) | s g = t h}` with the `k`-ification of the
  topology induced by the product topology of `R × R`.
* `TopGroupoid.TopologicalGroupoid.IsHom G G' f₁ f₂` : the pair `(f₁, f₂)` is a *map of topological
  groupoids*, i.e. a morphism of the underlying groupoids in sets with `f₁` and `f₂` continuous.

Source: A. M. Masullo, *The Music of the Primes*, Definition E.4.1.1, Definition E.4.2.1,
Definition E.4.2.3 and (E.4.2.1) (following the Stacks Project, Tag 022L, for the notation).
-/

universe u v u' v'

open Topology

namespace TopGroupoid

/-- A *groupoid in sets* `(X, R, s, t, c, e, i)`: a set of objects `X`, a set of morphisms `R`,
source and target maps `s, t : R → X`, a composition law `c : R ×_{s,X,t} R → R` on the pairs
`(g, h)` with `s g = t h`, a unit section `e : X → R` and an inversion `i : R → R`, subject to the
associativity, identity and inverse axioms. -/
structure SetGroupoid (X : Type u) (R : Type v) where
  /-- The source map `s : R → X`. -/
  src : R → X
  /-- The target map `t : R → X`. -/
  tgt : R → X
  /-- The composition law `c : R ×_{s,X,t} R → R`, defined on the pairs `(g, h)` with
  `s g = t h`. -/
  comp : {p : R × R // src p.1 = tgt p.2} → R
  /-- The unit section `e : X → R`. -/
  unit : X → R
  /-- The inversion `i : R → R`. -/
  inv : R → R
  /-- `t ∘ c = t ∘ pr₁`. -/
  tgt_comp : ∀ p : {p : R × R // src p.1 = tgt p.2}, tgt (comp p) = tgt p.1.1
  /-- `s ∘ c = s ∘ pr₂`. -/
  src_comp : ∀ p : {p : R × R // src p.1 = tgt p.2}, src (comp p) = src p.1.2
  /-- Associativity: `c (g, c (h, k)) = c (c (g, h), k)` for composable `g`, `h`, `k`. -/
  comp_assoc : ∀ (g h k : R) (hgh : src g = tgt h) (hhk : src h = tgt k),
    comp ⟨(g, comp ⟨(h, k), hhk⟩), hgh.trans (tgt_comp ⟨(h, k), hhk⟩).symm⟩ =
      comp ⟨(comp ⟨(g, h), hgh⟩, k), (src_comp ⟨(g, h), hgh⟩).trans hhk⟩
  /-- `s ∘ e = id`. -/
  src_unit : ∀ x : X, src (unit x) = x
  /-- `t ∘ e = id`. -/
  tgt_unit : ∀ x : X, tgt (unit x) = x
  /-- `c (g, e (s g)) = g`. -/
  comp_unit : ∀ g : R, comp ⟨(g, unit (src g)), (tgt_unit (src g)).symm⟩ = g
  /-- `c (e (t g), g) = g`. -/
  unit_comp : ∀ g : R, comp ⟨(unit (tgt g), g), src_unit (tgt g)⟩ = g
  /-- `s ∘ i = t`. -/
  src_inv : ∀ g : R, src (inv g) = tgt g
  /-- `t ∘ i = s`. -/
  tgt_inv : ∀ g : R, tgt (inv g) = src g
  /-- `c (g, i g) = e (t g)`. -/
  comp_inv : ∀ g : R, comp ⟨(g, inv g), (tgt_inv g).symm⟩ = unit (tgt g)
  /-- `c (i g, g) = e (s g)`. -/
  inv_comp : ∀ g : R, comp ⟨(inv g, g), src_inv g⟩ = unit (src g)

/-- The *isotropy* (vertex) set `R_x = s⁻¹(x) ∩ t⁻¹(x)` of a groupoid at an object `x`: the
morphisms with source `x` and target `x`. -/
def SetGroupoid.isotropy {X : Type u} {R : Type v} (G : SetGroupoid X R) (x : X) : Set R :=
  {g : R | G.src g = x ∧ G.tgt g = x}

/-- The pair of maps `(f₁ : X → X', f₂ : R → R')` is a *morphism of groupoids* from `G` to `G'`:
it is compatible with the source and target maps, the composition laws, the unit sections and the
inversions. -/
structure SetGroupoid.IsHom {X : Type u} {R : Type v} {X' : Type u'} {R' : Type v'}
    (G : SetGroupoid X R) (G' : SetGroupoid X' R') (f₁ : X → X') (f₂ : R → R') : Prop where
  /-- Compatibility with the source maps: `s' ∘ f₂ = f₁ ∘ s`. -/
  map_src : ∀ g : R, G'.src (f₂ g) = f₁ (G.src g)
  /-- Compatibility with the target maps: `t' ∘ f₂ = f₁ ∘ t`. -/
  map_tgt : ∀ g : R, G'.tgt (f₂ g) = f₁ (G.tgt g)
  /-- Compatibility with the composition laws: `f₂ (c (g, h)) = c' (f₂ g, f₂ h)`. -/
  map_comp : ∀ (g h : R) (hgh : G.src g = G.tgt h),
    f₂ (G.comp ⟨(g, h), hgh⟩) =
      G'.comp ⟨(f₂ g, f₂ h), (map_src g).trans ((congrArg f₁ hgh).trans (map_tgt h).symm)⟩
  /-- Compatibility with the unit sections: `f₂ ∘ e = e' ∘ f₁`. -/
  map_unit : ∀ x : X, f₂ (G.unit x) = G'.unit (f₁ x)
  /-- Compatibility with the inversions: `f₂ ∘ i = i' ∘ f₂`. -/
  map_inv : ∀ g : R, f₂ (G.inv g) = G'.inv (f₂ g)

/-- A *topological groupoid* `(X, R, s, t, c, e, i)`, i.e. a groupoid internal to the category of
compactly generated weakly Hausdorff spaces: a groupoid in sets whose set of objects `X` and set of
morphisms `R` are compactly generated weakly Hausdorff topological spaces and whose structure maps
are continuous. The composition law is required to be continuous on the fibre product
`R ×_{s,X,t} R` *of compactly generated weakly Hausdorff spaces*: the set `{(g, h) | s g = t h}`
with the `k`-ification of the topology induced by the product topology of `R × R`. -/
structure TopologicalGroupoid (X R : Type u) [TopologicalSpace X] [TopologicalSpace R]
    extends SetGroupoid X R where
  /-- The space of objects is compactly generated. -/
  compactlyGeneratedSpace_obj : CompactlyGeneratedSpace X
  /-- The space of objects is weakly Hausdorff. -/
  weaklyHausdorffSpace_obj : CGWH.WeaklyHausdorffSpace X
  /-- The space of morphisms is compactly generated. -/
  compactlyGeneratedSpace_arr : CompactlyGeneratedSpace R
  /-- The space of morphisms is weakly Hausdorff. -/
  weaklyHausdorffSpace_arr : CGWH.WeaklyHausdorffSpace R
  /-- The source map is continuous. -/
  continuous_src : Continuous src
  /-- The target map is continuous. -/
  continuous_tgt : Continuous tgt
  /-- The unit section is continuous. -/
  continuous_unit : Continuous unit
  /-- The inversion is continuous. -/
  continuous_inv : Continuous inv
  /-- The composition law is continuous for the `k`-ification of the subspace topology of the
  set of composable pairs in `R × R`. -/
  continuous_comp :
    Continuous[TopologicalSpace.compactlyGenerated.{u} {p : R × R // src p.1 = tgt p.2}, _] comp

/-- The pair of maps `(f₁ : X → X', f₂ : R → R')` is a *map of topological groupoids* from `G` to
`G'`: it is a morphism of the underlying groupoids in sets and `f₁`, `f₂` are continuous. -/
structure TopologicalGroupoid.IsHom {X R X' R' : Type u} [TopologicalSpace X] [TopologicalSpace R]
    [TopologicalSpace X'] [TopologicalSpace R'] (G : TopologicalGroupoid X R)
    (G' : TopologicalGroupoid X' R') (f₁ : X → X') (f₂ : R → R') : Prop
    extends SetGroupoid.IsHom G.toSetGroupoid G'.toSetGroupoid f₁ f₂ where
  /-- The map on objects is continuous. -/
  continuous_obj : Continuous f₁
  /-- The map on morphisms is continuous. -/
  continuous_arr : Continuous f₂

end TopGroupoid


