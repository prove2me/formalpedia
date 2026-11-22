-- Prove2me | Definitions.Def_Monotonicity_Theorem_Window_Loci
-- name    : Monotonicity_Theorem_Window_Loci
-- status  : Definition
-- author  : @Gabewhigham
-- created : 2026-09-12T20:25:50.784973+00:00
-- url     : https://prove2.me/theorems/174ad342-5bf5-4257-972b-84984debea38
-- title:
--   Window loci of a definable one-variable function
-- statement:
--   These definitions fix the vocabulary used by the local analysis of a definable one-variable function in an o-minimal structure.
--
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, and let $f : I \to B$ be a definable function of one variable, with $I, B$ definable subsets of the line.
--
--   For $u < v$ in $R$ we say that $f$ is **constant**, **strictly increasing**, or **strictly decreasing on the interval** $(u,v)$ when the corresponding property holds for all points of $I \cap (u,v)$:
--
--   $$\mathrm{Const}(u,v):\ f(x) = f(y),\qquad \mathrm{Inc}(u,v):\ x < y \Rightarrow f(x) < f(y),\qquad \mathrm{Dec}(u,v):\ x < y \Rightarrow f(y) < f(x)$$
--
--   for all $x, y \in I \cap (u,v)$.
--
--   The three **window loci** collect the points of the line that admit a witnessing neighbourhood:
--
--   1. the constancy locus, consisting of the points $x$ for which some $u < x < v$ satisfies $\mathrm{Const}(u,v)$;
--   2. the increase locus, consisting of the points $x$ for which some $u < x < v$ satisfies $(u,v) \subseteq I$ and $\mathrm{Inc}(u,v)$;
--   3. the decrease locus, defined in the same way with $\mathrm{Dec}(u,v)$.
--
--   The **good window locus** is the union of the three. Its complement is the set of points near which $f$ exhibits no uniform behaviour, and in an o-minimal structure that complement is finite; this is the mechanism behind the Monotonicity Theorem. The containment $(u,v) \subseteq I$ required in the monotone cases records that the witnessing window lies inside the domain, which is what makes the monotone branch of the Monotonicity Theorem meaningful.
--
--   **Formalization Note.** The definitions are stated inside the mission's existing framework: points of the line are tuples in $\mathrm{Power}\,R\,1$, intervals are `openInterval`, and the order on tuples is `Lt1`. Constancy is equality of the dependent-subtype values of `f.toFun`, so it does not presuppose decidable equality or a choice of representatives.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem): the local constancy / strict increase / strict decrease loci used in the proof.

import Definitions.Def_Monotonicity_Theorem_Framework

set_option autoImplicit false

universe u

namespace Monotonicity_Theorem

variable {R : Type u}

/-- `f` is constant on the part of its domain lying in the open interval `(u,v)`. -/
def ConstOnInterval {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) (u v : R) : Prop :=
  ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
    ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy)

/-- `f` is strictly increasing on the part of its domain lying in the open interval `(u,v)`. -/
def IncOnInterval {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) (u v : R) : Prop :=
  ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
    ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y → Lt1 D x y →
      Lt1 D (f.toFun (Subtype.mk x hx)).1 (f.toFun (Subtype.mk y hy)).1

/-- `f` is strictly decreasing on the part of its domain lying in the open interval `(u,v)`. -/
def DecOnInterval {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) (u v : R) : Prop :=
  ∀ x (hx : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
    ∀ y (hy : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y → Lt1 D x y →
      Lt1 D (f.toFun (Subtype.mk y hy)).1 (f.toFun (Subtype.mk x hx)).1

/-- Points admitting an open window on which `f` is constant. -/
def ConstWindowLocus {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) : Set (Power R 1) :=
  fun x => ∃ u v : R, D.lt u (x 0) ∧ D.lt (x 0) v ∧ ConstOnInterval f u v

/-- Points admitting an open window contained in the domain on which `f` is strictly increasing. -/
def IncWindowLocus {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) : Set (Power R 1) :=
  fun x => ∃ u v : R, D.lt u (x 0) ∧ D.lt (x 0) v ∧
    (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I ∧ IncOnInterval f u v

/-- Points admitting an open window contained in the domain on which `f` is strictly decreasing. -/
def DecWindowLocus {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) : Set (Power R 1) :=
  fun x => ∃ u v : R, D.lt u (x 0) ∧ D.lt (x 0) v ∧
    (openInterval D (Endpoint.finite u) (Endpoint.finite v)).Subset I ∧ DecOnInterval f u v

/-- Points admitting a good window: constant, or strictly monotone inside the domain. -/
def GoodWindowLocus {D : DenseLinearOrderNoEndpoints R} {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) : Set (Power R 1) :=
  fun x => ConstWindowLocus f x ∨ IncWindowLocus f x ∨ DecWindowLocus f x

end Monotonicity_Theorem


