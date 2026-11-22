-- Prove2me | Definitions.Def_Monotonicity_Theorem_Uniform_Germs
-- name    : Monotonicity_Theorem_Uniform_Germs
-- status  : Definition
-- author  : @Gabewhigham
-- created : 2026-09-13T06:33:35.413947+00:00
-- url     : https://prove2.me/theorems/42d6987c-9a5c-45e7-a2e4-c831ecf520e0
-- title:
--   Uniform one-sided germ patterns of a definable function
-- statement:
--   These definitions name the two one-sided germ patterns that a definable function of one variable can exhibit uniformly on an interval.
--
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u < v$.
--
--   We say that $f$ has the **below-above pattern** on $(u,v)$ when every point $x \in I \cap (u,v)$ admits a window $c_1 < x < c_2$ with $c_1, c_2 \in (u,v)$ such that
--
--   $$y \in I \cap (c_1,x) \Rightarrow f(y) < f(x), \qquad y \in I \cap (x,c_2) \Rightarrow f(x) < f(y).$$
--
--   Symmetrically, $f$ has the **above-below pattern** on $(u,v)$ when every such $x$ admits a window $c_1 < x < c_2$ inside $(u,v)$ with
--
--   $$y \in I \cap (c_1,x) \Rightarrow f(x) < f(y), \qquad y \in I \cap (x,c_2) \Rightarrow f(y) < f(x).$$
--
--   These are strictly weaker than strict monotonicity on a window: they only compare the values of $f$ with the single value $f(x)$, and only on the two sides of $x$ separately. They are exactly the data produced by o-minimality when one analyses the germ of the definable sets $\{y : f(y) > f(x)\}$ and $\{y : f(y) < f(x)\}$ on each side of a point, and they are strong enough to force strict monotonicity on the whole interval.
--
--   **Formalization Note.** Points of the line are tuples in $\mathrm{Power}\,R\,1$, intervals are `openInterval`, and the order on tuples is `Lt1`, following the mission's framework. Membership of the domain $I$ is carried explicitly because the function is formalized on the subtype of its domain.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem): the one-sided comparisons used in the proof that an injective definable function is strictly monotone on a subinterval.

import Definitions.Def_Monotonicity_Theorem_Window_Loci

set_option autoImplicit false

universe u

namespace Monotonicity_Theorem

variable {R : Type u}

/-- The "below-above" germ pattern of `f` on the interval `(u,v)`: every point `x` of the
interval which lies in the domain has a window `(c₁,c₂)` inside `(u,v)` such that `f` takes
values below `f x` on `(c₁,x)` and values above `f x` on `(x,c₂)`. -/
def UniformBelowAbove (D : DenseLinearOrderNoEndpoints R) {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) (u v : R) : Prop :=
  ∀ x (hxI : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
    ∃ c₁ c₂ : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) c₁ ∧
      openInterval D (Endpoint.finite u) (Endpoint.finite v) c₂ ∧
      Lt1 D c₁ x ∧ Lt1 D x c₂ ∧
      (∀ y (hyI : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        Lt1 D c₁ y → Lt1 D y x →
        Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1) ∧
      (∀ y (hyI : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        Lt1 D x y → Lt1 D y c₂ →
        Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)

/-- The "above-below" germ pattern of `f` on the interval `(u,v)`: every point `x` of the
interval which lies in the domain has a window `(c₁,c₂)` inside `(u,v)` such that `f` takes
values above `f x` on `(c₁,x)` and values below `f x` on `(x,c₂)`. -/
def UniformAboveBelow (D : DenseLinearOrderNoEndpoints R) {M : OMinimalStructure D}
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) (u v : R) : Prop :=
  ∀ x (hxI : I x), openInterval D (Endpoint.finite u) (Endpoint.finite v) x →
    ∃ c₁ c₂ : Power R 1,
      openInterval D (Endpoint.finite u) (Endpoint.finite v) c₁ ∧
      openInterval D (Endpoint.finite u) (Endpoint.finite v) c₂ ∧
      Lt1 D c₁ x ∧ Lt1 D x c₂ ∧
      (∀ y (hyI : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        Lt1 D c₁ y → Lt1 D y x →
        Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) ∧
      (∀ y (hyI : I y), openInterval D (Endpoint.finite u) (Endpoint.finite v) y →
        Lt1 D x y → Lt1 D y c₂ →
        Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)

end Monotonicity_Theorem


