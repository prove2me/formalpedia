-- Prove2me | Definitions.Def_Monotonicity_Theorem_Extremal_Germs
-- name    : Monotonicity_Theorem_Extremal_Germs
-- status  : Definition
-- author  : @Gabewhigham
-- created : 2026-09-13T06:48:45.648009+00:00
-- url     : https://prove2.me/theorems/98fcccc6-4c26-48f6-8cac-f9d4033b0094
-- title:
--   The extremal germ patterns: local minima and local maxima everywhere
-- statement:
--   These definitions name the two extremal one-sided germ patterns of a definable function of one variable on an interval, completing the four-fold germ classification begun by the below-above and above-below patterns.
--
--   Let $M$ be an o-minimal structure over a dense linear order without endpoints $D$, let $f : I \to B$ be a definable function of one variable, and let $u < v$.
--
--   We say that $f$ has the **above-above pattern** on $(u,v)$ when every point $x \in I \cap (u,v)$ admits a window $c_1 < x < c_2$ with $c_1, c_2 \in (u,v)$ such that
--
--   $$y \in I \cap (c_1,x) \Rightarrow f(x) < f(y), \qquad y \in I \cap (x,c_2) \Rightarrow f(x) < f(y),$$
--
--   that is, every point of the interval is a strict local minimum of $f$. Dually, $f$ has the **below-below pattern** on $(u,v)$ when every such $x$ admits a window with
--
--   $$y \in I \cap (c_1,x) \Rightarrow f(y) < f(x), \qquad y \in I \cap (x,c_2) \Rightarrow f(y) < f(x),$$
--
--   that is, every point of the interval is a strict local maximum of $f$.
--
--   Together with the below-above and above-below patterns these exhaust the germ behaviour of an injective definable function: by o-minimality the definable sets $\{y : f(y) > f(x)\}$ and $\{y : f(y) < f(x)\}$ each contain or miss an interval on each side of $x$, and injectivity makes them partition a punctured neighbourhood of $x$. The two extremal patterns are exactly the ones that cannot occur on a whole interval, and excluding them is the substantive step in the proof that an injective definable function is strictly monotone on a subinterval.
--
--   **Formalization Note.** Points of the line are tuples in $\mathrm{Power}\,R\,1$, intervals are `openInterval`, and the order on tuples is `Lt1`, following the mission's framework.
-- source:
--   Lou van den Dries, Tame Topology and O-minimal Structures, LMS Lecture Note Series 248, CUP 1998, Chapter 3, Section 1 (Monotonicity Theorem): the two germ classes that are excluded in the proof that an injective definable function is strictly monotone on a subinterval.

import Definitions.Def_Monotonicity_Theorem_Uniform_Germs

set_option autoImplicit false

universe u

namespace Monotonicity_Theorem

variable {R : Type u}

/-- The "above-above" germ pattern of `f` on the interval `(u,v)`: every point `x` of the
interval which lies in the domain has a window `(c₁,c₂)` inside `(u,v)` on which `f` takes
values above `f x` on both sides of `x`.  Equivalently, every point of the interval is a
strict local minimum of `f`. -/
def UniformAboveAbove (D : DenseLinearOrderNoEndpoints R) {M : OMinimalStructure D}
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
        Lt1 D (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1)

/-- The "below-below" germ pattern of `f` on the interval `(u,v)`: every point `x` of the
interval which lies in the domain has a window `(c₁,c₂)` inside `(u,v)` on which `f` takes
values below `f x` on both sides of `x`.  Equivalently, every point of the interval is a
strict local maximum of `f`. -/
def UniformBelowBelow (D : DenseLinearOrderNoEndpoints R) {M : OMinimalStructure D}
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
        Lt1 D (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)

end Monotonicity_Theorem


