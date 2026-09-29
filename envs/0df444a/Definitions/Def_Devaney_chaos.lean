-- Prove2me | Definitions.Def_Devaney_chaos
-- name    : Devaney_chaos
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T06:57:27.402428+00:00
-- url     : https://prove2.me/theorems/78b4383d-8735-4697-9f56-709bf734c8cb
-- title:
--   Devaney's chaos: transitivity, sensitive dependence, dense periodic points
-- statement:
--   This file fixes the vocabulary of chaos used throughout the book.
--
--   Let $X$ be a metric space, $J \subseteq X$ a subset (thought of as invariant), and $f : X \to X$ a map.
--
--   1. $\operatorname{Per}_n(f, J)$ is the set of points of $J$ fixed by the $n$-th iterate, $\{x \in J : f^n(x) = x\}$, and $\operatorname{Per}(f, J)$ is the set of points of $J$ that are periodic, i.e. fixed by $f^n$ for some $n > 0$.
--
--   2. (Definition 8.1) $f$ is **topologically transitive** on $J$ if for every pair of open sets $U, V$ of the ambient space that meet $J$, there is an iterate $k > 0$ with $f^k(U \cap J) \cap V \neq \emptyset$. Intuitively, orbits move from any small neighbourhood to any other, so the system cannot be split into two non-interacting invariant open pieces.
--
--   3. (Definition 8.2) $f$ has **sensitive dependence on initial conditions** on $J$ if there is $\delta > 0$ such that for every $x \in J$ and every $\varepsilon > 0$ there are $y \in J$ with $d(x,y) < \varepsilon$ and $n \ge 0$ with $d(f^n(x), f^n(y)) > \delta$. Not all nearby points must separate — one in every neighbourhood suffices.
--
--   4. (Definition 8.7) $f$ is **expansive** on $J$ if there is $\nu > 0$ such that the orbits of any two distinct points of $J$ separate by more than $\nu$ at some time. This is the stronger, "all nearby points separate" variant of 3.
--
--   5. (Definition 8.5) $f$ is **chaotic on $V$** if it has sensitive dependence on initial conditions, is topologically transitive, and its periodic points are dense in $V$: unpredictability, indecomposability, and an element of regularity.
--
--   These four predicates are the interface every later mission in this series is phrased against.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.8, pp. 49–50, Definitions 8.1, 8.2, 8.5, 8.7

import Mathlib

namespace Devaney

variable {X : Type*}

/-- The set of points of `J` that are fixed by the `n`-th iterate of `f`
(Devaney's `Perₙ(f)`, restricted to the invariant set `J`). -/
def PerOfPeriod (J : Set X) (f : X → X) (n : ℕ) : Set X :=
  {x ∈ J | f^[n] x = x}

/-- The set of periodic points of `f` lying in `J` (Devaney's `Per(f)`). -/
def Per (J : Set X) (f : X → X) : Set X :=
  {x ∈ J | ∃ n > 0, f^[n] x = x}

/-- Devaney, Definition 8.1: `f : J → J` is topologically transitive if for any pair of
open sets `U`, `V` meeting `J` there is `k > 0` with `f^k(U ∩ J) ∩ V ≠ ∅`. -/
def TopologicallyTransitive [TopologicalSpace X] (J : Set X) (f : X → X) : Prop :=
  ∀ U V : Set X, IsOpen U → IsOpen V → (U ∩ J).Nonempty → (V ∩ J).Nonempty →
    ∃ k > 0, (f^[k] '' (U ∩ J) ∩ V).Nonempty

/-- Devaney, Definition 8.2: `f : J → J` has sensitive dependence on initial conditions if
there is `δ > 0` such that every point of `J` has points of `J` arbitrarily close to it whose
orbit eventually separates from its own orbit by more than `δ`. -/
def SensitiveDependence [PseudoMetricSpace X] (J : Set X) (f : X → X) : Prop :=
  ∃ δ > 0, ∀ x ∈ J, ∀ ε > 0, ∃ y ∈ J, dist x y < ε ∧ ∃ n : ℕ, dist (f^[n] x) (f^[n] y) > δ

/-- Devaney, Definition 8.7: `f : J → J` is expansive if there is `ν > 0` such that the orbits
of any two distinct points of `J` eventually separate by more than `ν`. -/
def Expansive [PseudoMetricSpace X] (J : Set X) (f : X → X) : Prop :=
  ∃ ν > 0, ∀ x ∈ J, ∀ y ∈ J, x ≠ y → ∃ n : ℕ, dist (f^[n] x) (f^[n] y) > ν

/-- Devaney, Definition 8.5: `f` is chaotic on `V` if it has sensitive dependence on initial
conditions, is topologically transitive, and its periodic points are dense in `V`. -/
def Chaotic [PseudoMetricSpace X] (V : Set X) (f : X → X) : Prop :=
  SensitiveDependence V f ∧ TopologicallyTransitive V f ∧ V ⊆ closure (Per V f)

end Devaney


