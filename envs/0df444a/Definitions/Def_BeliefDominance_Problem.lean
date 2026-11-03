-- Prove2me | Definitions.Def_BeliefDominance_Problem
-- name    : BeliefDominance_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:56.967485+00:00
-- url     : https://prove2.me/theorems/e7d8f3f5-5a0d-4bda-9380-a44f0a204e4a
-- title:
--   Decision problems with multiple beliefs, expected utilities (1)–(2), belief dominance (3)–(4)
-- statement:
--   A **decision problem with multiple beliefs** consists of a decision space, a utility function $U(x_1,x_2,z)$, and a set $\Phi$ of discrete beliefs $f$ on signal–outcome pairs $(y,z)$. For a belief $f$, write $f(z,y)$ for its mass, $f_Y(y)=\sum_z f(z,y)$ for the marginal, and $f_Z(z\mid y)=f(z,y)/f_Y(y)$ for the conditional. The set $\Phi_y=\{f\in\Phi: f_Y(y)\ne0\}$ collects the beliefs for which the conditional is well defined.
--
--   The first- and second-period expected utilities are
--
--   $$
--   V(x,f)=\sum_{y}\sum_{z}U(x_1,x_2(y),z)\,f(z,y),\qquad
--   V_2(x_1,x_2,y,f)=\sum_{z}U(x_1,x_2,z)\,f_Z(z\mid y).
--   $$
--
--   Strategy $x^*$ **belief-dominates** $x$, written $x^*\succ x$, if
--
--   $$
--   V(x^*,f)\ge V(x,f)\quad\forall f\in\Phi,
--   $$
--
--   with the inequality strict for some $f\in\Phi$. The decision-maker is indifferent, $x^*\sim x$, if the values are equal for all $f\in\Phi$, and $x^*\succeq x$ means that one of the two holds. In the second period, after $x_1$ and $y$, the action $x_2^*$ belief-dominates $x_2$, written $x_2^*\succ_{x_1,y}x_2$, if
--
--   $$
--   V_2(x_1,x_2^*,y,f)\ge V_2(x_1,x_2,y,f)\quad\forall f\in\Phi_y,
--   $$
--
--   with the inequality strict for some $f\in\Phi_y$. Second-period indifference and $\succeq_{x_1,y}$ are defined in the same way over $\Phi_y$.
--
--   Belief dominance compares strategies without weighting the beliefs against each other. It is incomplete, and its nondominated strategies are the mission's optimal strategies.
--
--   **Formalization Note** Beliefs are `PMF (Y × Z)` on arbitrary types, and $\Phi$ is an arbitrary set of them, possibly empty. $V$ is one `tsum` over `Y × Z`. `WellPosed` says that this sum is summable for each $f\in\Phi$ and each $x\in X$; without it `tsum` returns $0$. Lean's division returns $0$ where the paper leaves $f_Z(z\mid y)$ undefined, and the relations read $V_2$ only over $\Phi_y$, so the junk value is never used. `le x x'` means $x\preceq x'$, that is, $x'\succeq x$. Dominance and indifference transcribe the paper instead of being defined as parts of `le`.
-- source:
--   Ekholm–Baker, Multiple Beliefs, Dominance and Dynamic Consistency, Management Science, §3, pp.4–5; eqs. (1)–(4), p.5; §3.1, p.5

import Mathlib
import Definitions.Def_BeliefDominance_DecisionSpace

namespace BeliefDominance

/-- The value `m(y, z) = f(z, y)` of a discrete belief `f` on `Y × Z`, as a real number
(Ekholm–Baker, *Multiple Beliefs, Dominance and Dynamic Consistency*, Management Science,
doi:10.1287/mnsc.2020.3908, §3, p.4 (PDF p.5)).

**Formalization Note** Beliefs are `PMF (Y × Z)`: the paper's proof is "for discrete random
variables" (§3.4, p.7). `Y` and `Z` are arbitrary types, with no finiteness or countability
assumption; a `PMF` has countable support. -/
noncomputable def mass {Y Z : Type*} (f : PMF (Y × Z)) (y : Y) (z : Z) : ℝ :=
  (f (y, z)).toReal

/-- The marginal `f_Y(y)` of a belief `f` (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3, p.4 (PDF p.5)). -/
noncomputable def fY {Y Z : Type*} (f : PMF (Y × Z)) (y : Y) : ℝ :=
  ∑' z : Z, mass f y z

/-- The conditional `f_Z(z | y) = f(z, y) / f_Y(y)` (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3, p.4 (PDF p.5)).

**Formalization Note** The paper leaves `f_Z(z | y)` undefined when `f_Y(y) = 0`. Lean's division
returns `0` there; every statement of this mission uses `fZ f z y` only for `f ∈ Φ_y`, where
`f_Y(y) ≠ 0`. -/
noncomputable def fZ {Y Z : Type*} (f : PMF (Y × Z)) (z : Z) (y : Y) : ℝ :=
  mass f y z / fY f y

/-- A two-period decision problem with multiple beliefs (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3, pp.4–5 (PDF pp.5–6)): a decision space, a utility function
`U(x₁, x₂, z)`, and a set `Φ` of beliefs on `Y × Z`.

**Formalization Note** `Φ` is an arbitrary set of `PMF (Y × Z)`: of any cardinality, not assumed
convex, possibly empty. -/
structure Problem (A₁ A₂ Y Z : Type*) where
  /-- The decision space. -/
  space : DecisionSpace A₁ A₂ Y
  /-- The utility function `U(x₁, x₂, z)`. -/
  U : A₁ → A₂ → Z → ℝ
  /-- The set `Φ` of beliefs. -/
  Φ : Set (PMF (Y × Z))

namespace Problem

variable {A₁ A₂ Y Z : Type*} (P : Problem A₁ A₂ Y Z)

/-- The set `Φ_y` of beliefs for which `f_Z(z | y)` is well defined (Ekholm–Baker, Management
Science, doi:10.1287/mnsc.2020.3908, §3, p.5 (PDF p.6)). -/
def Φy (y : Y) : Set (PMF (Y × Z)) :=
  {f | f ∈ P.Φ ∧ fY f y ≠ 0}

/-- The first-period expected utility, eq. (1) (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, p.5 (PDF p.6)):
`V(x, f) = ∫_y ∫_z U(x₁, x₂(y), z) f(z, y) dz dy`.

**Formalization Note** For discrete beliefs the paper's integrals are sums, and the iterated sum is
written as one sum over `Y × Z`. Under `WellPosed` the two are equal. -/
noncomputable def V (x : A₁ × (Y → A₂)) (f : PMF (Y × Z)) : ℝ :=
  ∑' ω : Y × Z, P.U x.1 (x.2 ω.1) ω.2 * mass f ω.1 ω.2

/-- The second-period expected utility, eq. (2) (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, p.5 (PDF p.6)): `V₂(x₁, x₂, y, f) = ∫_z U(x₁, x₂, z) f_Z(z | y) dz`.

**Formalization Note** The paper states eq. (2) for `f ∈ Φ_y`. Every statement of this mission uses
it only there. -/
noncomputable def V₂ (x₁ : A₁) (a : A₂) (y : Y) (f : PMF (Y × Z)) : ℝ :=
  ∑' z : Z, P.U x₁ a z * fZ f z y

/-- The sums (1) exist for every belief of `Φ` and every strategy of `X`.

**Formalization Note** The paper writes `V(x, f)` without comment, which presumes that the
expectations exist. Without this hypothesis Lean's `tsum` returns `0`. Summability in `ℝ` is
absolute. -/
def WellPosed : Prop :=
  ∀ f ∈ P.Φ, ∀ x ∈ P.space.strategies,
    Summable fun ω : Y × Z => P.U x.1 (x.2 ω.1) ω.2 * mass f ω.1 ω.2

/-- First-period belief dominance, eq. (3) (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3.1, p.5 (PDF p.6)): `x'` belief-dominates `x` if
`V(x', f) ≥ V(x, f)` for all `f ∈ Φ`, with the inequality strict for some `f ∈ Φ`. -/
def Dominates (x' x : A₁ × (Y → A₂)) : Prop :=
  (∀ f ∈ P.Φ, P.V x' f ≥ P.V x f) ∧ ∃ f ∈ P.Φ, P.V x' f > P.V x f

/-- First-period indifference `x' ~ x` (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3.1, p.5 (PDF p.6)): the expected utilities are equal for all
`f ∈ Φ`. -/
def Indiff (x' x : A₁ × (Y → A₂)) : Prop :=
  ∀ f ∈ P.Φ, P.V x' f = P.V x f

/-- The first-period relation of belief dominance (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3.1, p.5 (PDF p.6)): `x' ≽ x` "implies that either" `x' ≻ x` or
`x' ~ x` holds.

**Formalization Note** `le x x'` means `x ≼ x'`, that is `x' ≽ x`. -/
def le (x x' : A₁ × (Y → A₂)) : Prop :=
  P.Dominates x' x ∨ P.Indiff x' x

/-- Second-period belief dominance `a' ≻_{x₁,y} a`, eq. (4) (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3.1, p.5 (PDF p.6)): `V₂(x₁, a', y, f) ≥ V₂(x₁, a, y, f)` for all
`f ∈ Φ_y`, with the inequality strict for some `f ∈ Φ_y`. -/
def Dominates₂ (x₁ : A₁) (y : Y) (a' a : A₂) : Prop :=
  (∀ f ∈ P.Φy y, P.V₂ x₁ a' y f ≥ P.V₂ x₁ a y f) ∧ ∃ f ∈ P.Φy y, P.V₂ x₁ a' y f > P.V₂ x₁ a y f

/-- Second-period indifference `a' ~_{x₁,y} a`.

**Formalization Note** The paper uses `~_{x₁,y}` on p.6 (PDF p.7) without defining it. By analogy
with the first period (Ekholm–Baker, Management Science, doi:10.1287/mnsc.2020.3908, §3.1, p.5), it
is equality of `V₂` for all `f ∈ Φ_y`. -/
def Indiff₂ (x₁ : A₁) (y : Y) (a' a : A₂) : Prop :=
  ∀ f ∈ P.Φy y, P.V₂ x₁ a' y f = P.V₂ x₁ a y f

/-- The second-period relation of belief dominance.

**Formalization Note** The paper uses `≼_{x₁,y}` on p.6 (PDF p.7) without defining it for belief
dominance. By analogy with the first period (Ekholm–Baker, Management Science,
doi:10.1287/mnsc.2020.3908, §3.1, p.5), `le₂ x₁ y a a'` (`a ≼_{x₁,y} a'`) means `a' ≻_{x₁,y} a` or
`a' ~_{x₁,y} a`. -/
def le₂ (x₁ : A₁) (y : Y) (a a' : A₂) : Prop :=
  P.Dominates₂ x₁ y a' a ∨ P.Indiff₂ x₁ y a' a

end Problem

end BeliefDominance


