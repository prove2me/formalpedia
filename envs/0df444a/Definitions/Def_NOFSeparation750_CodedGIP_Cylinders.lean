-- Prove2me | Definitions.Def_NOFSeparation750_CodedGIP_Cylinders
-- name    : NOFSeparation750_CodedGIP_Cylinders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:42:29.356696+00:00
-- url     : https://prove2.me/theorems/3a535d19-503e-456a-9eeb-f2886b01f661
-- title:
--   NOF cylinders, counting probabilities, and generalized inner product
-- statement:
--   An $i$-cylinder is a set whose membership is unchanged by changing block $i$ alone. A cylinder intersection is an intersection of one such cylinder for each player. An accepting cover of a Boolean function $F$ with budget $d$ consists of at most $2^d$ cylinder intersections, each contained in $F^{-1}(1)$, whose union equals $F^{-1}(1)$.
--
--   For a finite nonempty ambient space $\Omega$, uniform and conditional probabilities are exact cardinality ratios:
--   $$\Pr(A)=\frac{|A|}{|\Omega|},\qquad \Pr(A\mid E)=\frac{|A\cap E|}{|E|}.$$
--   The latter is used only for nonempty conditioning events. These ratios totalize to zero on empty denominators; all probability applications in this mission have positive denominators.
--
--   For field vectors $y^{(1)},\ldots,y^{(k)}\in\mathbb F_q^w$, the field-valued generalized inner product is
--   $$\operatorname{GIP}_{q,w}^{k}(y)=\sum_{t=1}^{w}\prod_{i=1}^{k}y^{(i)}(t).$$
--   The cover predicate is separate from the operational protocol definitions, so the cover theorem remains substantive.
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), §2, pp.5–6; Fact 5.2, p.8; §5.1, pp.8–9; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Protocols

namespace NOFSeparation750.CodedGIP

/-- Invariance under changes of the hidden block (§2, p.6). -/
def IsCylinder {k : ℕ} {X : Fin k → Type} (i : Fin k) (A : Set (Input X)) : Prop :=
  ∀ x y, (∀ j, j ≠ i → x j = y j) → (x ∈ A ↔ y ∈ A)

def IsCylinderIntersection {k : ℕ} {X : Fin k → Type} (A : Set (Input X)) : Prop :=
  ∃ C : Fin k → Set (Input X), (∀ i, IsCylinder i (C i)) ∧ A = ⋂ i, C i

/-- Exact counting probability on a finite space. On the empty space its totalized
value is zero; all applications below have nonempty ambient spaces. -/
noncomputable def uniformMass {α : Type} (A : Set α) : ℝ :=
  (Nat.card {x // x ∈ A} : ℝ) / (Nat.card α : ℝ)

/-- Conditional counting probability. The conditioning fibers used below contain
all choices of factor codewords and hence have positive cardinality. -/
noncomputable def conditionalMass {α : Type} (A E : Set α) : ℝ :=
  (Nat.card {x // x ∈ A ∩ E} : ℝ) / (Nat.card {x // x ∈ E} : ℝ)

def AcceptingCover {k : ℕ} {X : Fin k → Type} (F : Input X → Bool) (d : ℕ) : Prop :=
  ∃ t : ℕ, t ≤ 2 ^ d ∧ ∃ A : Fin t → Set (Input X),
    (∀ a, IsCylinderIntersection (A a) ∧ A a ⊆ {x | F x = true}) ∧
    {x | F x = true} = ⋃ a, A a

/-- Field-valued generalized inner product, with no Boolean trace applied. -/
def gip {F : Type} [CommSemiring F] {k w : ℕ} (x : Fin k → Fin w → F) : F :=
  ∑ t, ∏ i, x i t

end NOFSeparation750.CodedGIP


