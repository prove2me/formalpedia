-- Prove2me | Definitions.Def_ProcNetStab_IsWeakOrder
-- name    : ProcNetStab_IsWeakOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:06.46703+00:00
-- url     : https://prove2.me/theorems/1f38375c-ef9f-4c49-ab33-64ab097327a2
-- title:
--   Preference relation (weak order) and its strict part
-- statement:
--   A **preference relation** on a set $X$ is a binary relation $\succeq$ on $X$ that is complete and transitive (a weak order):
--   $$
--   \forall x, y:\ x \succeq y \ \text{or}\ y \succeq x, \qquad \forall x, y, z:\ x \succeq y \ \text{and}\ y \succeq z \implies x \succeq z .
--   $$
--   Its **strict part** $\succ$ is defined by $x \succ y$ iff $x \succeq y$ and not $y \succeq x$; $x \prec y$ means $y \succ x$.
--
--   Agents' preferences over networks are weak orders on the set of all networks on $V$.
--
--   **Formalization Note** A relation on $X$ is `X → X → Prop`, with `R x y` read as $x \succeq y$.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), §3.2, p.7; p.OA-1

import Mathlib

namespace ProcNetStab

/-- A **preference relation** (weak order) (Chiong, Qi, *Stability of Procurement Networks*
(authors' manuscript, 2025), §3.2, p.7, and p.OA-1): a binary relation that is complete and
transitive.

**Formalization Note** A binary relation on `X` is `R : X → X → Prop`, with `R x y` read as
`x ⪰ y`. Completeness is `∀ x y, R x y ∨ R y x` (so `R` is reflexive). -/
def IsWeakOrder {X : Type*} (R : X → X → Prop) : Prop :=
  (∀ x y, R x y ∨ R y x) ∧ ∀ x y z, R x y → R y z → R x z

/-- The **strict part** `≻` of a binary relation `⪰` (Chiong, Qi, *Stability of Procurement
Networks* (authors' manuscript, 2025), §3.2, p.7): `x ≻ y` iff `x ⪰ y` and not `y ⪰ x`.
The relation `x ≺ y` of Definition 3.9 is `strictPart R y x`. -/
def strictPart {X : Type*} (R : X → X → Prop) (x y : X) : Prop :=
  R x y ∧ ¬ R y x

end ProcNetStab


