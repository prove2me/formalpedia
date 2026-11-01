-- Prove2me | Definitions.Def_ProcNetStab_IsAcyclic
-- name    : ProcNetStab_IsAcyclic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:45.36513+00:00
-- url     : https://prove2.me/theorems/a4031246-a549-4c8d-8ef5-9e78f4c4c6eb
-- title:
--   Acyclic order pair and order pair extension
-- statement:
--   Let $R, P$ be binary relations on a set $X$. The pair $\langle R, P\rangle$ is **acyclic** if there is no sequence $x_1, x_2, \dots, x_L$ ($L \ge 1$) with
--   $$
--   x_1 \mathrel R x_2 \mathrel R \cdots \mathrel R x_L \qquad\text{and}\qquad x_L \mathrel P x_1 .
--   $$
--   A weak order $\succeq$ with strict part $\succ$ gives an **order pair extension** $\langle \succeq, \succ\rangle$ of $\langle R, P\rangle$ if $R \subseteq {\succeq}$ and $P \subseteq {\succ}$.
--
--   An order pair is a pair with $P \subseteq R$; acyclicity is what remains of rationality when preferences are only partially observed.
--
--   **Formalization Note** A chain $x_1 \mathrel R \cdots \mathrel R x_L$ is the reflexive–transitive closure `Relation.ReflTransGen R x₁ x_L`; the case $L = 1$ forbids $x \mathrel P x$. The order-pair condition $P \subseteq R$ is not built into the definition; it is a hypothesis where the paper assumes it.
-- source:
--   Chiong, Qi, Stability of Procurement Networks (authors' manuscript, 2025), Definitions A.6–A.7, pp.OA-3–OA-4; order pair, p.OA-2

import Mathlib
import Definitions.Def_ProcNetStab_IsWeakOrder

namespace ProcNetStab

/-- An **acyclic** order pair (Chiong, Qi, *Stability of Procurement Networks* (authors'
manuscript, 2025), Definition A.7, p.OA-4): `⟨R, P⟩` is acyclic if there is no sequence
`x₁, x₂, …, x_L` (`L ≥ 1`) with `x₁ R x₂ R … R x_L` and `x_L P x₁`.

**Formalization Note** A chain `x₁ R … R x_L` is `Relation.ReflTransGen R x₁ x_L`; the case
`L = 1` forbids `x P x`. The order-pair condition `P ⊆ R` (p.OA-2) is not part of this
definition; it is a hypothesis where the paper assumes it. -/
def IsAcyclic {X : Type*} (R P : X → X → Prop) : Prop :=
  ∀ x y, Relation.ReflTransGen R x y → ¬ P y x

/-- A weak order `W` gives an **order pair extension** `⟨W, ≻_W⟩` of `⟨R, P⟩` (Chiong, Qi,
*Stability of Procurement Networks* (authors' manuscript, 2025), Definition A.6, p.OA-3):
`R ⊆ W` and `P ⊆ ≻_W`, where `≻_W` is the strict part of `W`. -/
def IsOrderPairExtension {X : Type*} (W R P : X → X → Prop) : Prop :=
  (∀ x y, R x y → W x y) ∧ ∀ x y, P x y → strictPart W x y

end ProcNetStab


