-- Prove2me | Definitions.Def_SubmodMFG_Assumption23
-- name    : SubmodMFG_Assumption23
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:15:26.498236+00:00
-- url     : https://prove2.me/theorems/f4d37a41-ed24-4f44-8ac3-a692f068da2d
-- title:
--   Assumption 2.3 — submodularity conditions
-- statement:
--   **Assumption 2.3 (Submodularity Conditions).** There exist operations $\wedge^E,\vee^E:E\times E\to E$ such that:
--
--   1. the projection $p$ behaves like a homomorphism of lattices: for all $\nu,\bar\nu\in E$,
--   $$
--   p(\nu\wedge^E\bar\nu)\le^L p\nu\wedge^L p\bar\nu\le^L p\nu\vee^L p\bar\nu\le^L p(\nu\vee^E\bar\nu);
--   $$
--   2. the cost functional satisfies, for all $\nu,\bar\nu\in E$ and $\mu,\bar\mu\in L$ with $\mu\le^L\bar\mu$,
--   $$
--   J(\nu\vee^E\bar\nu,\bar\mu)-J(\bar\nu,\bar\mu)\le J(\nu\vee^E\bar\nu,\mu)-J(\bar\nu,\mu)\le J(\nu,\mu)-J(\nu\wedge^E\bar\nu,\mu).
--   $$
--
--   These conditions make the best-response sets directed and their extremal points monotone in $\mu$ (Lemma 2.4), which is the basis of the lattice-theoretic existence argument.
--
--   **Formalization Note** The two operations are existentially quantified; no order or lattice structure on $E$ is assumed (the paper notes that $(E,\wedge^E,\vee^E)$ need not be a lattice). The middle inequality of (1) holds in every lattice and is kept as printed. The paper's wording "homeomorphism of lattices" is rendered "homomorphism" here; the formula is the definition.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.2, Assumption 2.3, p.6

import Mathlib

namespace SubmodMFG

/-- **Assumption 2.3** (Submodularity Conditions).
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.2, Assumption 2.3, p.6: "There exist operations ∧^E, ∨^E : E × E → E
such that:
(1) The projection p behaves like a homeomorphism of lattices; that is,
p(ν ∧^E ν̄) ≤^L pν ∧^L pν̄ ≤^L pν ∨^L pν̄ ≤^L p(ν ∨^E ν̄), for each ν, ν̄ ∈ E.
(2) The cost functional satisfies the following submodularity properties
J(ν ∨^E ν̄, µ̄) − J(ν̄, µ̄) ≤ J(ν ∨^E ν̄, µ) − J(ν̄, µ) ≤ J(ν, µ) − J(ν ∧^E ν̄, µ),
for each ν, ν̄ ∈ E and µ, µ̄ ∈ L with µ ≤^L µ̄."

**Formalization Note.** The operations `meet = ∧^E` and `join = ∨^E` are existentially
quantified binary operations on `E`; no order or lattice structure on `E` is assumed (the paper,
p.6, stresses that `(E, ∧^E, ∨^E)` need not be a lattice). `J` is curried
(`J ν µ = J(ν, µ)`). The middle inequality `pν ∧ pν̄ ≤ pν ∨ pν̄` of (1) holds in every lattice and
is kept verbatim. -/
def Assumption23 {E L : Type*} [Lattice L] (p : E → L) (J : E → L → ℝ) : Prop :=
  ∃ meet join : E → E → E,
    (∀ ν ν' : E, p (meet ν ν') ≤ p ν ⊓ p ν' ∧ p ν ⊓ p ν' ≤ p ν ⊔ p ν' ∧
      p ν ⊔ p ν' ≤ p (join ν ν')) ∧
    (∀ (ν ν' : E) (μ μ' : L), μ ≤ μ' →
      J (join ν ν') μ' - J ν' μ' ≤ J (join ν ν') μ - J ν' μ ∧
      J (join ν ν') μ - J ν' μ ≤ J ν μ - J (meet ν ν') μ)

end SubmodMFG


