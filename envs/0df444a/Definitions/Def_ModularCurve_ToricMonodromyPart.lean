-- Prove2me | Definitions.Def_ModularCurve_ToricMonodromyPart
-- name    : ModularCurve_ToricMonodromyPart
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/bfd86e66-2b36-5026-bead-8fac3c01fc55
-- title:
--   Monodromy toric part of a Hecke module
-- statement:
--   The setting is a group $G$ acting on an additive abelian group $J$ by a distributive multiplicative action, where $J$ also carries a module structure over `HeckeAlg` $=\mathbb{Z}[X_\ell : \ell \text{ prime}]$, the polynomial ring over $\mathbb{Z}$ on one indeterminate `heckeGen` $\ell$ for each rational prime (the formal Hecke algebra of the project). For a natural number $q$ and a subgroup $I \le G$, [`ModularCurve.toricMonodromyPart q I`](../def/ModularCurve_ToricMonodromyPart.html#L13) is defined to be the `HeckeAlg`-submodule of $J$ spanned by the set of all elements of the form $\sigma \cdot x - x$, where $\sigma$ ranges over $I$ and $x$ ranges over those elements of $J$ annihilated by some natural number $m$ with $m > 0$ and $\gcd(m,q) = 1$; that is, over the prime-to-$q$ torsion of $J$ in the strong sense that a single such $m$ kills $x$. Being a span over `HeckeAlg`, the result is by construction stable under the Hecke operators, while no claim about $G$-stability is built into the definition.
--
--   The accompanying lemma [`ModularCurve.smul_sub_self_mem_toricMonodromyPart`](../def/ModularCurve_ToricMonodromyPart.html#L17) records the generating property: for $\sigma \in I$ and $x \in J$ with $m \cdot x = 0$ for some $m > 0$ coprime to $q$, the difference $\sigma \cdot x - x$ lies in `toricMonodromyPart q I`.
--
--   **Relation to Mathlib.** Mathlib supplies the Hecke-module span (`Submodule.span`) but has no notion of the toric part of a semistable Jacobian; the submodule defined here is the project's own.
--
--   **Where it is used.** This submodule is an explicit, Néron-model-free substitute for the toric part of a Jacobian with semistable reduction at $q$: one takes $G$ to be an absolute Galois group and $I$ the inertia subgroup at a place above $q$, so that the generators $\sigma \cdot x - x$ on prime-to-$q$ torsion are exactly the image of the unipotent monodromy. It is used to make the toric alternative in Ribet's dichotomy at the level-lowering prime concrete, providing a Hecke-stable submodule on which the Frobenius and $T_q$ relations can be imposed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ToricMonodromyPart.lean

import Mathlib
import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]

def toricMonodromyPart (q : ℕ) (I : Subgroup G) : Submodule HeckeAlg J :=
  Submodule.span HeckeAlg
    {y : J | ∃ σ ∈ I, ∃ x : J, (∃ m : ℕ, 0 < m ∧ m.Coprime q ∧ m • x = 0) ∧ y = σ • x - x}

theorem smul_sub_self_mem_toricMonodromyPart {q : ℕ} {I : Subgroup G} {σ : G} (hσ : σ ∈ I) {x : J}
    {m : ℕ} (hm : 0 < m) (hmq : m.Coprime q) (hx : m • x = 0) :
    σ • x - x ∈ toricMonodromyPart (J := J) q I :=
  Submodule.subset_span ⟨σ, hσ, x, ⟨m, hm, hmq, hx⟩, rfl⟩

end ModularCurve

end


