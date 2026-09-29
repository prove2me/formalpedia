-- Prove2me | Definitions.Def_ModularCurve_DeligneRapoport
-- name    : ModularCurve_DeligneRapoport
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/dd51ecd8-4c5e-5d35-adda-f6fdb0066d2e
-- title:
--   Abstract inertia-filtration predicates for a toric submodule
-- statement:
--   Fix a group $G$, a commutative ring $R$, and an $R$-module $J$ carrying a distributive multiplicative $G$-action; all five declarations are predicates on a chosen $R$-submodule $\mathcal{T} \subseteq J$ (and, in two cases, on a subgroup $I \le G$ or on a distinguished element of $G$). `ToricStable G 𝒯` says that $g \cdot x \in \mathcal{T}$ for every $g \in G$ and every $x \in \mathcal{T}$, i.e. $\mathcal{T}$ is a $G$-stable submodule. `ToricInertiaFixed I 𝒯` says that every $\sigma \in I$ acts as the identity on $\mathcal{T}$: $\sigma \cdot x = x$ for all $x \in \mathcal{T}$. `InertiaUnipotentTowards I 𝒯` says that $(\sigma - 1)J \subseteq \mathcal{T}$, spelled out as $\sigma \cdot x - x \in \mathcal{T}$ for all $\sigma \in I$ and all $x \in J$ (note the quantifier is over all of $J$, not only over $\mathcal{T}$). `IsInertiaFiltration I 𝒯` is the conjunction of four clauses: $\mathcal{T} \neq \top$ (properness: $\mathcal{T}$ is not all of $J$), `ToricStable G 𝒯`, `ToricInertiaFixed I 𝒯` and `InertiaUnipotentTowards I 𝒯`. Together the last two clauses say exactly that $I$ acts unipotently of level two through $\mathcal{T}$, i.e. $(\sigma-1)(\tau-1) = 0$ on $J$ for $\sigma, \tau \in I$. Finally, `ToricFrobeniusSq q φ 𝒯`, for $q : \mathbb{N}$ and $\varphi \in G$, asserts that $\varphi$ acts on $\mathcal{T}$ with square the scalar $q^2$: $\varphi \cdot (\varphi \cdot x) = (q^2 : \mathbb{Z}) \cdot x$ for all $x \in \mathcal{T}$; it does not assert that $\varphi$ itself acts by $\pm q$. No geometry is present here: nothing ties $J$ to a Jacobian, $G$ to a decomposition group, or $\mathcal{T}$ to a toric part; the names record the intended instantiation only, and these predicates are hypotheses to be supplied by the consumer.
--
--   **Relation to Mathlib.** Mathlib has no notion of a semistable inertia filtration or toric part; these are the project's own predicates, built from Mathlib's `Submodule`, `Subgroup` and `DistribMulAction`.
--
--   **Where it is used.** The intended instantiation has $J$ the $p$-torsion of the Jacobian of a modular curve of level divisible by a prime $q$, $G$ the decomposition group at $q$, $I$ its inertia subgroup, $\mathcal{T}$ the toric part of the special fibre and $\varphi$ a Frobenius lift; the predicates then package the semistable-reduction input to Mazur's principle used for level lowering in the Frey–Serre–Ribet step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DeligneRapoport.lean

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section FiltrationPredicates

variable {G : Type*} [Group G] {R : Type*} [CommRing R]
  {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]

def ToricStable (G : Type*) [Group G] [DistribMulAction G J] (𝒯 : Submodule R J) : Prop :=
  ∀ g : G, ∀ x ∈ 𝒯, g • x ∈ 𝒯

def ToricInertiaFixed (I : Subgroup G) (𝒯 : Submodule R J) : Prop :=
  ∀ σ ∈ I, ∀ x ∈ 𝒯, σ • x = x

def InertiaUnipotentTowards (I : Subgroup G) (𝒯 : Submodule R J) : Prop :=
  ∀ σ ∈ I, ∀ x : J, σ • x - x ∈ 𝒯

def IsInertiaFiltration (I : Subgroup G) (𝒯 : Submodule R J) : Prop :=
  𝒯 ≠ ⊤ ∧ ToricStable G 𝒯 ∧ ToricInertiaFixed I 𝒯 ∧ InertiaUnipotentTowards I 𝒯

end FiltrationPredicates

section ToricFrobenius

variable {G : Type*} [Group G] {R : Type*} [CommRing R]
  {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]

def ToricFrobeniusSq (q : ℕ) (φ : G) (𝒯 : Submodule R J) : Prop :=
  ∀ x ∈ 𝒯, φ • φ • x = ((q : ℤ) ^ 2) • x

end ToricFrobenius

end ModularCurve

end


