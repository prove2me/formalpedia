-- Prove2me | Definitions.Def_Algebra_PatchingDatum
-- name    : Algebra_PatchingDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/bb1d710d-21de-5c44-921f-df8df1c68a64
-- title:
--   Taylor–Wiles patching data over a power-series ring
-- statement:
--   Fix a commutative ring $\mathcal O$, an $r \in \mathbb N$, a commutative $\mathcal O$-algebra $R$ and an $R$-module $M$, and write $A := \mathcal O[[X_1,\dots,X_r]]$ for `MvPowerSeries (Fin r) 𝒪`. For an ideal $J \subseteq A$, a term of [`Algebra.PatchingLevel 𝒪 r R M J`](../def/Algebra_PatchingDatum.html#L5) — one level of patching data with relation ideal $J$ — consists of: a carrier type $N$ with an additive group structure and an $A$-module structure (the only module structure registered; there is a single power-series ring here, occurring as source and target of $\varphi$, as the scalars on $N$ and as the source of $\psi$); an $\mathcal O$-algebra endomorphism $\varphi \colon A \to A$; a surjective $\mathcal O$-algebra map $\psi \colon A \to R$ with $\psi(\varphi(X_i)) = 0$ for every $i$; a surjective additive map $\pi \colon N \to M$ that is semilinear along $\psi$, i.e. $\pi(f \cdot x) = \psi(f)\cdot \pi(x)$, and whose kernel is exactly the submodule $\big(\varphi(X_1),\dots,\varphi(X_r)\big)\cdot N$ (stated as an iff, membership in the span of the range of $i \mapsto \varphi(X_i)$ acting on $\top$); and a natural number $d$ together with a family $b \colon \mathrm{Fin}\,d \to N$ such that the map $c \mapsto \sum_i \varphi(c_i)\cdot b_i$ from $A^d$ to $N$ is surjective and $\sum_i \varphi(c_i) \cdot b_i = 0$ holds precisely when every $c_i$ lies in $J$. These last two fields are the explicit-coordinate form of the usual freeness requirement; no $A/J$-module structure on $N$, and no quotient module, is constructed anywhere.
--
--   A term of [`Algebra.PatchingDatum 𝒪 ℓ r R M`](../def/Algebra_PatchingDatum.html#L39) has a single field: for every $n \in \mathbb N$, a `PatchingLevel` whose relation ideal is $J_n := \big((1+X_j)^{\ell^n} - 1 : j \in \mathrm{Fin}\,r\big)$. Nothing is required to be shared or compatible across the levels: the module $N$, the maps $\varphi$, $\psi$, $\pi$ and the rank $d$ may all depend on $n$, and no transition maps between levels are part of the data. Likewise $\mathcal O$ is an arbitrary commutative ring, $\ell$ and $r$ arbitrary naturals with no primality or completeness or locality hypothesis, and no topology is used; all carriers live in `Type`.
--
--   **Relation to Mathlib.** Mathlib has no notion of a Taylor–Wiles system or of patching data; these are the project's own structures, formulated with Mathlib's `MvPowerSeries`, `Ideal.span` and `Submodule` smul-of-ideal API.
--
--   **Where it is used.** This is the purely commutative-algebraic input of the Taylor–Wiles patching argument in Diamond's module-theoretic formulation: no Galois representation, modular form or Hecke algebra appears, and $r$ is the only trace of the arithmetic. Separate modules consume these structures — a datum produces a level with relation ideal $\bot$, and a level at $\bot$ with $M$ nontrivial yields freeness of $M$ over $R$ and a presentation of $R$ as $\mathcal O[[X_1,\dots,X_r]]$ modulo $r$ relations — while the arithmetic side of Wiles's proof supplies an inhabitant built from deformation rings and Hecke modules at auxiliary levels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Algebra_PatchingDatum.lean

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

structure Algebra.PatchingLevel (𝒪 : Type) [CommRing 𝒪] (r : ℕ) (R : Type) [CommRing R]
    [Algebra 𝒪 R] (M : Type) [AddCommGroup M] [Module R M]
    (J : Ideal (MvPowerSeries (Fin r) 𝒪)) : Type 1 where

  N : Type
  [instAddCommGroup : AddCommGroup N]
  [instModule : Module (MvPowerSeries (Fin r) 𝒪) N]

  φ : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] MvPowerSeries (Fin r) 𝒪

  ψ : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] R
  ψ_surjective : Function.Surjective ψ

  ψ_φ_X : ∀ i : Fin r, ψ (φ (MvPowerSeries.X i)) = 0

  π : N →+ M

  π_smul : ∀ (f : MvPowerSeries (Fin r) 𝒪) (x : N), π (f • x) = ψ f • π x
  π_surjective : Function.Surjective π

  ker_π : ∀ x : N, π x = 0 ↔
    x ∈ (Ideal.span (Set.range fun i : Fin r => φ (MvPowerSeries.X i))) •
      (⊤ : Submodule (MvPowerSeries (Fin r) 𝒪) N)

  d : ℕ

  b : Fin d → N

  b_span : ∀ x : N, ∃ c : Fin d → MvPowerSeries (Fin r) 𝒪, x = ∑ i, φ (c i) • b i

  b_rel : ∀ c : Fin d → MvPowerSeries (Fin r) 𝒪, ∑ i, φ (c i) • b i = 0 ↔ ∀ i, c i ∈ J

attribute [instance] Algebra.PatchingLevel.instAddCommGroup Algebra.PatchingLevel.instModule

structure Algebra.PatchingDatum (𝒪 : Type) [CommRing 𝒪] (ℓ r : ℕ) (R : Type) [CommRing R]
    [Algebra 𝒪 R] (M : Type) [AddCommGroup M] [Module R M] : Type 1 where

  level : ∀ n : ℕ, Algebra.PatchingLevel 𝒪 r R M
    (Ideal.span (Set.range fun j : Fin r =>
      ((1 + MvPowerSeries.X j) ^ (ℓ ^ n) - 1 : MvPowerSeries (Fin r) 𝒪)))


