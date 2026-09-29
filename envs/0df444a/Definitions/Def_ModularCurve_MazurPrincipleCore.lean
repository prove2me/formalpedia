-- Prove2me | Definitions.Def_ModularCurve_MazurPrincipleCore
-- name    : ModularCurve_MazurPrincipleCore
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/1c22503f-7dd8-59e0-b6c5-39251bf6f09a
-- title:
--   Vocabulary for Mazur's principle: Eisenstein ideals, abelian-part data
-- statement:
--   Three predicates over the project's abstract Hecke algebra `HeckeAlg` (defined in the imported module; the use of `MvPolynomial.C : ℤ →+* HeckeAlg` shows it to be a multivariate polynomial ring over $\mathbb{Z}$, with `heckeGen ℓ` the generator standing for $T_\ell$).
--
--   `IsEventuallyEisenstein 𝔪`, for an arbitrary ideal $\mathfrak m$ (maximality is not required), says that there is a finite set $S$ of primes with $T_\ell - (\ell + 1) \in \mathfrak m$ for every prime $\ell \notin S$: the Eisenstein congruence at all but finitely many primes.
--
--   `IsAbelianPartData S I 𝒯 δ` is a `Prop`-valued structure, i.e. a package of three hypotheses, in the following abstract setting: a group $G$ acting on an additive group $J$ which is a `HeckeAlg`-module, the two actions commuting; a second `HeckeAlg`-module $J_0$; a finite set $S$ of primes; a subgroup $I \le G$; a `HeckeAlg`-submodule $\mathcal T \le J$; and two merely additive maps $\delta_0, \delta_1 : J \to J_0$. The fields assert: (i) both $\delta_i$ vanish on $\mathcal T$; (ii) for $\ell \notin S$, $\delta_i$ commutes with the action of `heckeGen ℓ`; (iii) for every maximal ideal $\mathfrak m$ that is not eventually Eisenstein, any $x$ in the $\mathfrak m$-torsion of $J$ that is fixed by all of $I$ and killed by both $\delta_i$ lies in $\mathcal T$. In the intended geometry $\delta_0,\delta_1$ are the degeneracy pushforwards $J_0(N_0q) \to J_0(N_0)$, $I$ is inertia at $q$ and $\mathcal T$ the toric part; clause (iii) is an abstract assumption imposed uniformly over all non-Eisenstein maximal ideals, hence stronger than the geometric input it models, and its inhabitability must be checked in any application.
--
--   `HasLowerLevelTorsion S 𝔪 J₀` asserts the existence of a nonzero $y \in J_0$ annihilated by each natural number lying in $\mathfrak m$ and by each element $T_\ell - b$ ($\ell \notin S$ a prime, $b \in \mathbb{Z}$) lying in $\mathfrak m$; this is a generator-by-generator weakening of "$J_0[\mathfrak m] \neq 0$", not full annihilation by $\mathfrak m$.
--
--   The remaining declarations are routine: the case split giving $x \in \mathcal T$ or $\delta_i x \neq 0$ for some $i$; transport of the relation $(T_\ell - b)x = 0$ along $\delta_i$ for $\ell \notin S$; and transport of $(n)x = 0$ along an arbitrary additive map, both using automatic compatibility of additive maps with integer and natural scalars.
--
--   **Relation to Mathlib.** Mathlib has no Hecke algebras, modular Jacobians, degeneracy maps or Eisenstein ideals; all three predicates are the project's own, phrased with Mathlib's `Submodule`, `Ideal.IsMaximal`, `AddMonoidHom`, `Nat.Primes` and `MvPolynomial` API.
--
--   **Where it is used.** This is the vocabulary in which Mazur's principle is stated in the project: the non-toric branch of the case analysis is formulated using `IsAbelianPartData`, the Eisenstein exclusion using `IsEventuallyEisenstein`, and the conclusion — existence of a nonzero torsion class at the lower level — using `HasLowerLevelTorsion`. Mazur's principle is the step of the Ribet route that removes the prime $q$ from the level of the modular form attached to the Frey representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_MazurPrincipleCore.lean

import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPolynomial

namespace ModularCurve

def IsEventuallyEisenstein (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ S : Finset Nat.Primes, ∀ ℓ : Nat.Primes, ℓ ∉ S →
    heckeGen ℓ - (((ℓ : ℕ) : HeckeAlg) + 1) ∈ 𝔪

section AbelianPart

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]
  [SMulCommClass G HeckeAlg J]
  {J₀ : Type*} [AddCommGroup J₀] [Module HeckeAlg J₀]

structure IsAbelianPartData (S : Finset Nat.Primes) (I : Subgroup G)
    (𝒯 : Submodule HeckeAlg J) (δ : Fin 2 → J →+ J₀) : Prop where

  toric_le_ker : ∀ i : Fin 2, ∀ x ∈ 𝒯, δ i x = 0

  goodPrime_equivariant : ∀ i : Fin 2, ∀ ℓ : Nat.Primes, ℓ ∉ S →
    ∀ x : J, δ i (heckeGen ℓ • x) = heckeGen ℓ • δ i x

  component_eisenstein : ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal → ¬ IsEventuallyEisenstein 𝔪 →
    ∀ x ∈ heckeTorsion J 𝔪, (∀ σ ∈ I, σ • x = x) → (∀ i : Fin 2, δ i x = 0) → x ∈ 𝒯

namespace IsAbelianPartData

variable {S : Finset Nat.Primes} {I : Subgroup G} {𝒯 : Submodule HeckeAlg J}
  {δ : Fin 2 → J →+ J₀}

theorem mem_toric_or_exists_ne_zero (h : IsAbelianPartData S I 𝒯 δ)
    {𝔪 : Ideal HeckeAlg} (hmax : 𝔪.IsMaximal) (heis : ¬ IsEventuallyEisenstein 𝔪)
    {x : J} (hx : x ∈ heckeTorsion J 𝔪) (hinv : ∀ σ ∈ I, σ • x = x) :
    x ∈ 𝒯 ∨ ∃ i : Fin 2, δ i x ≠ 0 := by
  by_cases hker : ∀ i : Fin 2, δ i x = 0
  · exact Or.inl (h.component_eisenstein 𝔪 hmax heis x hx hinv hker)
  · exact Or.inr (not_forall.mp hker)

theorem heckeGen_sub_smul_image_eq_zero (h : IsAbelianPartData S I 𝒯 δ) (i : Fin 2)
    {ℓ : Nat.Primes} (hℓ : ℓ ∉ S) (b : ℤ) {x : J}
    (hx : (heckeGen ℓ - C b) • x = 0) :
    (heckeGen ℓ - C b) • δ i x = 0 := by
  rw [sub_smul] at hx ⊢
  rw [eq_intCast (MvPolynomial.C : ℤ →+* HeckeAlg) b] at hx ⊢
  rw [← h.goodPrime_equivariant i ℓ hℓ x,
    ← map_intCast_smul (δ i) HeckeAlg HeckeAlg b x, ← map_sub, hx, map_zero]

end IsAbelianPartData

theorem natCast_smul_addMonoidHom_eq_zero (f : J →+ J₀) (n : ℕ)
    {x : J} (hx : (n : HeckeAlg) • x = 0) : (n : HeckeAlg) • f x = 0 := by
  rw [← map_natCast_smul f HeckeAlg HeckeAlg n x, hx, map_zero]

end AbelianPart

def HasLowerLevelTorsion (S : Finset Nat.Primes) (𝔪 : Ideal HeckeAlg) (J₀ : Type*)
    [AddCommGroup J₀] [Module HeckeAlg J₀] : Prop :=
  ∃ y : J₀, y ≠ 0 ∧
    (∀ n : ℕ, (n : HeckeAlg) ∈ 𝔪 → (n : HeckeAlg) • y = 0) ∧
    ∀ ℓ : Nat.Primes, ℓ ∉ S → ∀ b : ℤ, heckeGen ℓ - C b ∈ 𝔪 →
      (heckeGen ℓ - C b) • y = 0

end ModularCurve


