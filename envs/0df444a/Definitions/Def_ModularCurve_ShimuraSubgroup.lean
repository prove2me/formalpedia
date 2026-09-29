-- Prove2me | Definitions.Def_ModularCurve_ShimuraSubgroup
-- name    : ModularCurve_ShimuraSubgroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/c7c3cf60-f956-5482-874b-1f52227c4f19
-- title:
--   μ-type subgroups and Shimura subgroups of JZero
-- statement:
--   Two predicates on additive subgroups of the Jacobian `JZero N`, the degree-zero divisor class group of the base change to $\overline{\mathbb{Q}}$ of the modular function field of level $N$, carrying the Galois action induced coefficientwise on Laurent series. First, `IsMuTypeJZeroSubgroup N S` is a structure with two fields: `galoisStable`, saying that $\sigma \cdot x \in S$ for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every $x \in S$; and `galoisActsCyclotomic`, saying that for every natural number $n$, every $x \in S$ with $n x = 0$, every $\sigma$ and every natural number $k$ such that $\sigma \zeta = \zeta^{k}$ for all $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^{n} = 1$, one has $\sigma \cdot x = k x$. Thus $S$ is Galois-stable and, on each $n$-torsion layer, Galois acts through the mod-$n$ cyclotomic character; the clause is imposed for all $n$, not only prime $n$. (For $n = 0$ the hypothesis on $\sigma$ and $k$ forces $k = 1$ and $\sigma = \mathrm{id}$, so nothing is required there.)
--
--   Second, for a prime $p$, `IsShimuraSubgroup p S` is a structure with three fields: $S$ is of $\mu$-type in the above sense; for every prime $\ell$ and every $x \in S$, $\bar{T}_\ell x = e_N(\ell)\, x$ where $e_N(\ell)$ is the Eisenstein system, equal to $1$ if $\ell \mid p$ and to $1 + \ell$ otherwise; and $\operatorname{card} S = (p-1)/\gcd(p-1,12)$, the Eisenstein numerator. Since that numerator is at least $1$, the cardinality clause forces $S$ to be finite of exactly that order. Two accompanying lemmas record that the trivial subgroup is of $\mu$-type, and that it is a Shimura subgroup whenever the Eisenstein numerator equals $1$, as happens for $p = 13$.
--
--   **Relation to Mathlib.** Mathlib has no notion of the Shimura subgroup or of a subgroup of multiplicative type in a modular Jacobian; both predicates are the project's own, phrased on `JZero` with the Hecke operators `heckeOperatorBar` and the Eisenstein eigenvalue system `eisensteinSystem`.
--
--   **Where it is used.** These predicates axiomatise the properties of the Shimura subgroup $\Sigma \subset J_0(p)$, the kernel of the map $J_0(p) \to J_1(p)$: it is of multiplicative type, the Hecke operators act on it through the Eisenstein eigenvalues, and its order is the numerator of $(p-1)/12$. Statements in the level-lowering part of the argument take an arbitrary subgroup satisfying the predicate rather than a distinguished global object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_ShimuraSubgroup.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section MuType

variable (N : ℕ)

structure IsMuTypeJZeroSubgroup (S : AddSubgroup (JZero N)) : Prop where

  galoisStable : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ x ∈ S, σ • x ∈ S

  galoisActsCyclotomic : ∀ (n : ℕ), ∀ x ∈ S, (n : ℤ) • x = 0 →
    ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (k : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ n = 1 → σ ζ = ζ ^ k) → σ • x = (k : ℤ) • x

theorem isMuTypeJZeroSubgroup_bot : IsMuTypeJZeroSubgroup N ⊥ where
  galoisStable := fun σ x hx => by
    obtain rfl : x = 0 := AddSubgroup.mem_bot.mp hx
    exact AddSubgroup.mem_bot.mpr (@smul_zero _ (JZero N) _ _ σ)
  galoisActsCyclotomic := fun n x hx _ σ k _ => by
    obtain rfl : x = 0 := AddSubgroup.mem_bot.mp hx
    exact (@smul_zero _ (JZero N) _ _ σ).trans (smul_zero (k : ℤ)).symm

end MuType

section Shimura

variable (p : ℕ) [Fact p.Prime]

structure IsShimuraSubgroup (S : AddSubgroup (JZero p)) : Prop where

  isMuType : IsMuTypeJZeroSubgroup p S

  hecke_eq : ∀ ℓ : Nat.Primes, ∀ x ∈ S, heckeOperatorBar p ℓ x = eisensteinSystem p ℓ • x

  card_eq : Nat.card ↥S = eisensteinNumerator p

theorem isShimuraSubgroup_bot_of_eisensteinNumerator_eq_one
    (hp : eisensteinNumerator p = 1) : IsShimuraSubgroup p ⊥ where
  isMuType := isMuTypeJZeroSubgroup_bot p
  hecke_eq := fun ℓ x hx => by
    rw [AddSubgroup.mem_bot] at hx
    rw [hx, map_zero, smul_zero]
  card_eq := by rw [hp, AddSubgroup.card_bot]

example : @IsShimuraSubgroup 13 ⟨by decide⟩ ⊥ :=
  @isShimuraSubgroup_bot_of_eisensteinNumerator_eq_one 13 ⟨by decide⟩ (by decide)

end Shimura

end ModularCurve


