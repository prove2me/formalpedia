-- Prove2me | Definitions.Def_ExtCitation_AdmissibleExtension
-- name    : ExtCitation_AdmissibleExtension
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/27597bc5-2ae9-57e5-bd51-4836467989ff
-- title:
--   Admissible mod-p extensions of μp​ by Z/p over Q
-- statement:
--   Fix a prime $p$ and work with $G=\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ realised as the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. Two helper results record that an algebraically closed field of characteristic zero has exactly $n$ $n$-th roots of unity, and specialise this to the statement that the group of $p$-th roots of unity of $\overline{\mathbb{Q}}$ has exactly $p$ elements; this equality is precisely the datum Mathlib's `modularCyclotomicCharacter` requires, and [`ExtCitation.cycloExp p σ`](../def/ExtCitation_AdmissibleExtension.html#L24) is the value of that character at $\sigma$, taken as the representative in $\{0,\dots,p-1\}$ of the corresponding element of $(\mathbb{Z}/p)^\times$.
--
--   The data are a $\mathbb{Z}/p$-module $V$ with a distributive $G$-action commuting with the scalars, and a $\mathbb{Z}/p$-submodule $C\subseteq V$. The Prop-valued structure [`ExtCitation.IsAdmissibleExtension`](../def/ExtCitation_AdmissibleExtension.html#L33) bundles: $C$ is $G$-stable and $G$ acts trivially on $C$ (so $C$ is the constant module $\mathbb{Z}/p$); for all $\sigma$ and all $x\in V$, $\sigma\cdot x-\mathrm{cycloExp}\,p\,\sigma\cdot x\in C$ (so $V/C$ carries the mod-$p$ cyclotomic character, i.e. is $\mu_p$); $C$ has exactly $p$ elements and $V$ exactly $p^2$; unramifiedness outside $p$, in the form that for every prime $\ell\neq p$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ in which $\ell$ is a non-unit, the image in $G$ of the inertia subgroup of $A$ over $\mathbb{Q}$ acts trivially on all of $V$; and local splitting at $p$, namely for every valuation subring $A$ in which $p$ is a non-unit there is a complement $C'$ of $C$ stable under the decomposition subgroup of $A$.
--
--   `SplitsGlobally C` asks for a complement of $C$ stable under all of $G$. `ExtVanishing p` asserts that every admissible extension for $p$ splits globally, and `ExtVanishingAll` asserts `ExtVanishing p` for every prime $p\ge 3$. No topology or continuity is imposed; finiteness of the modules comes only from the two fields fixing the orders of $C$ and $V$.
--
--   **Relation to Mathlib.** Builds on Mathlib's `modularCyclotomicCharacter` and on Mathlib's inertia and decomposition subgroups of a valuation subring, through the project's wrappers [`ValuationSubring.LiesOverPrime`](../def/FLTPrelim_Ramification.html#L16) (the given prime is a non-unit of the valuation subring) and [`ValuationSubring.inertiaSubgroupIn`](../def/FLTPrelim_Ramification.html#L21) (the image of the inertia subgroup in the full automorphism group). The counting lemma is a convenience restatement of Mathlib's `HasEnoughRootsOfUnity.natCard_rootsOfUnity`; the admissibility predicate and the vanishing statements are the project's own, Mathlib having no notion of finite flat group scheme or of $\mathrm{Ext}^1$ over $\mathrm{Spec}\,\mathbb{Z}$.
--
--   **Where it is used.** These definitions package, in purely Galois-theoretic terms, the vanishing of $\mathrm{Ext}^1(\mu_p,\mathbb{Z}/p)$ in the category of finite flat group schemes over $\mathrm{Spec}\,\mathbb{Z}$: an extension of $\mu_p$ by the constant group $\mathbb{Z}/p$ that is unramified away from $p$ and split at $p$ is globally split. The statement serves as an input to the Greenberg–Wiles style argument behind Mazur's irreducibility theorem for the mod-$p$ representation attached to the Frey curve of a Frey package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ExtCitation_AdmissibleExtension.lean

import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsAlgClosed.card_rootsOfUnity_eq (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (n : ℕ) [NeZero n] : Nat.card (rootsOfUnity n K) = n :=
  haveI : NeZero (n : K) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  HasEnoughRootsOfUnity.natCard_rootsOfUnity K n

namespace ExtCitation

open ValuationSubring

variable (p : ℕ) [Fact p.Prime]

theorem card_rootsOfUnity_eq_self :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    Nat.card (rootsOfUnity p (AlgebraicClosure ℚ)) = p :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) p

noncomputable def cycloExp (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ℕ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ((modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) : (ZMod p)ˣ) : ZMod p).val

variable (V : Type) [AddCommGroup V] [Module (ZMod p) V]
  [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
  [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]

structure IsAdmissibleExtension (C : Submodule (ZMod p) V) : Prop where
  stable : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ C, σ • x ∈ C
  fixed_sub : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ C, σ • x = x
  cyclo_quot : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x : V,
    σ • x - (cycloExp p σ : ZMod p) • x ∈ C
  card_sub : Nat.card C = p
  card_total : Nat.card V = p ^ 2
  unramified_outside : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : V, σ • x = x
  locally_split : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∃ C' : Submodule (ZMod p) V,
      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ C', σ • x ∈ C') ∧ IsCompl C C'

variable {p V} in

def SplitsGlobally (C : Submodule (ZMod p) V) : Prop :=
  ∃ C' : Submodule (ZMod p) V,
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∀ x ∈ C', σ • x ∈ C') ∧ IsCompl C C'

def ExtVanishing : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ZMod p) V]
    (C : Submodule (ZMod p) V),
    IsAdmissibleExtension p V C → SplitsGlobally C

def ExtVanishingAll : Prop :=
  ∀ p : ℕ, (hp : p.Prime) → 3 ≤ p → @ExtVanishing p ⟨hp⟩

end ExtCitation


