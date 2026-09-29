-- Prove2me | Definitions.Def_LocalReciprocity_IsLocalReciprocityMap
-- name    : LocalReciprocity_IsLocalReciprocityMap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/85927773-5781-5b65-bcc6-2eca2b18e37a
-- title:
--   Axiomatic local reciprocity maps via valuations
-- statement:
--   Throughout, $K$ and $M$ are fields each equipped with a valuation with values in $\mathbb{Z} \cup \{0\}$ written multiplicatively (`WithZero (Multiplicative ℤ)`), so that "$v(x) \le 1$" says $x$ is in the valuation ring and "$v(y) < 1$" says $y$ lies in the maximal ideal. Three notions are introduced, all formulated for a group $H$ acting on $M$ by ring automorphisms.
--
--   First, `inertiaSet M H` is the subset of $h \in H$ such that $v(h \cdot x - x) < 1$ for every $x \in M$ with $v(x) \le 1$, i.e. the elements acting trivially on the residue field of $M$; it is defined as a `Set H`, not as a subgroup. Second, `IsArithFrobenius K M H φ` holds when $v(\varphi \cdot x - x^{q}) < 1$ for all $x$ with $v(x) \le 1$, where $q$ is the cardinality (`Nat.card`) of the residue field of the valuation subring of $K$.
--
--   Third, `IsLocalReciprocityMap i H θ` is a structure, i.e. a conjunction of properties, attached to a ring homomorphism $i \colon K \to M$ and a group homomorphism $\theta \colon K^\times \to H$, with five fields: $\theta$ is surjective; $\theta(a) = 1$ if and only if $i(a) = \prod^{\mathrm{f}}_{h \in H} h \cdot b$ for some $b \in M$ (a finprod over $H$); for every subgroup $H' \le H$, if $b \in M$ is fixed by $H'$ and $i(a)$ equals the finprod of $\mathrm{out}(c) \cdot b$ over the cosets $c \in H/H'$ (chosen representatives), then $\theta(a) \in H'$; the image under $\theta$ of $\{a : v(a) = 1\}$ equals `inertiaSet M H`; and for every arithmetic Frobenius $\varphi$ and every $a$ with $v(a) = \exp(-n)$, $n \in \mathbb{Z}$, the element $\theta(a)\varphi^{-n}$ lies in `inertiaSet M H`.
--
--   No algebra structure relating $K$ and $M$ is assumed: norms appear as products of conjugates in $M$ compared to $K$ through $i$. This is a list of properties of $\theta$, not a characterisation of it.
--
--   **Relation to Mathlib.** Mathlib supplies the valuation framework (`Valued`, `Valuation.valuationSubring`, `IsLocalRing.ResidueField`) and `finprod`, but has no notion of a local reciprocity (norm-residue) map; the inertia set, the arithmetic-Frobenius predicate and the axiom list are the project's own, phrased directly in terms of valuations rather than via Mathlib's ramification theory.
--
--   **Where it is used.** These definitions form the interface for the project's local class field theory: they are used to identify the local component of the global idelic Artin map as a local reciprocity map, and to compare the filtration of $K^\times$ by unit groups with the higher ramification filtration on $H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalReciprocity_IsLocalReciprocityMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LocalReciprocity

variable (K M : Type*) [Field K] [Field M]
  [Valued K (WithZero (Multiplicative ℤ))] [Valued M (WithZero (Multiplicative ℤ))]

def inertiaSet (H : Type*) [Group H] [MulSemiringAction H M] : Set H :=
  {h : H | ∀ x : M, Valued.v x ≤ 1 → Valued.v (h • x - x) < 1}

def IsArithFrobenius (H : Type*) [Group H] [MulSemiringAction H M] (φ : H) : Prop :=
  ∀ x : M, Valued.v x ≤ 1 →
    Valued.v (φ • x - x ^ Nat.card (IsLocalRing.ResidueField ((Valued.v (R := K)).valuationSubring))) < 1

structure IsLocalReciprocityMap (i : K →+* M) (H : Type*) [Group H] [MulSemiringAction H M] (θ : Kˣ →* H) : Prop where

  surjective : Function.Surjective θ

  apply_eq_one_iff : ∀ a : Kˣ, θ a = 1 ↔ ∃ b : M, (∏ᶠ h : H, h • b) = i (a : K)

  mem_of_finprod_quotient_smul_eq : ∀ (H' : Subgroup H) (a : Kˣ) (b : M), (∀ h ∈ H', h • b = b) →
    (∏ᶠ c : H ⧸ H', (Quotient.out c) • b) = i (a : K) → θ a ∈ H'

  image_units_eq_inertiaSet : (⇑θ) '' {a : Kˣ | Valued.v (a : K) = 1} = inertiaSet M H

  mul_zpow_neg_mem_inertiaSet : ∀ (φ : H), IsArithFrobenius K M H φ →
    ∀ (a : Kˣ) (n : ℤ), Valued.v (a : K) = WithZero.exp (-n) → θ a * φ ^ (-n) ∈ inertiaSet M H

end LocalReciprocity


