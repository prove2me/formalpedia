-- Prove2me | Definitions.Def_ExtCitation_KummerBridge
-- name    : ExtCitation_KummerBridge
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/67ab8a80-a82a-5ebe-94e3-6343ec8e5b0a
-- title:
--   Twisted extension cocycle and mod-p cyclotomic character
-- statement:
--   Two carriers are set up. The first lives in a general setting: a group $\Gamma$, a commutative ring $R$, and an $R$-module $V$ carrying a distributive $\Gamma$-action whose scalars commute with the $R$-action. Given a character $\chi : \Gamma \to R^\times$ and a vector $v_0 \in V$, [`groupCohomology.extClassFun`](../def/ExtCitation_KummerBridge.html#L13) is the function $\sigma \mapsto \chi(\sigma)^{-1} \cdot (\sigma \cdot v_0 - \chi(\sigma)\cdot v_0)$, the $\chi^{-1}$-twisted difference measuring the failure of $v_0$ to be a $\chi$-eigenvector. It is a bare function $\Gamma \to V$; no cocycle identity is asserted at this stage. The accompanying lemma [`groupCohomology.extClassFun_mem`](../def/ExtCitation_KummerBridge.html#L18) records that if $C \subseteq V$ is an $R$-submodule such that $\sigma \cdot x - \chi(\sigma)\cdot x \in C$ for every $\sigma \in \Gamma$ and every $x \in V$, then $\mathrm{extClassFun}\,\chi\,v_0\,\sigma \in C$ for all $\sigma$, since $C$ is closed under scalars.
--
--   The second carrier fixes a prime $p$ and packages the mod-$p$ cyclotomic character of $\mathbb{Q}$ as a monoid homomorphism [`ExtCitation.cycloChar`](../def/ExtCitation_KummerBridge.html#L29) from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ to $(\mathbb{Z}/p)^\times$: it sends $\sigma$ to the value of Mathlib's `modularCyclotomicCharacter` on the underlying ring equivalence, the input being the count $p$ of $p$-th roots of unity in $\overline{\mathbb{Q}}$. Two compatibility lemmas tie it to the natural-number exponent `cycloExp` used in the definition of admissible extensions: `val_cycloChar` states that the canonical representative in $\{0,\dots,p-1\}$ of $\mathrm{cycloChar}\,p\,\sigma$, viewed in $\mathbb{Z}/p$, is $\mathrm{cycloExp}\,p\,\sigma$, and `coe_cycloChar` states the resulting equality $\mathrm{cycloChar}\,p\,\sigma = \mathrm{cycloExp}\,p\,\sigma$ in $\mathbb{Z}/p$.
--
--   **Relation to Mathlib.** Mathlib supplies `modularCyclotomicCharacter` together with the count of roots of unity in an algebraically closed field of characteristic zero; `cycloChar` repackages its values on $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ as a `MonoidHom` into $(\mathbb{Z}/p)^\times$. The twisted difference function `extClassFun` is the project's own.
--
--   **Where it is used.** The admissibility predicate for extensions of $\mathbb{Z}/p$ by $\mu_p$ over $\mathbb{Q}$ is phrased with the exponent `cycloExp`, while arguments about eigenvectors and coboundaries are more convenient with a multiplicative character; these definitions and compatibility lemmas provide the translation and the twisted cocycle attached to a chosen vector. They feed the analysis of when an admissible extension splits globally, which is the form in which the vanishing of the relevant extension group enters the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ExtCitation_KummerBridge.lean

import Definitions.Def_ExtCitation_AdmissibleExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace groupCohomology

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]
variable {V : Type*} [AddCommGroup V] [Module R V]
variable [DistribMulAction Γ V] [SMulCommClass Γ R V]

def extClassFun (χ : Γ →* Rˣ) (v₀ : V) (σ : Γ) : V :=
  (((χ σ)⁻¹ : Rˣ) : R) • (σ • v₀ - (χ σ : R) • v₀)

omit [SMulCommClass Γ R V] in

lemma extClassFun_mem (χ : Γ →* Rˣ) (v₀ : V) (C : Submodule R V)
    (hquot : ∀ σ : Γ, ∀ x : V, σ • x - (χ σ : R) • x ∈ C) (σ : Γ) :
    extClassFun χ v₀ σ ∈ C :=
  C.smul_mem _ (hquot σ v₀)

end groupCohomology

namespace ExtCitation

variable (p : ℕ) [Fact p.Prime]

noncomputable def cycloChar :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod p)ˣ :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  MonoidHom.mk'
    (fun σ => modularCyclotomicCharacter (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ))
    (fun a b => by rw [← map_mul]; congr 1)

lemma val_cycloChar (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((cycloChar p σ : ZMod p) : ZMod p).val = cycloExp p σ := rfl

lemma coe_cycloChar (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ((cycloChar p σ : ZMod p)) = (cycloExp p σ : ZMod p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [← val_cycloChar, ZMod.natCast_val, ZMod.cast_id]

end ExtCitation


