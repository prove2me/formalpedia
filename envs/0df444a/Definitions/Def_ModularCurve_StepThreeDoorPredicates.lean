-- Prove2me | Definitions.Def_ModularCurve_StepThreeDoorPredicates
-- name    : ModularCurve_StepThreeDoorPredicates
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/a7fcac43-cde0-5fe4-a8f6-1c3e2241abb3
-- title:
--   Predicates on a specialisation map of J0​(p)
-- statement:
--   Fix a natural number $p$ with `[NeZero p]` (primality is never used in the bodies), an additive commutative group $T$, and an additive homomorphism $sp :$ `JZero p` $\to T$ out of the project's degree-zero divisor class group of the level-$p$ modular function field; $T$ and $sp$ are arbitrary, standing for the Picard group of a special fibre and a specialisation map. The module only defines predicates (and one subgroup); it proves nothing. `TorsBijFor ℓ sp` says: for every prime $q \neq \ell$ and every $y \in T$ killed by some power $q^n$, there is an $x \in$ `JZero p` killed by some power of $q$ with $sp\,x = y$ — i.e. surjectivity of $sp$ on prime-to-$\ell$ torsion only. `FTorsionFor T` says $T$ is a torsion group: every $y$ is killed by some $m > 0$ (it does not mention $sp$). `CuspRuleStrongFor A sp`, for a valuation subring $A \subseteq \overline{\mathbb{Q}}$, quantifies over a place $x$ of the geometric function field and $j_1, j_2 \in \overline{\mathbb{Q}}$, together with the two hypotheses that the divisors `placeDiff p x (cuspInftyBar p)` and `placeDiff p x (cuspZeroBar p)` have degree zero, the hypothesis that $x$ is fixed by the project's arithmetic Galois action of every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, positivity of the orders of $x$ at `jBar p` $- j_1$ and `jpBar p` $- j_2$, and $1 < A$-valuation of $j_1$; its conclusion is the conjunction: if $v(j_2) = v(j_1)^p$ then $sp$ of the class of $x - \bar\infty$ vanishes, and if $v(j_2)^p = v(j_1)$ then $sp$ of the class of $x - \bar 0$ vanishes. In the section assuming a `HeckeAlg`-module structure on `JZero p`, `spKernelImage sp` is the image under $sp$ of the Eisenstein-kernel submodule of `ModularCurve_HeckeModule`, `RaynaudFor ℓ sp` says that if $\ell \neq 2$ then any $\ell$-power-torsion element $z$ of the rational part of the Eisenstein quotient all of whose lifts are sent by $sp$ into `spKernelImage sp` must vanish, and `CuspRuleFor A sp` repeats `CuspRuleStrongFor` with both conclusions weakened from $0$ to membership in `spKernelImage sp`.
--
--   **Relation to Mathlib.** Mathlib has no notion of a Néron specialisation map or of the Eisenstein quotient of $J_0(p)$; all five predicates and the subgroup are the project's own, built on the project's modular function field, places, cusps and Hecke module. The only Mathlib ingredient used directly is `ValuationSubring.valuation` for the absolute values $|\cdot|_A$ on $\overline{\mathbb{Q}}$.
--
--   **Where it is used.** These are the hypotheses that the project's Mazur-style Eisenstein-quotient specialisation argument consumes at a chosen good-reduction witness $sp$: torsion surjectivity away from $\ell$, torsion of the target, injectivity on the $\ell$-torsion of the rational Eisenstein quotient, and the rule that a Galois-stable place with $j$ outside the valuation ring and $j_p$ matched to $j_1$ by a $p$-th power relation specialises to a cusp. They are conditions on the given map $sp$, not consequences of the surrounding good-reduction structure, and they feed the step bounding the rational points of $X_0(p)$ used in the irreducibility and level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_StepThreeDoorPredicates.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve

namespace ModularCurve

local notation "Qbar" => AlgebraicClosure ℚ

variable {p : ℕ} [NeZero p] {T : Type*} [AddCommGroup T]

def TorsBijFor (ℓ : ℕ) (sp : JZero p →+ T) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ ℓ → ∀ y : T, (∃ n : ℕ, q ^ n • y = 0) →
    ∃ x : JZero p, (∃ n : ℕ, q ^ n • x = 0) ∧ sp x = y

def FTorsionFor (T : Type*) [AddCommGroup T] : Prop :=
  ∀ y : T, ∃ m : ℕ, 0 < m ∧ m • y = 0

def CuspRuleStrongFor (A : ValuationSubring Qbar) (sp : JZero p →+ T) : Prop :=
  ∀ (x : Place Qbar (modularFunctionFieldBar p)) (j₁ j₂ : Qbar)
      (hinf : placeDiff p x (cuspInftyBar p) ∈ Divisor.degZero)
      (hzero : placeDiff p x (cuspZeroBar p) ∈ Divisor.degZero),
    (∀ σ : Qbar ≃ₐ[ℚ] Qbar, arithmeticGalois (modularFunctionFieldFull p) σ • x = x) →
    0 < x.ord (jBar p - algebraMap Qbar (modularFunctionFieldBar p) j₁) →
    0 < x.ord (jpBar p - algebraMap Qbar (modularFunctionFieldBar p) j₂) →
    1 < A.valuation j₁ →
      (A.valuation j₂ = A.valuation j₁ ^ p →
        sp (Pic0.mk ⟨placeDiff p x (cuspInftyBar p), hinf⟩) = 0) ∧
      (A.valuation j₂ ^ p = A.valuation j₁ →
        sp (Pic0.mk ⟨placeDiff p x (cuspZeroBar p), hzero⟩) = 0)

section WithHeckeModule

variable [iJ : Module HeckeAlg (JZero p)]

def spKernelImage (sp : JZero p →+ T) : AddSubgroup T :=
  (eisensteinKernelSubmodule p iJ).toAddSubgroup.map sp

def RaynaudFor (ℓ : ℕ) (sp : JZero p →+ T) : Prop :=
  ℓ ≠ 2 → ∀ z ∈ eisensteinQuotientRational p iJ,
    (∃ k : ℕ, ℓ ^ k • z = 0) →
    (∀ x : JZero p, eisensteinQuotientMk p iJ x = z → sp x ∈ spKernelImage sp) →
    z = 0

def CuspRuleFor (A : ValuationSubring Qbar) (sp : JZero p →+ T) : Prop :=
  ∀ (x : Place Qbar (modularFunctionFieldBar p)) (j₁ j₂ : Qbar)
      (hinf : placeDiff p x (cuspInftyBar p) ∈ Divisor.degZero)
      (hzero : placeDiff p x (cuspZeroBar p) ∈ Divisor.degZero),
    (∀ σ : Qbar ≃ₐ[ℚ] Qbar, arithmeticGalois (modularFunctionFieldFull p) σ • x = x) →
    0 < x.ord (jBar p - algebraMap Qbar (modularFunctionFieldBar p) j₁) →
    0 < x.ord (jpBar p - algebraMap Qbar (modularFunctionFieldBar p) j₂) →
    1 < A.valuation j₁ →
      (A.valuation j₂ = A.valuation j₁ ^ p →
        sp (Pic0.mk ⟨placeDiff p x (cuspInftyBar p), hinf⟩) ∈ spKernelImage sp) ∧
      (A.valuation j₂ ^ p = A.valuation j₁ →
        sp (Pic0.mk ⟨placeDiff p x (cuspZeroBar p), hzero⟩) ∈ spKernelImage sp)

end WithHeckeModule

end ModularCurve


