-- Prove2me | Definitions.Def_CircTrichotomy_InQEJ1
-- name    : CircTrichotomy_InQEJ1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:04.765449+00:00
-- url     : https://prove2.me/theorems/0553984c-7184-4678-8c65-ed7f5d6e0b25
-- title:
--   $\eta\in\mathbf{QEJ_1}$: identities of the stable semigroup
-- statement:
--   A morphism $\varphi$ with stability index $s$ belongs to $\mathbf{QEJ_1}$ if its stable semigroup $\mathrm{stab}(\varphi)=\varphi(\Sigma^s)$ satisfies
--   $$epxqf=epxxqf\qquad\text{and}\qquad epxyqf=epyxqf$$
--   for all idempotents $e,f$ of $\mathrm{stab}(\varphi)$ and all $p,q,x,y\in\mathrm{stab}(\varphi)$.
--
--   This is the algebraic side of the $O(1)$-characterization.
--
--   **Formalization Note** The definition asserts that the stability index exists (it does for every stamp).
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.2 (3), p.3

import Mathlib
import Definitions.Def_CircTrichotomy_IsStabilityIndex

set_option autoImplicit false

namespace CircTrichotomy

/-- **`φ ∈ QEJ₁`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.2 (3), p.3): "The syntactic morphism η_L belongs to the
length-multiplying pseudovariety of stamps QEJ₁, i.e., the stable semigroup stab(η_L) of η_L
satisfies the identities epxqf = epxxqf and epxyqf = epyxqf, where e, f range over idempotents and
where p, q, x, y range over all elements of stab(η_L)."

`InQEJ1 φ`: for the stability index `s` of `φ`, the stable semigroup `φ(Σˢ)` satisfies both
identities for all idempotents `e, f` and all elements `p, q, x, y` of `φ(Σˢ)`.

**Formalization Note** The stability index is asserted to exist (it does for every stamp). -/
def InQEJ1 {α S : Type} [Semigroup S] (φ : FreeSemigroup α →ₙ* S) : Prop :=
  ∃ s : ℕ, IsStabilityIndex φ s ∧
    ∀ e ∈ lenImage φ s, ∀ f ∈ lenImage φ s, ∀ p ∈ lenImage φ s, ∀ q ∈ lenImage φ s,
      ∀ x ∈ lenImage φ s, ∀ y ∈ lenImage φ s, e * e = e → f * f = f →
        e * p * x * q * f = e * p * x * x * q * f ∧ e * p * x * y * q * f = e * p * y * x * q * f

end CircTrichotomy


