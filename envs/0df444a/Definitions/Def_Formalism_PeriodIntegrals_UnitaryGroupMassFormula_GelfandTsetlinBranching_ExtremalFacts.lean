-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:33.587149+00:00
-- url     : https://prove2.me/theorems/70762e4f-e645-41ab-b549-2d72184e6344
-- title:
--   Extremal Facts
-- statement:
--   Definitions and structural lemmas for Extremal Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/ExtremalFacts.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGB
open Formalism.BasicNotions MvPolynomial
def IsFixedW {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (f : MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
    sqAct ℂ N lam (embGL ℂ n N h g) f = f) ∧
  ∀ t : Fin n → ℂˣ, sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) f = ((∏ j, t j ^ mu.w j : ℂˣ) : ℂ) • f
def IsStable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)) :
    Prop :=
  ∀ (g : GL (Fin n) ℂ), ∀ f ∈ W, sqAct ℂ N lam (embGL ℂ n N h g) f ∈ W
def IsEqv {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) : Prop :=
  (∀ s ∈ nablaSq ℂ n mu, φ s ∈ nablaSq ℂ N lam) ∧
  ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu, φ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (φ s)
def ExtremalFacts : Prop :=
  ∀ (n : ℕ) (mu : DomWeight n),
    (∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ n mu g (extremal ℂ n mu) = extremal ℂ n mu) ∧
    (∀ t : Fin n → ℂˣ, sqAct ℂ n mu (diagGL ℂ n t) (extremal ℂ n mu) =
      ((∏ j, t j ^ mu.w j : ℂˣ) : ℂ) • extremal ℂ n mu) ∧
    (∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu, sqAct ℂ n mu g s ∈ nablaSq ℂ n mu)
def FixedLine : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) (f₁ f₂ : MvPolynomial (Fin N × Fin N) ℂ),
    f₁ ∈ nablaSq ℂ N lam → f₂ ∈ nablaSq ℂ N lam → IsFixedW h lam mu f₁ → IsFixedW h lam mu f₂ → f₂ ≠ 0 →
    (∃ c : ℂ, f₁ = c • f₂) ∧ Interlace h lam mu
def StableCompl : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)),
    W ≤ nablaSq ℂ N lam → IsStable h lam W →
    ∃ W' : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ), W' ≤ nablaSq ℂ N lam ∧ IsStable h lam W' ∧
      W ⊔ W' = nablaSq ℂ N lam ∧ W ⊓ W' = ⊥
def HighestVec : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)),
    W ≤ nablaSq ℂ N lam → IsStable h lam W → W ≠ ⊥ →
    ∃ f ∈ W, f ≠ 0 ∧ ∃ mu : DomWeight n, IsFixedW h lam mu f
def Realize : Prop :=
  ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) (f : MvPolynomial (Fin N × Fin N) ℂ),
    f ∈ nablaSq ℂ N lam → IsFixedW h lam mu f → f ≠ 0 →
    ∃ φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      IsEqv h mu lam φ ∧ φ (extremal ℂ n mu) = f
end PI.WGB


