-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:37.655806+00:00
-- url     : https://prove2.me/theorems/a5bd34d5-9afe-482f-8094-d64db905e5aa
-- title:
--   Kappa Right
-- statement:
--   Definitions and structural lemmas for Kappa Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/KappaRight.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DualFockLinear_OpBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.OpWords
abbrev Pol (K : Type) [Field K] (k : ℕ) := MvPolynomial (Fin k ⊕ Fin k) K
def Rop (K : Type) [Field K] (k : ℕ) (a b : Fin k) : Pol K k →ₗ[K] Pol K k :=
  LinearMap.mulLeft K (X (Sum.inl a)) ∘ₗ (pderiv (Sum.inl b) : Derivation K (Pol K k) (Pol K k)).toLinearMap
  - LinearMap.mulLeft K (X (Sum.inr b)) ∘ₗ (pderiv (Sum.inr a) : Derivation K (Pol K k) (Pol K k)).toLinearMap
def tt (K : Type) [Field K] (k : ℕ) : Pol K k := ∑ i, X (Sum.inl i) * X (Sum.inr i)
def wx (k : ℕ) : Fin k ⊕ Fin k → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)
def wxi (k : ℕ) : Fin k ⊕ Fin k → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)
def Bihom (K : Type) [Field K] (k d : ℕ) : Submodule K (Pol K k) :=
  weightedHomogeneousSubmodule K (wx k) d ⊓ weightedHomogeneousSubmodule K (wxi k) d
def WtLe (K : Type) [Field K] (k : ℕ) (c : ℤ) (f : Pol K k) : Prop :=
  ∀ m ∈ f.support, ∀ a : Fin k, (m (Sum.inl a) : ℤ) - m (Sum.inr a) ≤ c
def mono (K : Type) [Field K] (k d : ℕ) (g : Fin k →₀ ℕ) : ↥(homogeneousSubmodule (Fin k) K d) :=
  if h : g.degree = d then ⟨monomial g 1, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial 1 h)⟩
  else 0
def invFact {k : ℕ} (K : Type) [Field K] (g : Fin k →₀ ℕ) : K := (g.prod fun _ n => (n.factorial : K))⁻¹
def kappa (K : Type) [Field K] (k d : ℕ) :
    Module.End K ↥(homogeneousSubmodule (Fin k) K d) →ₗ[K] Pol K k :=
  ∑ g ∈ (Finset.univ : Finset (Fin k)).finsuppAntidiag d,
    invFact K g • (LinearMap.mulRight K (monomial (g.mapDomain Sum.inr) (1 : K)) ∘ₗ
      (rename Sum.inl : MvPolynomial (Fin k) K →ₐ[K] Pol K k).toLinearMap ∘ₗ
      (homogeneousSubmodule (Fin k) K d).subtype ∘ₗ LinearMap.applyₗ (mono K k d g))
def Wc (K : Type) [Field K] (k d c : ℕ) :
    Submodule K (Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :=
  Submodule.span K {B | ∃ l : List (Fin k × Fin k), l.length ≤ c ∧ B = Formalism.MainNotions.TestSideCounting.EdWord K k d l}
def KappaInj : Prop := ∀ (K : Type) [Field K] [CharZero K] (k d : ℕ), Function.Injective (kappa K k d)
def KappaLeft : Prop := ∀ (K : Type) [Field K] [CharZero K] (k d : ℕ) (a b : Fin k)
    (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)),
    kappa K k d (Formalism.MainNotions.TestSideCounting.Ed K k d a b * A) = X (Sum.inl a) * pderiv (Sum.inl b) (kappa K k d A)
def KappaRight : Prop := ∀ (K : Type) [Field K] [CharZero K] (k d : ℕ) (a b : Fin k)
    (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)),
    kappa K k d (A * Formalism.MainNotions.TestSideCounting.Ed K k d a b) = X (Sum.inr b) * pderiv (Sum.inr a) (kappa K k d A)
def KappaId : Prop := ∀ (K : Type) [Field K] [CharZero K] (k d : ℕ),
    kappa K k d 1 = ((d.factorial : K)⁻¹) • tt K k ^ d
def KappaBihom : Prop := ∀ (K : Type) [Field K] [CharZero K] (k d : ℕ)
    (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)), kappa K k d A ∈ Bihom K k d
def WtOfEig : Prop := ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (a : Fin k) (w : ℤ) (f : Pol K k),
    Rop K k a a f = (w : K) • f → ∀ m ∈ f.support, (m (Sum.inl a) : ℤ) - m (Sum.inr a) = w
def RBihom : Prop := ∀ (K : Type) [Field K] [CharZero K] (k d : ℕ) (a b : Fin k) (f : Pol K k),
    f ∈ Bihom K k d → Rop K k a b f ∈ Bihom K k d
def RTT : Prop := ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (a b : Fin k) (g : Pol K k),
    Rop K k a b (tt K k * g) = tt K k * Rop K k a b g
def TTWt : Prop := ∀ (K : Type) [Field K] [CharZero K] (k : ℕ) (c : ℤ) (g : Pol K k),
    WtLe K k c (tt K k * g) → WtLe K k c g
def DivT : Prop := ∀ (K : Type) [Field K] [CharZero K] (k d : ℕ), 1 ≤ d → ∀ f ∈ Bihom K k d,
    (∀ p : Fin k ⊕ Fin k → K, ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → eval p f = 0) →
    ∃ g ∈ Bihom K k (d - 1), f = tt K k * g
def Vanish : Prop := ∀ (K : Type) [Field K] [CharZero K] (k d c : ℕ) (W : Submodule K (Pol K k)),
    W ≤ Bihom K k d → (∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) → (∀ f ∈ W, WtLe K k c f) → c < d →
    ∀ f ∈ W, ∀ p : Fin k ⊕ Fin k → K, ∑ i, p (Sum.inl i) * p (Sum.inr i) = 0 → eval p f = 0
def Surj : Prop := ∀ (K : Type) [Field K] [CharZero K] (k d c : ℕ), c ≤ d → ∀ g ∈ Bihom K k c,
    tt K k ^ (d - c) * g ∈ (Wc K k d c).map (kappa K k d)
end PI.OpWords


