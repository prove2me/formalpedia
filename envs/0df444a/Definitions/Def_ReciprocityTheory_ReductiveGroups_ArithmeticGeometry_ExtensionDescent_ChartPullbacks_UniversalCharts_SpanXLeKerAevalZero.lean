-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:03.883288+00:00
-- url     : https://prove2.me/theorems/31d4f9bb-4610-43cb-bfb7-4fec59d65b15
-- title:
--   Span XLe Ker Aeval Zero
-- statement:
--   Definitions and structural lemmas for Span XLe Ker Aeval Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/SpanXLeKerAevalZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Chart
open MvPolynomial
section Jet
variable (R : Type) [CommRing R]
abbrev JetR (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ R ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))) ^ (m + 1)
def jetTruncR (κ : Type) (m : ℕ) : JetR R κ (m + 1) →ₐ[R] JetR R κ m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))
def jetZeroR (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ 0 :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))
variable {R}
abbrev zR {κ : Type} (m : ℕ) (j : κ) : JetR R κ m := Ideal.Quotient.mk _ (MvPolynomial.X j)
variable (R)
theorem span_X_le_ker_aeval_zero (κ : Type) :
    Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) ≤
      RingHom.ker (MvPolynomial.aeval (R := R) (fun _ : κ => (0 : R))) := by
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  simp
def jetAug (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (fun _ : κ => (0 : R))) (fun a ha =>
    span_X_le_ker_aeval_zero R κ (Ideal.pow_le_self (by omega) ha))
variable {R}
variable (R) in

def jetLift {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] (J : Ideal A) (hJ : J ^ (m + 1) = ⊥)
    (b : κ → A) (hb : ∀ j, b j ∈ J) : JetR R κ m →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval b) (fun a ha => by
    have h1 : Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R)) ≤
        J.comap (MvPolynomial.aeval (R := R) b) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      simpa using hb j
    have h2 : a ∈ (J ^ (m + 1)).comap (MvPolynomial.aeval (R := R) b) :=
      Ideal.le_comap_pow _ (m + 1) (Ideal.pow_right_mono h1 (m + 1) ha)
    rw [hJ] at h2
    exact h2)
end Jet
section Etale
variable {R : Type} [CommRing R] {n : ℕ} {S : Type} [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial (Fin n) R) S] [IsScalarTower R (MvPolynomial (Fin n) R) S]
variable (R) in

abbrev sX (j : Fin n) : S := algebraMap (MvPolynomial (Fin n) R) S (MvPolynomial.X j)
variable [Algebra.FormallyEtale (MvPolynomial (Fin n) R) S] (ε : S →ₐ[R] R)
end Etale
end ReciprocityTheory.ChartRestriction.G.Chart


