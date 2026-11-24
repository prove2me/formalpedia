-- Prove2me | Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
-- name    : Formalism_GradedWeylDivisibility_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:23.119916+00:00
-- url     : https://prove2.me/theorems/0aeeafc8-78f3-4eb9-8d70-7bc00d1eb872
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/StatementE.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockQBilin
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.GradedWeylDivisibility
def idFrame (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → R := fun v => if v.1.val = v.2.val then 1 else 0
def wordOf {r n : ℕ} (e : Fin r × Fin n →₀ ℕ) : List (Fin r × Fin r × ℕ) :=
  ((List.finRange n).reverse.flatMap fun s =>
    (List.finRange r).filterMap fun a =>
      if h : s.val < a.val ∧ s.val < r then some (⟨s.val, h.2⟩, a, e (a, s)) else none)
def LowerTri {r n : ℕ} (e : Fin r × Fin n →₀ ℕ) : Prop := ∀ (a : Fin r) (s : Fin n), a.val < s.val → e (a, s) = 0
def transposeWord {r : ℕ} (w : List (Fin r × Fin r × ℕ)) : List (Fin r × Fin r × ℕ) :=
  (w.map fun x => (x.2.1, x.1, x.2.2)).reverse
def bDual (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)) :
    Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ) where
  carrier := {P | P ∈ dualWeyl ℚ r n ν ∧ ∀ Q ∈ M, ∃ z : ℤ, fockQ P Q = z * fockQ (hw ℚ hn ν) (hw ℚ hn ν)}
  add_mem' := by
    rintro P P' ⟨hP, hPQ⟩ ⟨hP', hP'Q⟩
    refine ⟨(dualWeyl ℚ r n ν).add_mem hP hP', fun Q hQ => ?_⟩
    obtain ⟨z, hz⟩ := hPQ Q hQ
    obtain ⟨z', hz'⟩ := hP'Q Q hQ
    refine ⟨z + z', ?_⟩
    rw [(fockQBilin _ P P' Q 1).1, hz, hz']
    push_cast; ring
  zero_mem' := by
    refine ⟨(dualWeyl ℚ r n ν).zero_mem, fun Q _ => ⟨0, ?_⟩⟩
    have h := (fockQBilin _ (0 : MvPolynomial (Fin r × Fin n) ℚ) 0 Q 0).2
    simp only [zero_smul, zero_mul] at h
    simp [h]
  smul_mem' := by
    rintro c P ⟨hP, hPQ⟩
    refine ⟨?_, fun Q hQ => ?_⟩
    · rw [← Int.cast_smul_eq_zsmul ℚ]
      exact (dualWeyl ℚ r n ν).smul_mem _ hP
    · obtain ⟨z, hz⟩ := hPQ Q hQ
      refine ⟨c * z, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℚ, (fockQBilin _ P 0 Q (c : ℚ)).2, hz]
      push_cast; ring
def intQ (r n : ℕ) : MvPolynomial (Fin r × Fin n) ℤ →ₗ[ℤ] MvPolynomial (Fin r × Fin n) ℚ :=
  (MvPolynomial.map (Int.castRingHom ℚ)).toIntAlgHom.toLinearMap
def CoeffWord : Prop :=
  ∀ (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin r × Fin n) R) (e : Fin r × Fin n →₀ ℕ),
    IsWeightedHomogeneous (colW r n) F ν → LowerTri e → (∀ s : Fin n, ∑ a : Fin r, e (a, s) = ν s) →
      coeff e F = eval (idFrame R r n) (applyWord R (wordOf e) F)
def FockQHW : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ F ∈ dualWeyl ℚ r n ν,
    fockQ (hw ℚ hn ν) F = eval (idFrame ℚ r n) F * fockQ (hw ℚ hn ν) (hw ℚ hn ν)
def FockQWordAdj : Prop :=
  ∀ (r n : ℕ) (w : List (Fin r × Fin r × ℕ)) (F G : MvPolynomial (Fin r × Fin n) ℚ),
    fockQ (applyWord ℚ w F) G = fockQ F (applyWord ℚ (transposeWord w) G)
def LowerTriIntegral : Prop :=
  ∀ (r n : ℕ) (ν : Fin n → ℕ) (Q : MvPolynomial (Fin r × Fin n) ℚ), Q ∈ dualWeyl ℚ r n ν →
    (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e Q = z) →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, Q = intQ r n Q'
def NablaEqDualWeyl : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    (dualWeyl ℤ r n ν).map (intQ r n) = bDual r n hn ν ((weyl ℤ r n hn ν).map (intQ r n))
def WeylEqDualNabla : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    (weyl ℤ r n hn ν).map (intQ r n) = bDual r n hn ν ((dualWeyl ℤ r n ν).map (intQ r n))
def FockQRowAct : Prop :=
  ∀ (r n : ℕ) (g : Matrix (Fin r) (Fin r) ℚ) (P Q : MvPolynomial (Fin r × Fin n) ℚ),
    fockQ (rowAct ℚ g P) Q = fockQ P (rowAct ℚ g.transpose Q)
def NablaLDualWeylL : Prop :=
  ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ g : Matrix (Fin r) (Fin r) ℚ, IsUnit g.det →
    ∀ Q : MvPolynomial (Fin r × Fin n) ℚ,
      Q ∈ nablaL ℤ ℚ r n ν (g⁻¹).transpose ↔
        (Q ∈ dualWeyl ℚ r n ν ∧ ∀ P ∈ weyl ℤ r n hn ν,
          ∃ z : ℤ, fockQ (rowAct ℚ g⁻¹ (intQ r n P)) Q = z * fockQ (hw ℚ hn ν) (hw ℚ hn ν))
def NablaEqDualWeylOf : Prop := CoeffWord → FockQHW → FockQWordAdj → LowerTriIntegral → NablaEqDualWeyl
def WeylEqDualNablaOf : Prop := NablaEqDualWeyl → WeylEqDualNabla
def NablaLDualWeylLOf : Prop := NablaEqDualWeyl → FockQRowAct → NablaLDualWeylL
end Formalism.GradedWeylDivisibility


