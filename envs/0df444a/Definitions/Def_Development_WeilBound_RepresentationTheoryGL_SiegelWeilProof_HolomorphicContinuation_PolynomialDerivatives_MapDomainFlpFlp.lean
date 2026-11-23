-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainFlpFlp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:05.722408+00:00
-- url     : https://prove2.me/theorems/3b13f541-6b0a-46b2-a6c5-d7acebb779e6
-- title:
--   Map Domain Flp Flp
-- statement:
--   Definitions and structural lemmas for Map Domain Flp Flp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/MapDomainFlpFlp.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace PositivityTheory.Rg.Sw.LC.Basic
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
abbrev Ix (m n : ℕ) := Fin m × Fin n × Bool
def flp (k : Ix m n) : Ix m n := (k.1, k.2.1, !k.2.2)
theorem flp_flp (k : Ix m n) : flp (flp k) = k := by
  obtain ⟨a, i, b⟩ := k; simp [flp]
def flpEquiv : Ix m n ≃ Ix m n := ⟨flp, flp, flp_flp, flp_flp⟩
theorem cr_apply (c : ℝ) (k : Ix m n) (P : PX m n) :
    cr c k P = (2 * c : ℂ) • (X (flp k) * P) - pderiv k P := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> (simp [cr, flp]; try abel)
theorem pderiv_comm' (k l : Ix m n) (P : PX m n) :
    pderiv k (pderiv l P) = pderiv l (pderiv k P) := by
  classical
  have h : ⁅(pderiv k : Derivation ℂ (PX m n) (PX m n)), (pderiv l : Derivation ℂ (PX m n) (PX m n))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D P) h
  simp only [Derivation.commutator_apply] at h2
  exact sub_eq_zero.mp (by simpa using h2)
theorem cr_comm (c : ℝ) (k l : Ix m n) (P : PX m n) :
    cr c k (cr c l P) = cr c l (cr c k P) := by
  classical
  simp only [cr_apply, map_sub, Derivation.map_smul, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul]
  simp only [MvPolynomial.smul_eq_C_mul, pderiv_C, mul_zero, zero_mul, add_zero, zero_add]
  rw [pderiv_comm' k l P]
  have e : (flp l = k) ↔ (flp k = l) :=
    ⟨fun h => by rw [← h, flp_flp], fun h => by rw [← h, flp_flp]⟩
  by_cases h : flp l = k
  · have h' := e.mp h
    simp only [h, h', if_true]
    ring
  · have h' : ¬ flp k = l := fun h'' => h (e.mpr h'')
    simp only [h, h', if_false]
    ring
theorem crAlg_comm (c : ℝ) : ∀ a ∈ Set.range (cr (m := m) (n := n) c), ∀ b ∈ Set.range (cr (m := m) (n := n) c),
    a * b = b * a := by
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  exact LinearMap.ext fun P => cr_comm c k l P
abbrev CrAlg (m n : ℕ) (c : ℝ) : Subalgebra ℂ (Module.End ℂ (PX m n)) := Algebra.adjoin ℂ (Set.range (cr c))
instance instCommRingCrAlg (c : ℝ) : CommRing (CrAlg m n c) := Algebra.adjoinCommRingOfComm ℂ (crAlg_comm c)
def gen (c : ℝ) (k : Ix m n) : CrAlg m n c := ⟨cr c k, Algebra.subset_adjoin ⟨k, rfl⟩⟩
def phi (c : ℝ) : PX m n →ₐ[ℂ] CrAlg m n c := MvPolynomial.aeval (gen c)
def DegLT (d : ℕ) (Q : PX m n) : Prop := ∀ t ∈ Q.support, t.degree < d
def Sm (c : ℝ) (s : Ix m n →₀ ℕ) : PX m n := monomial (Finsupp.mapDomain flp s) ((2 * c : ℂ) ^ s.degree)
def err (c : ℝ) (s : Ix m n →₀ ℕ) : PX m n := fockMono c s - Sm c s
end PositivityTheory.Rg.Sw.LC.Basic
namespace PositivityTheory.Rg.Sw.LC
end PositivityTheory.Rg.Sw.LC


