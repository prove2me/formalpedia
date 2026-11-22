-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Nabladual
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Nabladual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:47:02.433073+00:00
-- url     : https://prove2.me/theorems/ec66be03-dbd7-431b-a445-cd158f4fca6f
-- title:
--   Nabladual
-- statement:
--   Definitions and structural lemmas for Nabladual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Nabladual.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.UG.P
open MvPolynomial
section
variable (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
noncomputable def monFam (k : ℕ) : {d : n →₀ ℕ | d.degree = k} → MvPolynomial n O :=
  fun d => monomial (d : n →₀ ℕ) 1
theorem monFam_linearIndependent (k : ℕ) : LinearIndependent O (monFam O n k) := by
  have h := (basisMonomials n O).linearIndependent.comp
    (Subtype.val : {d : n →₀ ℕ | d.degree = k} → n →₀ ℕ) Subtype.val_injective
  have e : monFam O n k = ⇑(basisMonomials n O) ∘ Subtype.val := by
    funext d
    simp [monFam, coe_basisMonomials]
  rw [e]
  exact h
theorem span_monFam (k : ℕ) :
    Submodule.span O (Set.range (monFam O n k)) = Formalism.UG.nabla O n k := by
  rw [Formalism.UG.nabla, homogeneousSubmodule_eq_finsupp_supported]
  change _ = restrictSupport O _
  rw [restrictSupport_eq_span, Set.image_eq_range]
  rfl
noncomputable def nablaBasis (k : ℕ) :
    Module.Basis {d : n →₀ ℕ | d.degree = k} O (Formalism.UG.nabla O n k) :=
  (Module.Basis.span (monFam_linearIndependent O n k)).map
    (LinearEquiv.ofEq _ _ (span_monFam O n k))
end
section
variable (n : Type) [Fintype n] [DecidableEq n]
theorem degree_eq_one_iff (d : n →₀ ℕ) : d.degree = 1 ↔ ∃ i, d = Finsupp.single i 1 := by
  constructor
  · intro hd
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Finsupp.ext h)
    have hle : d i ≤ 1 := hd ▸ Finsupp.le_degree i d
    have hi1 : d i = 1 := by omega
    have hsle : Finsupp.single i 1 ≤ d := by
      rw [Finsupp.single_le_iff]
      omega
    have hsplit : d = Finsupp.single i 1 + (d - Finsupp.single i 1) :=
      (add_tsub_cancel_of_le hsle).symm
    have hdeg : (d - Finsupp.single i 1).degree = 0 := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single] at this
      omega
    rw [Finsupp.degree_eq_zero_iff] at hdeg
    refine ⟨i, ?_⟩
    rw [hdeg, add_zero] at hsplit
    exact hsplit
  · rintro ⟨i, rfl⟩
    simp
noncomputable def idx1 : n ≃ {d : n →₀ ℕ | d.degree = 1} :=
  Equiv.ofBijective (fun i => ⟨Finsupp.single i 1, by simp⟩)
    ⟨fun i j h => by
      have h' : Finsupp.single i 1 = Finsupp.single j 1 := congrArg Subtype.val h
      exact (Finsupp.single_left_inj one_ne_zero).mp h',
     fun d => by
      obtain ⟨i, hi⟩ := (degree_eq_one_iff n d).mp d.2
      exact ⟨i, Subtype.ext hi.symm⟩⟩
end
noncomputable def nablaDualEquiv (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Formalism.UG.nabla O n 1 ≃ₗ[O] Module.Dual O (n → O) :=
  (nablaBasis O n 1).equiv (Pi.basisFun O n).dualBasis (idx1 n).symm
end Formalism.UG.P


