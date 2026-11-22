-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:25:27.78827+00:00
-- url     : https://prove2.me/theorems/3fd50c79-0979-4ced-9664-2ee6b876e227
-- title:
--   Norm Rep Count Split One
-- statement:
--   Definitions and structural lemmas for Norm Rep Count Split One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjIdeal_eq_comap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace NormResidues
theorem coe_conjO (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl
theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO, coe_conjO, star_star]
theorem mem_conjIdeal (P : Ideal (𝓞 K)) (x : 𝓞 K) :
    x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ↔ conjO K x ∈ P := by
  rw [conjIdeal_eq_comap, Ideal.mem_comap]
def sigHom (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) : (𝓞 K ⧸ P) →+* (𝓞 K ⧸ P) :=
  Ideal.Quotient.lift P ((Ideal.Quotient.mk P).comp (conjO K)) (by
    intro a ha
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, ← mem_conjIdeal, hc]
    exact ha)
theorem sigHom_mk (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (x : 𝓞 K) :
    sigHom P hc (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (conjO K x) := rfl
theorem sigHom_sigHom (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (x : 𝓞 K ⧸ P) :
    sigHom P hc (sigHom P hc x) = x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sigHom_mk, sigHom_mk, conjO_conjO]
def sigEquiv (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) : (𝓞 K ⧸ P) ≃+* (𝓞 K ⧸ P) :=
  RingEquiv.ofRingHom (sigHom P hc) (sigHom P hc)
    (RingHom.ext (sigHom_sigHom P hc)) (RingHom.ext (sigHom_sigHom P hc))
end NormResidues
open NormResidues
namespace NormResidues
theorem sup_conjIdeal_eq_top {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) : P ⊔ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = ⊤ := by
  have := hP
  have hQ : (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).IsMaximal := by
    rw [conjIdeal_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _ fun x => ⟨conjO K x, conjO_conjO x⟩
  exact Ideal.IsMaximal.coprime_of_ne hP hQ (Ne.symm hc)
theorem mem_mul_conjIdeal {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (x : 𝓞 K) :
    x ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ↔ x ∈ P ∧ conjO K x ∈ P := by
  rw [Ideal.mul_eq_inf_of_coprime (sup_conjIdeal_eq_top hP hc), Ideal.mem_inf, mem_conjIdeal]
def pairHom (P : Ideal (𝓞 K)) : 𝓞 K →+* (𝓞 K ⧸ P) × (𝓞 K ⧸ P) :=
  ((Ideal.Quotient.mk P).comp (conjO K)).prod (Ideal.Quotient.mk P)
theorem pairHom_apply (P : Ideal (𝓞 K)) (x : 𝓞 K) :
    pairHom P x = (Ideal.Quotient.mk P (conjO K x), Ideal.Quotient.mk P x) := rfl
theorem pairHom_eq_zero_iff {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (x : 𝓞 K) :
    pairHom P x = 0 ↔ x ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  rw [pairHom_apply, Prod.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
    mem_mul_conjIdeal hP hc, and_comm]
theorem pairHom_surjective {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) : Function.Surjective (pairHom P) := by
  rintro ⟨a, b⟩
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  have h1 : (1 : 𝓞 K) ∈ P ⊔ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    rw [sup_conjIdeal_eq_top hP hc]
    exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have hf' : conjO K f ∈ P := (mem_conjIdeal P f).mp hf
  refine ⟨b' * f + conjO K a' * e, ?_⟩
  rw [pairHom_apply, Prod.mk.injEq]
  constructor
  · rw [Ideal.Quotient.eq]
    have hconj : conjO K e + conjO K f = 1 := by rw [← map_add, hef, map_one]
    have h2 : conjO K (b' * f + conjO K a' * e) - a' = conjO K b' * conjO K f - a' * conjO K f := by
      rw [map_add, map_mul, map_mul, conjO_conjO]
      linear_combination a' * hconj
    rw [h2]
    exact P.sub_mem (P.mul_mem_left _ hf') (P.mul_mem_left _ hf')
  · rw [Ideal.Quotient.eq]
    have h3 : b' * f + conjO K a' * e - b' = conjO K a' * e - b' * e := by
      linear_combination b' * hef
    rw [h3]
    exact P.sub_mem (P.mul_mem_left _ he) (P.mul_mem_left _ he)
def pairLift {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    (𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) →+* (𝓞 K ⧸ P) × (𝓞 K ⧸ P) :=
  Ideal.Quotient.lift _ (pairHom P) fun a ha => (pairHom_eq_zero_iff hP hc a).2 ha
theorem pairLift_mk {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (x : 𝓞 K) : pairLift hP hc (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk P (conjO K x), Ideal.Quotient.mk P x) := rfl
theorem pairLift_bijective {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) : Function.Bijective (pairLift hP hc) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun z hz => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [pairLift_mk] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((pairHom_eq_zero_iff hP hc x).mp hz)
  · obtain ⟨x, hx⟩ := pairHom_surjective hP hc y
    exact ⟨Ideal.Quotient.mk _ x, hx⟩
def vecEquiv {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M : ℕ) :
    (Fin M → 𝓞 K ⧸ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≃ (Fin M → 𝓞 K ⧸ P) × (Fin M → 𝓞 K ⧸ P) :=
  (Equiv.piCongrRight fun _ => Equiv.ofBijective _ (pairLift_bijective hP hc)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)
end NormResidues
end Formalism.HermitianLattices.Ext.L3


