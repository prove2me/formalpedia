-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:31.837054+00:00
-- url     : https://prove2.me/theorems/9d0279ac-de3d-4fd8-a7fe-864aed11f0f3
-- title:
--   Finite Primes Of Mem
-- statement:
--   Definitions and structural lemmas for Finite Primes Of Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinitePrimesOfMem.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SummableSqGeom
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_resChar_le_absNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_resChar_prime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.A5
variable {F : Type} [Field F] [NumberField F]
theorem two_le_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 2 ≤ Ideal.absNorm 𝔭 :=
  (IdealNormInequalities.resChar_prime h𝔭).two_le.trans (IdealNormInequalities.resChar_le_absNorm h𝔭)
theorem absNorm_span_ne_zero {n : 𝓞 F} (hn : n ≠ 0) : Ideal.absNorm (Ideal.span {n}) ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hn
theorem lt_of_mem_pow {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {e : ℕ}
    (he : n ∈ 𝔭 ^ e) : e < Ideal.absNorm (Ideal.span {n}) := by
  have h1 : Ideal.span {n} ≤ 𝔭 ^ e := (Ideal.span_singleton_le_iff_mem _).mpr he
  have h2 := Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_span_ne_zero hn))
    (Ideal.absNorm_dvd_absNorm_of_le h1)
  rw [map_pow] at h2
  calc e < 2 ^ e := Nat.lt_two_pow_self
    _ ≤ Ideal.absNorm 𝔭 ^ e := Nat.pow_le_pow_left (two_le_absNorm h𝔭) e
    _ ≤ _ := h2
theorem mem_pow_iff_le_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (e : ℕ) :
    n ∈ 𝔭 ^ e ↔ e ≤ vF 𝔭 n := by
  have hb : BddAbove {e : ℕ | n ∈ 𝔭 ^ e} :=
    ⟨Ideal.absNorm (Ideal.span {n}), fun e he => (lt_of_mem_pow h𝔭 hn he).le⟩
  constructor
  · intro he
    exact le_csSup hb he
  · intro he
    have hm : vF 𝔭 n ∈ {e : ℕ | n ∈ 𝔭 ^ e} := Nat.sSup_mem ⟨0, by simp⟩ hb
    exact Ideal.pow_le_pow_right he hm
theorem finite_primes_of_mem {n : 𝓞 F} (hn : n ≠ 0) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | n ∈ 𝔭.1}.Finite := by
  refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
  refine (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) (Ideal.absNorm (Ideal.span {n}))).subset ?_
  rintro _ ⟨𝔭, h𝔭, rfl⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_span_ne_zero hn))
    (Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr h𝔭))
open scoped Classical in

def valF (n : 𝓞 F) : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ :=
  if hn : n ≠ 0 then
    Finsupp.onFinset (finite_primes_of_mem hn).toFinset (fun 𝔭 => vF 𝔭.1 n) (fun 𝔭 h => by
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have := (mem_pow_iff_le_vF 𝔭.2 hn 1).mpr (Nat.one_le_iff_ne_zero.mpr h)
      simpa using this)
  else 0
def bId (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) : Ideal (𝓞 F) := v.prod fun 𝔭 e => 𝔭.1 ^ e
end Formalism.HermitianLattices.Ext.L3.A5


