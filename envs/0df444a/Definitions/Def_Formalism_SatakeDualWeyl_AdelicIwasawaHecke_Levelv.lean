-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:32.893945+00:00
-- url     : https://prove2.me/theorems/b3c0eaf4-e7ca-411f-be4a-f3eb244b5fcc
-- title:
--   Levelv
-- statement:
--   Definitions and structural lemmas for Levelv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
namespace Formalism.UG.P
open Formalism.UG
section Local
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
abbrev lvS (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
def levelvPsi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) →+
      E ⊗[F] v.adicCompletion F :=
  AddMonoidHom.mk' (fun a => ∑ i, algebraMap (𝓞 E) E (RingOfIntegers.basis E i) ⊗ₜ[F]
      ((a i : v.adicCompletionIntegers F) : v.adicCompletion F))
    (by intro a a'; simp [tmul_add, Finset.sum_add_distrib])
theorem levelv_tmul_mem_range (e : 𝓞 E) (x : v.adicCompletionIntegers F) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] (x : v.adicCompletion F) ∈ (levelvPsi F E v).range := by
  classical
  let φ : 𝓞 E →+ E ⊗[F] v.adicCompletion F :=
    AddMonoidHom.mk' (fun y => algebraMap (𝓞 E) E y ⊗ₜ[F] (x : v.adicCompletion F))
      (by intro a b; simp [TensorProduct.add_tmul])
  have hb : ∀ i, φ (RingOfIntegers.basis E i) ∈ (levelvPsi F E v).range := by
    intro i
    refine AddMonoidHom.mem_range.mpr ⟨Pi.single i x, ?_⟩
    simp only [levelvPsi, AddMonoidHom.mk'_apply, φ]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  show φ e ∈ _
  rw [← (RingOfIntegers.basis E).sum_repr e, map_sum]
  exact sum_mem fun i _ => by rw [map_zsmul]; exact zsmul_mem (hb i) _
theorem levelv_mul_mem_range (y y' : E ⊗[F] v.adicCompletion F)
    (hy : y ∈ (levelvPsi F E v).range) (hy' : y' ∈ (levelvPsi F E v).range) :
    y * y' ∈ (levelvPsi F E v).range := by
  have hPsi : ∀ c, levelvPsi F E v c = ∑ i, algebraMap (𝓞 E) E (RingOfIntegers.basis E i) ⊗ₜ[F]
      ((c i : v.adicCompletionIntegers F) : v.adicCompletion F) := fun c => rfl
  obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hy
  obtain ⟨a', rfl⟩ := AddMonoidHom.mem_range.mp hy'
  rw [hPsi, hPsi]
  simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  first
    | simpa using levelv_tmul_mem_range v (RingOfIntegers.basis E i * RingOfIntegers.basis E j) (a i * a' j)
    | simpa using levelv_tmul_mem_range v (RingOfIntegers.basis E j * RingOfIntegers.basis E i) (a j * a' i)
def levelvT (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) where
  carrier := (levelvPsi F E v).range
  mul_mem' := levelv_mul_mem_range v _ _
  one_mem' := by
    have h1 : (1 : E ⊗[F] v.adicCompletion F) = algebraMap (𝓞 E) E 1 ⊗ₜ[F]
        ((1 : v.adicCompletionIntegers F) : v.adicCompletion F) := by rw [map_one]; rfl
    rw [h1]
    exact levelv_tmul_mem_range v 1 1
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem
end Local
section Lattice
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
def levelvPhi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (n : Type) :
    (n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) →+
      (n → E ⊗[F] v.adicCompletion F) :=
  AddMonoidHom.mk' (fun α j => levelvPsi F E v (α j)) (by intro α β; ext j; simp)
end Lattice
section GLact
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
end GLact
end Formalism.UG.P


