-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:14:13.125622+00:00
-- url     : https://prove2.me/theorems/2d09e91c-5f3f-48d8-b632-ee6457870840
-- title:
--   Afsplit A
-- statement:
--   Definitions and structural lemmas for Afsplit A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitA.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG
section Adele
variable {F : Type} [Field F] [NumberField F]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
theorem afsplit_add_apply (a b : 𝔸) (w : HeightOneSpectrum (𝓞 F)) : (a + b) w = a w + b w := rfl
theorem afsplit_mul_apply (a b : 𝔸) (w : HeightOneSpectrum (𝓞 F)) : (a * b) w = a w * b w := rfl
theorem afsplit_smul_apply (c : F) (a : 𝔸) (w : HeightOneSpectrum (𝓞 F)) :
    (c • a) w = c • a w := by
  rw [Algebra.smul_def, afsplit_mul_apply, Algebra.smul_def]; rfl
def afsplitF (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : 𝔸 := by
  classical
  exact ⟨Pi.single v x, by
    filter_upwards [show ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) ∈ Filter.cofinite by simp] with w hw
    rw [Set.mem_compl_singleton_iff] at hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _⟩
theorem afsplitF_self (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) : afsplitF v x v = x := by
  classical
  show Pi.single v x v = x
  convert Pi.single_eq_same v x
theorem afsplitF_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) (x : v.adicCompletion F) :
    afsplitF v x w = 0 := by
  classical
  show Pi.single v x w = 0
  convert Pi.single_eq_of_ne h x
def afsplitI (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F →ₗ[F] 𝔸 where
  toFun := afsplitF v
  map_add' x y := by
    ext w
    by_cases h : w = v
    · subst h; simp only [afsplit_add_apply, afsplitF_self]
    · simp only [afsplit_add_apply, afsplitF_ne v w h, add_zero]
  map_smul' c x := by
    ext w
    by_cases h : w = v
    · subst h; simp only [afsplit_smul_apply, afsplitF_self, RingHom.id_apply]
    · simp only [afsplit_smul_apply, afsplitF_ne v w h, smul_zero, RingHom.id_apply]
end Adele
end Formalism.UG.P


