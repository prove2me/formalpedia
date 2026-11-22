-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm
-- name    : Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:21.626253+00:00
-- url     : https://prove2.me/theorems/a2d8ad13-b7d2-422f-a1ac-51352d75e44e
-- title:
--   Cup Kill Adm
-- statement:
--   Definitions and structural lemmas for Cup Kill Adm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/CupKillAdm.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatGlobalModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.NG
open Module
section Hom
variable {A T' K V G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [Module T' V] [IsScalarTower T' A V]
    {r : G →* A} {χ : G →* T'ˣ} {E : A} {ι : Type*} [Fintype ι] [DecidableEq ι] {j : ι → ℕ}
def colFreeMap (φY : Ymod r χ E →ₗ[A] V) (n : ι → V) (s : (l : ι) → Fin (j l) → V) (s0 : ι → V) :
    ColFreeJ A r χ E ι j →ₗ[A] V where
  toFun x := φY x.1 + ∑ l, ((x.2 l).1 • n l + ∑ a, (x.2 l).2.1 a • s l a + (x.2 l).2.2 • s0 l)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add, Finset.smul_sum]
end Hom
end Formalism.NG


