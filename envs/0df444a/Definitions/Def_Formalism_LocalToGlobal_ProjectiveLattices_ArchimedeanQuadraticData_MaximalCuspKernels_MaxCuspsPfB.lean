-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:18:04.906672+00:00
-- url     : https://prove2.me/theorems/f5f92acf-bd7e-4fdc-a130-2b78f8a10b7b
-- title:
--   Max Cusps Pf B
-- statement:
--   Definitions and structural lemmas for Max Cusps Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SublatticeCoefficients
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
open MeasureTheory Complex
namespace Formalism.L2.Pj.QAt
abbrev mcBox (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ : Fin n => Set.Ioc (0 : ℝ) 1
def mcE {n : ℕ} (m : Fin n → ℤ) (u : Fin n → ℝ) : ℂ :=
  cexp (-(2 * Real.pi * I) * ∑ j, (m j : ℂ) * (u j : ℂ))
def mcCo {n : ℕ} (g : (Fin n → ℝ) → ℂ) (m : Fin n → ℤ) : ℂ := ∫ u in mcBox n, g u * mcE m u
def mcT {n N : ℕ} (c : Fin n → Fin N → ℤ) (t : Fin n → ℝ) : Fin N → ℝ :=
  fun i => ∑ j, t j * (c j i : ℝ)
def mcG {n N : ℕ} (g : (Fin N → ℝ) → ℂ) (c : Fin n → Fin N → ℤ) (k : Fin n → ℤ)
    (u : Fin N → ℝ) : ℂ :=
  mcCo (fun t => g (u + mcT c t)) k
end Formalism.L2.Pj.QAt


