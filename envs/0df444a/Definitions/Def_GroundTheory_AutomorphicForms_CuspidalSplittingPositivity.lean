-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
-- name    : GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:04:23.925392+00:00
-- url     : https://prove2.me/theorems/bd395f64-21bb-4ef8-abb7-2385a20c646a
-- title:
--   Cuspidal Splitting Positivity
-- statement:
--   Definitions and structural lemmas for Cuspidal Splitting Positivity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingPositivity.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Function Topology ComplexConjugate
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
section ScalarDet
def scalarDet : GL (Fin n) F →* GL (Fin n) F :=
  (Matrix.GeneralLinearGroup.scalar (Fin n)).comp Matrix.GeneralLinearGroup.det
end ScalarDet
section NormChar
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}
def normChar (ω : GL (Fin n) F → ℂ) (g : GL (Fin n) F) : ℝ :=
  ‖ω (scalarDet g)‖ ^ ((n : ℝ)⁻¹)
variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv
end NormChar
section Twisted
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V}
variable (π ω) in

def twVec (x : V) (g : GL (Fin n) F) : V :=
  ((normChar ω g : ℂ)⁻¹) • π g x
variable (hωπ : HasCentralChar π ω) {v : V} (hv : v ≠ 0)
include hωπ hv
end Twisted
section Nonvanishing
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {ω : GL (Fin n) F → ℂ}
variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) {v : V}
  (hv : v ≠ 0) {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F)))
  {f : Module.Dual ℂ V} (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x)
include hπ hsc hωπ hv hKo hf
end Nonvanishing
end Parabolic
end GroundTheory.Automorphic


