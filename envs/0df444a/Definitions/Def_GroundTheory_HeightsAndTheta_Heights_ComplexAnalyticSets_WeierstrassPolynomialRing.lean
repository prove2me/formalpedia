-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassPolynomialRing
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassPolynomialRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:02.057813+00:00
-- url     : https://prove2.me/theorems/ec0ac53a-cfea-4b2e-8443-4bbdf0dc1f2d
-- title:
--   Weierstrass Polynomial Ring
-- statement:
--   Definitions and structural lemmas for Weierstrass Polynomial Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/WeierstrassPolynomialRing.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_WeierstrassRemainderUnique
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermsDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
def mkGerm {τ : Type} [Fintype τ] (f : (τ → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) : holGerms (0 : τ → ℂ) :=
  ⟨↑f, f, hf, rfl⟩
def germValue {τ : Type} [Fintype τ] (w : τ → ℂ) : holGerms w →+* ℂ :=
  Germ.valueRingHom.comp (holGerms w).subtype
def lastProj (σ : Type) [Fintype σ] : (Option σ → ℂ) →L[ℂ] (σ → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) (some i)
def germLift (σ : Type) [Fintype σ] : holGerms (0 : σ → ℂ) →+* holGerms (0 : Option σ → ℂ) :=
  germPull (lastProj σ) ((lastProj σ).analyticAt 0) (map_zero _)
def lastVarGerm (σ : Type) [Fintype σ] : holGerms (0 : Option σ → ℂ) :=
  mkGerm (fun x : Option σ → ℂ => x none)
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).analyticAt 0)
def polyToGerm (σ : Type) [Fintype σ] : (holGerms (0 : σ → ℂ))[X] →+* holGerms (0 : Option σ → ℂ) :=
  eval₂RingHom (germLift σ) (lastVarGerm σ)
def finPoly {R : Type*} [CommRing R] {d : ℕ} (b : Fin d → R) : R[X] :=
  ∑ j : Fin d, C (b j) * X ^ (j : ℕ)
def weierstrassPoly {σ : Type} [Fintype σ] {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ) (hc : ∀ j, AnalyticAt ℂ (c j) 0) :
    (holGerms (0 : σ → ℂ))[X] :=
  X ^ d + finPoly (fun j => mkGerm (c j) (hc j))
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


