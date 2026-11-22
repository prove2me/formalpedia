-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
-- name    : Formalism_SharpRestriction_GrowthBounds_MultisetValuation_CoeffProdRename
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:39.644137+00:00
-- url     : https://prove2.me/theorems/451ff79f-3737-47ca-8468-41d30bfba904
-- title:
--   Coeff Prod Rename
-- statement:
--   Definitions and structural lemmas for Coeff Prod Rename, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/CoeffProdRename.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.FormalGroupSystem.Pf.Gen
open Finset
def fac {σ : Type} (κ : σ →₀ ℕ) : ℕ := ∏ x ∈ κ.support, (κ x).factorial
def jp {K A σ : Type} [CommRing K] [CommRing A] [Algebra K A] (P : MvPolynomial σ A) (f : MvPowerSeries σ K) : A :=
  ∑ κ ∈ P.support, (((fac κ : ℕ) : K) * MvPowerSeries.coeff κ f) • MvPolynomial.coeff κ P
section Alg
variable {K Pl : Type} [CommRing K] {ι : Pl → Type}
def atP (v : Pl) (f : MvPowerSeries (ι v) K) : MvPowerSeries (Σ v, ι v) K :=
  MvPowerSeries.rename (Function.Embedding.sigmaMk v) f
variable [Fintype Pl]
abbrev eqv : ((Σ v, ι v) →₀ ℕ) ≃+ (∀ v, ι v →₀ ℕ) := Finsupp.sigmaFinsuppAddEquivPiFinsupp
variable [DecidableEq Pl]
end Alg
end Formalism.MainNotions.FormalGroupSystem.Pf.Gen


