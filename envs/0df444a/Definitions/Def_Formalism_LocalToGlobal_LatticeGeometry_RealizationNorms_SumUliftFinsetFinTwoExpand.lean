-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
-- name    : Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:59.554255+00:00
-- url     : https://prove2.me/theorems/7b0e1e01-210f-42f2-adbb-866c8b9c35e1
-- title:
--   Sum Ulift Finset Fin Two Expand
-- statement:
--   Definitions and structural lemmas for Sum Ulift Finset Fin Two Expand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/RealizationNorms/SumUliftFinsetFinTwoExpand.lean

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
abbrev Amb (K : Type) [Field K] [NumberField K] (n : ℕ) : Type :=
  EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2)
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
def fc (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x : Fin n → K) : Fin n → ℂ :=
  (Xf v)⁻¹ *ᵥ (fun i => v.embedding (x i))
def mkE (c : InfinitePlace K → Fin n → ℂ) : Amb K n :=
  WithLp.toLp 2 (fun p => if p.2.2 = 0 then (c p.1 p.2.1).re else (c p.1 p.2.1).im)
variable [StarRing K]
def yv (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → K) : Amb K n :=
  mkE (fun v => (2 : ℂ) • ((Xf v)ᴴ *ᵥ (fun i => star (v.embedding (ξ i)))))
variable [IsTotallyComplex K]
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
variable [StarRing K]
def Mz (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (X : Submodule (𝓞 K) (Fin n → K)) :
    Submodule ℤ (Amb K n) :=
  Formalism.HN.zl (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) Xf) X
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ} [StarRing K] [IsTotallyComplex K]
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings


