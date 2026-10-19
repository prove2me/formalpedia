-- Prove2me | Definitions.Def_QAlgorithms_Defs_DiscreteAdiabaticTransport
-- name    : QAlgorithms_Defs_DiscreteAdiabaticTransport
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:39:09.020294+00:00
-- url     : https://prove2.me/theorems/07a295d6-9d8b-42f2-8cfd-3f49fea23cf3
-- title:
--   DiscreteAdiabaticTransport
-- statement:
--   DiscreteAdiabaticTransport
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\DiscreteAdiabaticTransport.lean

import Definitions.Def_QAlgorithms_Defs_DiscreteAdiabaticSpectra
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.DiscreteAdiabatic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {T : ℕ}

/-- QAlgorithms.DiscreteAdiabatic.overlap: arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.10. Source domains are explicit below. -/
def overlap (D : SpectralBandData H T) (j i : Fin (T+1)) : H →L[ℂ] H :=
  bandProjector D j*bandProjector D i+(1-bandProjector D j)*(1-bandProjector D i)

/-- QAlgorithms.DiscreteAdiabatic.polarFactor: arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.10, arxiv-2111.08152v1 PDF p.17. Source domains are explicit below. -/
def polarFactor (D : SpectralBandData H T) (j i : Fin (T+1)) : H →L[ℂ] H :=
  cfc Real.sqrt (overlap D j i*star (overlap D j i))

/-- QAlgorithms.DiscreteAdiabatic.transport: arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.10, arxiv-2111.08152v1 PDF p.17. Source domains are explicit below. -/
def transport (D : SpectralBandData H T) (j i : Fin (T+1)) : H →L[ℂ] H :=
  cfc (fun x : ℝ => x⁻¹) (polarFactor D j i)*overlap D j i

/-- QAlgorithms.DiscreteAdiabatic.adiabaticWalk: arxiv-2111.08152v1 PDF p.7. Source domains are explicit below. -/
def adiabaticWalk (D : SpectralBandData H T) (j : Fin T) : H →L[ℂ] H :=
  transport D j.succ j.castSucc*walkOperator (D.W j.castSucc)

/-- QAlgorithms.DiscreteAdiabatic.idealEvolution: arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.8. Source domains are explicit below. -/
def idealEvolution (D : SpectralBandData H T) : Fin (T+1) → H →L[ℂ] H :=
  Fin.induction 1 (fun j V => adiabaticWalk D j*V)

example (D : SpectralBandData H T) : idealEvolution D 0 = 1 := rfl

example (D : SpectralBandData H 1) : idealEvolution D 1 = adiabaticWalk D 0 := by
  change adiabaticWalk D 0*1 = adiabaticWalk D 0
  exact mul_one _

end QAlgorithms.DiscreteAdiabatic


