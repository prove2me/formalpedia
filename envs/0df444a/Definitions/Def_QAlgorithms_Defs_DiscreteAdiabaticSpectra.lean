-- Prove2me | Definitions.Def_QAlgorithms_Defs_DiscreteAdiabaticSpectra
-- name    : QAlgorithms_Defs_DiscreteAdiabaticSpectra
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:37:59.546812+00:00
-- url     : https://prove2.me/theorems/b399f8f6-caac-44b1-87fa-db810c1711a6
-- title:
--   DiscreteAdiabaticSpectra
-- statement:
--   DiscreteAdiabaticSpectra
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\DiscreteAdiabaticSpectra.lean

import Definitions.Def_QAlgorithms_Defs_DiscreteAdiabaticData
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.DiscreteAdiabatic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {T : ℕ}

/-- QAlgorithms.DiscreteAdiabatic.bandProjector: arxiv-2111.08152v1 PDF p.4, arxiv-2111.08152v1 PDF p.6, arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.31, arxiv-2111.08152v1 PDF p.32. Source domains are explicit below. -/
def bandProjector (D : SpectralBandData H T) (j : Fin (T+1)) : H →L[ℂ] H :=
  cfc (fun z : ℂ => if z ∈ D.sigmaP j then (1 : ℂ) else 0) (walkOperator (D.W j))

/-- QAlgorithms.DiscreteAdiabatic.sourceResolvent: arxiv-2111.08152v1 PDF p.7, arxiv-2111.08152v1 PDF p.31, arxiv-2111.08152v1 PDF p.32. Source domains are explicit below. -/
def sourceResolvent (D : SpectralBandData H T) (j : Fin (T+1))
    (z : ℂ) (offSpectrum : z ∉ spectrum ℂ (walkOperator (D.W j))) : H →L[ℂ] H :=
  -resolvent (walkOperator (D.W j)) z

/-- QAlgorithms.DiscreteAdiabatic.windowGap: arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6. Source domains are explicit below. -/
def windowGap (D : SpectralBandData H T) (j : Fin (T+1)) (k : Fin 3)
    (valid : j.val+k.val ≤ T) : ℝ :=
  arcSeparation (D.window j k valid).selected (D.window j k valid).complementary

/-- QAlgorithms.DiscreteAdiabatic.endpointGap: arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6. Source domains are explicit below. -/
def endpointGap (D : SpectralBandData H T) (j : Fin (T+1)) : ℝ :=
  if h : j.val+2 ≤ T then windowGap D j 2 h
  else if h : j.val+1 ≤ T then windowGap D j 1 h
  else windowGap D j 0 (by have := j.isLt; omega)

/-- QAlgorithms.DiscreteAdiabatic.neighborGap: arxiv-2111.08152v1 PDF p.5, arxiv-2111.08152v1 PDF p.6, arxiv-2111.08152v1 PDF p.30. Source domains are explicit below. -/
def neighborGap (D : SpectralBandData H T) (j : Fin (T+1)) : ℝ :=
  let neighbors := Finset.univ.filter fun i : Fin (T+1) => |(i.val : ℤ)-(j.val : ℤ)| ≤ 1
  neighbors.inf' (by change (Finset.univ.filter fun i : Fin (T+1) => |(i.val : ℤ)-(j.val : ℤ)| ≤ 1).Nonempty; exact ⟨j,by simp⟩) (endpointGap D)

example (D : SpectralBandData H 1) : endpointGap D 0 = windowGap D 0 1 (by decide) := by
  simp [endpointGap]

example (D : SpectralBandData H 1) : endpointGap D 1 = windowGap D 1 0 (by decide) := by
  simp [endpointGap]

end QAlgorithms.DiscreteAdiabatic


