-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:52.583158+00:00
-- url     : https://prove2.me/theorems/ab330920-9a89-4841-8b65-9d5ca8f6481b
-- title:
--   HDisc AD
-- statement:
--   Definitions and structural lemmas for HDisc AD, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAD.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsDedekindDomain
section
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
noncomputable abbrev algOTKT : Algebra (OT K D N) (KTf K D N) :=
  ((algebraMap (KTp K D N) (KTf K D N)).comp (OTtoKT K D N)).toAlgebra
noncomputable abbrev algOpKT (la : HeightOneSpectrum (𝓞 K)) : Algebra (Op D N la) (KTf K D N) :=
  (OpToKT D N la).toAlgebra
noncomputable def unifOp (la : HeightOneSpectrum (𝓞 K)) : Op D N la :=
  algebraMap (OT K D N) (Op D N la) (MvPolynomial.C (Data.unif la))
end
namespace Data
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
end Data
end ReciprocityTheory.ChartRestriction.G.T0


