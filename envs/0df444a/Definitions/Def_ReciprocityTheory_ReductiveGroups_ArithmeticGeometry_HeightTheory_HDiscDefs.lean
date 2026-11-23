-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:01.023018+00:00
-- url     : https://prove2.me/theorems/a0c5ec44-b248-44d5-a69d-f2878ebf2080
-- title:
--   HDisc Defs
-- statement:
--   Definitions and structural lemmas for HDisc Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscDefs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
noncomputable def unif (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 𝓞 K :=
  open Classical in
  if h : ∃ ϖ : 𝓞 K, ϖ ∈ la.asIdeal ∧ ϖ ∉ la.asIdeal ^ 2 then h.choose else 0
noncomputable def gOrd (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (q : KTf K d.D d.N) : ℤ :=
  open Classical in
  if h : ∃ m : ℤ, ∃ u : Op d.D d.N la, IsUnit u ∧
      q = (algebraMap K (KTf K d.D d.N) ((unif la : 𝓞 K) : K)) ^ m * OpToKT d.D d.N la u
  then h.choose else 0
noncomputable def De (hd : d.AxH 𝒜) (h : d.S1) : KTf K d.D d.N :=
  Matrix.det (Matrix.of fun k l : Fin d.del => ∑ c,
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    Algebra.trace (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (d.bvecG hd.sel hd.a4.choose k c * d.bvecG hd.sel hd.a4.choose l c))
end Data
end ReciprocityTheory.ChartRestriction.G.T0


