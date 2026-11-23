-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:28.587408+00:00
-- url     : https://prove2.me/theorems/e34f381b-9533-45b5-a242-1d92827ae0cd
-- title:
--   Exists Smul Mem Of Local
-- statement:
--   Definitions and structural lemmas for Exists Smul Mem Of Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalGlobalLattice/ExistsSmulMemOfLocal.lean

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Lemmata_GeneralBFactThirdBisAlt_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LatLocGlob.Proof
open PI.LatLocGlob
section General
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
theorem mem_loc {p : Ideal R} {N : Submodule R V} {x : V} :
    x ∈ loc p N ↔ ∃ s : R, s ∉ p ∧ s • x ∈ N := Iff.rfl
def locSub (p : Ideal R) (hp : p.IsPrime) (N : Submodule R V) : Submodule R V where
  carrier := loc p N
  add_mem' := by
    intro x y hx hy
    obtain ⟨s, hs, hsx⟩ := mem_loc.1 hx
    obtain ⟨t, ht, hty⟩ := mem_loc.1 hy
    refine mem_loc.2 ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add, mul_smul s t y, mul_comm s t, mul_smul t s x]
    exact N.add_mem (N.smul_mem t hsx) (N.smul_mem s hty)
  zero_mem' := mem_loc.2 ⟨1, (Ideal.ne_top_iff_one p).1 hp.ne_top, by simp⟩
  smul_mem' := by
    intro c x hx
    obtain ⟨s, hs, hsx⟩ := mem_loc.1 hx
    refine mem_loc.2 ⟨s, hs, ?_⟩
    rw [smul_comm s c x]
    exact N.smul_mem c hsx
end General
section Frac
variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end Frac
section DedekindLFunctions
variable {R V : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup V] [Module R V]
end DedekindLFunctions
section Main
variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end Main
end PI.LatLocGlob.Proof


