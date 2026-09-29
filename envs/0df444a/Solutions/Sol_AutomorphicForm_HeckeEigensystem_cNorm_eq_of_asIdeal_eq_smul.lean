-- Prove2me | solution 1 for AutomorphicForm.HeckeEigensystem.cNorm_eq_of_asIdeal_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/025598fa-60e1-5352-bdfe-05c9eee2433d

import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_HeckeEigensystem_cNorm_eq_of_asIdeal_eq_smul

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

namespace R1CNorm

theorem absNorm_map_ringEquiv {S : Type*} [CommRing S] [Nontrivial S] [IsDedekindDomain S]
    [Module.Free ℤ S] (e : S ≃+* S) (I : Ideal S) :
    Ideal.absNorm (Ideal.map (e : S →+* S) I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_eq_index, Ideal.absNorm_eq_index]

  have h1 : (Ideal.map (e : S →+* S) I).toAddSubgroup.index = Nat.card (S ⧸ Ideal.map (e : S →+* S) I) :=
    rfl
  have h2 : I.toAddSubgroup.index = Nat.card (S ⧸ I) := rfl
  rw [h1, h2]
  exact (Nat.card_congr (Ideal.quotientEquiv I (Ideal.map (e : S →+* S) I) e rfl).toEquiv).symm

end R1CNorm

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L)) (h : w'.asIdeal = σ • w.asIdeal) :
    AutomorphicForm.HeckeEigensystem.cNorm w' = AutomorphicForm.HeckeEigensystem.cNorm w := by
  unfold AutomorphicForm.HeckeEigensystem.cNorm
  rw [h, Ideal.pointwise_smul_def]
  have : (MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) σ)
      = ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) := rfl
  rw [this, R1CNorm.absNorm_map_ringEquiv]

end S_AutomorphicForm_HeckeEigensystem_cNorm_eq_of_asIdeal_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_HeckeEigensystem_cNorm_eq_of_asIdeal_eq_smul (solution)
