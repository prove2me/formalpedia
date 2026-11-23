-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallyStruct
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallyStruct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:14.318555+00:00
-- url     : https://prove2.me/theorems/fdb8bd25-0de8-482c-a08d-e06545b1bbed
-- title:
--   Eventually Struct
-- statement:
--   Definitions and structural lemmas for Eventually Struct, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/EventuallyStruct.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_PullLocSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
namespace CompGAux
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabSW.FiniteThetaCoordinates
open scoped TensorProduct
section Gen
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
theorem tmap_sigR (φ : R →ₐ[F] S) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ x) =
      sigR S σ (Algebra.TensorProduct.map φ (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]
theorem tmap_inclR (φ : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR]
theorem map_mem_HR (φ : R →ₐ[F] S) {g : GL (Fin M) (R ⊗[F] E)} (hg : g ∈ HR R σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom g ∈ HR S σ J := by
  unfold HR Formalism.UG.UJ at hg ⊢
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq] at hg ⊢
  have hb : ((Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom g :
      GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) (S ⊗[F] E)) =
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map
        (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom := by
    first
    | rfl
    | (ext i j; simp [Formalism.UG.bc])
  have hc : Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map
      (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom) =
      (Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))).map
        (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom := by
    ext i j
    simp [Formalism.UG.cT, tmap_sigR]
  have hJ : JR S J = (JR R J).map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom := by
    ext i j
    simp [JR, tmap_inclR]
  rw [hb, hc, hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg]
def haMap (φ : R →ₐ[F] S) : HA R σ J →* HA S σ J :=
  MonoidHom.codRestrict
    ((Formalism.UG.bc (n := Fin M) (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom).comp
      (HR R σ J).subtype) (HR S σ J) (fun h => map_mem_HR σ J φ h.2)
end Gen
section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
end Loc
end CompGAux
end PI.VolStabSW


