-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiTorsionFree_Lattice
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinkowskiTorsionFree_Lattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:12.901488+00:00
-- url     : https://prove2.me/theorems/c6957df8-9abc-475c-b708-cc707d0baba7
-- title:
--   Lattice
-- statement:
--   Definitions and structural lemmas for Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinkowskiTorsionFree/Lattice.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MinkowskiQ
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_Minkowski
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.MkQ
open Matrix
variable {N : ℕ} (G : Subgroup (GeneralLinearGroup (Fin N) ℚ))
def orbitSet : Set (Fin N → ℚ) :=
  Set.range fun p : G × Fin N =>
    ((p.1 : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (Pi.single p.2 1)
def lat : Submodule ℤ (Fin N → ℚ) := Submodule.span ℤ (orbitSet G)
theorem single_mem (i : Fin N) : (Pi.single i 1 : Fin N → ℚ) ∈ lat G := by
  apply Submodule.subset_span
  refine ⟨(1, i), ?_⟩
  show (((1 : G) : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1 =
    Pi.single i 1
  exact Matrix.one_mulVec _
theorem mulVec_mem (g : G) {v : Fin N → ℚ} (hv : v ∈ lat G) :
    ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec v ∈ lat G := by
  have hv' : v ∈ Submodule.span ℤ (orbitSet G) := hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨(g * h, i), ?_⟩
    show (((g * h : G) : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1 =
      ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ
        (((h : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ) *ᵥ Pi.single i 1)
    rw [Matrix.mulVec_mulVec]
    rfl
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ a hx
noncomputable def rho : G →* Module.End ℤ (lat G) where
  toFun g := ((((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVecLin).restrictScalars
    ℤ).restrict (fun v hv => mulVec_mem G g hv)
  map_one' := by ext v i; simp
  map_mul' g g' := by
    ext v : 1
    apply Subtype.ext
    show _ = ((g : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec
      (((g' : GeneralLinearGroup (Fin N) ℚ) : Matrix (Fin N) (Fin N) ℚ).mulVec (v : Fin N → ℚ))
    simp [Matrix.mulVec_mulVec]
section finite
variable [Finite G]
theorem orbitSet_finite : (orbitSet G).Finite := Set.finite_range _
instance : Module.Finite ℤ (lat G) := Module.Finite.span_of_finite ℤ (orbitSet_finite G)
instance : Module.IsTorsionFree ℤ (lat G) := inferInstance
instance : Module.Free ℤ (lat G) := Module.free_of_finite_type_torsion_free'
theorem card_basis : Fintype.card (Module.Free.ChooseBasisIndex ℤ (lat G)) = N := by
  classical
  apply le_antisymm
  · have h1 : LinearIndependent ℤ
        (fun i => ((Module.Free.chooseBasis ℤ (lat G) i : lat G) : Fin N → ℚ)) :=
      (Module.Free.chooseBasis ℤ (lat G)).linearIndependent.map' (lat G).subtype
        (Submodule.ker_subtype _)
    have h2 : LinearIndependent ℚ
        (fun i => ((Module.Free.chooseBasis ℤ (lat G) i : lat G) : Fin N → ℚ)) :=
      (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).1 h1
    simpa using h2.fintype_card_le_finrank
  · have h3 : LinearIndependent ℚ (fun i : Fin N => (Pi.single i 1 : Fin N → ℚ)) := by
      have h7 := (Pi.basisFun ℚ (Fin N)).linearIndependent
      rwa [show ⇑(Pi.basisFun ℚ (Fin N)) = fun i : Fin N => (Pi.single i 1 : Fin N → ℚ) from
        funext fun i => by simp] at h7
    have h4 : LinearIndependent ℤ (fun i : Fin N => (Pi.single i 1 : Fin N → ℚ)) :=
      (LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)).2 h3
    have h5 : LinearIndependent ℤ (fun i : Fin N => (⟨Pi.single i 1, single_mem G i⟩ : lat G)) :=
      LinearIndependent.of_comp (lat G).subtype h4
    have h6 := h5.fintype_card_le_finrank
    rw [Module.finrank_eq_card_chooseBasisIndex] at h6
    simpa using h6
noncomputable def basisFin : Module.Basis (Fin N) ℤ (lat G) :=
  (Module.Free.chooseBasis ℤ (lat G)).reindex (Fintype.equivFinOfCardEq (card_basis G))
noncomputable def phi : G →* GeneralLinearGroup (Fin N) ℤ :=
  (Units.map (LinearMap.toMatrixAlgEquiv (basisFin G)).toRingEquiv.toMonoidHom).comp
    (rho G).toHomUnits
end finite
end PI.MkQ


