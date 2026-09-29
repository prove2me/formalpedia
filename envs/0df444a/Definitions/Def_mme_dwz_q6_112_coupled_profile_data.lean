-- Prove2me | Definitions.Def_mme_dwz_q6_112_coupled_profile_data
-- name    : mme_dwz_q6_112_coupled_profile_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T07:05:00.519031+00:00
-- url     : https://prove2.me/theorems/11e62b07-428b-4087-9497-b8a0ad9c45c3
-- title:
--   Coupled-coordinate grading and Z decoder for enhanced row 112
-- statement:
--   This package equips the explicit q=6 four-sum coupled constituent with its standard coordinate basis and internal three-grading. It also decodes every canonical coarse-grade-two basis pair in the literal CW-square 112 block as the corresponding coupled third-mode coordinate: the two boundary pairs become the two exceptional coordinates, while all remaining pairs become the 6 by 6 middle grid. This is the coordinate-level interface used to compare the primary-hash exact address with the prescribed Table-2 row-112 histogram.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and enhanced 112 analysis in Section 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_q6_canonical_112_router_data
import Definitions.Def_mme_dwz_q6_112_exact_profile_data
import Definitions.Def_mme_dwz_component_word_projection

open MME Module

namespace MME.DWZComponentRestriction

universe u

set_option autoImplicit false

/-- The internal three-grading carried by the explicit coupled coordinates. -/
def dwzQ6CoupledCoordGrade :
    ∀ s : Fin 3, DWZCanonical112Coord 6 s → Fin 3
  | ⟨0, _⟩, Sum.inl _ => 0
  | ⟨0, _⟩, Sum.inr _ => 1
  | ⟨1, _⟩, Sum.inl _ => 0
  | ⟨1, _⟩, Sum.inr _ => 1
  | ⟨2, _⟩, Sum.inl a => ⟨a.val, by omega⟩
  | ⟨2, _⟩, Sum.inr _ => 2

/-- Decode a canonical coarse-grade-two CW-square pair as its coupled
third-mode coordinate. -/
def dwzQ6Canonical112ZCoord
    (p : LiftedCoarsePair.{u} 6 2) :
      DWZCanonical112Coord 6 (2 : Fin 3) := by
  let a := p.down.1.1
  let b := p.down.1.2
  by_cases haT : a.val = 7
  · exact Sum.inl 0
  by_cases haO : a.val = 0
  · exact Sum.inl 1
  have haPos : 0 < a.val := by omega
  have haLt : a.val - 1 < 6 := by omega
  have hgrade := congrArg Fin.val p.down.2
  have hbO : b.val ≠ 0 := by
    intro hbO
    simp [cwSquarePairGrade, cwSquareCoordGrade, a, b,
      haT, haO, hbO] at hgrade
  have hbT : b.val ≠ 7 := by
    intro hbT
    simp [cwSquarePairGrade, cwSquareCoordGrade, a, b,
      haT, haO, hbT] at hgrade
  have hbPos : 0 < b.val := by omega
  have hbLt : b.val - 1 < 6 := by omega
  exact Sum.inr
    (⟨b.val - 1, hbLt⟩, ⟨a.val - 1, haLt⟩)

instance dwzQ6Canonical112CoordFinite (s : Fin 3) :
    Finite (DWZCanonical112Coord 6 s) := by
  exact match s with
  | ⟨0, _⟩ => inferInstanceAs (Finite (Fin 6 ⊕ Fin 6))
  | ⟨1, _⟩ => inferInstanceAs (Finite (Fin 6 ⊕ Fin 6))
  | ⟨2, _⟩ => inferInstanceAs (Finite (Fin 2 ⊕ (Fin 6 × Fin 6)))

instance dwzQ6Canonical112CoordDecidableEq (s : Fin 3) :
    DecidableEq (DWZCanonical112Coord 6 s) := by
  exact match s with
  | ⟨0, _⟩ => inferInstanceAs (DecidableEq (Fin 6 ⊕ Fin 6))
  | ⟨1, _⟩ => inferInstanceAs (DecidableEq (Fin 6 ⊕ Fin 6))
  | ⟨2, _⟩ => inferInstanceAs (DecidableEq (Fin 2 ⊕ (Fin 6 × Fin 6)))

/-- The standard coordinate basis of the explicit q=6 coupled constituent. -/
noncomputable def dwzQ6CoupledBasis
    (K : Type u) [Field K] (s : Fin 3) :
    Basis (DWZCanonical112Coord 6 s) K ((coupledObj K 6).V s) :=
  match s with
  | ⟨0, _⟩ => Pi.basisFun K (Fin 6 ⊕ Fin 6)
  | ⟨1, _⟩ => Pi.basisFun K (Fin 6 ⊕ Fin 6)
  | ⟨2, _⟩ => Pi.basisFun K (Fin 2 ⊕ (Fin 6 × Fin 6))

@[simp] theorem dwzQ6CoupledBasis_apply
    (K : Type u) [Field K] (s : Fin 3)
    (c : DWZCanonical112Coord 6 s) :
    dwzQ6CoupledBasis K s c = dwzCanonical112Vec K 6 s c := by
  rcases s with ⟨s, hs⟩
  interval_cases s <;> exact Pi.basisFun_apply K _ _

end MME.DWZComponentRestriction


