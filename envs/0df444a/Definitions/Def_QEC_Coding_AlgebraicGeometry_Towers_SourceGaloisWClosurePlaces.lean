-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
-- name    : QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWClosurePlaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:30:28.305011+00:00
-- url     : https://prove2.me/theorems/2fe3605a-f7f1-40f7-ab27-f8da8364bdf3
-- title:
--   Source Galois WClosure Places
-- statement:
--   Definitions and structural lemmas for Source Galois WClosure Places, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceGaloisWClosurePlaces.lean

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
noncomputable def sourceGaloisWFieldEquivClosureField (m : ℕ) :
    SourceGaloisWField ≃ₐ[GaloisBaseField] SourceGaloisWClosureField m :=
  AlgEquiv.ofInjectiveField (sourceGaloisWFieldToClosure m)
noncomputable instance sourceGaloisWFieldConstantTower :
    IsScalarTower F256 GaloisBaseField SourceGaloisWField :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable instance sourceGaloisWClosureFieldConstantTower (m : ℕ) :
    IsScalarTower F256 GaloisBaseField (SourceGaloisWClosureField m) :=
  IsScalarTower.of_algebraMap_eq' rfl
noncomputable def sourceGaloisWFieldEquivClosureFieldOverF256 (m : ℕ) :
    SourceGaloisWField ≃ₐ[F256] SourceGaloisWClosureField m :=
  (sourceGaloisWFieldEquivClosureField m).restrictScalars F256
noncomputable def sourceGaloisWClosureZeroPlace (m : ℕ) :
    GlobalPlace F256 (SourceGaloisWClosureField m) :=
  GlobalPlace.comapAlgEquiv
    (sourceGaloisWFieldEquivClosureFieldOverF256 m).symm sourceGaloisWZeroPlace
noncomputable def sourceGaloisWClosureInfinityPlace (m : ℕ) :
    GlobalPlace F256 (SourceGaloisWClosureField m) :=
  GlobalPlace.comapAlgEquiv
    (sourceGaloisWFieldEquivClosureFieldOverF256 m).symm sourceGaloisWInfinityPlace
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth


