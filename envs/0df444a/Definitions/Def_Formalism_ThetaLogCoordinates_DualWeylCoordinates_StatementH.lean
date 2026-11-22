-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:48.036701+00:00
-- url     : https://prove2.me/theorems/c2483f1c-039c-4926-b261-79b6e0cdae4a
-- title:
--   Statement H
-- statement:
--   Definitions and structural lemmas for Statement H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/StatementH.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
def InducedSectionsSpanStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (R : Type) [CommRing R] [IsDomain R],
    (IsField R ∨ IsDiscreteValuationRing R ∨ Nonempty (R ≃+* ℤ)) →
    (Dominant mu → inducedSections R mu = (Submodule.span R (Set.range fun I : TIdx mu => mapCoord (n := n) R (brk mu I)) : Set _)) ∧
    (¬ Dominant mu → inducedSections R mu = {0})
def RationalBitableauLatticeStatement : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu →
    (Submodule.span ℤ (Set.range fun I : TIdx mu => MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu I)) :
        Set (MvPolynomial (Fin n × Fin n) ℚ)) =
      {x | x ∈ Submodule.span ℚ (Set.range fun I : TIdx mu => MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu I)) ∧
        x ∈ Nabla (O := ℤ) (glOps ℚ n (rowLetters n) Set.univ) (fun a => mu a + ((-(mu (lastIdx n))).toNat : ℤ))
          (MvPolynomial.map (Int.castRingHom ℚ) (brkPol mu (canT mu)))}
def WeightLatticeSaturationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (La : Submodule O V),
    IsGLRep E → Dominant mu → isoSub E mu = ⊤ → UZLattice E La →
    (∀ x ∈ La, ∀ nu e, IsWtProj E nu e → e x ∈ La) →
    Submodule.span O {x | ∃ u ∈ UZmon E, ∃ y ∈ La, y ∈ weightSp E mu ∧ x = u y} ≤ La ∧
    ∀ y ∈ La, ∀ u ∈ UZmon E, ∀ e, IsWtProj E mu e → e (u y) ∈ La ∧ e (u y) ∈ weightSp E mu
def dualOps {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) :
    GLOps n K (Module.Dual K V) := fun a b => -(LinearMap.dualMap (E a b))
def MinimalLatticeDualityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (_S : UniformizedDVR p O) (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (mu : Fin n → ℤ) (v : V) (v' : Module.Dual (KK O) V),
    IsIrrHW E mu v → IsHWV (dualOps E) (dualWt mu) v' →
    v' '' (Delta (O := O) E v : Set V) = Set.range (algebraMap O (KK O)) →
    (Delta (O := O) E v : Set V) =
      {x | ∀ φ ∈ Nabla (O := O) (dualOps E) (dualWt mu) v', φ x ∈ Set.range (algebraMap O (KK O))}
end Formalism.InvariantFactorPaths.ColumnFamilies


