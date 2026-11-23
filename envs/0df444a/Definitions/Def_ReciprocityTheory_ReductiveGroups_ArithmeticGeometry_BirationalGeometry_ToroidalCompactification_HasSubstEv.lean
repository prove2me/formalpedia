-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:55.951405+00:00
-- url     : https://prove2.me/theorems/21f556c3-27e4-4e16-902a-ad038689e26b
-- title:
--   Has Subst Ev
-- statement:
--   Definitions and structural lemmas for Has Subst Ev, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/HasSubstEv.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {R : Type} [CommRing R] {d : ℕ}
lemma hasSubst_ev {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => h p.1 p.2)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => h p.1 p.2)
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [h p.1 p.2]; exact IsNilpotent.zero)
lemma ev_X {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0)
    (j : Fin m) (i : Fin d) : ev a (X (j, i) : PS R m d) = a j i := by
  unfold ev
  rw [MvPowerSeries.subst_X (hasSubst_ev a h)]
lemma ev_add {m n : ℕ} (a : Fin m → Pt R n d) (h : ∀ j i, constantCoeff (a j i) = 0)
    (f g : PS R m d) : ev a (f + g) = ev a f + ev a g := by
  unfold ev
  exact MvPowerSeries.subst_add (hasSubst_ev a h) f g
def addLaw (R : Type) [CommRing R] (d : ℕ) : FGLaw R d where
  F := fun i => X ((0 : Fin 2), i) + X ((1 : Fin 2), i)
  const := fun i => by simp
  unit := fun i => by
    have h : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![0, pt R d 0] : Fin 2 → Pt R 1 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    rw [ev_add _ h, ev_X _ h, ev_X _ h]
    simp [pt]
  comm := fun i => by
    have h : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    rw [ev_add _ h, ev_X _ h, ev_X _ h]
    simp [pt, add_comm]
  assoc := fun i => by
    have h2 : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![pt R d 0, pt R d 1] : Fin 2 → Pt R 3 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    have h2' : ∀ (j : Fin 2) (l : Fin d),
        constantCoeff ((![pt R d 1, pt R d 2] : Fin 2 → Pt R 3 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    have e1 : (fun l => ev ![pt R d 0, pt R d 1] (X ((0 : Fin 2), l) + X ((1 : Fin 2), l)) :
        Pt R 3 d) = fun l => X ((0 : Fin 3), l) + X ((1 : Fin 3), l) := by
      funext l; rw [ev_add _ h2, ev_X _ h2, ev_X _ h2]; simp [pt]
    have e2 : (fun l => ev ![pt R d 1, pt R d 2] (X ((0 : Fin 2), l) + X ((1 : Fin 2), l)) :
        Pt R 3 d) = fun l => X ((1 : Fin 3), l) + X ((2 : Fin 3), l) := by
      funext l; rw [ev_add _ h2', ev_X _ h2', ev_X _ h2']; simp [pt]
    rw [e1, e2]
    have h3 : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![fun l => X ((0 : Fin 3), l) +
        X ((1 : Fin 3), l), pt R d 2] : Fin 2 → Pt R 3 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    have h3' : ∀ (j : Fin 2) (l : Fin d), constantCoeff ((![pt R d 0, fun l => X ((1 : Fin 3), l) +
        X ((2 : Fin 3), l)] : Fin 2 → Pt R 3 d) j l) = 0 := by
      intro j l; fin_cases j <;> simp [pt]
    rw [ev_add _ h3, ev_X _ h3, ev_X _ h3, ev_add _ h3', ev_X _ h3', ev_X _ h3']
    simp [pt, add_assoc]
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ


