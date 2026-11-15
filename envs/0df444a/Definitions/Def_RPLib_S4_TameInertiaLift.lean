-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaLift
-- name    : RPLib_S4_TameInertiaLift
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:45:49.518175+00:00
-- url     : https://prove2.me/theorems/11d14377-7647-4d01-be13-0b457a540feb
-- title:
--   Inertia at a given prime of the pro-chart surjects onto finite-level inertia
-- statement:
--   For a finite Galois level $L \le K_U$ and a prime $Q$ of the pro-chart (integral closure of $R_0$ in $K_U$), every $\tau$ in the inertia group of $Q \cap B_L$ in $\operatorname{Gal}(L/K)$ is the restriction of some $g$ in the inertia group of $Q$ in $\operatorname{Gal}(K_U/K)$: $$I(Q \cap B_L) = \{ g|_L : g \in I(Q) \}.$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter I, Section 7, Proposition 22

import Mathlib
import Definitions.Def_RPLib_S4_CP4aLift

/-!
# Tame inertia, part Lift: inertia at a GIVEN prime of the pro-chart surjects onto finite-level inertia (S4-PD (2), T8 lift)

* `exists_inertia_lift`: for a finite Galois level `L ≤ K_U` and a prime `Q` of the pro-chart, every `τ` in the inertia
  group of `Q ∩ B_L` is the restriction of some `g` in the inertia group of `Q` (the argument of `CP4a.bdryLift`,
  kept at the given prime `Q`).
-/

set_option autoImplicit false

namespace RamanujanPetersson
namespace TameInertia

open CurveCoh Kummer

noncomputable section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {R0 : Type} [CommRing R0] [Algebra R0 K]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 400000 in
/-- Inertia lifting at a given prime `Q` of the pro-chart. -/
theorem exists_inertia_lift {L : IntermediateField K (AlgebraicClosure K)} (hLU : L ≤ maxUnram A K)
    [FiniteDimensional K L] [IsGalois K L] {Q : Ideal (proChart A K R0)} [Q.IsPrime] {τ : L ≃ₐ[K] L}
    (hτ : τ ∈ (Q.comap (inclU R0 hLU)).inertia (L ≃ₐ[K] L)) :
    ∃ g ∈ Q.inertia (Pi1 A K), ∀ y : L,
      g (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU (τ y) := by
  obtain ⟨g1, hg1L⟩ := CP4a.exists_lift_level hLU τ
  obtain ⟨h, hhH, hh⟩ := CP4a.exists_fix_mul_mem_inertia hLU Q g1 fun b hb => by
    obtain ⟨y, rfl⟩ := CP4a.exists_inclU_eq hLU b hb
    exact CP4a.inclU_sub_mem hLU hτ rfl hg1L y
  refine ⟨g1 * h, AddSubgroup.mem_inertia.2 hh, fun y => ?_⟩
  have hfix : h (IntermediateField.inclusion hLU y) = IntermediateField.inclusion hLU y :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hhH _ ((IntermediateField.mem_restrict hLU _).2 y.2)
  rw [AlgEquiv.mul_apply, hfix, hg1L]

end

end TameInertia
end RamanujanPetersson


