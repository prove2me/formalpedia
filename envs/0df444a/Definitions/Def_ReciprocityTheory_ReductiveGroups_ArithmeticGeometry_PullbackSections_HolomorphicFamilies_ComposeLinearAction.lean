-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ComposeLinearAction
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ComposeLinearAction
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T17:38:06.736898+00:00
-- url     : https://prove2.me/theorems/c1943a2e-f421-4c74-9ecb-0b8bb95cf7dd
-- title:
--   Compose Linear Action
-- statement:
--   Definitions and structural lemmas for Compose Linear Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ComposeLinearAction.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ NumberField
section Ev
variable {g m n : ℕ}
theorem ev_addF (a : Fin 2 → Pt ℂ n g) (ha : ∀ p : Fin 2 × Fin g, constantCoeff (a p.1 p.2) = 0) (i : Fin g) :
    ev a (addF ℂ g i) = a 0 i + a 1 i := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  simp only [ev, addF]
  rw [MvPowerSeries.subst_add hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
theorem ev_CX (a : Fin 1 → Pt ℂ n g) (ha : ∀ p : Fin 1 × Fin g, constantCoeff (a p.1 p.2) = 0) (c : ℂ)
    (i : Fin g) : ev a (C c * X ((0 : Fin 1), i) : PS ℂ 1 g) = C c * a 0 i := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul]
  simp only [ev]
  rw [MvPowerSeries.subst_smul hs, MvPowerSeries.subst_X hs]
theorem addOf_addF (a b : Pt ℂ n g) (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    addOf (addF ℂ g) a b = a + b := by
  funext i
  simp only [addOf]
  rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [ha, hb])]
  simp
theorem cc_pt (j : Fin n) (i : Fin g) : constantCoeff (pt ℂ g j i) = 0 := by
  simp [pt]
end Ev
def addFGLaw (g : ℕ) : FGLaw ℂ g where
  F := addF ℂ g
  const i := by simp [addF]
  unit i := by
    rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt]
  comm i := by
    rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, addF, add_comm]
  assoc i := by
    have h01 : (fun l => ev (n := 3) ![pt ℂ g 0, pt ℂ g 1] (addF ℂ g l)) =
        fun l => (X ((0 : Fin 3), l) + X ((1 : Fin 3), l) : PS ℂ 3 g) :=
      funext fun l => by rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    have h12 : (fun l => ev (n := 3) ![pt ℂ g 1, pt ℂ g 2] (addF ℂ g l)) =
        fun l => (X ((1 : Fin 3), l) + X ((2 : Fin 3), l) : PS ℂ 3 g) :=
      funext fun l => by rw [ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]; simp [pt]
    rw [h01, h12, ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt]),
      ev_addF _ (fun ⟨j, k⟩ => by fin_cases j <;> simp [pt])]
    simp [pt, add_assoc]
section Act
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ}
def linAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Pt ℂ 1 g :=
  fun k => C (ty k (a : E)) * X ((0 : Fin 1), k)
theorem cc_linAct (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (i : Fin g) : constantCoeff (linAct ty a i) = 0 := by
  simp [linAct]
theorem compose_linear_action (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (b : Pt ℂ n g) (hb : ∀ i, constantCoeff (b i) = 0) :
    comp1 (linAct ty a) b = fun i => C (ty i (a : E)) * b i := by
  funext i
  simp only [comp1, linAct]
  rw [ev_CX _ (fun ⟨j, k⟩ => by fin_cases j; simp [hb])]
  simp
def linOAct (ty : Fin g → (E →+* ℂ)) : OAct (𝓞 E) (addFGLaw g) where
  act := linAct ty
  const := cc_linAct ty
  hom a := by
    show comp1 (linAct ty a) (addOf (addF ℂ g) (pt ℂ g 0) (pt ℂ g 1)) =
      addOf (addF ℂ g) (comp1 (linAct ty a) (pt ℂ g 0)) (comp1 (linAct ty a) (pt ℂ g 1))
    rw [addOf_addF _ _ (cc_pt 0) (cc_pt 1), compose_linear_action _ _ _ (fun i => by simp [pt]),
      compose_linear_action _ _ _ (cc_pt 0), compose_linear_action _ _ _ (cc_pt 1), addOf_addF _ _ (fun i => by simp [pt])
        (fun i => by simp [pt])]
    funext i
    simp [mul_add]
  add_act a b := by
    show linAct ty (a + b) = addOf (addF ℂ g) (linAct ty a) (linAct ty b)
    rw [addOf_addF _ _ (cc_linAct ty a) (cc_linAct ty b)]
    funext i
    simp [linAct, add_mul]
  mul_act a b := by
    show linAct ty (a * b) = comp1 (linAct ty a) (linAct ty b)
    rw [compose_linear_action _ _ _ (cc_linAct ty b)]
    funext i
    simp [linAct, mul_assoc]
  one_act := by
    funext i
    simp [linAct, pt]
def anFB [StarRing (𝓞 E)] (ty : Fin g → (E →+* ℂ)) : FB ℂ g (𝓞 E) := FB.triv (addFGLaw g) (linOAct ty)
end Act
end ReciprocityTheory.ChartRestriction.G.PullbackSections


