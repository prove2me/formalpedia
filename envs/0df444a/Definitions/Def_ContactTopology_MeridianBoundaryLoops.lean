-- Prove2me | Definitions.Def_ContactTopology_MeridianBoundaryLoops
-- name    : ContactTopology_MeridianBoundaryLoops
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-31T04:19:51.996456+00:00
-- url     : https://prove2.me/theorems/0b6a5222-6afd-4dd2-8b72-e813820a8f7c
-- title:
--   Product-torus meridian loops and their simultaneous rotations
-- statement:
--   Use the plane unit circle $S^1$ and its product torus $S^1\times S^1$. The standard meridian and its simultaneous rotations are the continuous maps
--   $$\mu(U)=(U,(1,0)),\qquad \mu_s(U)=(R_sU,R_s(1,0)).$$
--   Here $R_s$ is ordinary plane rotation by angle $s$. The interface gives the coordinate identification between the plane unit circle and the complex unit circle and uses multiplication by $e^{is}$ to define this rotation. It contains these maps and the elementary membership and continuity proofs needed to construct them. The actual homotopy, dividing-set calculation and geometric minimality of the meridian boundary are proved in the accompanying theorem.
-- source:
--   Derived explicit sphere-model boundary-minimality preparation for Hyunki Min, The contact mapping class group and rational unknots in lens spaces, arXiv:2207.03590v2, https://arxiv.org/html/2207.03590v2, Proposition 3.3, first paragraph of the proof. The explicit convex meridian, torus and fields are from the previously proved sphere-model construction. The meridian-class lower bound is supplied here by an actual homotopy-lifting argument using Mathlib Circle.isCoveringMap_exp. This is not the full proposition, a classification of all solid-torus meridians from disk essentiality, a projective minimality theorem, or a bypass/tightness/core-classification result.

import Definitions.Def_ContactTopology_MeridianTorus
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

namespace ContactTopology.TorusMeridian
open BirkhoffGlobalSection Set Function Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev PlaneCircle := MeridianTorus.UnitPlaneCircle
abbrev PlaneTorus := PlaneCircle × PlaneCircle


def complexUnit : C(PlaneCircle,Circle) where
  toFun u := ⟨⟨u.val 0,u.val 1⟩,by
    apply mem_sphere_zero_iff_norm.mpr
    have he : ‖(⟨u.val 0,u.val 1⟩:ℂ)‖^2=1 := by
      rw [Complex.sq_norm]
      have hu : u.val 0^2+u.val 1^2=1 := u.property
      simpa only [Complex.normSq_mk,pow_two] using hu
    nlinarith [norm_nonneg (⟨u.val 0,u.val 1⟩:ℂ)]⟩
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    change Continuous (fun u : PlaneCircle => (⟨u.val 0,u.val 1⟩:ℂ))
    simp_rw [Complex.mk_eq_add_mul_I]
    exact (Complex.continuous_ofReal.comp ((continuous_apply 0).comp continuous_subtype_val)).add
      ((Complex.continuous_ofReal.comp ((continuous_apply 1).comp continuous_subtype_val)).mul continuous_const)

def planeUnit : C(Circle,PlaneCircle) where
  toFun z := ⟨![(z:ℂ).re,(z:ℂ).im],by
    change (z:ℂ).re^2+(z:ℂ).im^2=1
    simpa only [Complex.normSq_apply,pow_two] using Circle.normSq_coe z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop


def phaseRotate (s : ℝ) (u : PlaneCircle) : PlaneCircle := planeUnit (Circle.exp s*complexUnit u)

lemma phaseRotate_continuous : Continuous (fun p : ℝ × PlaneCircle => phaseRotate p.1 p.2) :=
  planeUnit.continuous.comp ((Circle.exp.continuous.comp continuous_fst).mul
    (complexUnit.continuous.comp continuous_snd))


def meridianLoop : C(PlaneCircle,PlaneTorus) where
  toFun u := (u,⟨MeridianTorus.pole,MeridianTorus.pole_unit⟩)
  continuous_toFun := continuous_id.prodMk continuous_const


def rotatedMeridianLoop (s : ℝ) : C(PlaneCircle,PlaneTorus) where
  toFun u := (phaseRotate s u,phaseRotate s ⟨MeridianTorus.pole,MeridianTorus.pole_unit⟩)
  continuous_toFun := (phaseRotate_continuous.comp (continuous_const.prodMk continuous_id)).prodMk continuous_const


end
end ContactTopology.TorusMeridian


