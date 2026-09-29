-- Prove2me | solution 1 for AutomorphicForm.exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9c15e03e-9d25-59b7-8f5b-3c082104d456

import Theorems.Thm_AutomorphicForm_archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex

set_option autoImplicit false

noncomputable section

namespace S14ShiftC

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm~archFlowAtComplex_mul_comm_of_glArch_eq_one IsDedekindDomain"
open scoped Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

variable {K : Type} [Field K] [NumberField K]

private def _root_.S14ShiftC.lder {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex) (α : AdelicGL2 (𝓞 K) K → ℂ) :
    AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0

p2m_export "S14ShiftC" "lder"
theorem exists_lder_eq_pure {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    {α : AdelicGL2 (𝓞 K) K → ℂ} {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (hfa : IsArchTestFactor K fa)
    (hα : ∀ g, α g = fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) :
    ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
      ∀ g, lder hw d α g = fa' (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) := by
  obtain ⟨fa', hfa', heq⟩ :=
    (archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff hfa
  refine ⟨fa', hfa', fun g => ?_⟩
  have h1 : lder hw d α g = deriv (fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAtComplex hw d (-t) * g)) *
      ff (glFin (𝓞 K) K (archFlowAtComplex hw d (-t) * g))) 0 := by
    simp only [lder, hα]
  rw [h1]
  exact congrFun heq g

theorem archFlowAtComplex_mul_comm_of_glArch_eq_one {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (t : ℝ) {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) :
    archFlowAtComplex hw d t * k = k * archFlowAtComplex hw d t := by
  have hfin : glFin (𝓞 K) K (archFlowAtComplex hw d t) = 1 := glFin_adelicArchGLIncl K _
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hk, mul_one, one_mul]
  · rw [map_mul, map_mul, hfin, mul_one, one_mul]

theorem isBiInvariantUnder_lder {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    {U : Subgroup (AdelicGL2 (𝓞 K) K)} (hU : U ≤ finiteAdelicGL2Subgroup K)
    {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsBiInvariantUnder K U α) : IsBiInvariantUnder K U (lder hw d α) := by
  intro u hu y
  have hk : glArch (𝓞 K) K u = 1 := (mem_finiteAdelicGL2Subgroup_iff K u).1 (hU hu)
  constructor
  · show deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * (u * y))) 0 =
      deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0
    congr 1
    funext t
    rw [← mul_assoc, archFlowAtComplex_mul_comm_of_glArch_eq_one hw d (-t) hk, mul_assoc, (hα u hu _).1]
  · show deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * (y * u))) 0 =
      deriv (fun t : ℝ => α (archFlowAtComplex hw d (-t) * y)) 0
    congr 1
    funext t
    rw [← mul_assoc, (hα u hu _).2]

theorem isArchSmoothAtComplex_and_archDerivAtComplex_convOp {w : InfinitePlace K} (hw : w.IsComplex)
    (d : ArchDirComplex) (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : Continuous x) :
    IsArchSmoothAtComplex hw (convOp K α x) ∧
      archDerivAtComplex hw d (convOp K α x) = convOp K (lder hw d α) x :=
  (archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).1 x α hx hα

theorem isArchTestFactor_lin (a b : ℂ) {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (ha : IsArchTestFactor K fa) (hb : IsArchTestFactor K fb) :
    IsArchTestFactor K (fun g => a * fa g + b * fb g) := by
  obtain ⟨⟨Φa, hΦa, hea⟩, hca⟩ := ha
  obtain ⟨⟨Φb, hΦb, heb⟩, hcb⟩ := hb
  exact ⟨⟨fun e => a * Φa e + b * Φb e, (contDiff_const.mul hΦa).add (contDiff_const.mul hΦb), fun g => by
    show a * fa g + b * fb g = a * Φa (archEntries K g) + b * Φb (archEntries K g)
    rw [hea, heb]⟩, hca.mul_left.add hcb.mul_left⟩

theorem isBiInvariantUnder_lin {U : Subgroup (AdelicGL2 (𝓞 K) K)} (a b : ℂ) {fa fb : AdelicGL2 (𝓞 K) K → ℂ}
    (ha : IsBiInvariantUnder K U fa) (hb : IsBiInvariantUnder K U fb) :
    IsBiInvariantUnder K U (fun g => a * fa g + b * fb g) := fun u hu g =>
  ⟨by show a * fa (u * g) + b * fb (u * g) = a * fa g + b * fb g
      rw [(ha u hu g).1, (hb u hu g).1],
   by show a * fa (g * u) + b * fb (g * u) = a * fa g + b * fb g
      rw [(ha u hu g).2, (hb u hu g).2]⟩

theorem exists_pure_lin (a b : ℂ) {fa fb : AdelicGL2 (𝓞 K) K → ℂ}
    {pa pb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    (hpa : IsArchTestFactor K pa) (hpb : IsArchTestFactor K pb)
    (hea : ∀ g, fa g = pa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g))
    (heb : ∀ g, fb g = pb (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)) :
    ∃ p : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K p ∧
      ∀ g, (fun y => a * fa y + b * fb y) g = p (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) :=
  ⟨fun z => a * pa z + b * pb z, isArchTestFactor_lin a b hpa hpb, fun g => by
    show a * fa g + b * fb g = (a * pa (glArch (𝓞 K) K g) + b * pb (glArch (𝓞 K) K g)) * ff (glFin (𝓞 K) K g)
    rw [hea g, heb g]
    ring⟩

theorem integrable_conv_integrand (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : Continuous x)
    (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) (a : AdelicGL2 (𝓞 K) K) :
    Integrable (fun y => x (a * y) * g y) (adelicGLHaar (Fin 2) (𝓞 K) K) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  exact ((hx.comp (continuous_const.mul continuous_id)).mul hg).integrable_of_hasCompactSupport hgc.mul_left

theorem convOp_lin_apply (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : Continuous x) (a b : ℂ)
    (g h : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hh : Continuous h) (hhc : HasCompactSupport h) (z : AdelicGL2 (𝓞 K) K) :
    convOp K (fun y => a * g y + b * h y) x z = a * convOp K g x z + b * convOp K h x z := by
  show rightConv K x (fun y => a * g y + b * h y) z = a * rightConv K x g z + b * rightConv K x h z
  simp only [rightConv_apply]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_conv_integrand x hx g hg hgc z).const_mul a)
      ((integrable_conv_integrand x hx h hh hhc z).const_mul b)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)

structure Good (U : Subgroup (AdelicGL2 (𝓞 K) K)) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (α : AdelicGL2 (𝓞 K) K → ℂ) : Prop where
  pure : ∃ p : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K p ∧
    ∀ g, α g = p (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)
  binv : IsBiInvariantUnder K U α

variable {U : Subgroup (AdelicGL2 (𝓞 K) K)} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}

theorem Good.isFactorizableTestFn {α : AdelicGL2 (𝓞 K) K → ℂ} (hff : IsFinTestFactor K ff) (h : Good U ff α) :
    IsFactorizableTestFn K α := by
  obtain ⟨p, hp, he⟩ := h.pure
  exact ⟨p, ff, hp, hff, he⟩

theorem Good.lder {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex) (hU : U ≤ finiteAdelicGL2Subgroup K)
    {α : AdelicGL2 (𝓞 K) K → ℂ} (h : Good U ff α) : Good U ff (lder hw d α) := by
  obtain ⟨p, hp, he⟩ := h.pure
  obtain ⟨p', hp', he'⟩ := exists_lder_eq_pure hw d hp he
  exact ⟨⟨p', hp', he'⟩, isBiInvariantUnder_lder hw d hU h.binv⟩

theorem Good.lin (a b : ℂ) {fa fb : AdelicGL2 (𝓞 K) K → ℂ} (ha : Good U ff fa) (hb : Good U ff fb) :
    Good U ff (fun y => a * fa y + b * fb y) := by
  obtain ⟨pa, hpa, hea⟩ := ha.pure
  obtain ⟨pb, hpb, heb⟩ := hb.pure
  exact ⟨exists_pure_lin a b hpa hpb hea heb, isBiInvariantUnder_lin a b ha.binv hb.binv⟩

private def _root_.S14ShiftC.ldel {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDir) (α : AdelicGL2 (𝓞 K) K → ℂ) :
    AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => (1 / 2 : ℂ) * lder hw d.toComplex α y + (-(1 / 2 : ℂ) * Complex.I) * lder hw d.toComplexI α y

p2m_export "S14ShiftC" "ldel"

private def _root_.S14ShiftC.ldelBar {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDir) (α : AdelicGL2 (𝓞 K) K → ℂ) :
    AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => (1 / 2 : ℂ) * lder hw d.toComplex α y + ((1 / 2 : ℂ) * Complex.I) * lder hw d.toComplexI α y

p2m_export "S14ShiftC" "ldelBar"
theorem Good.ldel {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDir) (hU : U ≤ finiteAdelicGL2Subgroup K)
    {α : AdelicGL2 (𝓞 K) K → ℂ} (h : Good U ff α) : Good U ff (ldel hw d α) :=
  Good.lin _ _ (h.lder hw d.toComplex hU) (h.lder hw d.toComplexI hU)

theorem Good.ldelBar {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDir) (hU : U ≤ finiteAdelicGL2Subgroup K)
    {α : AdelicGL2 (𝓞 K) K → ℂ} (h : Good U ff α) : Good U ff (ldelBar hw d α) :=
  Good.lin _ _ (h.lder hw d.toComplex hU) (h.lder hw d.toComplexI hU)

theorem archDelAt_convOp_and_archDelBarAt_convOp {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDir)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α) (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : Continuous x) :
    archDelAt hw d (convOp K α x) = convOp K (ldel hw d α) x ∧
      archDelBarAt hw d (convOp K α x) = convOp K (ldelBar hw d α) x := by
  obtain ⟨-, h1⟩ := isArchSmoothAtComplex_and_archDerivAtComplex_convOp hw d.toComplex α hα x hx
  obtain ⟨-, h2⟩ := isArchSmoothAtComplex_and_archDerivAtComplex_convOp hw d.toComplexI α hα x hx
  have hf1 : IsFactorizableTestFn K (lder hw d.toComplex α) := by
    obtain ⟨fa, ff, hfa, hff, he⟩ := hα
    obtain ⟨fa', hfa', he'⟩ := exists_lder_eq_pure hw d.toComplex hfa he
    exact ⟨fa', ff, hfa', hff, he'⟩
  have hf2 : IsFactorizableTestFn K (lder hw d.toComplexI α) := by
    obtain ⟨fa, ff, hfa, hff, he⟩ := hα
    obtain ⟨fa', hfa', he'⟩ := exists_lder_eq_pure hw d.toComplexI hfa he
    exact ⟨fa', ff, hfa', hff, he'⟩
  obtain ⟨hc1, hs1⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ hf1
  obtain ⟨hc2, hs2⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ hf2
  constructor
  · rw [archDelAt, h1, h2]
    funext z
    rw [show convOp K (ldel hw d α) x z = convOp K (fun y => (1 / 2 : ℂ) * lder hw d.toComplex α y +
        (-(1 / 2 : ℂ) * Complex.I) * lder hw d.toComplexI α y) x z from rfl,
      convOp_lin_apply x hx _ _ _ _ hc1 hs1 hc2 hs2 z]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · rw [archDelBarAt, h1, h2]
    funext z
    rw [show convOp K (ldelBar hw d α) x z = convOp K (fun y => (1 / 2 : ℂ) * lder hw d.toComplex α y +
        ((1 / 2 : ℂ) * Complex.I) * lder hw d.toComplexI α y) x z from rfl,
      convOp_lin_apply x hx _ _ _ _ hc1 hs1 hc2 hs2 z]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring

end S14ShiftC

end

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
p2m_open "AutomorphicForm~archFlowAtComplex_mul_comm_of_glArch_eq_one P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex.S14ShiftC"

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) (hw : w.IsComplex)
    (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : U ≤ finiteAdelicGL2Subgroup K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) (hfU : IsBiInvariantUnder K U f) :
    ∃ β βb : AdelicGL2 (𝓞 K) K → ℂ, IsFactorizableTestFn K β ∧ IsBiInvariantUnder K U β ∧
      IsFactorizableTestFn K βb ∧ IsBiInvariantUnder K U βb ∧
      ∀ x : AdelicGL2 (𝓞 K) K → ℂ, Continuous x →
        IsArchSmoothAtComplex hw (convOp K f x) ∧
        archCasimirAtComplex hw (convOp K f x) = convOp K β x ∧
        archCasimirBarAtComplex hw (convOp K f x) = convOp K βb x := by
  obtain ⟨fa, ff, hfa, hffin, hfeq⟩ := hff
  have hgf : Good U ff f := ⟨⟨fa, hfa, hfeq⟩, hfU⟩

  have hg1 : Good U ff (ldel hw .H f) := hgf.ldel hw .H hU
  have hg11 : Good U ff (ldel hw .H (ldel hw .H f)) := hg1.ldel hw .H hU
  have hg2 : Good U ff (ldel hw .Fm f) := hgf.ldel hw .Fm hU
  have hg21 : Good U ff (ldel hw .E (ldel hw .Fm f)) := hg2.ldel hw .E hU

  have hb1 : Good U ff (ldelBar hw .H f) := hgf.ldelBar hw .H hU
  have hb11 : Good U ff (ldelBar hw .H (ldelBar hw .H f)) := hb1.ldelBar hw .H hU
  have hb2 : Good U ff (ldelBar hw .Fm f) := hgf.ldelBar hw .Fm hU
  have hb21 : Good U ff (ldelBar hw .E (ldelBar hw .Fm f)) := hb2.ldelBar hw .E hU

  let β : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
    (-(1 / 4 : ℂ)) * ldel hw .H (ldel hw .H f) y +
      (1 : ℂ) * ((1 / 2 : ℂ) * ldel hw .H f y + (-1 : ℂ) * ldel hw .E (ldel hw .Fm f) y)
  let βb : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
    (-(1 / 4 : ℂ)) * ldelBar hw .H (ldelBar hw .H f) y +
      (1 : ℂ) * ((1 / 2 : ℂ) * ldelBar hw .H f y + (-1 : ℂ) * ldelBar hw .E (ldelBar hw .Fm f) y)
  have hgβ : Good U ff β := Good.lin _ _ hg11 (Good.lin _ _ hg1 hg21)
  have hgβb : Good U ff βb := Good.lin _ _ hb11 (Good.lin _ _ hb1 hb21)
  refine ⟨β, βb, hgβ.isFactorizableTestFn hffin, hgβ.binv, hgβb.isFactorizableTestFn hffin, hgβb.binv,
    fun x hx => ?_⟩
  have hff' : IsFactorizableTestFn K f := hgf.isFactorizableTestFn hffin
  obtain ⟨hsm, -⟩ := isArchSmoothAtComplex_and_archDerivAtComplex_convOp hw .H f hff' x hx
  refine ⟨hsm, ?_, ?_⟩
  ·
    obtain ⟨hD1, -⟩ := archDelAt_convOp_and_archDelBarAt_convOp hw .H f hff' x hx
    obtain ⟨hD11, -⟩ := archDelAt_convOp_and_archDelBarAt_convOp hw .H _ (hg1.isFactorizableTestFn hffin) x hx
    obtain ⟨hD2, -⟩ := archDelAt_convOp_and_archDelBarAt_convOp hw .Fm f hff' x hx
    obtain ⟨hD21, -⟩ := archDelAt_convOp_and_archDelBarAt_convOp hw .E _ (hg2.isFactorizableTestFn hffin) x hx
    obtain ⟨hc11, hs11⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hg11.isFactorizableTestFn hffin)
    obtain ⟨hc1, hs1⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hg1.isFactorizableTestFn hffin)
    obtain ⟨hc21, hs21⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hg21.isFactorizableTestFn hffin)
    have hin : Continuous (fun y => (1 / 2 : ℂ) * ldel hw .H f y + (-1 : ℂ) * ldel hw .E (ldel hw .Fm f) y) ∧
        HasCompactSupport (fun y => (1 / 2 : ℂ) * ldel hw .H f y + (-1 : ℂ) * ldel hw .E (ldel hw .Fm f) y) :=
      ⟨(continuous_const.mul hc1).add (continuous_const.mul hc21), hs1.mul_left.add hs21.mul_left⟩
    rw [archCasimirAtComplex, hD1, hD11, hD2, hD21]
    funext z
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show convOp K β x z = convOp K (fun y => (-(1 / 4 : ℂ)) * ldel hw .H (ldel hw .H f) y +
        (1 : ℂ) * ((1 / 2 : ℂ) * ldel hw .H f y + (-1 : ℂ) * ldel hw .E (ldel hw .Fm f) y)) x z from rfl,
      convOp_lin_apply x hx _ _ _ _ hc11 hs11 hin.1 hin.2 z,
      convOp_lin_apply x hx _ _ _ _ hc1 hs1 hc21 hs21 z]
    ring
  ·
    obtain ⟨-, hD1⟩ := archDelAt_convOp_and_archDelBarAt_convOp hw .H f hff' x hx
    obtain ⟨-, hD11⟩ := archDelAt_convOp_and_archDelBarAt_convOp hw .H _ (hb1.isFactorizableTestFn hffin) x hx
    obtain ⟨-, hD2⟩ := archDelAt_convOp_and_archDelBarAt_convOp hw .Fm f hff' x hx
    obtain ⟨-, hD21⟩ := archDelAt_convOp_and_archDelBarAt_convOp hw .E _ (hb2.isFactorizableTestFn hffin) x hx
    obtain ⟨hc11, hs11⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hb11.isFactorizableTestFn hffin)
    obtain ⟨hc1, hs1⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hb1.isFactorizableTestFn hffin)
    obtain ⟨hc21, hs21⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hb21.isFactorizableTestFn hffin)
    have hin : Continuous (fun y => (1 / 2 : ℂ) * ldelBar hw .H f y + (-1 : ℂ) * ldelBar hw .E (ldelBar hw .Fm f) y) ∧
        HasCompactSupport (fun y => (1 / 2 : ℂ) * ldelBar hw .H f y +
          (-1 : ℂ) * ldelBar hw .E (ldelBar hw .Fm f) y) :=
      ⟨(continuous_const.mul hc1).add (continuous_const.mul hc21), hs1.mul_left.add hs21.mul_left⟩
    rw [archCasimirBarAtComplex, hD1, hD11, hD2, hD21]
    funext z
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show convOp K βb x z = convOp K (fun y => (-(1 / 4 : ℂ)) * ldelBar hw .H (ldelBar hw .H f) y +
        (1 : ℂ) * ((1 / 2 : ℂ) * ldelBar hw .H f y + (-1 : ℂ) * ldelBar hw .E (ldelBar hw .Fm f) y)) x z from rfl,
      convOp_lin_apply x hx _ _ _ _ hc11 hs11 hin.1 hin.2 z,
      convOp_lin_apply x hx _ _ _ _ hc1 hs1 hc21 hs21 z]
    ring

end S_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex
end P2MW
export P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isBiInvariantUnder_forall_archCasimirAtComplex_convOp_eq_convOp_of_isComplex (solution)
