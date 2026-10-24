-- Prove2me | Definitions.Def_OAIQWST001
-- name    : OAIQWST001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T19:27:36.473883+00:00
-- url     : https://prove2.me/theorems/96859d50-a267-466b-8ed6-95b0b54ae263
-- title:
--   OpenAI split tangent bundles split: definitions bundle OAIQWST001
-- statement:
--   One of the three definitions bundles (`OAIQWST000`, `OAIQWST001`, `OAIQWST002`) of the split of OpenAI's proof that both summands of a holomorphic splitting of the tangent bundle of a rationally connected projective manifold are integrable (`OAI.SplitTangent.integrability_main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Geometry/SplitTangent` (OpenAI, *Integrability of split tangent bundles on rationally connected manifolds*, OpenAI Math Release, September 23, 2026, result family 052, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. The bundles split the material only to keep each one within the platform's compile limits.
--
--   The definitions of the published statement (`ComplexManifold`, `ProjectiveEmbedding`, `RationalCurve`, `RationallyConnected`, `TangentSplitting`, `Integrable` and the rest) are not repeated: every bundle imports them from the published bundle `Def_SplitTangentIntegrability`. It imports no other bundle of this split..
--
--   Modules (some only in part): `BoxTransportBase`, `FormalBoxes`, `RationalReparam`, `RationalTrivialization`.
--
--   The theorems the definitions do not need are proved in the four solutions of this split: three prove the published intermediate statements `OAI.SplitTangent.TangentSplitting.exists_projective_tangent_box`, `OAI.SplitTangent.RationalFamily.integrable_both_of_submersive` and `OAI.SplitTangent.RationallyConnected.exists_submersive_familyAlternative`, and the fourth proves `OAI.SplitTangent.integrability_main` from them. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Integrability of split tangent bundles on rationally connected manifolds, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 052; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integrability-of-split-tangent-bundles-on-rationally-connected-manifolds-September-23-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/SplitTangent at commit adc7f12

import Mathlib
import Definitions.Def_SplitTangentIntegrability

section
-- module Solutions.OAIQW_SplitTangent.RationalTrivialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Trivialization. -/

noncomputable section
universe u
open Filter Topology Set Bundle
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace SplitTangent.PullbackConnection
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]



def coefficient (P : E → E →L[ℂ] E) (g : ℂ → E) (z : ℂ) : E →L[ℂ] E :=
  (fderiv ℂ P (g z)).flip (deriv g z)

 
def covariantDerivative (P : E → E →L[ℂ] E) (g v : ℂ → E) (z : ℂ) : E :=
  P (g z) (deriv v z) + P (g z) (coefficient P g z (v z))

lemma coefficient_analyticAt {P : E → E →L[ℂ] E} {g : ℂ → E} {z : ℂ}
    (hP : AnalyticAt ℂ P (g z)) (hg : AnalyticAt ℂ g z) :
    AnalyticAt ℂ (coefficient P g) z := by
  have ha : AnalyticAt ℂ (fun w => (fderiv ℂ P (g w)).flip) z :=
    ((ContinuousLinearMap.flipₗᵢ (𝕜 := ℂ) (E := E) (Fₗ := E) (Gₗ := E)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
      (hP.fderiv.comp hg)
  exact (ha.contDiffAt.clm_apply hg.deriv.contDiffAt).analyticAt


def familyCoefficient (P : E → E →L[ℂ] E) (F : ℂ × ℂ → E) (w : ℂ × ℂ) : E →L[ℂ] E :=
  (fderiv ℂ P (F w)).flip (fderiv ℂ F w (0,1))

lemma familyCoefficient_analyticAt {P : E → E →L[ℂ] E} {F : ℂ × ℂ → E} {w : ℂ × ℂ}
    (hP : AnalyticAt ℂ P (F w)) (hF : AnalyticAt ℂ F w) :
    AnalyticAt ℂ (familyCoefficient P F) w := by
  have ha : AnalyticAt ℂ (fun w => (fderiv ℂ P (F w)).flip) w :=
    ((ContinuousLinearMap.flipₗᵢ (𝕜 := ℂ) (E := E) (Fₗ := E) (Gₗ := E)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
      (hP.fderiv.comp hF)
  have hb : AnalyticAt ℂ (fun w => fderiv ℂ F w (0,1)) w :=
    ((ContinuousLinearMap.apply ℂ E (E := ℂ × ℂ)).analyticAt_bilinear _).comp
      (analyticAt_const.prod hF.fderiv)
  exact (ha.contDiffAt.clm_apply hb.contDiffAt).analyticAt

omit [CompleteSpace E] in
lemma familyCoefficient_eq {P : E → E →L[ℂ] E} {F : ℂ × ℂ → E} {s t : ℂ}
    (hF : DifferentiableAt ℂ F (s,t)) :
    familyCoefficient P F (s,t) = coefficient P (fun v => F (s,v)) t := by
  have hd := hF.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  have hd' : HasDerivAt (fun v => F (s,v)) (fderiv ℂ F (s,t) (0,1)) t := hd
  simp only [familyCoefficient,coefficient,hd'.deriv]

end

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

 

omit [CompleteSpace E] in
theorem covariantDerivative_naturality
    {P : E → E →L[ℂ] E} {Q : F → F →L[ℂ] F} {φ : E → F}
    {g v : ℂ → E} {z : ℂ}
    (hP : DifferentiableAt ℂ P (g z)) (hQ : DifferentiableAt ℂ Q (φ (g z)))
    (hφ : AnalyticAt ℂ φ (g z)) (hg : DifferentiableAt ℂ g z)
    (hv : DifferentiableAt ℂ v z)
    (hnat : ∀ᶠ y in 𝓝 (g z), ∀ w : E,
      Q (φ y) (fderiv ℂ φ y w) = fderiv ℂ φ y (P y w))
    (hvel : P (g z) (deriv g z) = 0)
    (hid : ∀ w : F, Q (φ (g z)) (Q (φ (g z)) w) = Q (φ (g z)) w) :
    covariantDerivative Q (φ ∘ g) (fun t => fderiv ℂ φ (g t) (v t)) z =
      fderiv ℂ φ (g z) (covariantDerivative P g v z) := by
  let G := fderiv ℂ φ
  have hG : DifferentiableAt ℂ G (g z) := hφ.fderiv.differentiableAt
  have hφd := hφ.differentiableAt.hasFDerivAt
  have he : (fun y => Q (φ y) (G y (deriv g z))) =ᶠ[𝓝 (g z)]
      (fun y => G y (P y (deriv g z))) := hnat.mono fun y hy => hy _
  have hl := (hQ.hasFDerivAt.comp (g z) hφd).clm_apply
    (hG.hasFDerivAt.clm_apply (hasFDerivAt_const (deriv g z) (g z)))
  have hr := hG.hasFDerivAt.clm_apply
    (hP.hasFDerivAt.clm_apply (hasFDerivAt_const (deriv g z) (g z)))
  have hd := hl.unique (hr.congr_of_eventuallyEq he)
  have hde := congrArg (fun A : E →L[ℂ] F => A (v z)) hd
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,zero_apply,map_zero,add_zero,hvel] at hde
  have hsym := hφ.contDiffAt.isSymmSndFDerivAt_of_omega (v z) (deriv g z)
  have hzero := congrArg (Q (φ (g z))) hde
  simp only [G,Function.comp_apply,map_add,hid,hnat.self_of_nhds,zero_add] at hzero
  have hdg := (hφd.comp_hasDerivAt z hg.hasDerivAt).deriv
  have hdv := ((hG.hasFDerivAt.comp_hasDerivAt z hg.hasDerivAt).clm_apply
    hv.hasDerivAt).deriv
  simp only [G,Function.comp_apply] at hdv
  unfold covariantDerivative coefficient
  rw [hdg,hdv]
  simp only [Function.comp_apply,ContinuousLinearMap.flip_apply,map_add,
    hnat.self_of_nhds]
  change Q (φ (g z)) ((fderiv ℂ G (g z) (deriv g z)) (v z)) +
      G (g z) (P (g z) (deriv v z)) +
      Q (φ (g z)) ((fderiv ℂ Q (φ (g z)) (G (g z) (v z))) (G (g z) (deriv g z))) =
      G (g z) (P (g z) (deriv v z)) +
      G (g z) (P (g z) ((fderiv ℂ P (g z) (v z)) (deriv g z)))
  rw [show (fderiv ℂ G (g z) (deriv g z)) (v z) =
    (fderiv ℂ G (g z) (v z)) (deriv g z) from hsym.symm]
  calc
    _ = G (g z) (P (g z) (deriv v z)) +
        (Q (φ (g z)) ((fderiv ℂ G (g z) (v z)) (deriv g z)) +
          Q (φ (g z)) ((fderiv ℂ Q (φ (g z)) (G (g z) (v z))) (G (g z) (deriv g z)))) := by abel
    _ = _ := by rw [hzero]

end SplitTangent.PullbackConnection

open Filter Topology Set

namespace SplitTangent.PullbackConnection

open Filter Topology Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
omit [CompleteSpace E] in
lemma covariantDerivative_congr {P : E → E →L[ℂ] E} {g f h : ℂ → E} {z : ℂ}
    (he : f =ᶠ[𝓝 z] h) : covariantDerivative P g f z=covariantDerivative P g h z := by
  simp only [covariantDerivative,he.deriv_eq,he.self_of_nhds]



end SplitTangent.PullbackConnection

open scoped Manifold LinearAlgebra.Projectivization
open Bundle

namespace SplitTangent.PullbackConnection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma covariantDerivative_curve_congr {P : E → E →L[ℂ] E} {g h v : ℂ → E} {z : ℂ}
    (he : g =ᶠ[𝓝 z] h) : covariantDerivative P g v z=covariantDerivative P h v z := by
  simp only [covariantDerivative,coefficient,he.eq_of_nhds,he.deriv_eq]
end SplitTangent.PullbackConnection

open Filter Topology

namespace SplitTangent.PullbackConnection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 
lemma covariantDerivative_reparam {P : E → E →L[ℂ] E} {g s : ℂ → E} {k : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g (k z)) (hs : DifferentiableAt ℂ s (k z))
    (hk : DifferentiableAt ℂ k z) :
    covariantDerivative P (g ∘ k) (s ∘ k) z =
      deriv k z • covariantDerivative P g s (k z) := by
  have hg' := (hg.hasDerivAt.scomp z hk.hasDerivAt).deriv
  have hs' := (hs.hasDerivAt.scomp z hk.hasDerivAt).deriv
  simp only [covariantDerivative,coefficient,Function.comp_apply,hg',hs',
    ContinuousLinearMap.flip_apply,map_smul,smul_apply,smul_add]

end SplitTangent.PullbackConnection

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.BoxTransportBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Box Transport Base. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle
universe u

namespace SplitTangent.ReciprocalCharts

def torus : Set (ℂ × ℂ) := {w | w.1 ≠ 0 ∧ w.2 ≠ 0}

def coord (b : Bool) (z : ℂ) : ℂ := if b then z⁻¹ else z
def scale (b : Bool) (z : ℂ) : ℂ := if b then -(z^2)⁻¹ else 1
def changeChart (b c : Bool) (w : ℂ × ℂ) : ℂ × ℂ := (coord b w.1,coord c w.2)


def overlap (a b c d : Bool) : Set (ℂ × ℂ) :=
  {w | (a ≠ c → w.1 ≠ 0) ∧ (b ≠ d → w.2 ≠ 0)}

end SplitTangent.ReciprocalCharts

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.FormalBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Formal Boxes. -/

noncomputable section
open scoped Manifold ContDiff LinearAlgebra.Projectivization
open Set Bundle Filter Topology
universe u
open Set Filter Topology

namespace SplitTangent
open PowerSeries
variable {X : ComplexManifold.{u}}



theorem projectiveCoordinates_mul {N : ℕ} (p : ProjectiveSpace N)
    (k l j : Fin (N+1)) (hl : p.rep l ≠ 0) :
    projectiveCoordinates k p l * projectiveCoordinates l p j = projectiveCoordinates k p j := by
  simp only [projectiveCoordinates]
  calc
    (p.rep k)⁻¹ * p.rep l * ((p.rep l)⁻¹ * p.rep j) =
      (p.rep k)⁻¹ * (p.rep l * (p.rep l)⁻¹) * p.rep j := by ring
    _ = _ := by rw [mul_inv_cancel₀ hl,mul_one]


end SplitTangent

open Filter Topology

section FiniteBaseImport
open Polynomial
namespace SplitTangent.RationalSurface

abbrev K := RatFunc ℂ
local instance formalBoxesDecidableEqRatFunc : DecidableEq K := Classical.decEq K

abbrev R := Polynomial ℂ
abbrev B := Polynomial R

def eval (p : B) (w : ℂ × ℂ) : ℂ := p.eval₂ (Polynomial.evalRingHom w.1) w.2

end SplitTangent.RationalSurface

end FiniteBaseImport

open Filter Topology

open Filter Topology Metric Set

 

open MvPowerSeries

open Filter Topology Set Metric

namespace SplitTangent.RationalSurface
open Polynomial

 
def RationalOn (U : Set (ℂ × ℂ)) (f : ℂ × ℂ → ℂ) : Prop :=
  ∃ A D : B, ∀ w ∈ U, eval D w ≠ 0 ∧ f w * eval D w = eval A w

lemma RationalOn.fst (U : Set (ℂ × ℂ)) : RationalOn U Prod.fst := by
  refine ⟨C X,1,?_⟩
  intro w hw; simp [eval]

lemma RationalOn.snd (U : Set (ℂ × ℂ)) : RationalOn U Prod.snd := by
  refine ⟨X,1,?_⟩
  intro w hw; simp [eval]

end SplitTangent.RationalSurface

end

end OAI
end

section
-- module Solutions.OAIQW_SplitTangent.RationalReparam
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Reparam. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent.RationalCurve
variable {X : ComplexManifold.{u}} (g : RationalCurve X)

 
def homogeneousValue (a b : ℂ) : X.Carrier :=
  if b=0 then g.infinity 0 else g.finite (a/b)

end SplitTangent.RationalCurve

end

end OAI
end


