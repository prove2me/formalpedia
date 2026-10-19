-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_OrdinaryStructure
-- name    : OAI_Analysis_BackwardIntertwiners_OrdinaryStructure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:06:43.14607+00:00
-- url     : https://prove2.me/theorems/af3d2f1a-c2d0-4fec-a0cc-884393ec1ed8
-- title:
--   Residue-class indicators and infinite dimensionality of the model Hilbert spaces
-- statement:
--   This file shows that the Hilbert spaces of the model are infinite-dimensional, using indicator functions of residue classes of 2-adic integers. Let $\mathbb{Z}_2$ be the 2-adic integers with completed normalized Haar measure $\mu$ (a probability measure), and for $m\in\mathbb{N}$ let $\rho_m(x)\in\{0,\dots,2^m-1\}$ be the residue of $x$ modulo $2^m$. Write $\mathcal{K}=L^2(\mathbb{Z}_2,\mu;\mathbb{C})$ and $\mathcal{H}=L^2(\mathbb{Z}_2,\mu;\ell^2(\mathbb{Z}))$.
--
--   1. **Residue classes.** For $m,t\in\mathbb{N}$, $C_{m,t}=\{x\in\mathbb{Z}_2\ :\ \rho_m(x)=t\}$. It is measurable, and $\mu(C_{m,t})>0$ whenever $t<2^m$ (it is empty for $t\ge2^m$).
--   2. **Residue indicators.** $\chi_{m,t}=\mathbf{1}_{C_{m,t}}\in\mathcal{K}$, the indicator function of the residue class with value $1$, as an element of $L^2$.
--
--   For fixed $m$ these vectors satisfy
--   $$\chi_{m,t}\ne0\ \ (t<2^m),\qquad \langle\chi_{m,s},\chi_{m,t}\rangle=0\ \ (s\ne t),$$
--   so $\chi_{m,0},\dots,\chi_{m,2^m-1}$ are linearly independent. Since $m$ is arbitrary, $\mathcal{K}$ is infinite-dimensional, and so is $\mathcal{H}$, because $g\mapsto(x\mapsto g(x)\,e_0)$ embeds $\mathcal{K}$ injectively into $\mathcal{H}$, where $e_0$ is the basis sequence with $1$ at position $0$.
--
--   Infinite dimensionality of $\mathcal{H}$, together with its separability, makes $\mathcal{H}$ isometrically isomorphic to any separable infinite-dimensional complex Hilbert space, so the model operator with transitive commutant can be transported to every such space.
--
--   **Formalization Note** The names are `residueClass m t` and `residueIndicator m t` (an `indicatorConstLp`), with lemmas `measurableSet_residueClass`, `residueClass_nonnull`, `residueIndicator_ae`, `residueIndicator_ne_zero`, `residueIndicator_orthogonal`, `residueIndicator_independent` (over the index type `Fin (2^m)`), `scalarHilbert_infinite` and `globalHilbert_infinite`; infinite dimensionality is stated as the negation of `FiniteDimensional`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/OrdinaryStructure.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/OrdinaryStructure.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_GlobalOperators
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ErgodicTransitivity

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

def residueClass (m t : ℕ) : Set Base := {x | residue m x = t}
lemma measurableSet_residueClass (m t : ℕ) : MeasurableSet (residueClass m t) :=
  measurableSet_eq_fun (measurable_residue m) measurable_const
lemma residueClass_nonnull {m t : ℕ} (ht : t < 2^m) : baseMeasure (residueClass m t) ≠ 0 := by
  change baseHaar {x : PadicInt 2 | twoResidue m x = t} ≠ 0
  have hcont : Continuous (twoResidue m) :=
    continuous_of_discreteTopology.comp (continuous_twoResidue m)
  have hOpen : IsOpen {x : PadicInt 2 | twoResidue m x = t} :=
    (isOpen_discrete ({t}:Set ℕ)).preimage hcont
  have hmem : twoResidue m (t : PadicInt 2) = t := by
    simp only [twoResidue, map_natCast]
    exact ZMod.val_natCast_of_lt ht
  exact (hOpen.measure_pos baseHaar ⟨(t : PadicInt 2),hmem⟩).ne'

def residueIndicator (m t : ℕ) : ScalarHilbert :=
  indicatorConstLp 2 (measurableSet_residueClass m t) (measure_ne_top baseMeasure _) (1:ℂ)
lemma residueIndicator_ae (m t : ℕ) : residueIndicator m t =ᵐ[baseMeasure]
    (residueClass m t).indicator (fun _ => (1:ℂ)) := indicatorConstLp_coeFn
lemma residueIndicator_ne_zero {m t : ℕ} (ht : t < 2^m) : residueIndicator m t ≠ 0 := by
  intro hz
  apply residueClass_nonnull ht
  rw [measure_eq_zero_iff_ae_notMem]
  have he := Lp.eq_zero_iff_ae_eq_zero.mp hz
  filter_upwards [he,residueIndicator_ae m t] with x hx hi
  intro hmem
  have h10 : (1:ℂ)=0 := by rw [← Set.indicator_of_mem hmem (fun _ => (1:ℂ)), ← hi]; exact hx
  exact one_ne_zero h10
lemma residueIndicator_orthogonal (m : ℕ) {s t : ℕ} (hst : s ≠ t) :
    inner ℂ (residueIndicator m s) (residueIndicator m t) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [residueIndicator_ae m s, residueIndicator_ae m t] with x hs ht
  rw [hs,ht]
  by_cases hxs : x ∈ residueClass m s
  · have hxt : x ∉ residueClass m t := fun hx => hst (hxs.symm.trans hx)
    simp [Set.indicator_of_notMem hxt]
  · simp [Set.indicator_of_notMem hxs]
lemma residueIndicator_independent (m : ℕ) :
    LinearIndependent ℂ (fun t : Fin (2^m) => residueIndicator m t) := by
  apply linearIndependent_of_ne_zero_of_inner_eq_zero
  · intro t; exact residueIndicator_ne_zero t.isLt
  · intro s t hst
    exact residueIndicator_orthogonal m (fun he => hst (Fin.ext he))
lemma scalarHilbert_infinite : ¬FiniteDimensional ℂ ScalarHilbert := by
  intro hfin
  let := hfin
  have hh := (residueIndicator_independent (Module.finrank ℂ ScalarHilbert + 1)).fintype_card_le_finrank
  simp only [Fintype.card_fin] at hh
  have hlt := Nat.lt_two_pow_self (n:=Module.finrank ℂ ScalarHilbert + 1)
  omega

lemma globalHilbert_infinite : ¬FiniteDimensional ℂ GlobalHilbert := by
  intro hfin
  let := hfin
  apply scalarHilbert_infinite
  apply FiniteDimensional.of_injective (singleL2 0).toLinearMap
  intro f g he
  have he' : singleL2 0 f = singleL2 0 g := he
  simpa only [coordinateL2_singleL2] using congrArg (coordinateL2 0) he'

end
end BackwardIntertwiners

end OAI


