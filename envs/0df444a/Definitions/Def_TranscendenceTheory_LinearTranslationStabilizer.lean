-- Prove2me | Definitions.Def_TranscendenceTheory_LinearTranslationStabilizer
-- name    : TranscendenceTheory_LinearTranslationStabilizer
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-20T06:08:07.781281+00:00
-- url     : https://prove2.me/theorems/5d0b6694-2ad5-4810-b16d-90eedd22037e
-- title:
--   Complex translation directions and their image in the period quotient
-- statement:
--   For a subset $W\subseteq\mathbb C^3$, define its complex translation directions by
--
--   $$
--   V_W=\{v\in\mathbb C^3:\ w+tv\in W\text{ for all }t\in\mathbb C
--   \text{ and all }w\in W\}.
--   $$
--
--   This is a complex linear subspace. For an integer submodule $\Lambda\subseteq\mathbb C$ and an integer-linear map $\eta:\Lambda\to\mathbb C$, put
--
--   $$
--   G=\mathbb C\times\bigl(\mathbb C^2/\{(\omega,-\eta(\omega)):\omega\in\Lambda\}\bigr),
--   \qquad q(v)=(v_0,[(v_1,v_2)]),\qquad H_W=q(V_W).
--   $$
--
--   The definitions provide the covering map $q$ as an integer-linear map and its image $H_W$ as an integer submodule. They give a concrete candidate subgroup attached to a locus. They impose no algebraicity, smoothness, degree, or multiplicity assumptions, and do not identify $H_W$ with the identity component of an algebraic stabilizer. Such an identification, when needed for a zero estimate, is a theorem obligation.
--
--   This is an analytic-coordinate construction associated with the stabilizer used in [Philippon (1986), §5, p. 380, before Lemma 5.1](https://www.numdam.org/item/10.24033/bsmf.2060.pdf), specialized to the covering space in Appendix A, §A.2 of [Senthil Kumar (2026)](https://doi.org/10.1017/S001309152610145X).
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2 and section A.2. https://doi.org/10.1017/S001309152610145X. Specialized covering-space translation-direction construction; no algebraic-stabilizer identification is assumed. Uniform locus selection and its multiplicity bound remain open.

import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Pi

noncomputable section
namespace TranscendenceTheory

/-- Complex directions whose every scalar multiple preserves a locus by translation.
This is a concrete linear subspace; no algebraic or Lie group identification is assumed. -/
def linearTranslationDirections (W : Set (Fin 3 → ℂ)) : Submodule ℂ (Fin 3 → ℂ) where
  carrier := {v | ∀ t : ℂ, ∀ w ∈ W, w + t • v ∈ W}
  zero_mem' := by intro t w hw; simpa using hw
  add_mem' := by
    intro v u hv hu t w hw
    simpa only [smul_add, add_assoc] using hu t (w + t • v) (hv t w hw)
  smul_mem' := by
    intro c v hv t w hw
    simpa only [smul_smul] using hv (t * c) w hw

/-- The additive covering map for the mission's explicit period quotient. -/
def extensionCoveringMap (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) :
    (Fin 3 → ℂ) →ₗ[ℤ] GraphExtensionGroup Λ η :=
  (LinearMap.proj 0).prod
    ((extensionPeriodGraph Λ η).mkQ.comp ((LinearMap.proj 1).prod (LinearMap.proj 2)))

/-- The image of all complex translation directions of a locus in the period quotient. -/
def linearTranslationImage (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (W : Set (Fin 3 → ℂ)) : Submodule ℤ (GraphExtensionGroup Λ η) :=
  ((linearTranslationDirections W).restrictScalars ℤ).map (extensionCoveringMap Λ η)

end TranscendenceTheory


