-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:51.61481+00:00
-- url     : https://prove2.me/theorems/380c4c2f-745e-4f45-82f7-88e624a06d7c
-- title:
--   Dedekind Factor K
-- statement:
--   Definitions and structural lemmas for Dedekind Factor K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/DedekindFactorK.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DedekindFactorization_OmegaPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
def eisG (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)
def g2 (Λ : AddSubgroup ℂ) : ℂ := 60 * eisG Λ 2
def g3 (Λ : AddSubgroup ℂ) : ℂ := 140 * eisG Λ 3
def discr (Λ : AddSubgroup ℂ) : ℂ := g2 Λ ^ 3 - 27 * g3 Λ ^ 2
def area (Λ : AddSubgroup ℂ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, a = |((starRingEnd ℂ) w₁ * w₂).im|}
def liftM (M : IntermediateField ℚ ℂ) (x : ℂ) : M := if h : x ∈ M then ⟨x, h⟩ else 0
def KroneckerLimit : Prop :=
  ∀ τ : ℂ, 0 < τ.im → ∃ C ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 1 < s → s < 1 + ε →
    |(∑' p : ℤ × ℤ, if p = 0 then (0 : ℝ) else τ.im ^ s / ‖(p.1 : ℂ) * τ + (p.2 : ℂ)‖ ^ (2 * s))
        - Real.pi / (s - 1)
        - 2 * Real.pi * (Real.eulerMascheroniConstant - Real.log 2
            - Real.log (Real.sqrt τ.im * ‖ModularForm.eta τ‖ ^ 2))| ≤ C * (s - 1)
def latI {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (δ : ℂ) :
    AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ 𝔞, w = δ * φ (c : K)}
def logDerivLOne (d : ℕ) [Fact d.Prime] : ℝ :=
  haveI : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
  (deriv (DirichletCharacter.LFunction (chiD d)) 1 /
    DirichletCharacter.LFunction (chiD d) 1).re
def DedekindFactorK (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] : Prop :=
  ∀ s : ℂ, 1 < s.re →
    NumberField.dedekindZeta K s =
      riemannZeta s * (haveI : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩
        DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) s)
def epst (Λ : AddSubgroup ℂ) (s : ℝ) : ℝ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, ‖(w : ℂ)‖ ^ (-(2 * s))
def yEta4 (z : ℂ) : ℝ := z.im * ‖ModularForm.eta z‖ ^ 4
def clsI {K : Type} [Field K] [NumberField K] (J : Ideal (𝓞 K)) : ClassGroup (𝓞 K) :=
  if h : J ∈ nonZeroDivisors (Ideal (𝓞 K)) then ClassGroup.mk0 ⟨J, h⟩ else 1
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5


