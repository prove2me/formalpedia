-- Prove2me | Definitions.Def_Formalism_AlgebraicWeights_InertDatumExists
-- name    : Formalism_AlgebraicWeights_InertDatumExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:03.556803+00:00
-- url     : https://prove2.me/theorems/e7f9e052-2104-4705-b3d9-cf499e42b26d
-- title:
--   Inert Datum Exists
-- statement:
--   Definitions and structural lemmas for Inert Datum Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/AlgebraicWeights/InertDatumExists.lean

import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial Filter TensorProduct
namespace Formalism.AUTREP
section Inert
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
open ReciprocityTheory.Aut
structure InertDatum (v : HeightOneSpectrum (𝓞 L⁺)) (w : HeightOneSpectrum (𝓞 L)) where
  e : L ⊗[L⁺] v.adicCompletion L⁺ ≃+* w.adicCompletion L
  σw : w.adicCompletion L →+* w.adicCompletion L
  ϖ : w.adicCompletion L
  P : GL (Fin n) (w.adicCompletion L)
  comm : ∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion L⁺) x) = σw (e x)
  unram : Formalism.UG.IsUnramInv ϖ σw (Formalism.UG.qV L⁺ v)
  integ : ∀ x, x ∈ Formalism.UG.tensInt (F := L⁺) (v.adicCompletion L⁺) (Formalism.UG.intOE L) (Formalism.UG.Ov L⁺ v) ↔
    e x ∈ Formalism.UG.intL (w.adicCompletion L)
  Pint : P ∈ (Formalism.UG.bc (n := Fin n) (Formalism.UG.intL (w.adicCompletion L)).subtype).range
  Panti : Formalism.UG.cT σw (P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * (P : Matrix (Fin n) (Fin n) _) =
    Formalism.UG.antiJ (w.adicCompletion L) n
variable {L n}
def InertDatum.loc {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (D : InertDatum L n v w)
    (x : GAf L n) : GL (Fin n) (w.adicCompletion L) :=
  D.P⁻¹ * Formalism.UG.bc (n := Fin n) (D.e : L ⊗[L⁺] v.adicCompletion L⁺ →+* w.adicCompletion L)
    (Matrix.GeneralLinearGroup.map (compAt L v) (x : GL (Fin n) (AL L))) * D.P
open Classical in

def InertDatum.hval {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (D : InertDatum L n v w)
    (h : Formalism.UG.GU D.σw n → ℂ) (y : GL (Fin n) (w.adicCompletion L)) : ℂ :=
  if hy : y ∈ Formalism.UG.GU D.σw n then h ⟨y, hy⟩ else 0
variable (L n)
open Classical in

def heckeFunI {W : Type} [AddCommGroup W] [Module ℂ W] (U : Subgroup (GAf L n))
    {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)} (D : InertDatum L n v w)
    (h : Formalism.UG.GU D.σw n → ℂ) (f : GAf L n → W) : GAf L n → W :=
  fun g => ∑ᶠ c : GAf L n ⧸ U,
    if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
      D.hval h (D.loc hc.choose) • f (g * hc.choose) else 0
open Classical in

def heckeEndI {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W)
    (U : Subgroup (GAf L n)) {v : HeightOneSpectrum (𝓞 L⁺)} {w : HeightOneSpectrum (𝓞 L)}
    (D : InertDatum L n v w) (h : Formalism.UG.GU D.σw n → ℂ) : Module.End ℂ (Forms L n ρ U) :=
  if hφ : ∃ φ : Module.End ℂ (Forms L n ρ U), ∀ f g,
      (φ f : GAf L n → W) g = heckeFunI L n U D h (f : GAf L n → W) g
  then hφ.choose else 0
end Inert
def inertPoly (q n : ℕ) {m : ℕ} (α : Fin m → ℂ) : ℂ[X] :=
  (∏ i, (X - C ((q : ℂ) ^ (n - 1) * α i)) * (X - C ((q : ℂ) ^ (n - 1) * (α i)⁻¹))) *
    (X - C ((q : ℂ) ^ (n - 1))) ^ (n % 2)
def InertDatumExists : Prop :=
  Formalism.UG.InertLocal → Formalism.UG.InertAntidiag →
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], GoodCM L →
  ∀ (n : ℕ) (v : HeightOneSpectrum (𝓞 (NumberField.maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)),
    Formalism.UG.IsInertAt (NumberField.maximalRealSubfield L) L v w → Nonempty (InertDatum L n v w)
end Formalism.AUTREP


