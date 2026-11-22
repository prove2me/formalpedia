-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:24:52.567823+00:00
-- url     : https://prove2.me/theorems/41aaa8aa-268f-4a6c-8166-bb7dc391898f
-- title:
--   One Lt Abs Norm Real
-- statement:
--   Definitions and structural lemmas for One Lt Abs Norm Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean

import Mathlib
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
open IsDedekindDomain NumberField
open scoped WithZero
namespace Formalism.L2.Pj
section Base
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]
def vLa (la : HeightOneSpectrum R) (x : K) : ℤ := -WithZero.log (la.valuation K x)
end Base
section Dvr
variable (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
def valV : Valuation K' ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal V).valuation K'
def vV (x : K') : ℤ := -WithZero.log (valV V x)
variable {V}
variable (V)
def nval (e : ℕ) (x : K') : EReal :=
  open Classical in if x = 0 then ⊤ else (((vV V x : ℝ) / e : ℝ) : EReal)
variable {V}
end Dvr
structure CDVR where

  V : Type
  [cr : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [cpl : IsAdicComplete (IsLocalRing.maximalIdeal V) V]
  [ch0 : CharZero V]
attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0
abbrev CDVR.Fr (T : CDVR) : Type := FractionRing T.V
def CDVR.FinRes (T : CDVR) : Prop := Finite (IsLocalRing.ResidueField T.V)
section Over
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]
def OverLa (la : HeightOneSpectrum R) (V : Type) {K' : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K'] (ι : K →+* K')
    (e : ℕ) : Prop :=
  0 < e ∧ ∀ a : K, vV V (ι a) = (e : ℤ) * vLa la a
variable {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K']
structure IsEval {W : Type} {Cusp : W → Type} [∀ w, AddCommGroup (Cusp w)] [∀ w, Module K (Cusp w)]
    (wadd : W → W → W) (mulC : ∀ w w', Cusp w → Cusp w' → Cusp (wadd w w')) {F : Type} [Field F]
    (ι : K →+* F) (ev : ∀ w, Cusp w → F) : Prop where
  add : ∀ w f g, ev w (f + g) = ev w f + ev w g
  smul : ∀ w (a : K) f, ev w (a • f) = ι a * ev w f
  mul : ∀ w w' f g, ev (wadd w w') (mulC w w' f g) = ev w f * ev w' g
end Over
section Norm
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
def nrmOf (v : EReal) : ℝ :=
  open Classical in if v = ⊤ then 0 else (Ideal.absNorm la.asIdeal : ℝ) ^ (-v.toReal)
end Norm
end Formalism.L2.Pj


