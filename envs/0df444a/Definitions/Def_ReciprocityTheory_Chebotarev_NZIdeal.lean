-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
-- name    : ReciprocityTheory_Chebotarev_NZIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:25.859152+00:00
-- url     : https://prove2.me/theorems/ad26cad7-68d4-4446-9b6e-4ad2afa51bc5
-- title:
--   NZIdeal
-- statement:
--   Definitions and structural lemmas for NZIdeal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/NZIdeal.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace ReciprocityTheory.Cheb
noncomputable section
abbrev NZIdeal (E : Type) [Field E] [NumberField E] : Type := {a : Ideal (𝓞 E) // a ≠ ⊥}
abbrev Prm (E : Type) [Field E] [NumberField E] : Type := IsDedekindDomain.HeightOneSpectrum (𝓞 E)
def Nrm {E : Type} [Field E] [NumberField E] (q : Prm E) : ℕ := Ideal.absNorm q.asIdeal
def Lser (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' a : NZIdeal E, χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))
def Psum (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' q : Prm E, χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))
def abelian₂ (E : Type) [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) : ℂ :=
  ∑' q : Prm E, -Complex.log (1 - χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))
def PE (E : Type) [Field E] [NumberField E] (s : ℝ) : ℝ :=
  ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-s)
def Pcl (E : Type) [Field E] [NumberField E] (l : ℕ) (a : ZMod l) (s : ℝ) : ℝ :=
  ∑' q : Prm E, if ((Nrm q : ℕ) : ZMod l) = a then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0
end
end ReciprocityTheory.Cheb


