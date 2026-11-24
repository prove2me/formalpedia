-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_Ucoord
-- name    : ReciprocityTheory_Chebotarev_Ucoord
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:12.295806+00:00
-- url     : https://prove2.me/theorems/001b9127-f896-4d66-8143-c708ea07a538
-- title:
--   Ucoord
-- statement:
--   Definitions and structural lemmas for Ucoord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/Ucoord.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
namespace ReciprocityTheory.Cheb
noncomputable section
open scoped Classical
variable {E : Type} [Field E] [NumberField E]
def ucoord (x : mixedSpace E) : Fin (rank E) → ℝ :=
  fun i => ((basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)).repr (logMap x) i
def uphi (x : mixedSpace E) : ℝ :=
  if mixedEmbedding.norm x = 0 then 0 else Tent (ucoord x)
def rsgn (x : mixedSpace E) : ℤ :=
  ∏ w : {w : InfinitePlace E // w.IsReal}, ((SignType.sign (x.1 w) : SignType) : ℤ)
def Gs {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ) (x : mixedSpace E) : ℂ :=
  χ (rsgn x : ZMod l) * (uphi x : ℂ) * ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (-(s : ℂ))
def embZ : 𝓞 E →ₗ[ℤ] mixedSpace E :=
  ((mixedEmbedding E).comp (algebraMap (𝓞 E) E)).toIntAlgHom.toLinearMap
def latOf (I : Ideal (𝓞 E)) : Submodule ℤ (mixedSpace E) :=
  Submodule.map (embZ (E := E)) (I.restrictScalars ℤ)
def mbc (l : ℕ) (b c : Ideal (𝓞 E)) : Ideal (𝓞 E) :=
  Ideal.span {((l * Ideal.absNorm b : ℕ) : 𝓞 E)} * b * c
def cls (a : NZIdeal E) : ClassGroup (𝓞 E) :=
  ClassGroup.mk0 ⟨a.1, mem_nonZeroDivisors_of_ne_zero a.2⟩
def preZ (x : mixedSpace E) : 𝓞 E := Function.invFun (embZ (E := E)) x
def cfun {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : Ideal (𝓞 E)) (x : mixedSpace E) : ℂ :=
  χ (((Algebra.norm ℤ (preZ x) / (Ideal.absNorm b : ℤ) : ℤ)) : ZMod l) *
    (1 - (Ideal.absNorm c : ℂ) * (if preZ x ∈ b * c then 1 else 0))
end
end ReciprocityTheory.Cheb


