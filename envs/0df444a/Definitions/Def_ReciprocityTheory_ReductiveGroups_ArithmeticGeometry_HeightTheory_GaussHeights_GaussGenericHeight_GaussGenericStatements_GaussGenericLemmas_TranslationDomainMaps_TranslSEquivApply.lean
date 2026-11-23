-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:34.431125+00:00
-- url     : https://prove2.me/theorems/1ca56fa3-c013-4c0a-ab26-6c8a8d0d8c29
-- title:
--   Transl SEquiv Apply
-- statement:
--   Definitions and structural lemmas for Transl SEquiv Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericLemmas/TranslationDomainMaps/TranslSEquivApply.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_MapDomainMemOfDvd
import Theorems.Thm_BlockPoly_translEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply


set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
namespace GaussGen
open MvPolynomial NumberField BlockPoly
section Img
variable {Ω : Type} [Field Ω] {D N : ℕ}
noncomputable def Pimg (j₀ : Fin (N + 1)) (x : Fin N → Ω) (p : TVar D N) :
    MvPolynomial (SVar D N) Ω :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) Ω) j₀
      (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
      (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2
def blk : SVar D N → Fin (D + 1)
  | Sum.inl _ => 0
  | Sum.inr q => q.1
def col (j₀ : Fin (N + 1)) : SVar D N → Fin (N + 1)
  | Sum.inl _ => j₀
  | Sum.inr q => j₀.succAbove q.2
def cS (b : Fin (D + 1)) (μ : Ω) : SVar D N → Ω := fun s => if blk s = b then μ else 1
def eS (e : Equiv.Perm (Fin (D + 1))) : SVar D N ≃ SVar D N :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.prodCongr e (Equiv.refl (Fin N)))
noncomputable def translS (j₀ : Fin (N + 1)) (a : Fin (N + 1) → Ω) :
    MvPolynomial (SVar D N) Ω →ₐ[Ω] MvPolynomial (SVar D N) Ω :=
  aeval fun s => if blk s = 0 then X s + C (a (col j₀ s)) else X s
theorem translS_X (j₀ : Fin (N + 1)) (a : Fin (N + 1) → Ω) (s : SVar D N) :
    translS j₀ a (X s) = if blk s = 0 then X s + C (a (col j₀ s)) else X s := by
  show aeval _ (X s) = _
  rw [aeval_X]
noncomputable def translSEquiv (j₀ : Fin (N + 1)) (a : Fin (N + 1) → Ω) :
    MvPolynomial (SVar D N) Ω ≃ₐ[Ω] MvPolynomial (SVar D N) Ω :=
  AlgEquiv.ofAlgHom (translS j₀ a) (translS j₀ (-a))
    (algHom_ext fun s => by by_cases h : blk s = 0 <;> simp [translS_X, h])
    (algHom_ext fun s => by by_cases h : blk s = 0 <;> simp [translS_X, h])
end Img
section Stab
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)
end Stab
end GaussGen
end ReciprocityTheory.ChartRestriction.G.T0


