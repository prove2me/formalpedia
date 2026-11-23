-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OffBaseSubstitution
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OffBaseSubstitution
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:34.259467+00:00
-- url     : https://prove2.me/theorems/7eb62397-399f-4230-8371-8f272f3f13c9
-- title:
--   Off Base Substitution
-- statement:
--   Definitions and structural lemmas for Off Base Substitution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/OffBaseSubstitution.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteDimensionalOfLiftY
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
namespace FractionFieldVariableLift
def eT (D N : ℕ) : TVar D N ≃ Fin (N + 1) ⊕ {v : TVar D N // v.1 ≠ 0} where
  toFun v := if h : v.1 = 0 then Sum.inl v.2 else Sum.inr ⟨v, h⟩
  invFun := Sum.elim (fun j => ((0 : Fin (D + 1)), j)) Subtype.val
  left_inv v := by
    by_cases h : v.1 = 0
    · simp only [h, dite_true, Sum.elim_inl]; exact Prod.ext h.symm rfl
    · simp [h]
  right_inv s := by
    rcases s with j | ⟨v, hv⟩
    · simp
    · simp [hv]
noncomputable def eS (D N : ℕ) (j0 : Fin (N + 1)) :
    SVar D N ≃ Fin (N + 1) ⊕ ({i : Fin (D + 1) // i ≠ 0} × Fin N) where
  toFun s := match s with
    | Sum.inl _ => Sum.inl j0
    | Sum.inr p => if h : p.1 = 0 then Sum.inl (j0.succAbove p.2) else Sum.inr (⟨p.1, h⟩, p.2)
  invFun t := match t with
    | Sum.inl j => if h : j = j0 then Sum.inl () else Sum.inr (0, (Fin.exists_succAbove_eq h).choose)
    | Sum.inr q => Sum.inr (q.1.1, q.2)
  left_inv s := by
    rcases s with u | ⟨i, k⟩
    · simp
    · by_cases h : i = 0
      · subst h
        have hne : j0.succAbove k ≠ j0 := Fin.succAbove_ne j0 k
        simp only [dite_true, hne, dite_false]
        congr
        exact Fin.succAbove_right_injective (Fin.exists_succAbove_eq hne).choose_spec
      · simp [h]
  right_inv t := by
    rcases t with j | ⟨⟨i, hi⟩, k⟩
    · by_cases h : j = j0
      · subst h; simp
      · simp only [h, dite_false, dite_true]
        exact congrArg Sum.inl (Fin.exists_succAbove_eq h).choose_spec
    · simp [hi]
noncomputable def hL (K : Type) [Field K] (D N : ℕ) :
    KTp K D N ≃+* MvPolynomial (Fin (N + 1)) (MvPolynomial {v : TVar D N // v.1 ≠ 0} K) :=
  (MvPolynomial.renameEquiv K (eT D N)).toRingEquiv.trans (MvPolynomial.sumRingEquiv K _ _)
noncomputable def hE (Ω : Type) [Field Ω] (D N : ℕ) (j0 : Fin (N + 1)) :
    MvPolynomial (SVar D N) Ω ≃+*
      MvPolynomial (Fin (N + 1)) (MvPolynomial ({i : Fin (D + 1) // i ≠ 0} × Fin N) Ω) :=
  (MvPolynomial.renameEquiv Ω (eS D N j0)).toRingEquiv.trans (MvPolynomial.sumRingEquiv Ω _ _)
variable {K : Type} [Field K] {Ω : Type} [Field Ω] {D N : ℕ}
end FractionFieldVariableLift
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
namespace Data
variable (d : Data K ι Ω WT A)
noncomputable def offBaseSubstitution (c : ι) :
    MvPolynomial {v : TVar d.D d.N // v.1 ≠ 0} K →ₐ[K]
      MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c) :=
  MvPolynomial.aeval fun v =>
    Fin.succAboveCases (α := fun _ => MvPolynomial ({i : Fin (d.D + 1) // i ≠ 0} × Fin d.N) (Ω c))
      (d.jc c) (-∑ k, MvPolynomial.X (⟨v.1.1, v.2⟩, k) * MvPolynomial.C (d.x c k))
      (fun k => MvPolynomial.X (⟨v.1.1, v.2⟩, k)) v.1.2
end Data
end ReciprocityTheory.ChartRestriction.G.T0


