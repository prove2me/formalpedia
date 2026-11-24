-- Prove2me | solution 1 for AAInvW.rightAA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:10:26.23882+00:00
-- url     : https://prove2.me/submissions/ae374abe-c3fb-4768-9778-20cf45ac7904

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdIntertwine
import Theorems.Thm_AAInvW_qminor_intertwine
import Theorems.Thm_AAInvW_herm_mul_bvec
import Theorems.Thm_AAInvW_inv_mul_apply
import Theorems.Thm_AAInvW_ana_mul
import Theorems.Thm_AAInvW_ana_mul_inv
import Theorems.Thm_P2M_AAInvW_smooth_right__23e71241d98e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
namespace AAInvW
theorem _root_.solution (hM : OpModel) (hA : AlgAA) (hAv : AlgAAv) (hH : HpkInvol) (hUH : SsetUH)
    (hIC : SsetInvCol) (hRS : SsetRowStar) : RightAA := by
  unfold RightAA
  intro E _ _ k r z' m hm u ell f s' g hf hs' hg
  obtain ⟨M, cls, Eh, hGl, hQ, hR⟩ := hM E (2 * r + k + 1) (Hpk k r) (hH k r)
  have hsU : inUH (Hpk k r) s' := hUH k r z' s' hs'
  obtain ⟨ρ, hρcls, hρev, hρE⟩ := hR s' hsU
  have hgs : inUH (Hpk k r) (g * s') := ana_mul hg hsU
  have hfs : SmoothOnH (Hpk k r) (fun x => f (x * s')) :=
    smooth_right' _ (Hpk k r) E f s' (hH k r) hsU hf
  have hQP : s' * s'⁻¹ = 1 := ana_mul_inv (hH k r) hsU
  have hint : ∀ {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (w : ℂ),
      qminor Eh a b w * ρ = ρ * qminor (fun i j => ∑ c, ∑ d, (s'⁻¹ c i * s' j d) • Eh c d) a b w :=
    fun a b w => qminor_intertwine Eh _ ρ hρE a b w
  have hev : ∀ {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (w : ℂ),
      qminorOp (EabH (Hpk k r)) a b w (fun x => f (x * s')) g =
        (qminor (fun i j => ∑ c, ∑ d, (s'⁻¹ c i * s' j d) • Eh c d) a b w (cls f)).1
          ⟨g * s', hgs⟩ := by
    intro t a b w
    rw [hQ t a b w _ g hg hfs, hρcls f hf, ← Module.End.mul_apply, hint, Module.End.mul_apply]
    exact hρev _ g hg (g * s') hgs rfl
  have hev2 : ∀ {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (w : ℂ),
      qminorOp (EabH (Hpk k r)) a b w f (g * s') = (qminor Eh a b w (cls f)).1 ⟨g * s', hgs⟩ :=
    fun a b w => hQ _ a b w f (g * s') hgs hf
  have hevsum : ∀ (S : (Fin m → Fin (2 * r + k + 1)) → Prop) [DecidablePred S]
      (α : (Fin m → Fin (2 * r + k + 1)) → ℂ) (T : (Fin m → Fin (2 * r + k + 1)) → Module.End ℂ M),
      ((∑ c, if S c then α c • T c else 0 : Module.End ℂ M) (cls f)).1 ⟨g * s', hgs⟩ =
        ∑ c, if S c then α c • (T c (cls f)).1 ⟨g * s', hgs⟩ else 0 := by
    intro S _ α T
    rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    split_ifs <;> simp
  constructor
  · have hdet : ∀ C : Fin m → Fin (2 * r + k + 1),
        (Matrix.of fun a l : Fin m => ∑ d, s' d (C l) *
          herm (Hpk k r) (g *ᵥ bvec d) (bvec (eI k r (Fin.castLE hm a)))) =
        Matrix.of fun a l : Fin m => herm (Hpk k r) ((g * s') *ᵥ bvec (C l)) (bvec (eI k r (Fin.castLE hm a))) := by
      intro C
      ext a l
      simp only [Matrix.of_apply]
      rw [herm_mul_bvec]
    have hA' := hA (Module.End ℂ M) k r m hm Eh s'⁻¹ s'
      (fun a j => herm (Hpk k r) (g *ᵥ bvec j) (bvec (eI k r (Fin.castLE hm a)))) u hGl hQP
      (hIC k r z' s' hs')
    have h1 := congrArg (fun T : Module.End ℂ M => (T (cls f)).1 ⟨g * s', hgs⟩) hA'
    beta_reduce at h1
    rw [hevsum, hevsum] at h1
    simp only [hdet] at h1
    simp only [AAop, hev, hev2]
    convert h1
  · have hdetv : ∀ C : Fin m → Fin (2 * r + k + 1),
        (Matrix.of fun a l : Fin m => ∑ d, s'⁻¹ (C l) d * (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) d) =
        Matrix.of fun a l : Fin m => ((g * s')⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (C l) := by
      intro C
      ext a l
      simp only [Matrix.of_apply]
      rw [inv_mul_apply]
    have hA' := hAv (Module.End ℂ M) k r m hm Eh s'⁻¹ s'
      (fun a j => (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) j) (ell + (m : ℂ) - 1) hGl hQP
      (hRS k r z' s' hs')
    have h1 := congrArg (fun T : Module.End ℂ M => (T (cls f)).1 ⟨g * s', hgs⟩) hA'
    beta_reduce at h1
    rw [hevsum, hevsum] at h1
    simp only [hdetv] at h1
    simp only [AAvop, hev, hev2]
    convert h1
end AAInvW
