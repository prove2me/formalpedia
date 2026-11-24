-- Prove2me | solution 1 for AAInvW.ana_EcComm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:55:07.487059+00:00
-- url     : https://prove2.me/submissions/8e845b9e-df99-4e70-adf7-24f014eff3df

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
import Theorems.Thm_AAInvW_ana_rdBracket
import Theorems.Thm_AAInvW_ana_add
import Theorems.Thm_AAInvW_ana_bracket
import Theorems.Thm_AAInvW_ana_hpartMem
import Theorems.Thm_AAInvW_ana_hpart_unique
import Theorems.Thm_AAInvW_ana_rdAdd
import Theorems.Thm_AAInvW_ana_rdLin
import Theorems.Thm_AAInvW_ana_rdSmooth
import Theorems.Thm_AAInvW_ana_rdSub
import Theorems.Thm_AAInvW_ana_sub
import Theorems.Thm_Formalism_REAL_commutator_complex_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace AAInvW
theorem _root_.solution (hH : HInvol H) (f : Matrix (Fin n) (Fin n) ℂ → E) (Z W g : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnH H f) (hg : inUH H g) :
    EcH H Z (EcH H W f) g - EcH H W (EcH H Z f) g = EcH H (Z * W - W * Z) f g := by
  obtain ⟨hX1, hX2, hZ, -⟩ := ana_hpartMem hH Z
  obtain ⟨hY1, hY2, hW, -⟩ := ana_hpartMem hH W
  have hEc : ∀ (Z' : Matrix (Fin n) (Fin n) ℂ) (f' : Matrix (Fin n) (Fin n) ℂ → E),
      EcH H Z' f' g = RdV (hpart1 H Z') f' g + Complex.I • RdV (hpart2 H Z') f' g := fun _ _ => rfl
  have hE : ∀ V, inLH H V → ∀ W' : Matrix (Fin n) (Fin n) ℂ,
      RdV V (EcH H W' f) g = RdV V (RdV (hpart1 H W') f) g + Complex.I • RdV V (RdV (hpart2 H W') f) g :=
    fun V hV W' => ana_rdLin hH Complex.I (ana_rdSmooth hH hf (ana_hpartMem hH W').1)
      (ana_rdSmooth hH hf (ana_hpartMem hH W').2.1) hV hg
  have hZW := commutator_complex_expand (hpart1 H Z) (hpart2 H Z) (hpart1 H W) (hpart2 H W)
  rw [← hZ, ← hW] at hZW
  have hP := ana_sub (ana_bracket hX1 hY1) (ana_bracket hX2 hY2)
  have hQ := ana_add (ana_bracket hX1 hY2) (ana_bracket hX2 hY1)
  obtain ⟨h1, h2⟩ := ana_hpart_unique hH hP hQ
  rw [hEc Z, hEc W, hE _ hX1, hE _ hX2, hE _ hY1, hE _ hY2, hZW, hEc, h1, h2,
    ana_rdSub hH hf (ana_bracket hX1 hY1) (ana_bracket hX2 hY2) hg,
    ana_rdAdd hH hf (ana_bracket hX1 hY2) (ana_bracket hX2 hY1) hg,
    ← ana_rdBracket hH hf hX1 hY1 hg, ← ana_rdBracket hH hf hX2 hY2 hg,
    ← ana_rdBracket hH hf hX1 hY2 hg, ← ana_rdBracket hH hf hX2 hY1 hg]
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  abel
end AAInvW
