-- Prove2me | Definitions.Def_mme_stothers_phi116_outer_grading
-- name    : mme_stothers_phi116_outer_grading
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T19:24:28.614434+00:00
-- url     : https://prove2.me/theorems/83c3857b-6b31-425e-9022-ec627e878b9c
-- title:
--   Literal outer three-grading of the Davie--Stothers phi_116 constituent
-- statement:
--   Let $\varphi_{116}$ be the literal $(1,1,6)$ constituent of $CW_6^{\otimes4}$. This module defines its canonical coordinate basis and the outer three-grading used in the Davie--Stothers recursive extraction. In the first two modes, coarse grade $1$ is refined by whether the first square factor has grade $0$ or $1$; in the third mode, coarse grade $6$ is refined by first-factor grades $4$, $2$, and $3$.
--
--   The construction acts on the actual graded block of the fourth tensor power and retains its nested coordinate subspaces. It does not replace the constituent by an external direct sum. This supplies the common literal grading needed for the four component restrictions and the subsequent address-level hashing argument.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21 and its proof, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_stothers_fourth_data

open MME TensorProduct Module

universe u

namespace MME.StothersFourth.Phi116

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

/-- Canonical fourth-power coordinates at `q = 6`. -/
abbrev FourthIndex : Type :=
  (Fin 8 × Fin 8) × (Fin 8 × Fin 8)

/-- The fixed coarse mode grade of the literal `phi_116` constituent. -/
def phi116ModeTotalGrade (s : Fin 3) : Fin 9 :=
  cwFourthBlockType 1 1 6 s

/-- Canonical coordinates belonging to the `phi_116` mode space. -/
def Phi116ModeIndex (s : Fin 3) : Type :=
  {p : FourthIndex // cwFourthPairGrade 6 p = phi116ModeTotalGrade s}

private theorem phi116_mode_span_eq (K : Type u) [Field K] (s : Fin 3) :
    Submodule.span K
        (Set.range (fun p : Phi116ModeIndex s =>
          cwFourthCanonicalBasis K 6 s p.1)) =
      cwBasisGrade (cwFourthCanonicalBasis K 6 s)
        (cwFourthPairGrade 6) (phi116ModeTotalGrade s) := by
  unfold cwBasisGrade
  congr 1
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, rfl⟩

private theorem phi116_mode_linearIndependent
    (K : Type u) [Field K] (s : Fin 3) :
    LinearIndependent K (fun p : Phi116ModeIndex s =>
      cwFourthCanonicalBasis K 6 s p.1) :=
  (cwFourthCanonicalBasis K 6 s).linearIndependent.comp _ Subtype.val_injective

/-- The canonical basis of each mode of the literal `phi_116` block. -/
noncomputable def phi116CanonicalBasis
    (K : Type u) [Field K] (s : Fin 3) :
    Basis (Phi116ModeIndex s) K
      (((cwFourthConstituent K 6 1 1 6)).V s) :=
  (Basis.span (phi116_mode_linearIndependent K s)).map
    (LinearEquiv.ofEq _ _ (phi116_mode_span_eq K s))

@[simp] theorem phi116CanonicalBasis_coe
    (K : Type u) [Field K] (s : Fin 3) (p : Phi116ModeIndex s) :
    (phi116CanonicalBasis K s p).val =
      cwFourthCanonicalBasis K 6 s p.1 := by
  unfold phi116CanonicalBasis
  erw [Module.Basis.map_apply (Basis.span (phi116_mode_linearIndependent K s))
    (LinearEquiv.ofEq _ _ (phi116_mode_span_eq K s)) p, LinearEquiv.coe_ofEq_apply]
  exact congrArg Subtype.val
    (Module.Basis.span_apply (phi116_mode_linearIndependent K s) p)

/-- The three outer classes used in the Davie--Stothers `phi_116` extraction. -/
def phi116OuterClass (s : Fin 3) (a : Fin 5) : Fin 3 :=
  match s with
  | ⟨0, _⟩ => if a = 0 then 0 else if a = 1 then 1 else 2
  | ⟨1, _⟩ => if a = 0 then 0 else if a = 1 then 1 else 2
  | ⟨2, _⟩ => if a = 4 then 0 else if a = 2 then 1 else 2

/-- Outer grade of a canonical coordinate in the literal block. -/
def phi116OuterGrade (s : Fin 3) (p : Phi116ModeIndex s) : Fin 3 :=
  phi116OuterClass s (cwSquarePairGrade 6 p.1.1)

/-- The literal three-grading of the actual `phi_116` constituent. -/
noncomputable def cwPhi116ThreeGrading
    (K : Type u) [Field K] :
    ((cwFourthConstituent K 6 1 1 6)).TypeGrading 3 where
  decomp s := cwBasisGrade (phi116CanonicalBasis K s)
    (phi116OuterGrade s)
  is_internal s := cwBasisGrade_isInternal
    (phi116CanonicalBasis K s) (phi116OuterGrade s)

end MME.StothersFourth.Phi116


