-- Prove2me | Definitions.Def_QAlgorithms_Defs_SurgeryAuxiliaryComplexes
-- name    : QAlgorithms_Defs_SurgeryAuxiliaryComplexes
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:27:17.317379+00:00
-- url     : https://prove2.me/theorems/129f8e5a-fbe1-4f01-9641-a22dde1257ba
-- title:
--   SurgeryAuxiliaryComplexes
-- statement:
--   SurgeryAuxiliaryComplexes
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SurgeryAuxiliaryComplexes.lean

import Definitions.Def_QAlgorithms_Defs_SurgeryBasedComplexes
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Surgery

/-- arxiv-2510.14895v1 PDF p.15; arxiv-2510.14895v1 PDF p.16; arxiv-2510.14895v1 PDF p.76; arxiv-2510.14895v1 PDF p.82. -/
structure HypergraphCycleBasis (v e f checks2 : ℕ) where
  G : Matrix (Fin v) (Fin e) (ZMod 2)
  N : Matrix (Fin e) (Fin f) (ZMod 2)
  injective : Function.Injective N.mulVec
  full : LinearMap.range N.mulVecLin = LinearMap.ker G.mulVecLin
  cycles : G*N = 0
  metachecks : Matrix (Fin v) (Fin checks2) (ZMod 2)
  metacheckLaw : G.transpose*metachecks = 0

/-- Graded auxiliary coordinates, including faces in degree minus one
(2510.14895 pp.15--16,76,82). -/
abbrev AuxiliaryCell (v e f checks2 : ℕ) := Fin checks2 ⊕ (Fin v ⊕ (Fin e ⊕ Fin f))

/-- Vertex-metacheck, vertex, edge and face degrees (2510.14895 pp.15--16). -/
def auxiliaryDegree {v e f checks2 : ℕ} : AuxiliaryCell v e f checks2 → ℤ :=
  Sum.elim (fun _ => 2) (Sum.elim (fun _ => 1) (Sum.elim (fun _ => 0) (fun _ => -1)))

/-- The three actual auxiliary boundary blocks (2510.14895 pp.15--16,82). -/
def auxiliaryDifferential {v e f checks2 : ℕ} (H : HypergraphCycleBasis v e f checks2) :
    Matrix (AuxiliaryCell v e f checks2) (AuxiliaryCell v e f checks2) (ZMod 2)
  | .inr (.inl a), .inl b => H.metachecks a b
  | .inr (.inr (.inl a)), .inr (.inl b) => H.G b a
  | .inr (.inr (.inr a)), .inr (.inr (.inl b)) => H.N b a
  | _, _ => 0

/-- arxiv-2510.14895v1 PDF p.15; arxiv-2510.14895v1 PDF p.16; arxiv-2510.14895v1 PDF p.76; arxiv-2510.14895v1 PDF p.82. -/
def auxiliaryComplex {v e f checks2 : ℕ} (H : HypergraphCycleBasis v e f checks2) : BasedBinaryComplex where
  Cell := AuxiliaryCell v e f checks2
  finite := inferInstance
  degree := auxiliaryDegree
  differential := auxiliaryDifferential H
  lowers := by
    intro a b h
    rcases a with a|a|a|a <;> rcases b with b|b|b|b <;>
      simp [auxiliaryDifferential,auxiliaryDegree] at h ⊢
  square := by
    ext a b
    rcases a with a|a|a|a <;> rcases b with b|b|b|b <;>
      simp [Matrix.mul_apply,Fintype.sum_sum_type,auxiliaryDifferential]
    · exact congrFun (congrFun H.metacheckLaw a) b
    · have h := congrFun (congrFun (congrArg Matrix.transpose H.cycles) a) b
      simpa [Matrix.transpose_mul,Matrix.mul_apply,mul_comm] using h

/-- arxiv-2510.14895v1 PDF p.11; arxiv-2510.14895v1 PDF p.14; arxiv-2510.14895v1 PDF p.32; arxiv-2510.14895v1 PDF p.83. -/
def cosystolicDistance (A : BasedBinaryComplex) : ℕ∞ :=
  sInf {w | ∃ u : Basis A 1 → ZMod 2,
    (boundary A 2).transpose.mulVec u = 0 ∧
    u ∉ LinearMap.range (boundary A 1).transpose.mulVecLin ∧ w = (hammingNorm u : ℕ∞)}

/-- arxiv-2510.14895v1 PDF p.32; arxiv-2510.14895v1 PDF p.83. -/
def NonOverlappingVertices {A C : BasedBinaryComplex} (f : BasedChainMap A C) : Prop :=
  ∀ q : Basis C 1, (Finset.univ.filter fun v : Basis A 1 => component f 1 q v ≠ 0).card ≤ 1

/-- Sanity check for the source model (arxiv-2510.14895v1 PDF p.15). -/
example : cosystolicDistance zeroComplex = ⊤ := by
  have he : {w : ℕ∞ | ∃ u : Basis zeroComplex 1 → ZMod 2,
      (boundary zeroComplex 2).transpose.mulVec u = 0 ∧
      u ∉ LinearMap.range (boundary zeroComplex 1).transpose.mulVecLin ∧
      w = (hammingNorm u : ℕ∞)} = ∅ := by
    ext w
    simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
    rintro ⟨u,_,hu,_⟩
    apply hu
    refine ⟨0,?_⟩
    funext a; exact Fin.elim0 a.val
  rw [cosystolicDistance,he]
  simp

end QAlgorithms.Surgery


