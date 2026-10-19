-- Prove2me | Definitions.Def_QAlgorithms_Defs_SurgeryMappingCones
-- name    : QAlgorithms_Defs_SurgeryMappingCones
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:28:34.558121+00:00
-- url     : https://prove2.me/theorems/4fdbc6f4-2f0c-493b-a32b-75d1a6b711e2
-- title:
--   SurgeryMappingCones
-- statement:
--   SurgeryMappingCones
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SurgeryMappingCones.lean

import Definitions.Def_QAlgorithms_Defs_SurgeryAuxiliaryComplexes
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Surgery

/-- The computed cone shifts the auxiliary coordinates up one degree
(2510.14895 pp.12--13,32, Definition 5.2).
arxiv-2510.14895v1 PDF p.12; arxiv-2510.14895v1 PDF p.13; arxiv-2510.14895v1 PDF p.32. -/
def mappingCone {A C : BasedBinaryComplex} (f : BasedChainMap A C) : BasedBinaryComplex where
  Cell := C.Cell ⊕ A.Cell
  finite := inferInstance
  degree := Sum.elim C.degree (fun a => A.degree a+1)
  differential := Matrix.fromBlocks C.differential f.matrix 0 A.differential
  lowers := by
    intro a b h
    cases a <;> cases b <;> simp only [Matrix.fromBlocks] at h ⊢
    · exact C.lowers _ _ h
    · exact congrArg (fun z : ℤ => z+1) (f.graded _ _ h)
    · contradiction
    · rename_i a b
      change A.degree a+1+1 = A.degree b+1
      have ht := A.lowers a b h; omega
  square := by
    rw [Matrix.fromBlocks_multiply]
    simp only [C.square,A.square,mul_zero,zero_mul,zero_add,add_zero]
    rw [f.commutes]
    have hz : f.matrix*A.differential+f.matrix*A.differential = 0 := by
      ext a b; exact CharTwo.add_self_eq_zero _
    rw [hz]
    ext a b; cases a <;> cases b <;> simp [Matrix.fromBlocks]

/-- Sum attaching maps from tagged auxiliary domains into their common memory,
computed by summing their images (2510.14895 pp.30--31). -/
def sumAttachingMaps {A B C : BasedBinaryComplex} (f : BasedChainMap A C)
    (g : BasedChainMap B C) : BasedChainMap (directSumComplex A B) C where
  matrix := Matrix.of fun c a => Sum.elim (f.matrix c) (g.matrix c) a
  graded := by
    intro c a h
    cases a with
    | inl a => exact f.graded c a h
    | inr a => exact g.graded c a h
  commutes := by
    change C.differential * (Matrix.of fun c a => Sum.elim (f.matrix c) (g.matrix c) a) =
      (Matrix.of fun c a => Sum.elim (f.matrix c) (g.matrix c) a) *
        Matrix.fromBlocks A.differential 0 0 B.differential
    ext c a
    cases a with
    | inl a =>
      simpa [Matrix.mul_apply,Fintype.sum_sum_type,directSumComplex,Matrix.fromBlocks]
        using congrFun (congrFun f.commutes c) a
    | inr a =>
      simpa [Matrix.mul_apply,Fintype.sum_sum_type,directSumComplex,Matrix.fromBlocks]
        using congrFun (congrFun g.commutes c) a

/-- Finite ordered source attaching data (2510.14895 pp.30--31,75). -/
inductive AttachingFamily (C : BasedBinaryComplex) : Type 1 where
  | empty
  | cons {A : BasedBinaryComplex} (f : BasedChainMap A C) (rest : AttachingFamily C)

/-- Assemble the direct sum and the map from it by finite recursion
(2510.14895 pp.30--31,75). -/
def AttachingFamily.combined {C : BasedBinaryComplex} :
    AttachingFamily C → (A : BasedBinaryComplex) × BasedChainMap A C
  | .empty => ⟨zeroComplex,⟨0,by simp,by change C.differential*0=0*0; simp⟩⟩
  | .cons f rest =>
      let next := rest.combined
      ⟨directSumComplex _ next.1,sumAttachingMaps f next.2⟩

/-- Algebraic simultaneous cone from the actual finite attaching family. It is a proof
object and has no LDPC or executable-protocol field (2510.14895 pp.30--31,75). -/
def compactedPresentation {C : BasedBinaryComplex} (family : AttachingFamily C) : BasedBinaryComplex :=
  mappingCone family.combined.2

/-- Degree 2,1,0 CSS matrices in their retained bases (2510.14895 pp.12--13,32).
The dependent pair exposes the original labels as well as both check matrices.
arxiv-2510.14895v1 PDF p.12; arxiv-2510.14895v1 PDF p.13; arxiv-2510.14895v1 PDF p.32. -/
def deformedPresentation {A C : BasedBinaryComplex} (h : BasedChainMap A C) :=
  let D := mappingCone h
  (boundary D 1,(boundary D 2).transpose)

/-- Sanity check for the source model (arxiv-2510.14895v1 PDF p.12). -/
example {A C : BasedBinaryComplex} (f : BasedChainMap A C) (a : A.Cell) :
    (mappingCone f).degree (.inr a) = A.degree a+1 := rfl

end QAlgorithms.Surgery


