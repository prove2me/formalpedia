-- Prove2me | Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
-- name    : QAlgorithms_Defs_SurgeryFaultComplexes
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:37:50.028556+00:00
-- url     : https://prove2.me/theorems/1a252bad-13b5-416a-b088-b5e67abf48f4
-- title:
--   SurgeryFaultComplexes
-- statement:
--   SurgeryFaultComplexes
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SurgeryFaultComplexes.lean

import Definitions.Def_QAlgorithms_Defs_SurgerySpacetimeDetectors
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Surgery


/-- Tensor differential of two finite based binary complexes. Characteristic two
removes the Koszul sign (2510.14895 pp.10,63, Eq.(5)). -/
def tensorComplex (R C : BasedBinaryComplex) : BasedBinaryComplex where
  Cell := R.Cell × C.Cell
  finite := inferInstance
  degree := fun a => R.degree a.1+C.degree a.2
  differential := Matrix.kronecker R.differential 1+Matrix.kronecker 1 C.differential
  lowers := by
    intro a b h
    by_cases hr : R.differential a.1 b.1 = 0
    · by_cases hc : C.differential a.2 b.2 = 0
      · simp [Matrix.kronecker_apply,hr,hc] at h
      · by_cases hab : a.1 = b.1
        · have ht := C.lowers _ _ hc; simp only [hab]; omega
        · simp [Matrix.kronecker_apply,Matrix.one_apply,hr,hab] at h
    · by_cases hab : a.2 = b.2
      · have ht := R.lowers _ _ hr; simp only [hab]; omega
      · by_cases hcd : C.differential a.2 b.2 = 0
        · simp [Matrix.kronecker_apply,Matrix.one_apply,hab,hcd] at h
        · by_cases he : a.1 = b.1
          · have ht := C.lowers _ _ hcd; simp only [he]; omega
          · simp [Matrix.kronecker_apply,Matrix.one_apply,hab,he] at h
  square := by
    let IC : Matrix C.Cell C.Cell (ZMod 2) := 1
    let IR : Matrix R.Cell R.Cell (ZMod 2) := 1
    have hRR : (Matrix.kronecker R.differential IC) *
        (Matrix.kronecker R.differential IC) = 0 := by
      calc
        _ = Matrix.kronecker (R.differential*R.differential) (IC*IC) :=
          (Matrix.mul_kronecker_mul R.differential R.differential IC IC).symm
        _ = 0 := by rw [R.square]; exact Matrix.zero_kronecker _
    have hCC : (Matrix.kronecker IR C.differential) *
        (Matrix.kronecker IR C.differential) = 0 := by
      calc
        _ = Matrix.kronecker (IR*IR) (C.differential*C.differential) :=
          (Matrix.mul_kronecker_mul IR IR C.differential C.differential).symm
        _ = 0 := by rw [C.square]; exact Matrix.kronecker_zero _
    have hRC : (Matrix.kronecker R.differential IC) * (Matrix.kronecker IR C.differential) =
        Matrix.kronecker R.differential C.differential := by
      calc
        _ = Matrix.kronecker (R.differential*IR) (IC*C.differential) :=
          (Matrix.mul_kronecker_mul R.differential IR IC C.differential).symm
        _ = _ := by simp [IR,IC]
    have hCR : (Matrix.kronecker IR C.differential) * (Matrix.kronecker R.differential IC) =
        Matrix.kronecker R.differential C.differential := by
      calc
        _ = Matrix.kronecker (IR*R.differential) (C.differential*IC) :=
          (Matrix.mul_kronecker_mul IR R.differential C.differential IC).symm
        _ = _ := by simp [IR,IC]
    change ((Matrix.kronecker R.differential IC)+(Matrix.kronecker IR C.differential))*
      ((Matrix.kronecker R.differential IC)+(Matrix.kronecker IR C.differential)) = 0
    rw [Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,hRR,hRC,hCR,hCC]
    simp only [zero_add,add_zero]
    ext a b; exact CharTwo.add_self_eq_zero ((Matrix.kronecker R.differential C.differential) a b)

/-- Transpose the differential and reflect its degrees; this interchanges primal and
 dual boundary conventions (2510.14895 pp.63--65,69--71). -/
def dualComplex (shift : ℤ) (C : BasedBinaryComplex) : BasedBinaryComplex where
  Cell := C.Cell
  finite := inferInstance
  degree := fun a => shift-C.degree a
  differential := C.differential.transpose
  lowers := by
    intro a b h; have ht := C.lowers b a h; omega
  square := by
    rw [← Matrix.transpose_mul,C.square]; rfl

/-- Full-rank path incidence with l vertices, dual to the length-l repetition parity
 check (2510.14895 pp.63--65). l=1 is the one-vertex, no-edge path. -/
def repetitionComplex (l : ℕ) (_hl : 0 < l) : BasedBinaryComplex where
  Cell := Fin l ⊕ Fin (l-1)
  finite := inferInstance
  degree := Sum.elim (fun _ => 0) (fun _ => 1)
  differential := Matrix.of fun a b => match a,b with
    | .inl v,.inr e => if v.val = e.val ∨ v.val = e.val+1 then 1 else 0
    | _,_ => 0
  lowers := by
    intro a b h; cases a <;> cases b <;> simp at h ⊢
  square := by
    ext a b; cases a <;> cases b <;> simp [Matrix.mul_apply,Fintype.sum_sum_type]

/-- Source memory complexes have only degrees 0,1,2, including dependent checks
(2510.14895 pp.10--11,63). -/
def IsCSSComplex (C : BasedBinaryComplex) : Prop := ∀ c, 0 ≤ C.degree c ∧ C.degree c ≤ 2

/-- Boundary degree-zero columns vanish in a nonnegatively supported complex
(2510.14895 pp.10--11). -/
theorem bottomColumn_zero (F : BasedBinaryComplex) (nonnegative : ∀ c, 0 ≤ F.degree c)
    (c : F.Cell) (hc : F.degree c = 0) (r : F.Cell) : F.differential r c = 0 := by
  by_contra h
  have ht := F.lowers r c h
  have hn := nonnegative r
  omega

/-- Top/bottom timelike entry terms: two copies of the memory X-check space in degree
zero, with zero boundary (2510.14895 p.65, displayed g0). -/
def entryComplex (C : BasedBinaryComplex) : BasedBinaryComplex where
  Cell := Bool × Basis C 0
  finite := inferInstance
  degree := fun _ => 0
  differential := 0
  lowers := by simp
  square := by simp

/-- Coordinate matrix of the top/bottom temporal entry injection (2510.14895 p.65). -/
def temporalEntryMatrix (C : BasedBinaryComplex) (l : ℕ) (hl : 0 < l) :
    Matrix (tensorComplex (repetitionComplex l hl) C).Cell (entryComplex C).Cell (ZMod 2) :=
  Matrix.of fun target source =>
    if target = (Sum.inl (if source.1 then (⟨l-1,by omega⟩ : Fin l) else ⟨0,hl⟩),source.2.val)
    then 1 else 0

/-- The actual injection g0 into the two end X-detector layers of the idling volume
(2510.14895 p.65). This map is not chosen to have a desired homology image. -/
def temporalEntryMap (C : BasedBinaryComplex) (css : IsCSSComplex C) (l : ℕ) (hl : 0 < l) :
    BasedChainMap (entryComplex C) (tensorComplex (repetitionComplex l hl) C) where
  matrix := temporalEntryMatrix C l hl
  graded := by
    intro a b h
    simp only [temporalEntryMatrix,Matrix.of_apply,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] at h
    subst a
    simp [tensorComplex,repetitionComplex,entryComplex,b.2.property]
  commutes := by
    have hz : (entryComplex C).differential =
        (0 : Matrix (entryComplex C).Cell (entryComplex C).Cell (ZMod 2)) := rfl
    rw [hz,Matrix.mul_zero]
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro x hx
    unfold temporalEntryMatrix
    simp only [Matrix.of_apply]
    by_cases he : x =
        (Sum.inl (if b.1 then (⟨l-1,by omega⟩ : Fin l) else ⟨0,hl⟩),b.2.val)
    · rw [if_pos he]
      subst x
      have hn : ∀ c : (tensorComplex (repetitionComplex l hl) C).Cell,
          0 ≤ (tensorComplex (repetitionComplex l hl) C).degree c := by
        rintro ⟨r,c⟩
        have hc := (css c).1
        cases r <;> dsimp [tensorComplex,repetitionComplex] <;> omega
      have hc : (tensorComplex (repetitionComplex l hl) C).degree
          (Sum.inl (if b.1 then (⟨l-1,by omega⟩ : Fin l) else ⟨0,hl⟩),b.2.val) = 0 := by
        simp [tensorComplex,repetitionComplex,b.2.property]
      exact (mul_one _).trans (bottomColumn_zero _ hn _ hc a)
    · rw [if_neg he]; simp

/-- Both temporal boundary types are required (2510.14895 pp.64--65,69--71). -/
inductive BoundaryType where
  | X | Z

/-- Add top and bottom timelike entry terms. The Z-boundary volume is the degree-three
 dual of the X-boundary construction on the degree-two dual memory complex;
 consequently both types retain the source's fault-entry terms
 (2510.14895 pp.63--65,69--71). -/
def openIdlingVolume (C : BasedBinaryComplex) (css : IsCSSComplex C) (l : ℕ) (hl : 0 < l) :
    BoundaryType → BasedBinaryComplex
  | .X => mappingCone (temporalEntryMap C css l hl)
  | .Z => dualComplex 3 (mappingCone (temporalEntryMap (dualComplex 2 C)
      (fun c => by have hc := css c; dsimp [dualComplex]; omega) l hl))

/-- Ordered cone attachments at public scheduled spacetime layers. The supplied
 attaching maps are algebraic surgery data, not detector, distance or success fields
 (2510.14895 pp.76,82). Their placement at the specified primal layers is the
 source-specific qualification used by the fault-distance theorem. -/
inductive FaultConeSequence : BasedBinaryComplex → Type 1 where
  | stop (F : BasedBinaryComplex) : FaultConeSequence F
  | attach {F : BasedBinaryComplex} {v e f checks2 : ℕ}
      (H : HypergraphCycleBasis v e f checks2)
      (h : BasedChainMap (auxiliaryComplex H) F)
      (rest : FaultConeSequence (mappingCone h)) : FaultConeSequence F

/-- Execute the ordered auxiliary cones (2510.14895 pp.76,82). -/
def FaultConeSequence.result {F : BasedBinaryComplex} : FaultConeSequence F → BasedBinaryComplex
  | .stop _ => F
  | .attach _ _ rest => rest.result

/-- Four-term open-boundary idling volume, followed by the ordered auxiliary mapping
cones at the supplied scheduled layers. Retains the source's graded coordinate bases,
including face detectors. Both boundary types use the actual entry construction
(2510.14895 pp.60--65,69--71,76,82--83). -/
def openBoundaryFaultComplex (C : BasedBinaryComplex) (css : IsCSSComplex C)
    (l : ℕ) (hl : 0 < l) (side : BoundaryType)
    (attachments : FaultConeSequence (openIdlingVolume C css l hl side)) : BasedBinaryComplex :=
  attachments.result

/-- Sanity check for the source model (arxiv-2510.14895v1 PDF p.60). -/
example (hl : 0 < 1) : (repetitionComplex 1 hl).differential = 0 := by
  ext a b
  cases a with
  | inl a => cases b with
    | inl b => rfl
    | inr b => exact Fin.elim0 b
  | inr a => exact Fin.elim0 a


/-- Source physical fault weight: each nonidentity data Pauli counts once, including Y;
each reported check flip counts once (2510.14895 pp.60--65,69,76). -/
def faultWeight {n : ℕ} {S : PhenomenologicalSchedule n} (e : ScheduleFault n S) : ℕ :=
  (Finset.univ.filter fun site : Fin (S.layers.length+1) × Fin (n+S.ancillas) =>
    e.data site.1 site.2 ≠ Stabilizer.Pauli.I).card +
  (Finset.univ.filter fun site => e.flip site = true).card

/-- Minimum undetected nontrivial operational fault weight. An empty set of nontrivial
faults has infinite distance. Detection includes the ideal outgoing syndrome boundary,
so a residual detectable data error is not a logical fault. Encoded input/projector validity belongs to the protocol's
hypotheses; no distance bound is a field (2510.14895 pp.60--65,69,76,82--83).
arxiv-2510.14895v1 PDF p.60; arxiv-2510.14895v1 PDF p.61; arxiv-2510.14895v1 PDF p.62; arxiv-2510.14895v1 PDF p.63; arxiv-2510.14895v1 PDF p.64; arxiv-2510.14895v1 PDF p.65; arxiv-2510.14895v1 PDF p.69; arxiv-2510.14895v1 PDF p.76; arxiv-2510.14895v1 PDF p.82; arxiv-2510.14895v1 PDF p.83. -/
def phenomenologicalFaultDistance {n mx mz : ℕ} (S : PhenomenologicalSchedule n)
    (C : PresentedCSS.CheckPresentation n mx mz) : ℕ∞ :=
  sInf {w | ∃ e : ScheduleFault n S,
    (∀ record, detectorMap S C record ≠ 0 → recordOperator S C e record (codeProjector C) = 0) ∧
    ¬ (spacetimeStabilizers S C).r e (noFault S) ∧ w = (faultWeight e : ℕ∞)}

/-- Sanity check for the source model (arxiv-2510.14895v1 PDF p.60). -/
example {n : ℕ} (S : PhenomenologicalSchedule n) : faultWeight (noFault S) = 0 := by
  simp [faultWeight,noFault]

end QAlgorithms.Surgery


