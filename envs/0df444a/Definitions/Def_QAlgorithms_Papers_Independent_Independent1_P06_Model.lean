-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P06_Model
-- name    : QAlgorithms_Papers_Independent_Independent1_P06_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:39:31.993699+00:00
-- url     : https://prove2.me/theorems/b99f5dd4-30b7-4130-9d24-30a69e85a433
-- title:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery: supporting definitions
-- statement:
--   Reviewed paper-local supporting definitions and conventions. The attached text aggregates the existing blind readbacks of every definition; it makes no theorem proof claim.
-- source:
--   Fast and fault-tolerant logical measurements: Auxiliary hypergraphs and transversal surgery, arXiv:2510.14895v1. PDF SHA-256: 5432b21da79d052ade1546bd9aa83b711bc517ad598c27fc785a711aeaafe54e. Exact locators remain in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_SurgeryFaultComplexes
import Definitions.Def_QAlgorithms_Defs_MitigationOperationBasis
/-!
# Fast and fault-tolerant logical measurements (arXiv:2510.14895v1)

Paper-local definitions and statement-only targets. Deferred nodes are recorded in the
assigned unit's HARD.md and GAPS.json. No operational fault-distance lower bound is
inferred from the open-boundary homology calculation.
-/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P06

abbrev F2 := ZMod 2


/-- Old data in each block and one X-check register per pattern row (Def.3.6, PDF p.20). -/
abbrev ReadingData (c r n mx : ℕ) := (Fin c × Fin n) ⊕ (Fin r × Fin mx)

/-- X checks of the actual Definition-3.6 deformation, in chain orientation, PDF p.20. -/
def readingX {c r n mx : ℕ} (HX : Matrix (Fin mx) (Fin n) F2)
    (P : Matrix (Fin r) (Fin c) F2) :
    Matrix (Fin c × Fin mx) (ReadingData c r n mx) F2 :=
  Matrix.of fun row col => match col with
    | .inl q => if row.1 = q.1 then HX row.2 q.2 else 0
    | .inr e => if row.2 = e.2 then P e.1 row.1 else 0

/-- Z checks: old checks followed by new vertex checks (Def.3.6, PDF p.20). -/
def readingZ {c r n mx mz : ℕ} (HX : Matrix (Fin mx) (Fin n) F2)
    (HZ : Matrix (Fin mz) (Fin n) F2) (P : Matrix (Fin r) (Fin c) F2) :
    Matrix ((Fin c × Fin mz) ⊕ (Fin r × Fin n)) (ReadingData c r n mx) F2 :=
  Matrix.of fun row col => match row, col with
    | .inl old, .inl q => if old.1 = q.1 then HZ old.2 q.2 else 0
    | .inl _, .inr _ => 0
    | .inr vertex, .inl q => if vertex.2 = q.2 then P vertex.1 q.1 else 0
    | .inr vertex, .inr e => if vertex.1 = e.1 then HX e.2 vertex.2 else 0

/-- The pair-reading pattern of Eq.(2), PDF pp.17–18. -/
def pairPattern : Matrix (Fin 1) (Fin 2) F2 := fun _ _ => 1

/-- The metachecks in degree three, retained in Lemma 3.3 (PDF pp.19,21–22). -/
def readingMeta {c r n mz : ℕ} (HZ : Matrix (Fin mz) (Fin n) F2)
    (P : Matrix (Fin r) (Fin c) F2) :
    Matrix (Fin r × Fin mz) ((Fin c × Fin mz) ⊕ (Fin r × Fin n)) F2 :=
  Matrix.of fun row col => match col with
    | .inl old => if row.2 = old.2 then P row.1 old.1 else 0
    | .inr vertex => if row.1 = vertex.1 then HZ row.2 vertex.2 else 0

example {c r n mz : ℕ} (HZ : Matrix (Fin mz) (Fin n) F2)
    (P : Matrix (Fin r) (Fin c) F2) (i : Fin r) (j : Fin mz) (v : Fin n) :
    readingMeta HZ P (i,j) (.inr (i,v)) = HZ j v := by simp [readingMeta]


/-- Logical Z space with quotient by stabilizers, PDF pp.10–11. Under CSS commutation,
this comap is exactly the stabilizer space inside the normalizer. -/
abbrev logicalSpace {Q X Z : Type*} [Fintype Q] [Fintype Z]
    (HX : Matrix X Q F2) (HZ : Matrix Z Q F2) :=
  (LinearMap.ker HX.mulVecLin) ⧸
    (LinearMap.range HZ.transpose.mulVecLin).comap (LinearMap.ker HX.mulVecLin).subtype

/-- Both CSS distances bounded below, with no finite-distance assertion when no logical
class remains (PDF p.11). -/
def HasCSSDistance {Q X Z : Type*} [Fintype Q] [Fintype X] [Fintype Z]
    (HX : Matrix X Q F2) (HZ : Matrix Z Q F2) (d : ℕ) : Prop :=
  HX * HZ.transpose = 0 ∧
    (∀ v : Q → F2, HX.mulVec v = 0 → v ∉ LinearMap.range HZ.transpose.mulVecLin →
      d ≤ hammingNorm v) ∧
    ∀ v : Q → F2, HZ.mulVec v = 0 → v ∉ LinearMap.range HX.transpose.mulVecLin →
      d ≤ hammingNorm v

example {n mx : ℕ} (HX : Matrix (Fin mx) (Fin n) F2) (i : Fin mx) (j : Fin n) :
    readingX HX pairPattern (0,i) (.inl (0,j)) = HX i j ∧
      readingX HX pairPattern (0,i) (.inr (0,i)) = 1 := by
  simp [readingX, pairPattern]

example {n mx mz : ℕ} (HX : Matrix (Fin mx) (Fin n) F2)
    (HZ : Matrix (Fin mz) (Fin n) F2) (j : Fin n) (i : Fin mx) :
    readingZ HX HZ pairPattern (.inr (0,j)) (.inr (0,i)) = HX i j := by
  simp [readingZ]

example {Q X Z : Type*} [Fintype Q] [Fintype X] [Fintype Z]
    (HX : Matrix X Q F2) (HZ : Matrix Z Q F2) (h : HX * HZ.transpose = 0) :
    HasCSSDistance HX HZ 0 :=
  ⟨h, fun _ _ _ => Nat.zero_le _, fun _ _ _ => Nat.zero_le _⟩




/-- Union of supports of W, independent of the choice of its basis (Def.7.1, PDF p.35). -/
def addressed {V : Type*} [Fintype V] (W : Submodule F2 (V → F2)) : Finset V :=
  Finset.univ.filter fun v => ∃ w ∈ W, w v ≠ 0

/-- Zero extension of restriction to addressed vertices (Def.7.2, PDF p.35). -/
def restrictVertices {V : Type*} (U : Finset V) (v : V → F2) : V → F2 :=
  fun j => if j ∈ U then v j else 0

/-- Attained finite minimum Hamming distance to W; W contains zero (PDF p.35). -/
def modularCosetWeight {V : Type*} [Fintype V] (W : Submodule F2 (V → F2))
    (v : V → F2) : ℕ :=
  (Finset.univ : Finset W).inf' (Finset.univ_nonempty_iff.mpr ⟨0⟩)
    (fun w => hammingNorm (v + w.val))

/-- Certified cut bound of Def.7.2, PDF p.35. The restricted-vector distance equals
|kappa|-|v intersect kappa|+|v intersect U minus kappa|. -/
def HasModularExpansion {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (W : Submodule F2 (V → F2)) (t M : ℝ) : Prop :=
  0 < t ∧ ∀ v : V → F2,
    M * min t (modularCosetWeight W (restrictVertices (addressed W) v) : ℝ) ≤
      (hammingNorm (G.transpose.mulVec v) : ℝ)

/-- L vertices and L-1 edges (Theorem 7.8, PDF p.37). -/
def pathIncidence (L : ℕ) : Matrix (Fin L) (Fin (L-1)) F2 :=
  Matrix.of fun v e => if v.val = e.val ∨ v.val = e.val+1 then 1 else 0

/-- G_L = [G tensor I_L, I_V tensor R_L] (Appendix C, PDF p.87). -/
def thickIncidence {V E : Type*} [DecidableEq V] (G : Matrix V E F2) (L : ℕ) :
    Matrix (V × Fin L) ((E × Fin L) ⊕ (V × Fin (L-1))) F2 :=
  Matrix.fromCols (Matrix.kronecker G 1) (Matrix.kronecker 1 (pathIncidence L))

/-- Linear embedding into one selected level (Theorem 7.8, PDF p.37). -/
def levelEmbedding {V : Type*} (L : ℕ) (ell : Fin L) :
    (V → F2) →ₗ[F2] (V × Fin L → F2) where
  toFun v := fun p => if p.2 = ell then v p.1 else 0
  map_add' v w := by funext p; split_ifs <;> simp_all
  map_smul' a v := by funext p; split_ifs <;> simp_all

/-- W embedded in one selected level, rather than in every level (PDF p.37). -/
def levelSpace {V : Type*} (W : Submodule F2 (V → F2)) (L : ℕ) (ell : Fin L) :
    Submodule F2 (V × Fin L → F2) := W.map (levelEmbedding L ell)

/-- Certified relative expansion (Def.7.4, PDF p.36). -/
def HasRelativeExpansion {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (U : Finset V) (t M : ℝ) : Prop :=
  0 < t ∧ ∀ v : V → F2,
    M * min t (min (hammingNorm (restrictVertices U v) : ℝ)
      ((U.card : ℝ) - hammingNorm (restrictVertices U v))) ≤
        (hammingNorm (G.transpose.mulVec v) : ℝ)

/-- Certified global expansion (Def.7.3, PDF p.35). -/
def HasGlobalExpansion {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (M : ℝ) : Prop :=
  ∀ v : V → F2, M * min (hammingNorm v : ℝ)
    ((Fintype.card V : ℝ) - hammingNorm v) ≤ (hammingNorm (G.transpose.mulVec v) : ℝ)

/-- Classical local testability, including locality (Def.7.5, PDF p.36). -/
def HasClassicalSoundness {V E : Type*} [Fintype V] [Fintype E]
    (G : Matrix V E F2) (omega : ℕ) (rho : ℝ) : Prop :=
  (∀ e, hammingNorm (fun v => G v e) ≤ omega) ∧ ∀ v : V → F2,
    rho / (Fintype.card V : ℝ) * modularCosetWeight (LinearMap.ker G.transpose.mulVecLin) v ≤
      (hammingNorm (G.transpose.mulVec v) : ℝ) / Fintype.card E

example {V : Type*} [Fintype V] : addressed (⊥ : Submodule F2 (V → F2)) = ∅ := by
  ext v
  simp [addressed]

example {V : Type*} (U : Finset V) : restrictVertices U (0 : V → F2) = 0 := by
  funext v; simp [restrictVertices]

example : pathIncidence 2 0 0 = 1 ∧ pathIncidence 2 1 0 = 1 := by
  constructor <;> decide

example {V : Type*} (v : V → F2) (j : V) : levelEmbedding 1 0 v (j,0) = v j := by
  simp [levelEmbedding]

example {V E : Type*} [Fintype V] [Fintype E] (G : Matrix V E F2)
    (W : Submodule F2 (V → F2)) (t : ℝ) (ht : 0 < t) :
    HasModularExpansion G W t 0 :=
  ⟨ht, fun _ => by simp⟩





/-- Constructed image of the induced homology map (Appendix A, PDF pp.60–61). -/
def homologyImage {A C : Surgery.BasedBinaryComplex} (f : Surgery.BasedChainMap A C)
    (i : ℤ) : Submodule F2 (Surgery.Homology C i) :=
  ((LinearMap.range ((Surgery.component f i).mulVecLin.comp (Surgery.cycles A i).subtype)).comap
    (Surgery.cycles C i).subtype).map (Surgery.boundaries C i).mkQ

example {A C : Surgery.BasedBinaryComplex} (f : Surgery.BasedChainMap A C) (i : ℤ) :
    (0 : Surgery.Homology C i) ∈ homologyImage f i := Submodule.zero_mem _



/-- Pure X or Z products for a binary support (PDF p.85). -/
def binaryPauli {n : ℕ} (x : Bool) (v : Fin n → F2) : Matrix (Qubits n) (Qubits n) ℂ :=
  pauliOps fun j => if v j = 0 then Stabilizer.Pauli.I
    else if x then Stabilizer.Pauli.X else Stabilizer.Pauli.Z

example {n : ℕ} (x : Bool) : binaryPauli x (0 : Fin n → F2) = 1 := by
  ext y z
  simp [binaryPauli, pauliOps, Stabilizer.PauliString.toMatrix,
    Stabilizer.Pauli.mat, Matrix.one_apply, Finset.prod_boole, funext_iff]




end QAlgorithms.Papers.Independent.Independent1.P06


