-- Prove2me | Definitions.Def_QAlgorithms_Defs_NLTSCodeGeometry
-- name    : QAlgorithms_Defs_NLTSCodeGeometry
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:36.50834+00:00
-- url     : https://prove2.me/theorems/38bd9487-44c4-46bd-9aa1-cc64add2a88a
-- title:
--   NLTSCodeGeometry
-- statement:
--   NLTSCodeGeometry
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\NLTSCodeGeometry.lean

import Definitions.Def_QAlgorithms_Defs_BinaryCheckPresentations
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.NLTS

/-- arxiv-2206.13228v4 PDF p.2. -/
def reducedHammingWeight {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (y : Fin n → ZMod 2) : ℕ :=
  (Finset.univ : Finset S).inf' (Finset.univ_nonempty_iff.mpr ⟨0⟩)
    (fun s => hammingNorm (y+(s : Fin n → ZMod 2)))

/-- arxiv-2206.13228v4 PDF p.2. -/
def approximateCodewords {n m : ℕ} (H : Matrix (Fin m) (Fin n) (ZMod 2))
    (delta : ℝ) (_hd : 0 ≤ delta) : Set (Fin n → ZMod 2) :=
  {y | (hammingNorm (H.mulVec y) : ℝ) ≤ delta*m}

/-- arxiv-2206.13228v4 PDF p.2; arxiv-2206.13228v4 PDF p.4. -/
def ClustersApproximateCodewords {n mx mz : ℕ} (C : PresentedCSS.CheckPresentation n mx mz)
    (c1 c2 delta0 : ℝ) : Prop :=
  0 < c1 ∧ 0 < c2 ∧ 0 < delta0 ∧ ∀ delta, ∀ hd : 0 ≤ delta, delta < delta0 →
    ∀ y : Fin n → ZMod 2,
    (y ∈ approximateCodewords C.HZ delta hd →
      (reducedHammingWeight (codeDual C.Cx) y : ℝ) ≤ c1*delta*n ∨
      c2*n ≤ (reducedHammingWeight (codeDual C.Cx) y : ℝ)) ∧
    (y ∈ approximateCodewords C.HX delta hd →
      (reducedHammingWeight (codeDual C.Cz) y : ℝ) ≤ c1*delta*n ∨
      c2*n ≤ (reducedHammingWeight (codeDual C.Cz) y : ℝ))

/-- Positive-phase X or Z row Pauli (NLTS p.2, local Hamiltonian definition). -/
def rowOperator {n : ℕ} (x : Bool) (r : Fin n → ZMod 2) : Matrix (Qubits n) (Qubits n) ℂ :=
  pauliOps fun i => if r i = 0 then Stabilizer.Pauli.I
    else if x then Stabilizer.Pauli.X else Stabilizer.Pauli.Z

/-- arxiv-2206.13228v4 PDF p.2. -/
def cssCheckHamiltonian {n mx mz : ℕ} (C : PresentedCSS.CheckPresentation n mx mz) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  (∑ i, (2⁻¹ : ℂ) • (1-rowOperator true (C.HX i))) +
    ∑ i, (2⁻¹ : ℂ) • (1-rowOperator false (C.HZ i))

/-- arxiv-2206.13228v4 PDF p.5, Theorem 5. The middle cutoff is delta0. -/
def energyCutoff {n mx mz : ℕ} (C : PresentedCSS.CheckPresentation n mx mz)
    (_positive : 0 < n ∧ 0 < mx ∧ 0 < mz) (c1 c2 delta0 : ℝ) (_hc : 0 < c1) : ℝ :=
  ((min mx mz : ℕ) : ℝ)/(400*c1*(n : ℝ))*
    min ((((C.logicalDimension : ℝ)-1)/(4*(n : ℝ)))^2) (min delta0 (c2/2))

/-- Sanity check for the source model (arxiv-2206.13228v4 PDF p.2). -/
example {n m : ℕ} (delta : ℝ) (hd : 0 ≤ delta) :
    approximateCodewords (0 : Matrix (Fin m) (Fin n) (ZMod 2)) delta hd = Set.univ := by
  ext y; simp [approximateCodewords,mul_nonneg hd (Nat.cast_nonneg m)]

/-- The printed unsquared middle cutoff gives this small admissible parameter choice
(arxiv-2206.13228v4 PDF p.5). -/
example (C : PresentedCSS.CheckPresentation 4 1 1) (hk : C.logicalDimension = 4) :
    energyCutoff C (by omega) 1 1 (1/10) (by norm_num) = 9/409600 := by
  norm_num [energyCutoff,hk]

end QAlgorithms.NLTS


