-- Prove2me | Definitions.Def_AsymSpecConn_Supplement_nonCrossingUpperQuantum
-- name    : AsymSpecConn_Supplement_nonCrossingUpperQuantum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:24:20.88993+00:00
-- url     : https://prove2.me/theorems/2c25bbbc-3462-4c52-b8b0-9953a1209cfa
-- title:
--   Non-crossing upper quantum functional
-- statement:
--   For a non-crossing family $B$ and a probability weight $\theta$, the non-crossing upper quantum functional is zero at the zero tensor and otherwise satisfies
--
--   $$
--   \log_2 F^\theta(t)=\sup\left\{\sum_{b\in B}\theta(b)H(\lambda_b/n):n\ge1,\ \lambda_b\vdash n,\ \left(\prod_{b\in B}P^b_{\lambda_b}\right)t^{\otimes n}\ne0\right\}.
--   $$
--
--   The module constructs the Specht character from a Young symmetrizer and uses the exact character projector formula on every canonical side $S_b$. Nested or disjoint sides give the commuting projector family of §6.6.
--
--   **Formalization Note** Partitions are padded with zero parts and represented by labelled Young diagrams; cell labels only conjugate the row and column groups. Natural-log entropy divided by $\log 2$ is the source's base-two entropy. Chosen bases and quotient representatives only coordinatize the invariant functional.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), §6.6–6.7, pp.47–49

import Mathlib
import Definitions.Def_AsymSpecConn_kronPowPi
import Definitions.Def_AsymSpecConn_permRep
import Definitions.Def_AsymSpecConn_Supplement_nonCrossing

set_option autoImplicit false
set_option maxHeartbeats 800000

open PiTensorProduct BigOperators
open scoped NNReal

namespace AsymSpecConn.Supplement

/-- A partition of `n`, presented as a labelled Young diagram.  Re-labelling the cells conjugates
all row and column groups and hence leaves the Specht character and projector unchanged.  Padding
the row-length vector by zeroes implements the paper's convention for `λ/n`. -/
structure YoungLabel (n : ℕ) where
  rowLength : Fin n → ℕ
  rowLength_antitone : Antitone rowLength
  rowLength_sum : ∑ r, rowLength r = n
  row : Fin n → Fin n
  col : Fin n → ℕ
  col_lt : ∀ x, col x < rowLength (row x)
  cell_unique : ∀ (r : Fin n) (c : ℕ), c < rowLength r →
    ∃! x : Fin n, row x = r ∧ col x = c

/-- Shannon entropy of the normalized row lengths of a partition, with natural logarithm.
The outer quantum functional exponentiates the base-two version; using `2 ^ (H / log 2)` below
is exactly the same normalization. -/
noncomputable def YoungLabel.entropyNat {n : ℕ} (hn : 1 ≤ n) (lam : YoungLabel n) : ℝ :=
  ∑ r, Real.negMulLog ((lam.rowLength r : ℝ) / n)

abbrev SymmetricGroup (n : ℕ) := Equiv.Perm (Fin n)
abbrev SymmetricGroupAlgebra (n : ℕ) := MonoidAlgebra ℂ (SymmetricGroup n)

/-- The row symmetrizer of a labelled Young diagram. -/
noncomputable def rowSymmetrizer {n : ℕ} (lam : YoungLabel n) : SymmetricGroupAlgebra n :=
  ∑ σ : SymmetricGroup n, if ∀ x, lam.row (σ x) = lam.row x then MonoidAlgebra.single σ 1 else 0

/-- The alternating column symmetrizer of a labelled Young diagram. -/
noncomputable def columnAntisymmetrizer {n : ℕ} (lam : YoungLabel n) : SymmetricGroupAlgebra n :=
  ∑ σ : SymmetricGroup n, if ∀ x, lam.col (σ x) = lam.col x then
    MonoidAlgebra.single σ ((Equiv.Perm.sign σ : ℤ) : ℂ) else 0

/-- A Young symmetrizer. -/
noncomputable def youngSymmetrizer {n : ℕ} (lam : YoungLabel n) : SymmetricGroupAlgebra n :=
  rowSymmetrizer lam * columnAntisymmetrizer lam

/-- The Specht space `[\lambda]`, realized as the span of the left orbit of a Young symmetrizer. -/
noncomputable def spechtSpace {n : ℕ} (lam : YoungLabel n) :
    Submodule ℂ (SymmetricGroupAlgebra n) :=
  LinearMap.range (LinearMap.mulRight ℂ (youngSymmetrizer lam))

/-- Left multiplication of the symmetric group on its complex group algebra. -/
noncomputable def groupAlgebraLeftRepresentation (n : ℕ) :
    Representation ℂ (SymmetricGroup n) (SymmetricGroupAlgebra n) where
  toFun σ := LinearMap.mulLeft ℂ (MonoidAlgebra.single σ 1)
  map_one' := by
    ext x
    simp [LinearMap.mulLeft_apply]
  map_mul' σ τ := by
    ext x
    simp [LinearMap.mulLeft_apply, ← mul_assoc]

/-- The standard symmetric-group action on the Specht space. -/
noncomputable def spechtRepresentation {n : ℕ} (lam : YoungLabel n) :
    Representation ℂ (SymmetricGroup n) (spechtSpace lam) :=
  (groupAlgebraLeftRepresentation n).subrepresentation (spechtSpace lam) (by
    intro σ x hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨MonoidAlgebra.single σ 1 * z, ?_⟩
    simp [groupAlgebraLeftRepresentation, LinearMap.mulRight_apply, mul_assoc])

/-- The irreducible character `χ_λ` of the Specht representation. -/
noncomputable def spechtCharacter {n : ℕ} (lam : YoungLabel n) (σ : SymmetricGroup n) : ℂ :=
  LinearMap.trace ℂ (spechtSpace lam) (spechtRepresentation lam σ)

/-- The action `π_S` from Section 6.6: simultaneously permute the `n` copies of every tensor
leg in `S`, and act trivially on all other legs. -/
noncomputable def subsetPermRep {k n : ℕ} (X : MME.TensorObj ℂ k) (S : Finset (Fin k)) :
    Representation ℂ (SymmetricGroup n) (PiTensorProduct ℂ (fun i : Fin k =>
      PiTensorProduct ℂ (fun _ : Fin n => X.V i))) where
  toFun σ := PiTensorProduct.map (fun i =>
    if i ∈ S then AsymSpecConn.permRep ℂ (X.V i) n σ else LinearMap.id)
  map_one' := by
    change PiTensorProduct.map (fun i =>
      if i ∈ S then AsymSpecConn.permRep ℂ (X.V i) n 1 else LinearMap.id) = LinearMap.id
    rw [← PiTensorProduct.map_id]
    congr 1
    funext i
    by_cases hi : i ∈ S
    · rw [if_pos hi, map_one]
      exact Module.End.one_eq_id
    · rw [if_neg hi]
  map_mul' σ τ := by
    change PiTensorProduct.map (fun i =>
      if i ∈ S then AsymSpecConn.permRep ℂ (X.V i) n (σ * τ) else LinearMap.id) =
      PiTensorProduct.map (fun i =>
        if i ∈ S then AsymSpecConn.permRep ℂ (X.V i) n σ else LinearMap.id) ∘ₗ
      PiTensorProduct.map (fun i =>
        if i ∈ S then AsymSpecConn.permRep ℂ (X.V i) n τ else LinearMap.id)
    rw [← PiTensorProduct.map_comp]
    congr 1
    funext i
    by_cases hi : i ∈ S
    · rw [if_pos hi, if_pos hi, if_pos hi, map_mul]
      exact Module.End.mul_eq_comp _ _
    · rw [if_neg hi, if_neg hi, if_neg hi]
      ext x
      rfl

/-- The source's isotypic projector `P^{V_S}_λ`, by the character formula displayed on p.48. -/
noncomputable def subsetIsotypicProjector {k n : ℕ} (X : MME.TensorObj ℂ k)
    (S : Finset (Fin k)) (lam : YoungLabel n) :
    Module.End ℂ (PiTensorProduct ℂ (fun i : Fin k =>
      PiTensorProduct ℂ (fun _ : Fin n => X.V i))) :=
  (((Module.finrank ℂ (spechtSpace lam) : ℕ) : ℂ) / (n.factorial : ℂ)) •
    ∑ σ : SymmetricGroup n,
      spechtCharacter lam σ⁻¹ • subsetPermRep X S σ

/-- Apply the commuting isotypic projectors for a non-crossing family to `t^{⊗n}`.  The
`Fintype.equivFin` enumeration merely fixes an order; Lemma 6.7(ii) says the result is independent
of it because the canonical sides are nested or disjoint. -/
noncomputable def projectedKronPower {k n : ℕ} {root : Fin k}
    (B : Finset (Bipartition k root)) (X : MME.TensorObj ℂ k)
    (lam : ∀ b : ↑B, YoungLabel n) :
    PiTensorProduct ℂ (fun i : Fin k => PiTensorProduct ℂ (fun _ : Fin n => X.V i)) :=
  let enum := (Fintype.equivFin ↑B).symm
  (List.ofFn (fun q : Fin (Fintype.card ↑B) => enum q)).foldl
    (fun y b => subsetIsotypicProjector X b.1.side (lam b) y)
    (AsymSpecConn.kronPowPi X n).t

/-- The logarithm appearing in the definition of the non-crossing upper quantum functional on
a concrete nonzero tensor (Section 6.7, pp.48--49).  Entropies use natural logarithms here and are
divided by `log 2`, yielding the paper's base-two logarithm. -/
noncomputable def nonCrossingLogQuantumObj {k : ℕ} {root : Fin k}
    (B : Finset (Bipartition k root)) (θ : ↑B → ℝ) (X : MME.TensorObj ℂ k) : ℝ :=
  sSup {z : ℝ | ∃ (n : ℕ) (hn : 1 ≤ n) (lam : ∀ b : ↑B, YoungLabel n),
    projectedKronPower B X lam ≠ 0 ∧
      z = (∑ b : ↑B, θ b * YoungLabel.entropyNat hn (lam b)) / Real.log 2}

/-- The non-crossing upper quantum functional `F^θ` of Section 6.7 on a concrete tensor:
zero on the zero tensor and `2` to the entropy supremum otherwise. -/
noncomputable def nonCrossingUpperQuantumObj {k : ℕ} {root : Fin k}
    (B : Finset (Bipartition k root)) (θ : ↑B → ℝ) (X : MME.TensorObj ℂ k) : ℝ≥0 :=
  by
    classical
    exact if X.t = 0 then 0 else Real.toNNReal (2 ^ nonCrossingLogQuantumObj B θ X)

/-- The non-crossing upper quantum functional on tensor-equivalence classes.  A chosen concrete
representative and chosen bases only coordinatize the source definition; the isotypic-support
condition and its value are invariant under tensor equivalence. -/
noncomputable def nonCrossingUpperQuantum {k : ℕ} {root : Fin k}
    (B : Finset (Bipartition k root)) (θ : ↑B → ℝ) : MME.TensorQ ℂ k → ℝ≥0 :=
  fun s => nonCrossingUpperQuantumObj B θ (Quotient.out s)

end AsymSpecConn.Supplement


