-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P63
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P63
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:31:57.140959+00:00
-- url     : https://prove2.me/theorems/e3e74411-b987-479e-bf06-936e76c5fc68
-- title:
--   Definitions for On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy
-- statement:
--   The objects the formalized statements of *On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy* (arXiv:quant-ph/0311193) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SpectralExpansion`: PDF pp.2,5: a countable spectral resolution of a normalized density operator. Only positive eigenvalues require unit, mutually orthogonal eigenvectors. Zero padding permits finite rank and does not require an infinite orthonormal set in a finite space.
--   - `spectralKernel`: PDF p.2: the operator itself, computed from its spectral resolution. The sum converges in trace norm, since each active projector has trace norm one.
--   - `herbutEntropy`: PDF pp.2,6: intrinsic von Neumann entropy, in nats, including infinity. The defining set is a singleton value on densities, even with spectral degeneracies. The formula -x log x is zero at x=0 and x=1.
--   - `frameCompression`: PDF p.6: finite operator compression in an arbitrary orthonormal frame. Each nested coefficient series is absolutely convergent on density kernels.
--   - `traceClassDivergence`: PDF p.6: full trace-class Umegaki divergence in nats, via all finite orthogonal compressions, retaining infinite values. This is the same complete projection formula as the accepted Dependency50.P13.relativeEntropy, expressed in countable coordinates; its finiteRelativeEntropy definition is imported directly. The rank-zero frame contributes zero. No arbitrary eigenbasis or finite cutoff is fixed.
--   - `DiscreteDensityEnsemble`: PDF pp.5–7: an arbitrary discrete ensemble. The actual component set is the positive-weight support; a zero label carries no normalization or orthogonality premise.
--   - `herbutMixture`: PDF pp.5–7, (11),(14a),(17a): the computed weighted density operator. The norm of each active density is at most its trace norm one; the weighted series converges in trace norm. Inactive kernels contribute zero, regardless of their values.
--   - `Cluster`: PDF p.2: finite sets of parties, numbered from zero in Lean.
--   - `Coordinates`: PDF p.2: the orthonormal coordinates of a completed cluster tensor product. The empty cluster has the unique empty coordinate, hence the scalar tensor factor.
--   - `restrictCoordinate`: PDF p.2: restrict a full tensor coordinate to a cluster.
--   - `joinCoordinate`: PDF p.2: combine retained and discarded coordinates, without changing party order.
--   - `herbutReduction`: PDF p.2: the actual partial trace, computed from the single full density kernel. Positivity and trace one guarantee absolute convergence of every coefficient series.
--   - `herbutMarginalEntropy`: PDF pp.2–3: real marginal entropy, used only under finite-entropy hypotheses.
--   - `FiniteSubsystemEntropies`: PDF pp.2–8: finite-entropy arithmetic domain. Finiteness of all one-party entropies is equivalent to this condition by subadditivity. Empty-cluster entropy is zero. This imposes no bound on Hilbert-space dimension or the number of mixture terms.
--   - `clusterInformation`: PDF p.3, (4b): within-cluster correlation information; singletons contribute zero.
--   - `clusterMutualInformation`: PDF pp.3–4: mutual information of disjoint clusters, using their computed marginals.
--   - `IsPartition`: PDF pp.2–3, (3): unordered partitions into nonempty, pairwise disjoint blocks.
--   - `amongCorrelation`: PDF p.3, (5b): among-cluster correlation information.
--   - `tensorMarginals`: PDF p.2, Lemma 1: the tensor product of the state's own one-party marginals.
--   - `productAcross`: PDF p.4, (8), and Corollary 2: independence of the two complementary blocks. Both blocks may have arbitrary internal correlations.
--   - `kernelProduct`: PDF pp.5–7: ordinary operator multiplication in countable orthonormal coordinates.
--   - `Biorthogonal`: PDF p.5, (10b): biorthogonality on two specified disjoint clusters. The two zero-product conditions are imposed for every pair of distinct active labels.
--   - `Monoorthogonal`: PDF p.7, (17b): only the designated cluster's marginals are orthogonal.
--   - `BinaryTree`: PDF p.3, Corollary 1: syntax for arbitrary successive binary splits.
--   - `BinaryTree.parties`: PDF p.3: the parties in a binary subtree.
--   - `BinaryTree.Valid`: PDF p.3: every split is into disjoint nonempty child clusters. Nonemptiness is inherited from singleton leaves; validity prohibits duplicated parties.
--   - `BinaryTree.information`: PDF p.3: sum of the binary mutual information at every internal node, including the last split into two singletons.
--   - `attachThird`: PDF p.7, Remark 2: product of a two-party density and an arbitrary third factor.
--   - `productMixture`: PDF p.7, Remark 2: the explicit computed mixture of the product components. Third factors may coincide or differ, and zero labels are ignored.
--   - `pureExpansion`: A one-term spectral expansion exists on any unit ray, including finite spaces.
-- source:
--   On Mutual Information in Multipartite Quantum States and Equality in Strong Subadditivity of Entropy, arXiv:quant-ph/0311193v1, https://arxiv.org/abs/quant-ph/0311193v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08

/-!
# Herbut: multipartite correlation information and equality in SSA

arXiv:quant-ph/0311193v1. All page numbers below are PDF page numbers.
Countable orthonormal coordinates model completed complex Hilbert tensor products.
Finite dimensional factors embed with zero coefficients; finite Hilbert dimension is
never a theorem hypothesis. Countably many densities share separable local supports.
The accepted Dependency50.P33.IsDensity predicate supplies nuclear trace class,
positivity and trace one. Spectral expansions compute intrinsic entropy on these
operator coefficient matrices; they are not a replacement density predicate. Entropy is the
nonnegative extended spectral sum with natural logarithms. Every expansion of the same
kernel has the same spectrum with multiplicities; the extended infimum below therefore
selects its intrinsic entropy. Empty expansion sets give infinity, and are never used
as states. Real entropy differences are used only on the stated finite-entropy domain.
Lemma 3 is stated with its attribution to Herbut [8], Lemma 9, retained in the metadata.
Compilation and fresh independent readbacks are pending the batch handoff.
-/

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted nuclear trace-class, positive, trace-one predicate verbatim.
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)
open QAlgorithms.Papers.Independent.Dependency50.P13 (finiteRelativeEntropy)

/-- PDF pp.2,5: a countable spectral resolution of a normalized density operator.
Only positive eigenvalues require unit, mutually orthogonal eigenvectors. Zero padding
permits finite rank and does not require an infinite orthonormal set in a finite space. -/
structure SpectralExpansion (I : Type*) where
  weight : ℕ → ℝ
  vector : ℕ → QAlgorithms.RealRegisters.Hilbert I
  nonnegative : ∀ k, 0 ≤ weight k
  summable : Summable weight
  mass : (∑' k, weight k) = 1
  unit : ∀ k, 0 < weight k → ‖vector k‖ = 1
  orthogonal : ∀ k l, k ≠ l → 0 < weight k → 0 < weight l →
    inner ℂ (vector k) (vector l) = 0

/-- PDF p.2: the operator itself, computed from its spectral resolution.
The sum converges in trace norm, since each active projector has trace norm one. -/
def spectralKernel {I : Type*} (e : SpectralExpansion I) : (Matrix I I ℂ) :=
  fun i j => ∑' k, (e.weight k : ℂ) * e.vector k i * star (e.vector k j)

/-- PDF pp.2,6: intrinsic von Neumann entropy, in nats, including infinity.
The defining set is a singleton value on densities, even with spectral degeneracies.
The formula -x log x is zero at x=0 and x=1. -/
def herbutEntropy {I : Type*} (rho : (Matrix I I ℂ)) : ℝ≥0∞ :=
  sInf {s | ∃ e : SpectralExpansion I, spectralKernel e = rho ∧
    s = ∑' k, ENNReal.ofReal (-e.weight k * Real.log (e.weight k))}

/-- PDF p.6: finite operator compression in an arbitrary orthonormal frame.
Each nested coefficient series is absolutely convergent on density kernels. -/
def frameCompression {I : Type*} {m : ℕ}
    (rho : (Matrix I I ℂ)) (v : Fin m → QAlgorithms.RealRegisters.Hilbert I) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun a b => ∑' i, star (v a i) * (∑' j, rho i j * v b j)

/-- PDF p.6: full trace-class Umegaki divergence in nats, via all finite orthogonal
compressions, retaining infinite values. This is the same complete projection formula
as the accepted Dependency50.P13.relativeEntropy, expressed in countable coordinates;
its finiteRelativeEntropy definition is imported directly.
The rank-zero frame contributes zero. No arbitrary eigenbasis or finite cutoff is fixed. -/
def traceClassDivergence {I : Type*} (rho sigma : (Matrix I I ℂ)) : ℝ≥0∞ :=
  ⨆ m : ℕ, ⨆ v : {v : Fin m → QAlgorithms.RealRegisters.Hilbert I // Orthonormal ℂ v},
    finiteRelativeEntropy (frameCompression rho v.val) (frameCompression sigma v.val)

/-- PDF pp.5–7: an arbitrary discrete ensemble. The actual component set is the
positive-weight support; a zero label carries no normalization or orthogonality premise. -/
structure DiscreteDensityEnsemble (I : Type) where
  weight : ℕ → ℝ
  component : ℕ → (Matrix I I ℂ)
  nonnegative : ∀ k, 0 ≤ weight k
  summable : Summable weight
  mass : (∑' k, weight k) = 1
  density : ∀ k, 0 < weight k → IsDensity (component k)

/-- PDF pp.5–7, (11),(14a),(17a): the computed weighted density operator.
The norm of each active density is at most its trace norm one; the weighted series
converges in trace norm. Inactive kernels contribute zero, regardless of their values. -/
def herbutMixture {I : Type} (e : DiscreteDensityEnsemble I) : (Matrix I I ℂ) :=
  fun i j => ∑' k, (e.weight k : ℂ) * e.component k i j

/-- PDF p.2: finite sets of parties, numbered from zero in Lean. -/
abbrev Cluster (n : ℕ) := Finset (Fin n)

/-- PDF p.2: the orthonormal coordinates of a completed cluster tensor product.
The empty cluster has the unique empty coordinate, hence the scalar tensor factor. -/
abbrev Coordinates {n : ℕ} (C : Cluster n) := C → ℕ

/-- PDF p.2: restrict a full tensor coordinate to a cluster. -/
def restrictCoordinate {n : ℕ} (C : Cluster n) (x : Fin n → ℕ) : Coordinates C :=
  fun i => x i.val

/-- PDF p.2: combine retained and discarded coordinates, without changing party order. -/
def joinCoordinate {n : ℕ} (C : Cluster n)
    (x : Coordinates C) (z : Coordinates Cᶜ) : Fin n → ℕ :=
  fun i => if h : i ∈ C then x ⟨i, h⟩ else z ⟨i, by simpa using h⟩

/-- PDF p.2: the actual partial trace, computed from the single full density kernel.
Positivity and trace one guarantee absolute convergence of every coefficient series. -/
def herbutReduction {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (C : Cluster n) :
    (Matrix (Coordinates C) (Coordinates C) ℂ) :=
  fun x y => ∑' z : Coordinates Cᶜ, rho (joinCoordinate C x z) (joinCoordinate C y z)

/-- PDF pp.2–3: real marginal entropy, used only under finite-entropy hypotheses. -/
def herbutMarginalEntropy {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (C : Cluster n) : ℝ :=
  (herbutEntropy (herbutReduction rho C)).toReal

/-- PDF pp.2–8: finite-entropy arithmetic domain. Finiteness of all one-party
entropies is equivalent to this condition by subadditivity. Empty-cluster entropy is zero.
This imposes no bound on Hilbert-space dimension or the number of mixture terms. -/
def FiniteSubsystemEntropies {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) : Prop :=
  ∀ C : Cluster n, herbutEntropy (herbutReduction rho C) ≠ ⊤

/-- PDF p.3, (4b): within-cluster correlation information; singletons contribute zero. -/
def clusterInformation {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (C : Cluster n) : ℝ :=
  (∑ i ∈ C, herbutMarginalEntropy rho {i}) - herbutMarginalEntropy rho C

/-- PDF pp.3–4: mutual information of disjoint clusters, using their computed marginals. -/
def clusterMutualInformation {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (A B : Cluster n) : ℝ :=
  herbutMarginalEntropy rho A + herbutMarginalEntropy rho B - herbutMarginalEntropy rho (A ∪ B)

/-- PDF pp.2–3, (3): unordered partitions into nonempty, pairwise disjoint blocks. -/
def IsPartition {n : ℕ} (P : Finset (Cluster n)) : Prop :=
  (∀ C ∈ P, C.Nonempty) ∧
    (∀ C ∈ P, ∀ D ∈ P, C ≠ D → Disjoint C D) ∧
    ∀ i : Fin n, ∃ C ∈ P, i ∈ C

/-- PDF p.3, (5b): among-cluster correlation information. -/
def amongCorrelation {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ))
    (P : Finset (Cluster n)) : ℝ :=
  (∑ C ∈ P, herbutMarginalEntropy rho C) - herbutMarginalEntropy rho Finset.univ

/-- PDF p.2, Lemma 1: the tensor product of the state's own one-party marginals. -/
def tensorMarginals {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) :=
  fun x y => ∏ i : Fin n, herbutReduction rho {i} (fun _ => x i) (fun _ => y i)

/-- PDF p.4, (8), and Corollary 2: independence of the two complementary blocks.
Both blocks may have arbitrary internal correlations. -/
def productAcross {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (C : Cluster n) :
    (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ) :=
  fun x y => herbutReduction rho C (restrictCoordinate C x) (restrictCoordinate C y) *
    herbutReduction rho Cᶜ (restrictCoordinate Cᶜ x) (restrictCoordinate Cᶜ y)

/-- PDF pp.5–7: ordinary operator multiplication in countable orthonormal coordinates. -/
def kernelProduct {I : Type*} (rho sigma : (Matrix I I ℂ)) : (Matrix I I ℂ) :=
  fun i j => ∑' z, rho i z * sigma z j

/-- PDF p.5, (10b): biorthogonality on two specified disjoint clusters.
The two zero-product conditions are imposed for every pair of distinct active labels. -/
def Biorthogonal {n : ℕ} (e : DiscreteDensityEnsemble (Fin n → ℕ)) (A B : Cluster n) : Prop :=
  ∀ k l, k ≠ l → 0 < e.weight k → 0 < e.weight l →
    kernelProduct (herbutReduction (e.component k) A) (herbutReduction (e.component l) A) = 0 ∧
    kernelProduct (herbutReduction (e.component k) B) (herbutReduction (e.component l) B) = 0

/-- PDF p.7, (17b): only the designated cluster's marginals are orthogonal. -/
def Monoorthogonal {n : ℕ} (e : DiscreteDensityEnsemble (Fin n → ℕ)) (B : Cluster n) : Prop :=
  ∀ k l, k ≠ l → 0 < e.weight k → 0 < e.weight l →
    kernelProduct (herbutReduction (e.component k) B) (herbutReduction (e.component l) B) = 0

/-- PDF p.3, Corollary 1: syntax for arbitrary successive binary splits. -/
inductive BinaryTree (n : ℕ) where
  | leaf (i : Fin n)
  | split (left right : BinaryTree n)

/-- PDF p.3: the parties in a binary subtree. -/
def BinaryTree.parties {n : ℕ} : BinaryTree n → Cluster n
  | .leaf i => {i}
  | .split l r => l.parties ∪ r.parties

/-- PDF p.3: every split is into disjoint nonempty child clusters. Nonemptiness is
inherited from singleton leaves; validity prohibits duplicated parties. -/
def BinaryTree.Valid {n : ℕ} : BinaryTree n → Prop
  | .leaf _ => True
  | .split l r => l.Valid ∧ r.Valid ∧ Disjoint l.parties r.parties

/-- PDF p.3: sum of the binary mutual information at every internal node,
including the last split into two singletons. -/
def BinaryTree.information {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) : BinaryTree n → ℝ
  | .leaf _ => 0
  | .split l r => clusterMutualInformation rho l.parties r.parties + l.information rho + r.information rho

/-- PDF p.7, Remark 2: product of a two-party density and an arbitrary third factor. -/
def attachThird (sigma : (Matrix (Fin 2 → ℕ) (Fin 2 → ℕ) ℂ)) (tau : (Matrix ℕ ℕ ℂ)) : (Matrix (Fin 3 → ℕ) (Fin 3 → ℕ) ℂ) :=
  fun x y => sigma (fun i => x i.castSucc) (fun i => y i.castSucc) * tau (x 2) (y 2)

/-- PDF p.7, Remark 2: the explicit computed mixture of the product components.
Third factors may coincide or differ, and zero labels are ignored. -/
def productMixture (e : DiscreteDensityEnsemble (Fin 2 → ℕ)) (tau : ℕ → (Matrix ℕ ℕ ℂ)) :
    (Matrix (Fin 3 → ℕ) (Fin 3 → ℕ) ℂ) :=
  fun x y => ∑' k, (e.weight k : ℂ) * attachThird (e.component k) (tau k) x y

/-! Sanity checks of local definitions, rather than proofs of source results. -/

/-- A one-term spectral expansion exists on any unit ray, including finite spaces. -/
def pureExpansion {I : Type*} (v : QAlgorithms.RealRegisters.Hilbert I)
    (hv : ‖v‖ = 1) : SpectralExpansion I where
  weight := fun k => if k = 0 then 1 else 0
  vector := fun _ => v
  nonnegative := by intro k; split_ifs <;> norm_num
  summable := (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  mass := by simp
  unit := by intro k hk; exact hv
  orthogonal := by
    intro k l hkl hk hl
    have hk0 : k = 0 := by by_contra h; simp [h] at hk
    have hl0 : l = 0 := by by_contra h; simp [h] at hl
    exact False.elim (hkl (hk0.trans hl0.symm))

example {I : Type*} (v : QAlgorithms.RealRegisters.Hilbert I) (hv : ‖v‖ = 1) :
    spectralKernel (pureExpansion v hv) = fun i j => v i * star (v j) := by
  funext i j
  change (∑' k : ℕ, ((if k = 0 then 1 else 0 : ℝ) : ℂ) *
    v i * star (v j)) = v i * star (v j)
  have hterm : (fun k : ℕ => ((if k = 0 then 1 else 0 : ℝ) : ℂ) *
      v i * star (v j)) =
      (fun k : ℕ => if k = 0 then v i * star (v j) else 0) := by
    funext k
    by_cases hk : k = 0 <;> simp [hk]
  rw [hterm]
  simp

/-- The concrete vacuum ray meets the unit-vector premise of pureExpansion. -/
example : ‖(lp.single (E := fun _ : ℕ => ℂ) 2 (0 : ℕ) (1 : ℂ))‖ = 1 := by
  simp

/-- Tensor coordinates reassemble exactly, so retained and traced factors are not swapped. -/
example {n : ℕ} (C : Cluster n) (x : Fin n → ℕ) :
    joinCoordinate C (restrictCoordinate C x) (restrictCoordinate Cᶜ x) = x := by
  funext i
  by_cases h : i ∈ C <;> simp [joinCoordinate, restrictCoordinate, h]

example : ENNReal.ofReal (-(0 : ℝ) * Real.log 0) = 0 := by simp

example : ENNReal.ofReal (-(1 : ℝ) * Real.log 1) = 0 := by simp

example {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (i : Fin n) :
    clusterInformation rho {i} = 0 := by simp [clusterInformation]

example {n : ℕ} (rho : (Matrix (Fin n → ℕ) (Fin n → ℕ) ℂ)) (i j : Fin n) :
    (BinaryTree.split (.leaf i) (.leaf j)).information rho = clusterMutualInformation rho {i} {j} := by
  simp [BinaryTree.information, BinaryTree.parties]

example {I : Type*} (rho : (Matrix I I ℂ)) : kernelProduct rho 0 = 0 := by
  funext i j
  simp [kernelProduct]

example {m : ℕ} (X Y : Matrix (Fin m) (Fin m) ℂ)
    (h : ¬ LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin) :
    finiteRelativeEntropy X Y = ⊤ := by simp [QAlgorithms.Papers.Independent.Dependency50.P13.finiteRelativeEntropy, h]

end QAlgorithms.Papers.Independent.Intakethird100.P63


