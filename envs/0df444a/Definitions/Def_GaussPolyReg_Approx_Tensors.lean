-- Prove2me | Definitions.Def_GaussPolyReg_Approx_Tensors
-- name    : GaussPolyReg_Approx_Tensors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:41.566209+00:00
-- url     : https://prove2.me/theorems/409c47ba-2b5d-4ea0-a602-bca474645fa2
-- title:
--   Hermite coefficient tensors, flattenings, matchings and tensor networks
-- statement:
--   For $p\in H_d(X_1,\ldots,X_n)$ and an ordered tuple $i=(i_1,\ldots,i_d)$, let $\alpha(i)$ record its multiplicities. Define
--
--   $$P_i=\frac{\mathbb E[p\,\mathrm{He}_{\alpha(i)}]}{\sqrt{d!}}.$$
--
--   This computes the symmetric Hermite coefficient tensor in (3.3). Its Frobenius norm is the square root of the sum of squared entries. A flattening partitions the first $r$ slots from the remaining $d-r$ slots; its spectral norm is the supremum of its bilinear form on two Euclidean unit balls. The contraction $P\otimes_r P$ is $(P^{(r)})^\top P^{(r)}$.
--
--   Perfect matchings are fixed-point-free involutions on explicit labeled objects, with no pair inside one group. Label-compatible matchings are counted directly. Tensor networks attach symmetric arrays to the incident endpoint slots of a published finite multigraph and sum over every edge labeling. Parallel edges remain distinct, and a self-loop contributes two tensor slots carrying the same edge label. The covariance permanent sums over all bijections between two copies of the index set. A centered Gaussian vector is specified by the laws of all its real linear combinations.
--
--   These definitions supply the combinatorial and analytic objects of Appendix B; they assert no moment identities.
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), §3.3.1, pp.8–9, (3.3)–(3.4); Appendix B, pp.17–19,22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_ContPatrol_Multigraph
import Definitions.Def_GaussPolyReg_Approx_Chaos

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

abbrev Tensor (n d : ℕ) := (Fin d → Fin n) → ℝ

/-- Multiplicity of each label of an ordered tuple, (3.3), p.8. -/
def tupleIndex {n d : ℕ} (i : Fin d → Fin n) : ℕ →₀ ℕ :=
  ∑ s : Fin d, Finsupp.single (i s).val 1

/-- The unique symmetric coefficient tensor, computed from Hermite coefficients.
E[p He_{α(i)}]/√d! is exactly P_i under (3.3), not an arbitrary witness. -/
def coefficientTensor {n d : ℕ} (p : Original) : Tensor n d :=
  fun i => (∫ x, p x * heMulti (tupleIndex i) x ∂gaussianProduct ℕ) /
    Real.sqrt (d.factorial : ℝ)

def frobenius {J : Type*} [Fintype J] (P : J → ℝ) : ℝ :=
  Real.sqrt (∑ j, (P j) ^ 2)

/-- First r positions versus the remaining d-r positions. -/
def flatten {n d : ℕ} (P : Tensor n d) (r : ℕ)
    (i : Fin r → Fin n) (j : Fin (d-r) → Fin n) : ℝ :=
  P (fun s => if h : s.val < r then i ⟨s.val, h⟩
    else j ⟨s.val-r, by omega⟩)

/-- Spectral norm, explicitly the ℓ² bilinear operator norm (never the matrix sup norm).
The set is nonempty (zero vectors) and bounded (finite matrix). -/
def flattenNorm {n d : ℕ} (P : Tensor n d) (r : ℕ) : ℝ :=
  sSup {a : ℝ | ∃ (u : EuclideanSpace ℝ (Fin r → Fin n))
      (v : EuclideanSpace ℝ (Fin (d-r) → Fin n)),
      ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧ a = |∑ i, ∑ j, u i * flatten P r i j * v j|}

/-- P⊗_r P as (P^(r))ᵀP^(r), App. B, p.17. -/
def contraction {n d : ℕ} (P : Tensor n d) (r : ℕ) :
    ((Fin (d-r) → Fin n) × (Fin (d-r) → Fin n)) → ℝ :=
  fun jk => ∑ i : Fin r → Fin n, flatten P r i jk.1 * flatten P r i jk.2

/-- Explicit objects in the groups of Lemma B.2, p.18. -/
abbrev MatchingObjects {I : Type*} {ℓ : ℕ} (α : Fin ℓ → I →₀ ℕ) :=
  (j : Fin ℓ) × (i : (α j).support) × Fin (α j i)

def labelMatchings {I : Type*} {ℓ : ℕ} (α : Fin ℓ → I →₀ ℕ) :
    Finset (Equiv.Perm (MatchingObjects α)) := by
  classical
  exact Finset.univ.filter (fun M =>
    (∀ u, M (M u) = u) ∧
    (∀ u, (M u).1 ≠ u.1) ∧
    (∀ u, (M u).2.1.val = u.2.1.val))

/-- Oriented presentation of a finite multigraph. Edges are distinct identifiers, so parallel
edges remain distinct. Self-loops are excluded explicitly in Lemma B.3. -/
abbrev Network (V E : Type) := ContPatrol.Multigraph V E

/-- Incident endpoint slots: a loop contributes both ends, as required by tensor order
deg(a). In the loopless case of B.3 these are in bijection with incident edges. -/
def Network.Incident {V E : Type} (π : Network V E) (a : V) :=
  {s : E × Bool // (if s.2 then π.src s.1 else π.tgt s.1) = a}

def Network.value {V E : Type} [Fintype V] [Fintype E]
    (π : Network V E) (n : ℕ) (T : (a : V) → (π.Incident a → Fin n) → ℝ) : ℝ := by
  classical
  exact ∑ φ : E → Fin n, ∏ a, T a (fun s => φ s.val.1)

def Network.symmetric {V E : Type} (π : Network V E) (n : ℕ)
    (T : (a : V) → (π.Incident a → Fin n) → ℝ) : Prop :=
  ∀ a (σ : Equiv.Perm (π.Incident a)) (x : π.Incident a → Fin n),
    T a (x ∘ σ) = T a x

def Network.normProduct {V E : Type} [Fintype V] [Fintype E]
    (π : Network V E) (n : ℕ) (T : (a : V) → (π.Incident a → Fin n) → ℝ) : ℝ := by
  classical
  letI (a : V) : Fintype (π.Incident a) := by
    unfold Network.Incident
    infer_instance
  exact ∏ a, frobenius (T a)

/-- Covariance matching permanent in B.6: bijections between the two copies of [k]. -/
def covariancePermanent {k : ℕ} (p : Fin k → Original) : ℝ :=
  ∑ σ : Equiv.Perm (Fin k), ∏ a, pairing (p a) (p (σ a))

/-- A centered Gaussian vector with covariance Σ, including singular Σ. -/
def IsCenteredGaussian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} (Z : Ω → Vec k) (C : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  AEMeasurable Z μ ∧ ∀ t : Vec k,
    μ.map (fun x => ∑ a, t a * Z x a) =
      gaussianReal 0 (Real.toNNReal (∑ a, ∑ b, t a * C a b * t b))

end GaussPolyReg.Approx


