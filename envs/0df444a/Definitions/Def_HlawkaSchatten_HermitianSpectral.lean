-- Prove2me | Definitions.Def_HlawkaSchatten_HermitianSpectral
-- name    : HlawkaSchatten_HermitianSpectral
-- status  : Definition
-- author  : @savarin
-- created : 2026-09-27T16:39:14.517433+00:00
-- url     : https://prove2.me/theorems/f3cb2cbd-93b4-4c5f-87c1-76454a754549
-- title:
--   Hermitian functional calculus, and trace-level Bregman/Mazur quantities for symmetric operators
-- statement:
--   Fix a complex inner product space $E$; some definitions below additionally need $E$ finite-dimensional (`[FiniteDimensional ℂ E]`), noted per item. Let $\iota,\kappa$ be finite index types.
--
--   - `spectralDiagonal e a`, for an orthonormal basis $e=(e_i)_{i\in\iota}$ of $E$ and real weights $a:\iota\to\mathbb{R}$, is the self-adjoint operator $\sum_i a_i\,\lvert e_i\rangle\langle e_i\rvert$, with eigenvalue $a_i$ on each $e_i$: "build a Hermitian operator from a prescribed real diagonal in a given basis." No finite-dimensionality hypothesis is needed for this definition.
--   - `hermitianFunctionalCalculus f A hA`, for a symmetric $A:E\to E$ (`hA : A.IsSymmetric`, $E$ finite-dimensional) and $f:\mathbb{R}\to\mathbb{R}$, is `spectralDiagonal` applied to Mathlib's canonical eigenvector basis and eigenvalue list of $A$: the operator $f(A)$ obtained from the (finite-dimensional) spectral theorem. The bundle records that this agrees with $f(\mu)$ on *any* $\mu$-eigenvector of $A$ (not only the canonical basis vectors); that it is the identity when $f=\mathrm{id}$; that a pointwise product of scalar functions becomes composition of the corresponding operators; that iterating the calculus composes the two functions; and — the fact the `HermitianDilation` bundle relies on — that the calculus of $x\mapsto g(x^2)$ at $A$ equals the calculus of $g$ at $A\circ A$.
--   - `spectralBregmanTrace p e a f b` and `spectralMazurDistanceSq p e a f b`, for two orthonormal bases $e,f$ (index types $\iota,\kappa$, $E$ finite-dimensional) with real weight lists $a,b$, are explicit trace expressions built from `spectralDiagonal`. They equal the overlap-weighted sums
--   $$
--   \sum_{i,j} w_{ij}\,\beta_p(a_i,b_j) \qquad\text{and}\qquad \sum_{i,j} w_{ij}\,\bigl(\psi_p(a_i)-\psi_p(b_j)\bigr)^2,
--   $$
--   where $w_{ij}=\mathrm{orthonormalBasisOverlap}\,e\,f\,(i,j)$ (the `SpectralLift` bundle), $\beta_p$ is the scalar Bregman divergence, and $\psi_p$ the scalar Mazur map (`ScalarBregman` bundle) — proved on the separate pages `spectralBregmanTrace_eq_sum` and `spectralMazurDistanceSq_eq_sum`, the trace-level lift of the scalar comparison.
--   - `hermitianBregmanTrace p A B hA hB` and `hermitianMazurDistanceSq p A B hA hB` are the same two quantities taken directly at two symmetric operators $A,B:E\to E$ ($E$ finite-dimensional), using their own canonical eigenbases and eigenvalues.
--   - `hermitianMazurMap p A hA` $:=$ `hermitianFunctionalCalculus (scalarMazur p) A hA` — the Hermitian (operator) Mazur map, applying $\psi_p$ to $A$ via functional calculus.
--
--   Briefly: the bundle also shows that for $p>0$ the Hermitian Mazur maps with exponents $p$ and $4/p$ are mutually inverse (`hermitianMazurMap_four_div_comp`); and that, writing $M_A:=\mathrm{hermitianMazurMap}\,p\,A\,hA$ and $M_B$ likewise, `hermitianMazurDistanceSq p A B hA hB` equals the real trace of $(M_A-M_B)\circ(M_A-M_B)$ — its genuine Hilbert–Schmidt distance-squared in operator form. (At $p=2$, `hermitianBregmanTrace` is half of `hermitianMazurDistanceSq` — `hermitianBregmanTrace_two_eq` in the source module, not part of this bundle.)
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/HermitianSpectral.lean#L45-L603

import Definitions.Def_HlawkaSchatten_ScalarBregman
import Definitions.Def_HlawkaSchatten_ScalarRatio
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Finite Hermitian spectral trace expansions

This file connects the overlap-weighted scalar comparison to traces of
finite-dimensional symmetric complex-linear maps.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace
open RCLike
open ComplexConjugate

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]





/-- The self-adjoint operator with prescribed real diagonal in an
orthonormal basis. -/
noncomputable def spectralDiagonal
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ) : E →ₗ[ℂ] E :=
  ∑ i, (a i : ℂ) •
    (InnerProductSpace.rankOne ℂ (e i) (e i)).toLinearMap

@[simp]
theorem spectralDiagonal_apply_basis
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ) (i : ι) :
    spectralDiagonal e a (e i) = (a i : ℂ) • e i := by
  classical
  simp [spectralDiagonal, OrthonormalBasis.inner_eq_ite]

/-- Coordinate formula for a spectral diagonal map in its defining basis. -/
theorem spectralDiagonal_repr_apply
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ) (x : E) (i : ι) :
    e.repr (spectralDiagonal e a x) i = (a i : ℂ) * e.repr x i := by
  classical
  calc
    e.repr (spectralDiagonal e a x) i =
        e.repr (spectralDiagonal e a (∑ j, e.repr x j • e j)) i := by
      rw [e.sum_repr]
    _ = (a i : ℂ) * e.repr x i := by
      simp only [map_sum, spectralDiagonal_apply_basis, map_smul]
      simp_rw [e.repr_apply_apply]
      simp [Pi.single_apply, mul_comm]

theorem spectralDiagonal_isSymmetric
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ) :
    (spectralDiagonal e a).IsSymmetric := by
  classical
  rw [spectralDiagonal]
  apply LinearMap.isSymmetric_sum Finset.univ
  intro i _
  apply InnerProductSpace.isSymmetric_rankOne_self (e i) |>.smul
  apply Complex.ext <;> simp

/-- Reconstructing a symmetric map from Mathlib's canonical eigenbasis and
eigenvalue list returns the original map. -/
theorem spectralDiagonal_eigenvectorBasis_eq [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    spectralDiagonal (hA.eigenvectorBasis rfl) (hA.eigenvalues rfl) = A := by
  apply (hA.eigenvectorBasis rfl).toBasis.ext
  intro i
  simpa only [OrthonormalBasis.coe_toBasis] using
    (spectralDiagonal_apply_basis (hA.eigenvectorBasis rfl)
      (hA.eigenvalues rfl) i).trans (hA.apply_eigenvectorBasis rfl i).symm

/-- The trace of a real diagonal operator is the sum of its diagonal. -/
theorem re_trace_spectralDiagonal [FiniteDimensional ℂ E]
    (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ) :
    (spectralDiagonal e a |>.trace ℂ E).re = ∑ i, a i := by
  rw [LinearMap.trace_eq_sum_inner (spectralDiagonal e a) e, Complex.re_sum]
  apply Fintype.sum_congr
  intro i
  rw [spectralDiagonal_apply_basis, inner_smul_right, e.inner_eq_one,
    mul_one]
  exact Complex.ofReal_re (a i)

/-- Apply a real scalar function to a symmetric map through Mathlib's
canonical finite-dimensional spectral resolution. -/
noncomputable def hermitianFunctionalCalculus [FiniteDimensional ℂ E]
    (f : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) : E →ₗ[ℂ] E :=
  spectralDiagonal (hA.eigenvectorBasis rfl) (f ∘ hA.eigenvalues rfl)

@[simp]
theorem hermitianFunctionalCalculus_apply_eigenvectorBasis
    [FiniteDimensional ℂ E] (f : ℝ → ℝ) (A : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) (i : Fin (Module.finrank ℂ E)) :
    hermitianFunctionalCalculus f A hA (hA.eigenvectorBasis rfl i) =
      (f (hA.eigenvalues rfl i) : ℂ) • hA.eigenvectorBasis rfl i := by
  exact spectralDiagonal_apply_basis (hA.eigenvectorBasis rfl)
    (f ∘ hA.eigenvalues rfl) i

/-- The canonical functional calculus acts by `f μ` on every `μ`-eigenvector,
not only on the chosen canonical eigenbasis. -/
theorem hermitianFunctionalCalculus_apply_of_apply_eq_smul
    [FiniteDimensional ℂ E] (f : ℝ → ℝ) (A : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) (x : E) (μ : ℝ)
    (hx : A x = (μ : ℂ) • x) :
    hermitianFunctionalCalculus f A hA x = (f μ : ℂ) • x := by
  apply (hA.eigenvectorBasis rfl).repr.injective
  ext i
  unfold hermitianFunctionalCalculus
  rw [spectralDiagonal_repr_apply]
  simp only [Function.comp_apply, map_smul]
  have hi := congrArg (fun y ↦ (hA.eigenvectorBasis rfl).repr y i) hx
  rw [hA.eigenvectorBasis_apply_self_apply] at hi
  simp only [map_smul] at hi
  by_cases hcoord : (hA.eigenvectorBasis rfl).repr x i = 0
  · simp [hcoord]
  · have heigen : hA.eigenvalues rfl i = μ := by
      apply Complex.ofReal_injective
      exact mul_right_cancel₀ hcoord hi
    rw [heigen]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]

theorem hermitianFunctionalCalculus_isSymmetric [FiniteDimensional ℂ E]
    (f : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    (hermitianFunctionalCalculus f A hA).IsSymmetric :=
  spectralDiagonal_isSymmetric (hA.eigenvectorBasis rfl)
    (f ∘ hA.eigenvalues rfl)

@[simp]
theorem hermitianFunctionalCalculus_id [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianFunctionalCalculus id A hA = A := by
  simpa only [hermitianFunctionalCalculus, Function.id_comp] using
    spectralDiagonal_eigenvectorBasis_eq A hA

/-- Functional calculus of the zero operator vanishes when the scalar
function vanishes at zero. -/
@[simp]
theorem hermitianFunctionalCalculus_zero [FiniteDimensional ℂ E]
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    hermitianFunctionalCalculus f (0 : E →ₗ[ℂ] E)
      LinearMap.IsSymmetric.zero = 0 := by
  apply LinearMap.ext
  intro x
  rw [hermitianFunctionalCalculus_apply_of_apply_eq_smul
    f _ _ x 0 (by simp)]
  simp [hf]

theorem re_trace_hermitianFunctionalCalculus [FiniteDimensional ℂ E]
    (f : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    ((hermitianFunctionalCalculus f A hA).trace ℂ E).re =
      ∑ i, f (hA.eigenvalues rfl i) := by
  exact re_trace_spectralDiagonal (hA.eigenvectorBasis rfl)
    (f ∘ hA.eigenvalues rfl)

/-- Trace of Hermitian functional calculus after real scaling, evaluated in
an eigenbasis of the original operator. -/
theorem re_trace_hermitianFunctionalCalculus_real_smul
    [FiniteDimensional ℂ E] (f : ℝ → ℝ) (c : ℝ)
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    ((hermitianFunctionalCalculus f ((c : ℂ) • A)
      (hA.smul (by simp))).trace ℂ E).re =
      ∑ i, f (c * hA.eigenvalues rfl i) := by
  rw [LinearMap.trace_eq_sum_inner _ (hA.eigenvectorBasis rfl), Complex.re_sum]
  apply Fintype.sum_congr
  intro i
  have heig : ((c : ℂ) • A) (hA.eigenvectorBasis rfl i) =
      ((c * hA.eigenvalues rfl i : ℝ) : ℂ) •
        hA.eigenvectorBasis rfl i := by
    rw [LinearMap.smul_apply, hA.apply_eigenvectorBasis]
    simp only [smul_smul]
    congr 1
    exact (map_mul (algebraMap ℝ ℂ) c (hA.eigenvalues rfl i)).symm
  rw [hermitianFunctionalCalculus_apply_of_apply_eq_smul f _ _ _ _ heig,
    inner_smul_right, (hA.eigenvectorBasis rfl).inner_eq_one]
  simp

/-- The trace of the power potential is homogeneous under positive real
scaling. -/
theorem re_trace_powerPotential_real_smul [FiniteDimensional ℂ E]
    {p c : ℝ} (hc : 0 < c) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    ((hermitianFunctionalCalculus (powerPotential p) ((c : ℂ) • A)
      (hA.smul (by simp))).trace ℂ E).re =
      c ^ p *
        ((hermitianFunctionalCalculus (powerPotential p) A hA).trace ℂ E).re := by
  rw [re_trace_hermitianFunctionalCalculus_real_smul,
    re_trace_hermitianFunctionalCalculus, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact powerPotential_mul_of_pos p _ hc





/-- Pointwise multiplication of real functions becomes composition of their
Hermitian functional-calculus maps. -/
theorem hermitianFunctionalCalculus_mul [FiniteDimensional ℂ E]
    (f g : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianFunctionalCalculus (fun x ↦ f x * g x) A hA =
      (hermitianFunctionalCalculus f A hA).comp
        (hermitianFunctionalCalculus g A hA) := by
  apply (hA.eigenvectorBasis rfl).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis,
    hermitianFunctionalCalculus_apply_eigenvectorBasis,
    LinearMap.comp_apply, map_smul, smul_smul]
  rw [mul_comm, Complex.ofReal_mul]

/-- Applying functional calculus twice composes the scalar functions. -/
theorem hermitianFunctionalCalculus_comp [FiniteDimensional ℂ E]
    (f g : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianFunctionalCalculus f (hermitianFunctionalCalculus g A hA)
        (hermitianFunctionalCalculus_isSymmetric g A hA) =
      hermitianFunctionalCalculus (f ∘ g) A hA := by
  apply (hA.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis,
    hermitianFunctionalCalculus_apply_of_apply_eq_smul f _ _ _
      (g (hA.eigenvalues rfl i))
      (hermitianFunctionalCalculus_apply_eigenvectorBasis g A hA i),
    hermitianFunctionalCalculus_apply_eigenvectorBasis]
  rfl

theorem isSymmetric_comp_self (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    (A.comp A).IsSymmetric := by
  intro x y
  simp only [LinearMap.comp_apply]
  rw [hA (A x) y, hA x (A y)]

/-- Even functional calculus factors through the square of a symmetric map. -/
theorem hermitianFunctionalCalculus_comp_self [FiniteDimensional ℂ E]
    (g : ℝ → ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianFunctionalCalculus (fun x ↦ g (x ^ 2)) A hA =
      hermitianFunctionalCalculus g (A.comp A) (isSymmetric_comp_self A hA) := by
  apply (hA.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis,
    hermitianFunctionalCalculus_apply_eigenvectorBasis]
  rw [hermitianFunctionalCalculus_apply_of_apply_eq_smul]
  simp only [LinearMap.comp_apply, hA.apply_eigenvectorBasis, map_smul,
    smul_smul, Complex.ofReal_pow]
  rw [pow_two]
  rfl

/-- The Hermitian power-potential map factors through the nonnegative square
of the symmetric operator. -/
theorem hermitianFunctionalCalculus_powerPotential_comp_self
    [FiniteDimensional ℂ E] (p : ℝ) (A : E →ₗ[ℂ] E)
    (hA : A.IsSymmetric) :
    hermitianFunctionalCalculus (powerPotential p) A hA =
      hermitianFunctionalCalculus (fun y ↦ y ^ (p / 2) / p)
        (A.comp A) (isSymmetric_comp_self A hA) := by
  rw [show powerPotential p = (fun x ↦ (x ^ 2) ^ (p / 2) / p) by
    funext x
    exact powerPotential_eq_sq_rpow_div_two p x]
  exact hermitianFunctionalCalculus_comp_self (fun y ↦ y ^ (p / 2) / p) A hA







/-- The trace form of the power-potential Bregman divergence for two finite
Hermitian spectral resolutions. -/
noncomputable def spectralBregmanTrace [FiniteDimensional ℂ E]
    (p : ℝ) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) : ℝ :=
  (spectralDiagonal e (powerPotential p ∘ a) |>.trace ℂ E).re -
    (spectralDiagonal f (powerPotential p ∘ b) |>.trace ℂ E).re -
    (((spectralDiagonal e a).comp
      (spectralDiagonal f (powerGradient p ∘ b))).trace ℂ E).re +
    (spectralDiagonal f (fun j ↦ powerGradient p (b j) * b j) |>.trace ℂ E).re





/-- The expanded Hilbert--Schmidt square of the difference of the two
spectral Mazur maps. -/
noncomputable def spectralMazurDistanceSq [FiniteDimensional ℂ E]
    (p : ℝ) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) : ℝ :=
  (spectralDiagonal e (fun i ↦ scalarMazur p (a i) ^ 2) |>.trace ℂ E).re -
    2 * (((spectralDiagonal e (scalarMazur p ∘ a)).comp
      (spectralDiagonal f (scalarMazur p ∘ b))).trace ℂ E).re +
    (spectralDiagonal f (fun j ↦ scalarMazur p (b j) ^ 2) |>.trace ℂ E).re









/-- Canonical trace Bregman quantity for two symmetric maps, using Mathlib's
eigenvalue lists and eigenvector bases. -/
noncomputable def hermitianBregmanTrace [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) : ℝ :=
  spectralBregmanTrace p (hA.eigenvectorBasis rfl) (hA.eigenvalues rfl)
    (hB.eigenvectorBasis rfl) (hB.eigenvalues rfl)

/-- Canonical expanded Hilbert--Schmidt square between the spectral Mazur
maps of two symmetric operators. -/
noncomputable def hermitianMazurDistanceSq [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) : ℝ :=
  spectralMazurDistanceSq p (hA.eigenvectorBasis rfl) (hA.eigenvalues rfl)
    (hB.eigenvectorBasis rfl) (hB.eigenvalues rfl)

/-- The Hermitian Mazur map obtained from the canonical spectral calculus. -/
noncomputable def hermitianMazurMap [FiniteDimensional ℂ E]
    (p : ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) : E →ₗ[ℂ] E :=
  hermitianFunctionalCalculus (scalarMazur p) A hA

theorem hermitianMazurMap_isSymmetric [FiniteDimensional ℂ E]
    (p : ℝ) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    (hermitianMazurMap p A hA).IsSymmetric :=
  hermitianFunctionalCalculus_isSymmetric (scalarMazur p) A hA

/-- The Hermitian Mazur maps with exponents `p` and `4 / p` are inverse. -/
theorem hermitianMazurMap_four_div_comp [FiniteDimensional ℂ E]
    {p : ℝ} (hp : 0 < p) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianMazurMap (4 / p) (hermitianMazurMap p A hA)
        (hermitianMazurMap_isSymmetric p A hA) = A := by
  unfold hermitianMazurMap
  rw [hermitianFunctionalCalculus_comp]
  rw [show scalarMazur (4 / p) ∘ scalarMazur p = id by
    funext x
    unfold scalarMazur
    simp only [Function.comp_apply]
    rw [signedPower_comp]
    rw [show (4 / p / 2) * (p / 2) = 1 by field_simp; norm_num]
    exact signedPower_one x]
  exact hermitianFunctionalCalculus_id A hA



/-- Operator-functional-calculus form of the canonical Hermitian Mazur
square. -/
theorem hermitianMazurDistanceSq_eq_functionalCalculus
    [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    hermitianMazurDistanceSq p A B hA hB =
      ((hermitianFunctionalCalculus
        (fun x ↦ scalarMazur p x ^ 2) A hA).trace ℂ E).re -
      2 * (((hermitianFunctionalCalculus (scalarMazur p) A hA).comp
        (hermitianFunctionalCalculus (scalarMazur p) B hB)).trace ℂ E).re +
      ((hermitianFunctionalCalculus
        (fun x ↦ scalarMazur p x ^ 2) B hB).trace ℂ E).re := by
  rfl

/-- Against the zero operator, the Mazur Hilbert--Schmidt square is `p`
times the power-potential trace. -/
theorem hermitianMazurDistanceSq_zero_eq_powerPotentialTrace
    [FiniteDimensional ℂ E] {p : ℝ} (hp : 0 < p)
    (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    hermitianMazurDistanceSq p A 0 hA LinearMap.IsSymmetric.zero =
      p * ((hermitianFunctionalCalculus
        (powerPotential p) A hA).trace ℂ E).re := by
  rw [hermitianMazurDistanceSq_eq_functionalCalculus,
    hermitianFunctionalCalculus_zero
      (scalarMazur p) (scalarMazur_zero p),
    hermitianFunctionalCalculus_zero
      (fun x ↦ scalarMazur p x ^ 2) (by simp)]
  simp only [LinearMap.comp_zero, map_zero, Complex.zero_re,
    mul_zero, sub_zero, add_zero]
  rw [re_trace_hermitianFunctionalCalculus,
    re_trace_hermitianFunctionalCalculus, Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  rw [scalarMazur_sq hp]
  unfold powerPotential
  field_simp

/-- The expanded spectral Mazur quantity is the real trace of the square of
the difference of the two Hermitian Mazur maps. -/
theorem hermitianMazurDistanceSq_eq_re_trace_sq_sub
    [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    hermitianMazurDistanceSq p A B hA hB =
      ((((hermitianMazurMap p A hA - hermitianMazurMap p B hB).comp
        (hermitianMazurMap p A hA - hermitianMazurMap p B hB)).trace ℂ E).re) := by
  rw [hermitianMazurDistanceSq_eq_functionalCalculus]
  have hA_sq :
      hermitianFunctionalCalculus (fun x ↦ scalarMazur p x ^ 2) A hA =
        (hermitianMazurMap p A hA).comp (hermitianMazurMap p A hA) := by
    rw [show (fun x ↦ scalarMazur p x ^ 2) =
        (fun x ↦ scalarMazur p x * scalarMazur p x) by funext x; ring]
    exact hermitianFunctionalCalculus_mul (scalarMazur p) (scalarMazur p) A hA
  have hB_sq :
      hermitianFunctionalCalculus (fun x ↦ scalarMazur p x ^ 2) B hB =
        (hermitianMazurMap p B hB).comp (hermitianMazurMap p B hB) := by
    rw [show (fun x ↦ scalarMazur p x ^ 2) =
        (fun x ↦ scalarMazur p x * scalarMazur p x) by funext x; ring]
    exact hermitianFunctionalCalculus_mul (scalarMazur p) (scalarMazur p) B hB
  rw [hA_sq, hB_sq]
  unfold hermitianMazurMap
  simp only [LinearMap.sub_comp, LinearMap.comp_sub, map_sub, Complex.sub_re]
  rw [LinearMap.trace_comp_comm'
    (hermitianFunctionalCalculus (scalarMazur p) B hB)
    (hermitianFunctionalCalculus (scalarMazur p) A hA)]
  ring











end HlawkaSchatten


