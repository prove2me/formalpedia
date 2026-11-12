-- Prove2me | Definitions.Def_SketchAttr_LOO_Taylor
-- name    : SketchAttr_LOO_Taylor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:26:46.5712+00:00
-- url     : https://prove2.me/theorems/4b5b9a95-801a-44c2-a965-15ecded156eb
-- title:
--   Section 3.1 — normalized Taylor tensors, contractions and proxies
-- statement:
--   For a circuit polynomial $f:\mathbb C^n\to\mathbb C$, the normalized order-$r$ Taylor tensor at zero has entries
--   $$T_f^{(r)}(j_1,\ldots,j_r)=\frac1{r!}D^r f(0)[e_{j_1},\ldots,e_{j_r}].$$
--   Here $e_i$ is the standard basis vector. Tensor contraction multiplies coordinates without conjugation. The Frobenius norm is the square root of the sum of squared absolute values of all ordered tensor entries. The Hermitian vector pairing conjugates its first argument. Symmetry means invariance under every permutation of indices, and real tensors have real entries. First-index slices and the holomorphic gradient use these coordinates.
--
--   The module also defines the normalized gradient coefficient $c_r(g)=\frac1r[z^{r-1}]\nabla f(zg)$, the directional tensor estimator $T[g^{\otimes r}](g^\dagger x)^r/r!$, and the proxies $v_{i,r}=\binom{2r-2}{r-1}\|T_f^{(r)}[e_i,\cdot]\|_F^2$ and $s_i=\sum_{r=2}^N\sqrt{v_{i,r}}$.
--
--   These objects share one normalization across the accuracy statements. **Formalization Note** Vectors have the Euclidean norm. The order-zero slice is totalized to zero and unused in source-domain statements. Taylor derivatives are used on circuit polynomials; no analyticity condition is replaced by a default derivative value.
-- source:
--   Liaw, Mehta, Velegkas, Zhou, Sketching Language Models for Context Attribution, STOC 2027 submission #9 (PDF sha256 86af2569e45c55b1009e7453d4f53047b5820d44868a7f528bdb6fed1a2ef0e2), pp. 8–9, Section 3.1; p. 12, Section 4.2; p. 15, Section 5.2; canonical PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/9.pdf

import Mathlib
import Definitions.Def_SketchAttr_LOO_Circuit
open scoped ENNReal

namespace SketchAttr.LOO

abbrev Vec (n : ℕ) := EuclideanSpace ℂ (Fin n)
abbrev Tensor (n r : ℕ) := (Fin r → Fin n) → ℂ

def Tensor.IsSymmetric {n r : ℕ} (T : Tensor n r) : Prop :=
  ∀ (σ : Equiv.Perm (Fin r)) (j : Fin r → Fin n), T (j ∘ σ) = T j

def Tensor.IsReal {n r : ℕ} (T : Tensor n r) : Prop :=
  ∀ j, (T j).im = 0

noncomputable def basis {n : ℕ} (i : Fin n) : Vec n :=
  WithLp.toLp 2 (Pi.single i 1)

noncomputable def tensorContract {n r : ℕ} (T : Tensor n r) (x : Fin r → Vec n) : ℂ :=
  ∑ j : Fin r → Fin n, T j * ∏ a, x a (j a)

noncomputable def frobNorm {n r : ℕ} (T : Tensor n r) : ℝ :=
  Real.sqrt (∑ j, ‖T j‖ ^ 2)

noncomputable def taylorTensor {n : ℕ} (f : Vec n → ℂ) (r : ℕ) : Tensor n r :=
  fun j => (Nat.factorial r : ℂ)⁻¹ * iteratedFDeriv ℂ r f 0 (fun a => basis (j a))

noncomputable def diagonal {n r : ℕ} (T : Tensor n r) (w : Vec n) : ℂ :=
  tensorContract T (fun _ => w)

/-- Hermitian vector pairing: only the first argument is conjugated. -/
noncomputable def hermitianPair {n : ℕ} (g x : Vec n) : ℂ :=
  ∑ i, starRingEnd ℂ (g i) * x i

noncomputable def directionalSketch {n r : ℕ} (T : Tensor n r) (x g : Vec n) : ℂ :=
  diagonal T g * hermitianPair g x ^ r / (Nat.factorial r : ℂ)

/-- First-index slice for positive order. The unused order-zero case is
totalized to zero; all source uses have r >= 1. -/
noncomputable def slice {n : ℕ} : {r : ℕ} → Tensor n r → Fin n → Tensor n (r-1)
  | 0, _, _ => fun _ => 0
  | _r+1, T, i => fun j => T (Fin.cons i j)

noncomputable def gradient {n : ℕ} (f : Vec n → ℂ) (w : Vec n) : Vec n :=
  WithLp.toLp 2 (fun i => fderiv ℂ f w (basis i))

noncomputable def circuitFunction {n : ℕ} (c : Circuit n 1) : Vec n → ℂ :=
  fun w => c.scalar (fun i => w i)

noncomputable def sketchCoeff {n : ℕ} (f : Vec n → ℂ) (r : ℕ) (g : Vec n) : Vec n :=
  WithLp.toLp 2 fun i =>
    (Nat.factorial (r-1) : ℂ)⁻¹ / (r : ℂ) *
      iteratedFDeriv ℂ (r-1) (fun w => gradient f w i) 0 (fun _ => g)

noncomputable def varianceProxy {n : ℕ} (f : Vec n → ℂ) (r : ℕ) (i : Fin n) : ℝ :=
  (Nat.choose (2*r-2) (r-1) : ℝ) * frobNorm (slice (taylorTensor f r) i) ^ 2

noncomputable def errorProxy {n : ℕ} (f : Vec n → ℂ) (N : ℕ) (i : Fin n) : ℝ :=
  ∑ r ∈ Finset.Icc 2 N, Real.sqrt (varianceProxy f r i)

end SketchAttr.LOO


