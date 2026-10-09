-- Prove2me | Definitions.Def_AffineVolterra_Transform_Core
-- name    : AffineVolterra_Transform_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:03.49425+00:00
-- url     : https://prove2.me/theorems/746df55b-37d4-406e-8cc0-eee6ce499310
-- title:
--   §2 — matrix kernels, convolutions, and second-kind resolvents
-- statement:
--   For matrix-valued kernels $K$ and $R$, their Volterra convolution is
--
--   $$
--   (K*R)(t)=\int_0^t K(t-s)R(s)\,ds.
--   $$
--
--   A second-kind resolvent $R$ of $K$ is locally integrable and satisfies $K*R=R*K=K-R$ almost everywhere on positive time. The definitions also give convolution against a column or row vector, componentwise local $L^p$ membership, and $E_B=K-R_B*K$.
--
--   **Formalization Note** The matrix products retain their order. Matrix-valued local $L^p$ membership is checked entrywise. Kernels are real-time functions, and the convolution identity is interpreted almost everywhere because $L^1_{\mathrm{loc}}$ kernels are equivalence classes in the source.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, (2.1)–(2.2), pp. 4–5; (2.11), p. 9

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace AffineVolterra.Transform

abbrev State (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev RVec (d : ℕ) := Fin d → ℝ
abbrev CVec (d : ℕ) := Fin d → ℂ
abbrev RKernel (d : ℕ) := ℝ → Matrix (Fin d) (Fin d) ℝ

/-- Componentwise local Lebesgue integrability on positive time. -/
def KernelLpLoc {d : ℕ} (p : ℝ≥0∞) (K : RKernel d) : Prop :=
  ∀ i j (T : ℝ), 0 < T → MemLp (fun t => K t i j) p (volume.restrict (Set.Ioc 0 T))

/-- The matrix convolution of (2.1), with Lebesgue measure. -/
noncomputable def kernelConv {d : ℕ} (K R : RKernel d) (t : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ k, ∫ s in (0 : ℝ)..t, K (t - s) i k * R s k j

/-- The resolvent of the second kind in (2.11). Equalities are a.e. on positive time. -/
def IsResolvent {d : ℕ} (K R : RKernel d) : Prop :=
  KernelLpLoc 1 K ∧ KernelLpLoc 1 R ∧
  (∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
    kernelConv K R t = K t - R t ∧ kernelConv R K t = K t - R t)

/-- Matrix kernel acting on a real column, as in (2.2). -/
noncomputable def kernelVecConv {d : ℕ} (K : RKernel d) (v : ℝ → RVec d) (t : ℝ) : RVec d :=
  fun i => ∑ j, ∫ s in (0 : ℝ)..t, K (t - s) i j * v s j

/-- Row-vector convolution with a matrix kernel. -/
noncomputable def rowKernelConv {d : ℕ} (v : ℝ → CVec d) (K : RKernel d) (t : ℝ) : CVec d :=
  fun j => ∑ i, ∫ s in (0 : ℝ)..t, v s i * (K (t - s) i j : ℂ)

/-- Pointwise multiplication of a complex row by a real matrix. -/
def rowMul {d : ℕ} (v : CVec d) (M : Matrix (Fin d) (Fin d) ℝ) : CVec d :=
  fun j => ∑ i, v i * (M i j : ℂ)

/-- Real matrix multiplication, used for K B and B K. -/
def kernelRight {d : ℕ} (K : RKernel d) (B : Matrix (Fin d) (Fin d) ℝ) : RKernel d :=
  fun t => K t * B

def kernelLeft {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (K : RKernel d) : RKernel d :=
  fun t => B * K t

/-- E_B = K - R_B * K, with the sign convention of (2.11). -/
noncomputable def EKernel {d : ℕ} (K R : RKernel d) : RKernel d :=
  fun t => K t - kernelConv R K t

end AffineVolterra.Transform


