-- Prove2me | Definitions.Def_GreedNorm_glbCost
-- name    : GreedNorm_glbCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:50.740205+00:00
-- url     : https://prove2.me/theorems/950dfde8-cb80-42b5-9142-26e811e6472c
-- title:
--   Generalized makespan $g(\mathrm{load}(\sigma))$
-- statement:
--   For a GLB instance with outer monotone symmetric norm $g$ on $\mathbb R^m$, the **generalized makespan** of an assignment $\sigma$ is
--
--   $$
--   g\bigl(\mathrm{load}(\sigma)\bigr).
--   $$
--
--   GLB asks for an assignment minimizing it. For $g=\ell_\infty$ and $f_i=\ell_1$ this is the classical makespan.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_GreedNorm_glbLoad

namespace GreedNorm

/-- **The generalized makespan** `g(load(σ))` of an assignment `σ`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.1, p.1 (PDF 3): "Define the generalized makespan of σ to be g (load(σ)), where
g : R^m_{≥0} → R_{≥0} is another monotone and symmetric norm."

**Formalization Note** `g : (Fin m → ℝ) → ℝ` is a plain function; the theorems assume it is a
`SymNormLoad.IsMonotoneSymmetricNorm`. -/
def glbCost {n m : ℕ} (p : Fin m → Fin n → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (g : (Fin m → ℝ) → ℝ) (σ : Fin n → Fin m) : ℝ :=
  g (glbLoad p f σ)

end GreedNorm


