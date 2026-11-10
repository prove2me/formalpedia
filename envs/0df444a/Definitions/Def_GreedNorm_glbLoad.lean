-- Prove2me | Definitions.Def_GreedNorm_glbLoad
-- name    : GreedNorm_glbLoad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:33.747828+00:00
-- url     : https://prove2.me/theorems/1eb78979-e38d-4fe4-9e0c-9a51cff12138
-- title:
--   GLB load vector $\mathrm{load}(\sigma)$
-- statement:
--   Given processing times $p_{ij}$ and, for every machine $i$, a monotone symmetric norm $f_i$ on $\mathbb R^n$, the load of machine $i$ under the assignment $\sigma$ is $\mathrm{load}_i(\sigma)=f_i(p_i[\sigma])$, and the load vector is
--
--   $$
--   \mathrm{load}(\sigma)=\bigl(f_i(p_i[\sigma])\bigr)_{i\in M}\in\mathbb R^m .
--   $$
--
--   **Formalization Note** The norms are plain functions `f i : (Fin n → ℝ) → ℝ`; the theorems assume each satisfies `SymNormLoad.IsMonotoneSymmetricNorm`.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_GreedNorm_glbVec

namespace GreedNorm

/-- **The GLB load vector** `load(σ) = (f_i(p_i[σ]))_{i ∈ M}`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 1.1, p.1 (PDF 3): "Denote the load of machine i by loadi(σ) := fi(pi[σ]) [...]
Let load(σ) := {loadi(σ)}i∈M be the m-dimensional load vector induced by σ."

**Formalization Note** The norms are plain functions `f i : (Fin n → ℝ) → ℝ`; the theorems
assume each is a `SymNormLoad.IsMonotoneSymmetricNorm`. Machines are `Fin m`, 0-based. -/
def glbLoad {n m : ℕ} (p : Fin m → Fin n → ℝ) (f : Fin m → (Fin n → ℝ) → ℝ)
    (σ : Fin n → Fin m) : Fin m → ℝ :=
  fun i => f i (glbVec p σ i)

end GreedNorm


