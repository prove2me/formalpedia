-- Prove2me | Definitions.Def_IntADSat_Supplement_dualLattice
-- name    : IntADSat_Supplement_dualLattice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:47:04.654185+00:00
-- url     : https://prove2.me/theorems/a7295428-7769-4ee8-8c33-dbb52fa2649d
-- title:
--   Dual lattice $K^\#$
-- statement:
--   For a lattice $K\subseteq V=\mathbb Q^n$, the **dual lattice** is
--   $$K^\#=\{x\in V:\ \langle x,y\rangle\in\mathbb Z\text{ for all }y\in K\},$$
--   with $\langle\cdot,\cdot\rangle$ the standard inner product. For $K=\Lambda_G$ of an AD-full graph, $\Lambda\subseteq\Lambda^\#$ and the discriminant group is $\Lambda^\#/\Lambda$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), §S5, p.40 (PDF 41)

import Mathlib

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The **dual lattice** `K^# = {x ∈ V : ⟨x, K⟩ ⊆ ℤ}` of a lattice `K ⊆ V = ℚⁿ` for the standard inner
product (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §S5, p.40 (PDF 41)).

**Formalization Note** `⟨x, y⟩` is the dot product `x ⬝ᵥ y`; the closure proofs are structural. -/
def dualLattice {n : ℕ} (K : Submodule ℤ (Fin n → ℚ)) : Submodule ℤ (Fin n → ℚ) where
  carrier := {x | ∀ y ∈ K, ∃ z : ℤ, x ⬝ᵥ y = z}
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨z₁, h₁⟩ := ha y hy
    obtain ⟨z₂, h₂⟩ := hb y hy
    exact ⟨z₁ + z₂, by rw [add_dotProduct, h₁, h₂]; push_cast; ring⟩
  zero_mem' := by
    intro y _
    exact ⟨0, by simp⟩
  smul_mem' := by
    intro c x hx y hy
    obtain ⟨z, h⟩ := hx y hy
    exact ⟨c * z, by rw [smul_dotProduct, h]; push_cast; simp⟩

end IntADSat.Supplement


