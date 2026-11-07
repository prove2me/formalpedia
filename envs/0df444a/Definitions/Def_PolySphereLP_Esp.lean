-- Prove2me | Definitions.Def_PolySphereLP_Esp
-- name    : PolySphereLP_Esp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:25.221204+00:00
-- url     : https://prove2.me/theorems/5fb429ba-2f23-468b-b761-a5aea5bee0bd
-- title:
--   The space $E_{n,k}$ of symmetric trace-free tensors
-- statement:
--   $E_{n,k}$ is the complex vector space of order-$k$ tensors $T$ on $\mathbb C^n$ that are
--   1. **symmetric**: invariant under every permutation of the $k$ slots;
--   2. **trace-free**: for $k\ge2$, $(\mathrm{Tr}_2T)_{i_3\dots i_k}=\sum_jT_{j,j,i_3,\dots,i_k}=0$.
--
--   Tensors of order $0$ or $1$ are trace-free by convention. Under $G\leftrightarrow T_G$ the space $E_{n,k}$ corresponds to $\mathcal H^{\mathbb C}_{n,k}$ ($\Delta G=0$ iff $\mathrm{Tr}_2T_G=0$).
--
--   **Formalization Note** The trace condition is imposed for every pair of distinct slots (other indices fixed); for a symmetric tensor this is the same as contracting the first two slots, and for $k\le1$ there is no pair, matching the convention.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), §2.3, p.12; p.13

import Mathlib
import Definitions.Def_PolySphereLP_Tensor

namespace PolySphereLP

/-- **The space `E_{n,k}` of symmetric trace-free complex tensors of order `k`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), p.13:
"the space `E_{n,k}` of symmetric trace-free complex tensors of order `k`"; §2.3, p.12: the trace
`(Tr₂ T)_{i₃…i_k} = ∑ⱼ T_{j,j,i₃,…,i_k}` (for `k ≥ 2`), and "Tensors of order zero or one are
trace-free by convention."

`T ∈ Esp n k` iff `T` is invariant under every permutation of its slots, and contracting any two
distinct slots `a ≠ b` (other indices fixed) gives `0`.

**Formalization Note.** For a symmetric tensor, contracting slots `a ≠ b` equals contracting the first
two ("Symmetry makes the choice of the two traced slots immaterial"), so the condition is `Tr₂ T = 0`;
for `k ≤ 1` there is no pair `a ≠ b` and the condition is empty, matching the convention. -/
def Esp (n k : ℕ) : Submodule ℂ (Tensor n k) where
  carrier := {T | (∀ (π : Equiv.Perm (Fin k)) (i : Fin k → Fin n), T (i ∘ π) = T i) ∧
    ∀ (i : Fin k → Fin n) (a b : Fin k), a ≠ b →
      ∑ j : Fin n, T (Function.update (Function.update i a j) b j) = 0}
  add_mem' := by
    rintro S T ⟨hS1, hS2⟩ ⟨hT1, hT2⟩
    refine ⟨fun π i => by simp [hS1 π i, hT1 π i], fun i a b hab => ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, hS2 i a b hab, hT2 i a b hab, add_zero]
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c T ⟨hT1, hT2⟩
    refine ⟨fun π i => by simp [hT1 π i], fun i a b hab => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hT2 i a b hab, mul_zero]

end PolySphereLP


