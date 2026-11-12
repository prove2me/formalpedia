-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialThm25
-- name    : OddOrder_GroupTheory_RepresentationTheory_ExtraspecialThm25
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:22.721298+00:00
-- url     : https://prove2.me/theorems/20022abb-6749-436d-bded-af839ce23264
-- title:
--   Towards BG Theorem 2.5: the divisibility conclusion
-- statement:
--   Assembles the machinery of Proposition 2.4 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem* into the divisibility step of Theorem 2.5: for a faithful representation $V$ of $P\rtimes\langle x\rangle$ with $P$ extraspecial, $h\mid q^n\pm 1$ where $q=\dim V$. The file reduces the conclusion to the single remaining input $\dim E_0=\dim E_m+1$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ExtraspecialThm25.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ExtraspecialThm25.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_EigenspaceBlockDecomp
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclicEndConjCount

namespace OddOrder.RepresentationTheory

open Finset EigenspaceUnderCyclicAction Module

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- **BG Theorem 2.5, `C_V(H) = 0` step (conditional on the H-module multiplicities).** With the
same keystone `dim E₀ = dim E_m + 1`, if the fixed space `C_V(x) = V₀` is trivial (`dim V₀ = 0`) and
`q ≥ 2`, then `q = h − 1`, i.e. `h = q + 1`. (This is the half Thm 3.4 uses for the even/odd
contradiction.) -/
theorem sum_eigenspaceFinDim_eq_sub_one_of_finrank_cyclicEndConjEigenspace {epsilon : F}
    {g : LinearMap.GeneralLinearGroup F V} {h : ℕ} [NeZero h] [FiniteDimensional F V]
    (hprim : IsPrimitiveRoot epsilon h)
    (hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily epsilon (g : Module.End F V) h))
    (hh : 2 ≤ h)
    (hEdim : ∀ m : Fin h, m ≠ 0 →
      finrank F (cyclicEndConjEigenspaceFin epsilon g (0 : Fin h))
        = finrank F (cyclicEndConjEigenspaceFin epsilon g m) + 1)
    (hq : 2 ≤ ∑ i : Fin h, (cyclicEigenspaceFinDim epsilon (g : Module.End F V) i : ℤ))
    (h0 : cyclicEigenspaceFinDim epsilon (g : Module.End F V) (0 : Fin h) = 0) :
    (∑ i : Fin h, (cyclicEigenspaceFinDim epsilon (g : Module.End F V) i : ℤ)) = (h : ℤ) - 1 := by
  have Hsum : ∀ m : Fin h, m ≠ 0 →
      ∑ i : Fin h, ((cyclicEigenspaceFinDim epsilon (g : Module.End F V) i : ℤ)
        - (cyclicEigenspaceFinDim epsilon (g : Module.End F V) (i + m) : ℤ)) ^ 2 = 2 := by
    intro m hm
    rw [sum_sq_sub_finrank_cyclicEndConjEigenspaceFin hprim hV m, hEdim m hm]
    push_cast; ring
  exact prop24k_fin hh (fun i => (cyclicEigenspaceFinDim epsilon (g : Module.End F V) i : ℤ))
    (fun i => Int.natCast_nonneg _) hq Hsum (by simpa using h0)

end OddOrder.RepresentationTheory


