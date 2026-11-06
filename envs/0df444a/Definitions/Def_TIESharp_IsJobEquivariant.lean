-- Prove2me | Definitions.Def_TIESharp_IsJobEquivariant
-- name    : TIESharp_IsJobEquivariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:19.310482+00:00
-- url     : https://prove2.me/theorems/e576d130-3906-4f60-8f3e-79aab55602be
-- title:
--   Invariance of a family under job relabeling
-- statement:
--   A family is **invariant under job relabeling** if for every job permutation $\pi$, moving column $j$ of the bids to position $\pi(j)$, $(b\pi^{-1})_{ij}=b_{i,\pi^{-1}(j)}$, relabels the assignment law and leaves every payment unchanged:
--   $$y^m_{A\circ\pi^{-1}}(b\pi^{-1})=y^m_A(b),\qquad p^m_i(b\pi^{-1})=p^m_i(b),$$
--   at every job count and every nonnegative profile. This is the job symmetry of the replacement family in Lemma 4.2.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 4.2, p.14; Step 1, p.14

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_Family

set_option autoImplicit false

namespace TIESharp

/-- A family is **invariant under job relabeling** (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, Lemma 4.2, p.14, and Step 1, p.14:
"job-equivariant families"). For a job permutation `π`, moving column `j` of the bid profile to
position `π(j)`, `(b ∘ π⁻¹)_{ij} = b_{i, π⁻¹(j)}`, relabels the assignment law,
`y(b ∘ π⁻¹)_{A ∘ π⁻¹} = y(b)_A`, and leaves every machine's payment unchanged.

**Formalization Note.** Imposed at every job count `m` and every nonnegative profile. -/
def IsJobEquivariant {n : ℕ} (F : Family n) : Prop :=
  ∀ (m : ℕ) (b : Fin n → Fin m → ℝ) (π : Equiv.Perm (Fin m)), Nonneg b →
    (∀ A : Fin m → Fin n,
      F.alloc m (fun i j => b i (π.symm j)) (A ∘ π.symm) = F.alloc m b A) ∧
    ∀ i, F.pay m (fun i' j => b i' (π.symm j)) i = F.pay m b i

end TIESharp


