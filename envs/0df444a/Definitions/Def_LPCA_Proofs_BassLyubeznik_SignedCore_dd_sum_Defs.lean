-- Prove2me | Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
-- name    : LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:29:09.162008+00:00
-- url     : https://prove2.me/theorems/8cea960c-b80e-4a11-ae2c-fb9098062f0e
-- title:
--   Square-zero signed differential on convex families
-- statement:
--   This bundle supplies square-zero signed differential on convex families. The declarations concern finite subsets of linearly ordered vertex types, with field-valued signs where used. Cancellation and square-zero statements retain their convex-family hypotheses; the contraction identity requires family membership to be invariant under insertion of the chosen vertex. No contraction of an arbitrary subset family is asserted.
--
--   The included constructions and necessary compatibility results are:
--
--   - The inner `d∘d` sum, indexed by the subtype of `𝓕`-sets of integer cardinality `c`, under the stated convex-family and endpoint-membership hypotheses, vanishes when `J` has cardinality `c - 1`: the cardinality constraint is automatic for the surviving terms, so the sum agrees with the one over all of `𝓕`.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Proofs/BassLyubeznik/SignedCore/dd_sum.lean, selected declarations in lines 23–88; source SHA-256 e3052a53c321fdddd39b8da43f23e780bfd60a379ba35435b9ad2573dc6ed897; source certificate Sapelo2 job 49172236.

import Mathlib
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs

namespace Proofs.BassLyubeznik.SignedCore

open Finset

variable {V : Type*} [LinearOrder V] {k : Type*} [Field k]

-- SWARM:HELPERS-BEGIN
/-- The inner `d∘d` sum, indexed by the subtype of `𝓕`-sets of integer cardinality `c`,
vanishes as soon as `J` has cardinality `c - 1`: the cardinality constraint is automatic
for the surviving terms, so the sum agrees with the one over all of `𝓕`. -/
theorem dd_sum_inner [Fintype V] {𝓕 : Finset V → Prop} [DecidablePred 𝓕] (hconv : IsConvex 𝓕)
    {c : ℤ} {J J'' : Finset V} (hJ : 𝓕 J) (hJ'' : 𝓕 J'') (hJc : (J.card : ℤ) + 1 = c) :
    ∑ J' : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = c}, inc k J J'.1 * inc k J'.1 J'' = 0 := by
  have hsub : (Finset.univ.filter (fun J : Finset V => 𝓕 J ∧ (J.card : ℤ) = c))
      ⊆ Finset.univ.filter 𝓕 := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.1⟩
  have hzero : ∀ x ∈ Finset.univ.filter 𝓕,
      x ∉ Finset.univ.filter (fun J : Finset V => 𝓕 J ∧ (J.card : ℤ) = c) →
      inc k J x * inc k x J'' = 0 := by
    intro x hx hx'
    have hxF : 𝓕 x := (Finset.mem_filter.mp hx).2
    have hc : (x.card : ℤ) ≠ c := fun h =>
      hx' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hxF, h⟩⟩)
    have hz : inc k J x = 0 := by
      by_contra hne
      obtain ⟨j, hjJ, rfl⟩ := exists_insert_of_inc_ne_zero hne
      rw [Finset.card_insert_of_notMem hjJ] at hc
      push_cast at hc
      omega
    rw [hz, zero_mul]
  have hmain : ∑ J' ∈ Finset.univ.filter (fun J : Finset V => 𝓕 J ∧ (J.card : ℤ) = c),
      inc k J J' * inc k J' J'' = 0 := by
    rw [Finset.sum_subset hsub hzero]
    exact inc_inc_sum hconv hJ hJ''
  have hmem : ∀ x : Finset V,
      x ∈ Finset.univ.filter (fun J : Finset V => 𝓕 J ∧ (J.card : ℤ) = c) ↔
        (𝓕 x ∧ (x.card : ℤ) = c) := by
    intro x
    simp [Finset.mem_filter]
  rw [← hmain]
  exact (Finset.sum_subtype _ hmem (fun J' => inc k J J' * inc k J' J'')).symm
-- SWARM:HELPERS-END
-- SWARM:STATEMENT-BEGIN
theorem dd_sum [Fintype V] {𝓕 : Finset V → Prop} [DecidablePred 𝓕] (hconv : IsConvex 𝓕) (m n : ℤ)
    (f : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n - m} → k)
    (J'' : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n + 1 + 1 - m}) :
    ∑ J' : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n + 1 - m},
      inc k J'.1 J''.1 * ∑ J, inc k J.1 J'.1 * f J = 0
-- SWARM:STATEMENT-END
:= by
  have key : ∀ J : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n - m},
      ∑ J' : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n + 1 - m},
        inc k J.1 J'.1 * inc k J'.1 J''.1 = 0 := by
    intro J
    refine dd_sum_inner hconv J.2.1 J''.2.1 ?_
    have hJ := J.2.2
    omega
  calc ∑ J' : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n + 1 - m},
        inc k J'.1 J''.1 * ∑ J, inc k J.1 J'.1 * f J
      = ∑ J' : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n + 1 - m},
          ∑ J : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n - m},
            inc k J.1 J'.1 * inc k J'.1 J''.1 * f J := by
        refine Finset.sum_congr rfl fun J' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun J _ => ?_
        ring
    _ = ∑ J : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n - m},
          ∑ J' : {J : Finset V // 𝓕 J ∧ (J.card : ℤ) = n + 1 - m},
            inc k J.1 J'.1 * inc k J'.1 J''.1 * f J := Finset.sum_comm
    _ = 0 := by
        refine Finset.sum_eq_zero fun J _ => ?_
        rw [← Finset.sum_mul, key J, zero_mul]
-- SWARM:PROOF-END

end Proofs.BassLyubeznik.SignedCore


