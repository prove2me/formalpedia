-- Prove2me | Definitions.Def_CompDesignBFM_Amc
-- name    : CompDesignBFM_Amc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:20.35125+00:00
-- url     : https://prove2.me/theorems/89fb65b7-4208-4625-8a6f-ab20afb3dee7
-- title:
--   Allocation rule A_mc
-- statement:
--   Given bids $b$, the allocation $A_{\mathrm{mc}}(b)$ is the global maximizer of the potential $\Phi^F_b$ over all subsets, ties broken by the fixed priority:
--
--   $$A_{\mathrm{mc}}(b)=\arg\max_{T\subseteq N}F(T)\prod_{i\in T}\Bigl(1-\frac{b_i}{B}\Bigr)_+.$$
--
--   **Formalization Note** Defined by choice from an existence lemma; `Amc_isMax` and `Amc_least` state that it maximizes the potential and has the least rank among maximizers, which determines it for an injective rank.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, eq. (10), p.20 (PDF 22), with Remark 2.1, p.12

import Mathlib
import Definitions.Def_CompDesignBFM_pot

namespace CompDesignBFM

/-- A potential maximizer of least rank exists, for any rank function. -/
theorem exists_Amc {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (r : Finset (Fin n) → ℕ) (b : Fin n → ℝ) :
    ∃ S : Finset (Fin n), (∀ T, pot F B b T ≤ pot F B b S) ∧
      ∀ T, (∀ U, pot F B b U ≤ pot F B b T) → r S ≤ r T := by
  classical
  obtain ⟨S₀, -, hS₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin n)))
    (pot F B b) ⟨∅, Finset.mem_univ _⟩
  have hne : (Finset.univ.filter fun T : Finset (Fin n) => ∀ U, pot F B b U ≤ pot F B b T).Nonempty :=
    ⟨S₀, by simpa using fun U => hS₀ U (Finset.mem_univ _)⟩
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image _ r hne
  refine ⟨S, by simpa using hS, fun T hT => hmin T (by simpa using hT)⟩

/-- The allocation rule `A_mc` (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, eq. (10), p.20, PDF 22, with Remark 2.1, p.12): the maximizer of
the potential `Φ^F_b` over all subsets, ties broken by the fixed rank `r`. -/
noncomputable def Amc {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (r : Finset (Fin n) → ℕ) (b : Fin n → ℝ) :
    Finset (Fin n) :=
  Classical.choose (exists_Amc F B r b)

/-- `A_mc b` is a global maximizer of the potential. -/
theorem Amc_isMax {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (r : Finset (Fin n) → ℕ) (b : Fin n → ℝ)
    (T : Finset (Fin n)) : pot F B b T ≤ pot F B b (Amc F B r b) :=
  (Classical.choose_spec (exists_Amc F B r b)).1 T

/-- `A_mc b` has the least rank among the global maximizers. -/
theorem Amc_least {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (r : Finset (Fin n) → ℕ) (b : Fin n → ℝ)
    (T : Finset (Fin n)) (hT : ∀ U, pot F B b U ≤ pot F B b T) : r (Amc F B r b) ≤ r T :=
  (Classical.choose_spec (exists_Amc F B r b)).2 T hT

end CompDesignBFM


