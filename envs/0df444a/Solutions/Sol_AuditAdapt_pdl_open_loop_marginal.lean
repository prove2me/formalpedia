-- Prove2me | solution 1 for AuditAdapt.pdl_open_loop_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-21T04:06:12.263858+00:00
-- url     : https://prove2.me/submissions/01520d9f-7910-4a98-af0a-1bcd7632c19b

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_AuditAdapt_stateLaw
import Definitions.Def_AuditAdapt_totalCost
import Definitions.Def_AuditAdapt_openLoopMarginal
import Theorems.Thm_AuditAdapt_openLoopMarginal_isPolicy
import Theorems.Thm_AuditAdapt_value_eq_inner_Q
import Theorems.Thm_AuditAdapt_lemma_3_3

namespace AuditAdapt

open FoundationsRL.RLBasics

theorem _root_.solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (hπ : IsPolicy H π) :
    totalCost M π - totalCost M (openLoopMarginal M π) =
      ∑ t ∈ Finset.range H, ∑ s : S, stateLaw M π t s *
        ∑ a : A, Q M (openLoopMarginal M π) t s a * (π t s a - marginal M π t a) := by
  have hν : IsPolicy H (openLoopMarginal M π) :=
    openLoopMarginal_isPolicy M π hπ
  rw [lemma_3_3 M π (openLoopMarginal M π) hπ hν]
  refine Finset.sum_congr rfl ?_
  intro t ht
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [(value_eq_inner_Q M (openLoopMarginal M π) hν).2.1 t
    (Finset.mem_range.mp ht) s]
  simp only [openLoopMarginal]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  ring

end AuditAdapt
