-- Prove2me | Definitions.Def_SublinearChoresMMS_Disposal_FiniteLaw
-- name    : SublinearChoresMMS_Disposal_FiniteLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:28:49.758052+00:00
-- url     : https://prove2.me/theorems/b27e3b79-182f-4971-bd49-3522cf116f56
-- title:
--   Finite allocation and coefficient lotteries
-- statement:
--   A **finite probability law** on a type of outcomes $\Omega$ is a finite list of pairs $(p_a,\omega_a)$ with real weights. It is a probability law when
--
--   $$p_a\ge0,\qquad \sum_a p_a=1.$$
--
--   Its expectation of a real function $f$ is $\sum_a p_af(\omega_a)$. An atom belongs to the support when its weight is positive; repeated outcomes are allowed and their weights add. The wrapper uses the published finite-list probability predicate and expectation, and supplies indexed access to the list. It can describe both complete-allocation lotteries and coefficient lotteries without requiring rational probabilities or a finite ambient outcome type.
--
--   These are the lotteries used in Section 2 and Lemmas 3.2–3.3.
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), §2 and §§3.2–3.3, printed pp. 4, 9–12 / PDF pp. 5, 10–13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery

namespace SublinearChoresMMS.Disposal

/-- Indexed access to the published finite real lottery, with its probability predicate.
Section 2, printed p. 4 / PDF p. 5. Repeated atoms are permitted. -/
structure FiniteLaw (α : Type*) where
  toLaw : OAI.CliqueFreeIndependence.Lottery.Law α
  isProb : OAI.CliqueFreeIndependence.Lottery.IsProb toLaw

def FiniteLaw.size {α : Type*} (P : FiniteLaw α) : ℕ := P.toLaw.length

def FiniteLaw.atom {α : Type*} (P : FiniteLaw α) (a : Fin P.size) : α := P.toLaw[a.val].2

def FiniteLaw.weight {α : Type*} (P : FiniteLaw α) (a : Fin P.size) : ℝ := P.toLaw[a.val].1

noncomputable def FiniteLaw.mean {α : Type*} (P : FiniteLaw α) (f : α → ℝ) : ℝ :=
  OAI.CliqueFreeIndependence.Lottery.expect P.toLaw f

end SublinearChoresMMS.Disposal


