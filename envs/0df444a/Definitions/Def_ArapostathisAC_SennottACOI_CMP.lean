-- Prove2me | Definitions.Def_ArapostathisAC_SennottACOI_CMP
-- name    : ArapostathisAC_SennottACOI_CMP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:05:35.585188+00:00
-- url     : https://prove2.me/theorems/a2c03d72-d83b-49b1-9e2c-8107b4f2131f
-- title:
--   Stationary deterministic policies Π_SD of the countable-state controlled Markov process of §5, as admissible policies
-- statement:
--   This file adds, on top of the shared model of the countable-state controlled Markov process of Arapostathis, Borkar, Fernández-Gaucherand, Ghosh and Marcus (1993) (state space $S=\{0,1,2,\dots\}$, compact nonempty action sets $U(i)$, nonnegative cost $c$, transition law $P$, admissible history-dependent randomized policies $\Pi$, path measures $P^\pi_i$ and the cost criteria), the class $\Pi_{SD}$ used in this mission.
--
--   A **stationary deterministic policy** $f\in\Pi_{SD}$ is a map $f:S\to A$ with $f(i)\in U(i)$ for every state $i$ (p. 286). It is regarded as an admissible policy $\pi\in\Pi$ that, after every history ending in state $i$, chooses the action $f(i)$ with probability one; this policy is admissible because $f(i)\in U(i)$.
--
--   These are the policies whose existence Theorem 5.9 asserts, and along which discount optimal and average cost optimal behaviour is compared with that of all admissible policies.
--
--   **Formalization Note** The type and the embedding coincide definitionally with `StationaryPolicy` and `StationaryPolicy.toPolicy` of the shared module `ArapostathisAC.VanishingDiscount.CMP`, so the shared predicates `IsDiscOptimal` and `IsAvgOptimal` apply to them. The file also registers the `IsMarkovKernel` instance of the one-step kernel of the path measure. Measurability of $f$ is automatic on the discrete state space.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), pp. 284–288 (§2.1, §2.2, §2.4, Assumption 2.1), p. 299 (§5 standing assumptions) and p. 301 (definition of h_β)

import Mathlib
import Definitions.Def_ArapostathisAC_VanishingDiscount_CMP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.SennottACOI

attribute [instance] ArapostathisAC.VanishingDiscount.CMP.P_markov

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

attribute [instance] ArapostathisAC.VanishingDiscount.Policy.isMarkov

/-- A stationary deterministic policy `f ∈ Π_SD`: a map `f : ℕ → A` with `f(i) ∈ U(i)`. -/
def StationaryPolicy (M : ArapostathisAC.VanishingDiscount.CMP A) : Type _ :=
  {f : ℕ → A // ∀ i, f i ∈ M.U i}

/-- A stationary deterministic policy viewed as an admissible policy: after every history ending in
state `i` it chooses `f(i)` with probability one. -/
noncomputable def StationaryPolicy.toPolicy {M : ArapostathisAC.VanishingDiscount.CMP A} (f : StationaryPolicy M) : ArapostathisAC.VanishingDiscount.Policy M where
  rule _ := Kernel.deterministic (fun hist => f.1 hist.2)
    ((measurable_from_top (f := f.1)).comp measurable_snd)
  adm t hist := by
    rw [Kernel.deterministic_apply' _ _ (M.U_compact hist.2).isClosed.measurableSet.compl]
    simp [f.2 hist.2]

omit [MetricSpace A] [BorelSpace A] in
lemma measurable_histFin (t : ℕ) : Measurable (ArapostathisAC.VanishingDiscount.histFin (A := A) t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

instance (M : ArapostathisAC.VanishingDiscount.CMP A) (π : ArapostathisAC.VanishingDiscount.Policy M) (t : ℕ) : IsMarkovKernel (ArapostathisAC.VanishingDiscount.stepKernel M π t) := by
  have h1 : IsMarkovKernel (M.P.comap (ArapostathisAC.VanishingDiscount.lastPair (A := A) t) (measurable_pi_apply _)) :=
    Kernel.IsMarkovKernel.comap _ _
  have h2 : IsMarkovKernel ((π.rule (t + 1)).comap (fun p : (Π _ : Finset.Iic t, ℕ × A) × ℕ =>
      (ArapostathisAC.VanishingDiscount.histFin t p.1, p.2)) (((measurable_histFin t).comp measurable_fst).prodMk measurable_snd)) :=
    Kernel.IsMarkovKernel.comap _ _
  exact Kernel.IsMarkovKernel.compProd _ _

end ArapostathisAC.SennottACOI


