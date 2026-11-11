-- Prove2me | Definitions.Def_KAQROM_IsBMPrefixLearner
-- name    : KAQROM_IsBMPrefixLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:38.96519+00:00
-- url     : https://prove2.me/theorems/d4663ddb-f8ca-4304-beab-487a904f6027
-- title:
--   The properties of $\mathsf{Learn}^{\mathsf{BM}}_\eta$ in Lemma 5.11
-- statement:
--   A prefix learner $L$ for the protocol $\Pi^{\mathrm{mr}}$, run on the complete public prefix transcript, **has the properties of Lemma 5.11 at level $\eta$** when, writing *reachable* for $\Pr[M=m,\ L^H(m)=h]>0$:
--
--   1. $L$ aborts with probability at most $\eta$;
--   2. for every reachable $(m,h)$, $\tfrac12\|\omega^{AB}_{m,h}-\omega^A_{m,h}\otimes\omega^B_{m,h}\|_1\le\eta$;
--   3. for every reachable $(m,h)$ and every $x\notin\mathrm{Dom}(h)$, $\Pr[x\in\mathrm{Dom}(T_A)\mid\mathsf F_{m,h}]\le\eta$;
--   4. for every reachable $(m,h)$ and every oracle $H$, $L^H(m)=h\iff h\preceq H$.
--
--   The hybrid steps of the proof of Theorem 5.14 are stated for every learner with these properties.
--
--   **Formalization Note** The query bound of Lemma 5.11 (i) is not part of the predicate; Lemma 5.11 states it alongside, and the hybrid steps do not use it.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.11, p.35

import Mathlib
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_CQ
import Definitions.Def_KAQROM_Protocol
import Definitions.Def_KAQROM_QueryTree
import Definitions.Def_KAQROM_Protocol_Omega

namespace KAQROM

namespace Protocol

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
  [DecidableEq Msg] [Fintype K]

/-- `Pr[M = m, Learn^H(m) = h]`, over `H ← ℋ` and the honest prefix (Lemma 5.11, p.35). A pair
`(m, h)` is **reachable** when this is positive. -/
noncomputable def probReach (P : Protocol X ℓ Msg K) (L : PrefixLearner (Fin P.n → Msg) X ℓ)
    (m : Fin P.n → Msg) (h : PartialOracle X ℓ) : ℝ := by
  classical
  exact (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ *
    ∑ H : Oracle X ℓ, ∑ o : P.Outcome,
      if P.msgs o = m ∧ L.result H m = some h then P.weight H o else 0

/-- The probability that the learner aborts when run on the complete prefix transcript. -/
noncomputable def abortProb (P : Protocol X ℓ Msg K) (L : PrefixLearner (Fin P.n → Msg) X ℓ) :
    ℝ := by
  classical
  exact (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ *
    ∑ H : Oracle X ℓ, ∑ o : P.Outcome,
      if L.result H (P.msgs o) = none then P.weight H o else 0

end Protocol

/-- **The properties of `Learn^{BM,H}_η` in Lemma 5.11** (p.35), for a prefix learner `L` of the
protocol `P` (a deterministic algorithm with classical oracle access that, on a complete public
prefix transcript, outputs a partial oracle or aborts); `(m, h)` ranges over reachable pairs:

* (i), second half: `L` aborts with probability at most `η`;
* (ii) `½‖ω^{AB}_{m,h} − ω^A_{m,h} ⊗ ω^B_{m,h}‖₁ ≤ η`;
* (iii) `Pr[x ∈ Dom(T_A) | F_{m,h}] ≤ η` for every `x ∉ Dom(h)`;
* "Moreover": `Learn^{BM,H}_η(m) = h ⟺ h ⪯ H` for every oracle `H`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Lemma 5.11, p.35.

**Formalization Note.** The query bound of Lemma 5.11 (i) (at most `Q_learn` queries) is not part
of this predicate; Lemma 5.11 states it next to the predicate, so that the hybrid steps, which do
not use it, assume only what their proofs use. -/
structure IsBMPrefixLearner {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type}
    [Fintype Msg] [DecidableEq Msg] [Fintype K] (P : Protocol X ℓ Msg K) (η : ℝ)
    (L : PrefixLearner (Fin P.n → Msg) X ℓ) : Prop where
  abort_le : P.abortProb L ≤ η
  indep : ∀ m h, 0 < P.probReach L m h →
    cqTraceDist (P.omegaAB m h) (cqProd (P.omegaA m h) (P.omegaB m h)) ≤ η
  queried_le : ∀ m h, 0 < P.probReach L m h → ∀ x, h x = none → P.probQueriedA m h x ≤ η
  result_iff : ∀ m h, 0 < P.probReach L m h → ∀ H : Oracle X ℓ, L.result H m = some h ↔ h.Le H

end KAQROM


