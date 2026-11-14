-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorRelays
-- name    : ConsistentSubmodular_Deterministic_Certificates_SelectorRelays
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:16:50.793916+00:00
-- url     : https://prove2.me/theorems/da39df94-391e-4f62-9a75-dd2fd0fc40e4
-- title:
--   Selector relay: envelope validity and the state `relayState` for a relayed child stage
-- statement:
--   Let $P$ be a canonical atomic profile with stages $0,\dots,m$ (designated residuals $\lambda_t$ = `designated`, baseline, benchmark $\mathrm{baseline}_t + \mathrm{designated}_t$, active stages $\mathrm{baseline}_t < 3\,\mathrm{designated}_t$). The selector walks through stages that are high ($> 3/4$) and below one, each carrying an access path from $\delta_0$, a strong credit, and a relay history to a parent.
--
--   - `relayState` builds a `SelectorState` at a child stage $s$ from a selector state $S$ at a parent $h < s$. The inputs are: $s$ is active; the raw envelope $q = $ `rawEnvelope h` satisfies $q \ge 1$; the denominator $\mathrm{designated}_h - \mathrm{residual}(h,s)$ is positive; the raw ratio of $(h,s)$ attains $q$; the edge from $h$ to $s$ is pessimistically safe; the child is high, $\mathrm{designated}_s > 3/4$; the actual-eligibility test (for $q \le 2$) and the sufficient-eligibility test (for $q > 2$) fail strictly at every later active stage, in the form $q\,(\mathrm{benchmark}_t - \mathrm{designated}_h) < 2\,\mathrm{designated}_h\,q - 3(4\,\mathrm{designated}_h - 3)$; and $\mathrm{designated}_h \ge 33/40$ whenever $q < 4/3$. The relay history uses $q$ as parameter (with $q < 3$ from the envelope bound), and the child's access path and strong credit are obtained by extending the parent's.
--
--   The file also proves that the raw envelope of the parent gives nonnegative envelope slack at every later active stage.
--
--   These relays are the step by which the selector advances from a stage to its successor when constructing a checkpoint certificate, part of the proof of Theorem 7.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/SelectorRelays.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ActualCheckpoint
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SuffConstructor
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Envelope
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarGeometry
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ConstructorScalar
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_FourThirdsBoundary

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem selector_envelope (hP : P.Canonical) (h : Fin (m + 1)) :
    ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h (P.rawEnvelope h) t := by
  classical
  intro t ht ha
  exact P.rawEnvelope_valid hP h t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, ha⟩)

def relayState (hP : P.Canonical) (h s : Fin (m + 1)) (S : SelectorState P h)
    (hhs : h < s) (ha : P.Active s)
    (hq1 : 1 ≤ P.rawEnvelope h)
    (hd : 0 < P.designated h - P.residual h s)
    (heq : P.rawRatio h s = P.rawEnvelope h)
    (hsafe : P.PessimisticSafeEdge h s) (hhigh : (3 : ℝ) / 4 < P.designated s)
    (hfactual : P.rawEnvelope h ≤ 2 → ∀ t, h < t → P.Active t →
      0 ≤ P.actualEligibility h (P.rawEnvelope h) t →
      P.rawEnvelope h * (P.benchmark t - P.designated h) <
        2 * P.designated h * P.rawEnvelope h - 3 * (4 * P.designated h - 3))
    (hfsuff : 2 < P.rawEnvelope h → ∀ t, h < t → P.Active t →
      0 ≤ P.suffEligibility h (P.rawEnvelope h) t →
      P.rawEnvelope h * (P.benchmark t - P.designated h) <
        2 * P.designated h * P.rawEnvelope h - 3 * (4 * P.designated h - 3))
    (hsmall : P.rawEnvelope h < 4 / 3 → 33 / 40 ≤ P.designated h) :
    SelectorState P s := by
  let H : RelayHistory P s := {
    parent := h
    advances := hhs
    child_active := ha
    parameter := P.rawEnvelope h
    parameter_ge_one := hq1
    parameter_lt_three := P.rawEnvelope_lt_three hP h (fun _ _ => Or.inl S.below_unit)
    parent_high := S.high
    parent_access := S.access
    parent_credit := S.credit
    envelope := P.selector_envelope hP h
    denominator := hd
    attaining := heq
    safe_edge := hsafe
    failed_actual := hfactual
    failed_suff := hfsuff
    small_parameter_high_anchor := hsmall }
  exact {
    high := hhigh
    below_unit := (P.designated_antitone hP hhs.le).trans_lt S.below_unit
    access := H.child_access
    credit := H.child_credit hP
    history := H }

end AtomicProfile

end ConsistentSubmodular

end


