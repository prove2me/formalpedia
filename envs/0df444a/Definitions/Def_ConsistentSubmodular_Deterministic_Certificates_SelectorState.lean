-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState
-- name    : ConsistentSubmodular_Deterministic_Certificates_SelectorState
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:15:01.143288+00:00
-- url     : https://prove2.me/theorems/cf9c70b9-4792-43dd-a0be-ccc6b349e4bd
-- title:
--   Relay histories and selector states of the carrier-selection procedure for atomic profiles
-- statement:
--   An atomic profile $P$ with stages $0,\dots,m$ consists of finitely many atoms $a$, each with a pool $\pi(a)\in\{0,\dots,m\}$, a nonempty label set $\Lambda_a\subseteq\{0,\dots,m\}$ with $i\le\pi(a)$ for every $i\in\Lambda_a$, and a weight $w_a\ge 0$. Its derived quantities at stage $t$ are the baseline $b_t=\sum_{\pi(a)<t}w_a$, the residual $\rho_i(t)=\sum_{\pi(a)\ge t,\ i\in\Lambda_a}w_a$, the designated value $g_t=\rho_t(t)$, the benchmark $P_t=b_t+g_t$, and, for a point $p$ of the simplex, the value $V_t(p)=b_t+\sum_{\pi(a)\ge t}w_a\bigl(1-\prod_{i\in\Lambda_a}(1-p_i)\bigr)$.
--
--   Further notation. $\mathrm{Active}(t)$ means $b_t<3g_t$. For a parent stage $a$, parameter $q$ and stage $t$ the envelope slack is $E_{a,q}(t)=q\bigl[(g_a-g_t)+(g_t-\rho_a(t))\bigr]+(P_t-g_a)+3(1-g_a)-4(g_t-\rho_a(t))$; the actual and sufficient eligibilities at $c$ are $A_{a,q}(c)=4g_a-3-q(g_a-g_c)-(q-q^2/4)\rho_a(c)$ and $S_{a,q}(c)=(g_c-\rho_a(c))-(q-1)(g_a-g_c)-3(1-g_a)$; the raw ratio of $a\to h$ is $\bigl[4(g_h-\rho_a(h))-(P_h-g_a)-3(1-g_a)\bigr]/(g_a-\rho_a(h))$. An *access certificate* for $h$ is a path from $\delta_0$ to $\delta_h$, safe at stage $0$ at level $\tfrac34$, with at most $h$ pieces. *Strong credit* at $h$ means $\tfrac12\le P_h-1$ or $1-g_h\le(P_h-1)(2-P_h)$. A *pessimistic safe edge* $a\to h$ means $\tfrac34\le g_a-(g_a-g_h)z-\rho_a(h)z(1-z)$ for all $z\in[0,1]$.
--
--   - `RelayHistory P h`: the record of how the selector reached an active stage $h$ (the child) from an earlier parent. It contains a parent $a<h$, with $h$ active; a parameter $q\in[1,3)$; $g_a>\tfrac34$; an access certificate and strong credit at $a$; envelope slack $E_{a,q}(t)\ge0$ at all active $t>a$; a positive denominator $g_a-\rho_a(h)>0$; the equality of the raw ratio of $a\to h$ with $q$; a pessimistic safe edge $a\to h$; for $q\le2$, the failure of the actual test at later active eligible stages, i.e. $A_{a,q}(t)\ge0$ implies $q(P_t-g_a)<2g_aq-3(4g_a-3)$; the same failure statement for $q>2$ with the sufficient eligibility $S_{a,q}(t)$; and $g_a\ge\tfrac{33}{40}$ whenever $q<\tfrac43$.
--   - `RelayHistory.child_access`: the access certificate for $h$ obtained by extending the parent's access path by the safe edge $a\to h$.
--   - `SelectorState P h`: the state of the selector at stage $h$: $\tfrac34<g_h<1$, an access certificate and strong credit at $h$, and a relay history ending at $h$.
--
--   The file also proves that strong credit passes from the parent to the child along a relay (for canonical $P$).
--
--   These records store everything the later rollback and relay arguments need (the failed parent tests are retained for all later active eligible rows, and the initial path is never discarded) in the construction of checkpoint certificates for the $(\tfrac34,m+3)$-certificates of Theorem 7.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/SelectorState.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access

noncomputable section

namespace ConsistentSubmodular

variable {m atomCount : ℕ}

structure RelayHistory (P : AtomicProfile m atomCount) (child : Fin (m + 1)) where
  parent : Fin (m + 1)
  advances : parent < child
  child_active : P.Active child
  parameter : ℝ
  parameter_ge_one : 1 ≤ parameter
  parameter_lt_three : parameter < 3
  parent_high : (3 : ℝ) / 4 < P.designated parent
  parent_access : AccessCertificate P parent
  parent_credit : P.StrongCredit parent
  envelope : ∀ t, parent < t → P.Active t → 0 ≤ P.envelopeSlack parent parameter t
  denominator : 0 < P.designated parent - P.residual parent child
  attaining : P.rawRatio parent child = parameter
  safe_edge : P.PessimisticSafeEdge parent child
  /-- Below two, failure of the actual test is essential; failure of the sufficient test alone
  would be insufficient for middle rollback. -/
  failed_actual : parameter ≤ 2 → ∀ t, parent < t → P.Active t →
    0 ≤ P.actualEligibility parent parameter t →
    parameter * (P.benchmark t - P.designated parent) <
      2 * P.designated parent * parameter - 3 * (4 * P.designated parent - 3)
  failed_suff : 2 < parameter → ∀ t, parent < t → P.Active t →
    0 ≤ P.suffEligibility parent parameter t →
    parameter * (P.benchmark t - P.designated parent) <
      2 * P.designated parent * parameter - 3 * (4 * P.designated parent - 3)
  /-- The selector only relays below four thirds from a high anchor. -/
  small_parameter_high_anchor : parameter < 4 / 3 → 33 / 40 ≤ P.designated parent

namespace RelayHistory

variable {P : AtomicProfile m atomCount} {child : Fin (m + 1)}

def child_access (H : RelayHistory P child) : AccessCertificate P child :=
  P.extendAccess H.parent child H.advances H.parent_access H.safe_edge

theorem child_credit (H : RelayHistory P child) (hP : P.Canonical) : P.StrongCredit child :=
  P.strongCredit_of_pessimisticEdge hP H.parent child H.advances.le H.safe_edge

end RelayHistory

structure SelectorState (P : AtomicProfile m atomCount) (h : Fin (m + 1)) where
  high : (3 : ℝ) / 4 < P.designated h
  below_unit : P.designated h < 1
  access : AccessCertificate P h
  credit : P.StrongCredit h
  history : RelayHistory P h

end ConsistentSubmodular

end


