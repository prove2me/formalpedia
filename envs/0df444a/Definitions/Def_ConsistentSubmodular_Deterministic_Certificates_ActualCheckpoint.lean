-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ActualCheckpoint
-- name    : ConsistentSubmodular_Deterministic_Certificates_ActualCheckpoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:12:20.536531+00:00
-- url     : https://prove2.me/theorems/66f1e29f-8617-47a4-a729-cfdc79342ac3
-- title:
--   Checkpoint certificates from actual-coverage constructors: assembling entry, local segment and terminal exit
-- statement:
--   An atomic profile $P$ with stages $0,\dots,m$ consists of finitely many atoms $a$, each with a pool $\pi(a)\in\{0,\dots,m\}$, a nonempty label set $\Lambda_a\subseteq\{0,\dots,m\}$ with $i\le\pi(a)$ for every $i\in\Lambda_a$, and a weight $w_a\ge 0$. Its derived quantities at stage $t$ are the baseline $b_t=\sum_{\pi(a)<t}w_a$, the residual $\rho_i(t)=\sum_{\pi(a)\ge t,\ i\in\Lambda_a}w_a$, the designated value $g_t=\rho_t(t)$, the benchmark $P_t=b_t+g_t$, and, for a point $p$ of the simplex, the value $V_t(p)=b_t+\sum_{\pi(a)\ge t}w_a\bigl(1-\prod_{i\in\Lambda_a}(1-p_i)\bigr)$.
--
--   A *checkpoint certificate* (`CheckpointCertificate P`) for a profile $P$ consists of a point $p\in\Delta$ with at most two nonzero coordinates, such that $V_t(p)\ge\tfrac34P_t$ for every stage $t$; an entry path from $\delta_0$ to $p$ that is safe at stage $0$ at level $\tfrac34$; an exit path from $p$ to $\delta_m$ that is safe at stage $m$ at level $\tfrac34P_m$; and a total number of pieces at most $(m+1)+2$. Write $\mathrm{Active}(t)$ for $b_t<3g_t$, and $E_{h,q}(t)$, $A_{h,q}(c)$ for the envelope slack and actual eligibility of the actual-coverage constructor.
--
--   - `checkpoint_of_actual_parts`: given $h,c$ and $q\in[0,4]$ such that the pair point $p=\mathrm{mix}(\delta_h,\delta_c,q/4)$ satisfies $V_t(p)\ge\tfrac34P_t$ for all $t$, the segment $\delta_h\to p$ is safe at stage $0$ at level $\tfrac34$, a safe entry path from $\delta_0$ to $\delta_h$ with at most $h$ pieces is given, and a safe exit path from $p$ to $\delta_m$ with at most two pieces is given, it returns the checkpoint certificate with point $p$, entry equal to the given entry followed by the segment $\delta_h\to p$, and the given exit; the piece count is at most $h+1+2\le m+3$.
--   - `checkpoint_of_actual_low`: the case $0<q\le1$, $h<c$, with eligibility $A_{h,q}(c)\ge0$, envelope slack $E_{h,q}(t)\ge0$ at later active stages, $A_{h,q}(t)\le0$ at active stages after $c$, and the carrier budget $3\le g_h+2P_h$. The exit is obtained from the terminal exit lemmas when the last stage is active, and by a single segment to $\delta_m$ when it is inactive.
--   - `checkpoint_of_actual_middle`: the case $1\le q\le2$, where instead of the carrier budget the credit inequality $2g_hq-3(4g_h-3)\le q(P_c-g_h)$ is assumed and canonical persistence supplies the terminal budget.
--
--   The file also proves that an inactive terminal stage allows a one-segment safe exit from any point of $\Delta$, and that nonnegative envelope slack at the terminal stage gives the inequality $4(1-q/4)(g_h-\rho_h(m))\le 3-3g_m+b_m$.
--
--   These assemblies convert a successful local construction (a carrier $h$, a partner $c$ and a mass $q/4$) into the checkpoint certificates required by the finite checkpoint theorem, which underlies Theorem 7.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ActualCheckpoint.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ActualConstructor
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_TerminalActual
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Checkpoint

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem inactive_terminal_exit (p : Point m) (hp : IsSimplex p)
    (hinactive : ¬ P.Active (Fin.last m)) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = p ∧ γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  refine ⟨PolygonalPath.segment p (vertex (Fin.last m)), by simp,
    PolygonalPath.segment_terminal _ _, ?_, by simp⟩
  apply safePath_segment
  intro x hx hx'
  have hs := hp.mix (simplex_vertex (Fin.last m)) hx hx'
  exact ⟨hs, P.inactive_stage_safe _ hs (le_of_not_gt hinactive)⟩

theorem terminal_envelope_inequality (h : Fin (m + 1)) (q : ℝ)
    (henv : 0 ≤ P.envelopeSlack h q (Fin.last m)) :
    4 * (1 - q / 4) * (P.designated h - P.residual h (Fin.last m)) ≤
      3 - 3 * P.designated (Fin.last m) + P.baseline (Fin.last m) := by
  unfold envelopeSlack benchmark at henv
  nlinarith only [henv]

def checkpoint_of_actual_parts (h c : Fin (m + 1)) (q : ℝ)
    (hq0 : 0 ≤ q) (hq4 : q ≤ 4)
    (hstages : ∀ t, (3 : ℝ) / 4 * P.benchmark t ≤
      P.value t (mix (vertex h) (vertex c) (q / 4)))
    (hlocal : SafePath P 0 ((3 : ℝ) / 4)
      (PolygonalPath.segment (vertex h) (mix (vertex h) (vertex c) (q / 4))))
    (entry : PolygonalPath m) (hentry0 : entry.node 0 = vertex 0)
    (hentryh : entry.node (Fin.last entry.pieces) = vertex h)
    (hentrysafe : SafePath P 0 ((3 : ℝ) / 4) entry) (hentrypieces : entry.pieces ≤ h.val)
    (exit : PolygonalPath m)
    (hexit0 : exit.node 0 = mix (vertex h) (vertex c) (q / 4))
    (hexit1 : exit.node (Fin.last exit.pieces) = vertex (Fin.last m))
    (hexitsafe : SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) exit)
    (hexitpieces : exit.pieces ≤ 2) : CheckpointCertificate P := by
  let p := mix (vertex h) (vertex c) (q / 4)
  let finalEntry := PolygonalPath.segment (vertex h) p
  have hjoin : entry.node (Fin.last entry.pieces) = finalEntry.node 0 := by
    simpa [finalEntry] using hentryh
  exact {
    point := p
    entry := PolygonalPath.append entry finalEntry
    exit := exit
    simplex := (simplex_vertex h).mix (simplex_vertex c) (by linarith) (by linarith)
    support := supportCard_mix_vertices _ _ _
    stages := hstages
    entry_initial := by rw [PolygonalPath.append_initial, hentry0]
    entry_terminal := by
      rw [PolygonalPath.append_terminal _ _ hjoin]
      exact PolygonalPath.segment_terminal _ _
    exit_initial := hexit0
    exit_terminal := hexit1
    entry_safe := hentrysafe.append hlocal hjoin
    exit_safe := hexitsafe
    piece_budget := by
      change entry.pieces + 1 + exit.pieces ≤ (m + 1) + 2
      have := h.isLt
      omega }

/-- A successful actual constructor for positive envelope at most one.
The stronger carrier budget supplies its arbitrary-partner terminal exit. -/
def checkpoint_of_actual_low (hP : P.Canonical)
    (h c : Fin (m + 1)) (hhc : h < c) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (helig : 0 ≤ P.actualEligibility h q c)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t)
    (hlast : ∀ t, c < t → P.Active t → P.actualEligibility h q t ≤ 0)
    (hbudget : 3 ≤ P.designated h + 2 * P.benchmark h)
    (entry : PolygonalPath m) (hentry0 : entry.node 0 = vertex 0)
    (hentryh : entry.node (Fin.last entry.pieces) = vertex h)
    (hentrysafe : SafePath P 0 ((3 : ℝ) / 4) entry) (hentrypieces : entry.pieces ≤ h.val) :
    CheckpointCertificate P := by
  have hstages := P.actual_low_constructor_stages hP h c hhc q hq hq1 helig henv hlast
  have hlocal := P.actual_pair_entry hP h c hhc q hq.le (by linarith) helig
  have hexit : ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex h) (vertex c) (q / 4) ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
    by_cases ht : P.Active (Fin.last m)
    · have henvT := P.terminal_envelope_inequality h q
        (henv _ (lt_of_lt_of_le hhc (Fin.le_last c)) ht)
      have hpersist := P.baseline_add_residual_monotone h (Fin.le_last h)
      change P.benchmark h ≤ P.baseline (Fin.last m) + P.residual h (Fin.last m) at hpersist
      exact P.actual_terminal_exit_of_budget hP h c (ne_of_lt hhc) (q / 4)
        (by positivity) (by linarith) (hstages _) (by linarith) henvT
    · exact P.inactive_terminal_exit _
        ((simplex_vertex h).mix (simplex_vertex c) (by positivity) (by linarith)) ht
  let exit := Classical.choose hexit
  have hexit0 := (Classical.choose_spec hexit).1
  have hexit1 := (Classical.choose_spec hexit).2.1
  have hexitsafe := (Classical.choose_spec hexit).2.2.1
  have hexitpieces := (Classical.choose_spec hexit).2.2.2
  exact P.checkpoint_of_actual_parts h c q hq.le (by linarith) hstages hlocal
    entry hentry0 hentryh hentrysafe hentrypieces exit hexit0 hexit1 hexitsafe hexitpieces

/-- The middle actual constructor only needs its successful credit test;
canonical persistence supplies the terminal budget. -/
def checkpoint_of_actual_middle (hP : P.Canonical)
    (h c : Fin (m + 1)) (hhc : h < c) (q : ℝ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (helig : 0 ≤ P.actualEligibility h q c)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t)
    (hlast : ∀ t, c < t → P.Active t → P.actualEligibility h q t ≤ 0)
    (hcredit : 2 * P.designated h * q - 3 * (4 * P.designated h - 3) ≤
      q * (P.benchmark c - P.designated h))
    (entry : PolygonalPath m) (hentry0 : entry.node 0 = vertex 0)
    (hentryh : entry.node (Fin.last entry.pieces) = vertex h)
    (hentrysafe : SafePath P 0 ((3 : ℝ) / 4) entry) (hentrypieces : entry.pieces ≤ h.val) :
    CheckpointCertificate P := by
  have hstages := P.actual_constructor_stages hP h c hhc q hq1 hq2 helig henv hlast hcredit
  have hlocal := P.actual_pair_entry hP h c hhc q (by linarith) hq2 helig
  have hexit : ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex h) (vertex c) (q / 4) ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
    by_cases ht : P.Active (Fin.last m)
    · exact P.actual_terminal_exit_of_canonical_budget hP h c (ne_of_lt hhc) (q / 4)
        (by linarith) (by linarith) (hstages _)
        (P.terminal_envelope_inequality h q
          (henv _ (lt_of_lt_of_le hhc (Fin.le_last c)) ht))
    · exact P.inactive_terminal_exit _
        ((simplex_vertex h).mix (simplex_vertex c) (by linarith) (by linarith)) ht
  let exit := Classical.choose hexit
  have hexit0 := (Classical.choose_spec hexit).1
  have hexit1 := (Classical.choose_spec hexit).2.1
  have hexitsafe := (Classical.choose_spec hexit).2.2.1
  have hexitpieces := (Classical.choose_spec hexit).2.2.2
  exact P.checkpoint_of_actual_parts h c q (by linarith) (by linarith) hstages hlocal
    entry hentry0 hentryh hentrysafe hentrypieces exit hexit0 hexit1 hexitsafe hexitpieces

end AtomicProfile

end ConsistentSubmodular

end


