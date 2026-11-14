-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SuffConstructor
-- name    : ConsistentSubmodular_Deterministic_Certificates_SuffConstructor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:11:54.131641+00:00
-- url     : https://prove2.me/theorems/42e4410c-5635-401d-8e5a-88498dd18dba
-- title:
--   Sufficient constructor on atomic profiles: sufficient credit and checkpoint certificates from a carrier or the root
-- statement:
--   An atomic profile $P$ with stages $0,\dots,m$ consists of finitely many atoms $a$, each with a pool $\pi(a)\in\{0,\dots,m\}$, a nonempty label set $\Lambda_a\subseteq\{0,\dots,m\}$ with $i\le\pi(a)$ for every $i\in\Lambda_a$, and a weight $w_a\ge 0$. Its derived quantities at stage $t$ are the baseline $b_t=\sum_{\pi(a)<t}w_a$, the residual $\rho_i(t)=\sum_{\pi(a)\ge t,\ i\in\Lambda_a}w_a$, the designated value $g_t=\rho_t(t)$, the benchmark $P_t=b_t+g_t$, and, for a point $p$ of the simplex, the value $V_t(p)=b_t+\sum_{\pi(a)\ge t}w_a\bigl(1-\prod_{i\in\Lambda_a}(1-p_i)\bigr)$.
--
--   Fix a canonical profile $P$ and write $E_{h,q}(t)$ for the envelope slack, $S_{h,q}(c)$ for the sufficient eligibility $(g_c-\rho_h(c))-(q-1)(g_h-g_c)-3(1-g_h)$, and $\mathrm{Active}(t)$ for $b_t<3g_t$. A `CheckpointCertificate` consists of a point $p\in\Delta$ with at most two nonzero coordinates and $V_t(p)\ge\tfrac34P_t$ for all $t$, an entry path from $\delta_0$ to $p$ safe at stage $0$ at level $\tfrac34$, an exit path from $p$ to $\delta_m$ safe at stage $m$ at level $\tfrac34P_m$, and at most $(m+1)+2$ pieces in total.
--
--   - `SuffCredit` $h\,q\,c$: the sufficient credit condition, which holds if either $g_h=1$ and $q\le\tfrac32$ (the root's low-parameter automatic case), or $q\ge\tfrac32$ and $2g_hq-3(4g_h-3)\le q(P_c-g_h)$.
--   - `checkpoint_of_suff_constructor`: for $h<c$, $1\le q\le3$, eligibility $S_{h,q}(c)\ge0$, envelope slack $E_{h,q}(t)\ge0$ at active $t>h$, $S_{h,q}(t)\le0$ at active $t>c$, sufficient credit, and a safe entry path to $\delta_h$ of at most $h$ pieces, the checkpoint certificate with point $p=\mathrm{mix}(\delta_h,\delta_c,q/4)$, entry equal to the given path followed by the segment $\delta_h\to p$, and a two-piece exit supplied by the terminal sufficient exit; the piece count is at most $h+1+2\le m+3$.
--   - `checkpoint_of_root_suff`: the case $h=0$ with the constant entry path at $\delta_0$, for $c>0$, $1\le q\le3$, and the root credit $q\le\tfrac32$ or $2q-3\le q(P_c-1)$.
--
--   The file also proves the pointwise bounds that make the construction work: the sufficient prefix row, the lower bound for the pair row, the safety of the final entry segment, the row inequality on stages after $c$, and the guarantee $V_t(p)\ge\tfrac34P_t$ at all stages and the terminal row.
--
--   This is the sufficient-credit counterpart of the actual constructor, used for the root and for large parameters in the checkpoint theorem that yields the $(\tfrac34,m+3)$-certificates of Theorem 7.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/SuffConstructor.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ActualConstructor
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SuffScalar
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_TerminalSuff
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Checkpoint

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

/-- The root's low-parameter automatic case, or the ordinary sufficient credit
used by both the root and the large-parameter carrier constructor. -/
def SuffCredit (h : Fin (m + 1)) (q : ℝ) (c : Fin (m + 1)) : Prop :=
  (P.designated h = 1 ∧ q ≤ (3 : ℝ) / 2) ∨
    ((3 : ℝ) / 2 ≤ q ∧
      2 * P.designated h * q - 3 * (4 * P.designated h - 3) ≤
        q * (P.benchmark c - P.designated h))

theorem suff_pair_prefix_row (h c t : Fin (m + 1)) (q : ℝ) (htc : t ≤ c)
    (helig : 0 ≤ P.suffEligibility h q c) (henv : 0 ≤ P.envelopeSlack h q t) :
    (3 : ℝ) / 4 * P.benchmark t ≤
      P.baseline t + (1 - q / 4) * P.residual h t + q / 4 * P.residual c t -
        P.residual h c / 4 := by
  rw [P.residual_persistence c t htc]
  apply suff_prefix_margin (P.designated h) q (P.baseline t) (P.designated t)
    (P.residual h t) (P.designated c) (P.residual h c) helig
  convert henv using 1
  unfold envelopeSlack benchmark
  ring

theorem suff_pair_prefix (h c t : Fin (m + 1)) (hc : h ≠ c)
    (q : ℝ) (hq0 : 0 ≤ q) (hq4 : q ≤ 4) (htc : t ≤ c)
    (helig : 0 ≤ P.suffEligibility h q c) (henv : 0 ≤ P.envelopeSlack h q t) :
    (3 : ℝ) / 4 * P.benchmark t ≤
      P.value t (mix (vertex h) (vertex c) (q / 4)) := by
  exact (P.suff_pair_prefix_row h c t q htc helig henv).trans
    (P.value_mix_vertices_sufficient t h c hc (by positivity) (by linarith)
      (P.overlap_le_persistent h c t))

theorem suff_pair_entry (hP : P.Canonical) (h c : Fin (m + 1)) (hhc : h < c)
    (q : ℝ) (hq0 : 0 ≤ q) (hq4 : q ≤ 4)
    (helig : 0 ≤ P.suffEligibility h q c) :
    SafePath P 0 ((3 : ℝ) / 4)
      (PolygonalPath.segment (vertex h) (mix (vertex h) (vertex c) (q / 4))) := by
  have hbase := P.suff_pair_prefix_row h c 0 q (Fin.zero_le c) helig
    (P.envelopeSlack_early hP h 0 q (Fin.zero_le h))
  rw [P.benchmark_zero hP, P.baseline_zero,
    P.residual_persistence h 0 (Fin.zero_le _),
    P.residual_persistence c 0 (Fin.zero_le _)] at hbase
  have horder := P.designated_antitone hP hhc.le
  apply safePath_segment
  intro y hy hy1
  have hmix : mix (vertex h) (mix (vertex h) (vertex c) (q / 4)) y =
      mix (vertex h) (vertex c) (y * (q / 4)) := by
    funext i
    simp only [mix]
    ring
  rw [hmix]
  have hx : 0 ≤ y * (q / 4) := by positivity
  have hxx : y * (q / 4) ≤ q / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy1) hq0]
  have hx1 : y * (q / 4) ≤ 1 := by linarith
  refine ⟨(simplex_vertex h).mix (simplex_vertex c) hx hx1, ?_⟩
  have hlow := P.value_mix_vertices_sufficient 0 h c (ne_of_lt hhc) hx hx1
    (P.overlap_le_persistent h c 0)
  rw [P.baseline_zero, P.residual_persistence h 0 (Fin.zero_le _),
    P.residual_persistence c 0 (Fin.zero_le _)] at hlow
  have hmove := mul_nonneg (sub_nonneg.mpr hxx) (sub_nonneg.mpr horder)
  nlinarith

theorem suff_pair_suffix_row (hP : P.Canonical) (h c t : Fin (m + 1))
    (q : ℝ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) (hct : c ≤ t)
    (hnoelig : P.suffEligibility h q t ≤ 0) (hcredit : P.SuffCredit h q c) :
    (3 : ℝ) / 4 * P.benchmark t ≤
      P.baseline t + (1 - q / 4) * P.residual h t + q / 4 * P.residual c t -
        min (P.residual h t) (P.residual c t) / 4 := by
  have hpersist := P.baseline_add_residual_monotone c hct
  change P.benchmark c ≤ P.baseline t + P.residual c t at hpersist
  rcases hcredit with ⟨hA, hq⟩ | ⟨hq, hcredit⟩
  · apply suff_suffix_margin_root_low q (P.baseline t) (P.designated t)
      (P.residual h t) (P.residual c t) (P.benchmark c) hq1 hq
      (P.designated_le_one hP t) (P.one_le_benchmark hP c) hpersist
    simpa [suffEligibility, hA] using hnoelig
  · exact suff_suffix_margin_credit (P.designated h) q (P.baseline t) (P.designated t)
      (P.residual h t) (P.residual c t) (P.benchmark c) hq hq3
      (P.residual_nonnegative _ _) (P.residual_nonnegative _ _) hpersist hnoelig hcredit

theorem suff_constructor_stages (hP : P.Canonical)
    (h c : Fin (m + 1)) (hhc : h < c) (q : ℝ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3)
    (helig : 0 ≤ P.suffEligibility h q c)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t)
    (hlast : ∀ t, c < t → P.Active t → P.suffEligibility h q t ≤ 0)
    (hcredit : P.SuffCredit h q c) :
    ∀ t, (3 : ℝ) / 4 * P.benchmark t ≤
      P.value t (mix (vertex h) (vertex c) (q / 4)) := by
  intro t
  by_cases ht : P.Active t
  · by_cases htc : t ≤ c
    · apply P.suff_pair_prefix h c t (ne_of_lt hhc) q (by linarith) (by linarith)
        htc helig
      by_cases hth : t ≤ h
      · exact P.envelopeSlack_early hP h t q hth
      · exact henv t (lt_of_not_ge hth) ht
    · exact (P.suff_pair_suffix_row hP h c t q hq1 hq3
        (le_of_not_ge htc) (hlast t (lt_of_not_ge htc) ht) hcredit).trans
        (P.value_mix_vertices_sufficient t h c (ne_of_lt hhc) (by linarith) (by linarith)
          (le_min (P.overlap_le_left h c t) (P.overlap_le_right h c t)))
  · apply P.inactive_stage_safe t
      ((simplex_vertex h).mix (simplex_vertex c) (by linarith) (by linarith))
    exact le_of_not_gt ht

theorem suff_constructor_terminal_row (hP : P.Canonical)
    (h c : Fin (m + 1)) (hhc : h < c) (q : ℝ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3)
    (helig : 0 ≤ P.suffEligibility h q c)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t)
    (hlast : ∀ t, c < t → P.Active t → P.suffEligibility h q t ≤ 0)
    (hcredit : P.SuffCredit h q c) :
    (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.baseline (Fin.last m) + (1 - q / 4) * P.residual h (Fin.last m) +
        q / 4 * P.residual c (Fin.last m) -
        min (P.residual h (Fin.last m)) (P.residual c (Fin.last m)) / 4 := by
  by_cases ht : P.Active (Fin.last m)
  · by_cases hceq : c = Fin.last m
    · subst c
      have hr := hP.2 (Fin.last m) h
      change P.residual h (Fin.last m) ≤ P.residual (Fin.last m) (Fin.last m) at hr
      rw [min_eq_left hr]
      exact P.suff_pair_prefix_row h (Fin.last m) (Fin.last m) q le_rfl helig
        (henv _ hhc ht)
    · have hct : c < Fin.last m := lt_of_le_of_ne (Fin.le_last c) hceq
      exact P.suff_pair_suffix_row hP h c (Fin.last m) q hq1 hq3 hct.le
        (hlast _ hct ht) hcredit
  · exact suff_inactive_margin _ _ _ _ _ (P.residual_nonnegative _ _)
      (P.residual_nonnegative _ _) (by linarith) (by linarith) (le_of_not_gt ht)

/-- Successful sufficient construction from an already accessible carrier. The
entry history bound is retained when adjoining its final affine piece. -/
def checkpoint_of_suff_constructor (hP : P.Canonical)
    (h c : Fin (m + 1)) (hhc : h < c) (q : ℝ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3)
    (helig : 0 ≤ P.suffEligibility h q c)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t)
    (hlast : ∀ t, c < t → P.Active t → P.suffEligibility h q t ≤ 0)
    (hcredit : P.SuffCredit h q c)
    (entry : PolygonalPath m) (hentry0 : entry.node 0 = vertex 0)
    (hentryh : entry.node (Fin.last entry.pieces) = vertex h)
    (hentrysafe : SafePath P 0 ((3 : ℝ) / 4) entry) (hentrypieces : entry.pieces ≤ h.val) :
    CheckpointCertificate P := by
  let p := mix (vertex h) (vertex c) (q / 4)
  let finalEntry := PolygonalPath.segment (vertex h) p
  have hfinalsafe := P.suff_pair_entry hP h c hhc q (by linarith) (by linarith) helig
  have hjoin : entry.node (Fin.last entry.pieces) = finalEntry.node 0 := by
    simpa [finalEntry] using hentryh
  have hterminal := P.suff_constructor_terminal_row hP h c hhc q hq1 hq3
    helig henv hlast hcredit
  have hexit := P.suff_terminal_exit hP h c (q / 4) (by linarith) (by linarith) hterminal
  let exit := Classical.choose hexit
  have hexit0 := (Classical.choose_spec hexit).1
  have hexit1 := (Classical.choose_spec hexit).2.1
  have hexitsafe := (Classical.choose_spec hexit).2.2.1
  have hexitpieces := (Classical.choose_spec hexit).2.2.2
  change exit.pieces ≤ 2 at hexitpieces
  exact {
    point := p
    entry := PolygonalPath.append entry finalEntry
    exit := exit
    simplex := (simplex_vertex h).mix (simplex_vertex c) (by linarith) (by linarith)
    support := supportCard_mix_vertices _ _ _
    stages := P.suff_constructor_stages hP h c hhc q hq1 hq3 helig henv hlast hcredit
    entry_initial := by rw [PolygonalPath.append_initial, hentry0]
    entry_terminal := by
      rw [PolygonalPath.append_terminal _ _ hjoin]
      exact PolygonalPath.segment_terminal _ _
    exit_initial := hexit0
    exit_terminal := hexit1
    entry_safe := hentrysafe.append hfinalsafe hjoin
    exit_safe := hexitsafe
    piece_budget := by
      change entry.pieces + 1 + exit.pieces ≤ (m + 1) + 2
      have := h.isLt
      omega }

/-- The general root credit criterion produces a complete checkpoint. -/
def checkpoint_of_root_suff (hP : P.Canonical)
    (c : Fin (m + 1)) (hc : 0 < c) (q : ℝ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3)
    (helig : 0 ≤ P.suffEligibility 0 q c)
    (henv : ∀ t, 0 < t → P.Active t → 0 ≤ P.envelopeSlack 0 q t)
    (hlast : ∀ t, c < t → P.Active t → P.suffEligibility 0 q t ≤ 0)
    (hcredit : q ≤ (3 : ℝ) / 2 ∨ 2 * q - 3 ≤ q * (P.benchmark c - 1)) :
    CheckpointCertificate P := by
  have hcredit' : P.SuffCredit 0 q c := by
    rcases hcredit with hq | hcredit
    · exact Or.inl ⟨hP.1, hq⟩
    · by_cases hq : q ≤ (3 : ℝ) / 2
      · exact Or.inl ⟨hP.1, hq⟩
      · right
        refine ⟨le_of_not_ge hq, ?_⟩
        rw [hP.1]
        nlinarith
  apply P.checkpoint_of_suff_constructor hP 0 c hc q hq1 hq3 helig henv hlast hcredit'
    (PolygonalPath.constant (vertex 0)) rfl rfl ?_ (by simp)
  apply (safePath_constant_iff _ _ _ _).2
  refine ⟨simplex_vertex _, ?_⟩
  rw [P.value_designated_vertex, P.benchmark_zero hP]
  norm_num

end AtomicProfile

end ConsistentSubmodular

end


