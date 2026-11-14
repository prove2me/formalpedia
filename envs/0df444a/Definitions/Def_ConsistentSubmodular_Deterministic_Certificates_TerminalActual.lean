-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_TerminalActual
-- name    : ConsistentSubmodular_Deterministic_Certificates_TerminalActual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:11:16.379079+00:00
-- url     : https://prove2.me/theorems/488021ea-0e6d-454e-9400-2ba23fd7ff9d
-- title:
--   Terminal exits of atomic profiles through a pure vertex or a vertex pair: safe paths to $\delta_m$ at level $\tfrac34 P_m$
-- statement:
--   An atomic profile $P$ with stages $0,\dots,m$ consists of finitely many atoms $a$, each with a pool $\pi(a)\in\{0,\dots,m\}$, a nonempty label set $\Lambda_a\subseteq\{0,\dots,m\}$ with $i\le\pi(a)$ for every $i\in\Lambda_a$, and a weight $w_a\ge 0$. Its derived quantities at stage $t$ are the baseline $b_t=\sum_{\pi(a)<t}w_a$, the residual $\rho_i(t)=\sum_{\pi(a)\ge t,\ i\in\Lambda_a}w_a$, the designated value $g_t=\rho_t(t)$, the benchmark $P_t=b_t+g_t$, and, for a point $p$ of the simplex, the value $V_t(p)=b_t+\sum_{\pi(a)\ge t}w_a\bigl(1-\prod_{i\in\Lambda_a}(1-p_i)\bigr)$.
--
--   This file introduces no new definitions; it works with the following notation. $\delta_i$ is the vertex of the simplex $\Delta$ putting all weight on candidate $i$, `mix` $(p,q,x)=(1-x)p+xq$, and a polygonal path is a finite list of nodes joined by affine segments (`PolygonalPath.constant`, `PolygonalPath.segment`, `PolygonalPath.append`). A path $\gamma$ is *safe at stage $t$ at level $\lambda$* (`SafePath`) if every node and every point of every segment lies in $\Delta$ and has $V_t\ge\lambda$. A profile is *canonical* if $g_0=1$ and $\rho_i(t)\le g_t$ for all $i,t$. The overlap $o_{ij}(t)=\sum_{\pi(a)\ge t,\ i,j\in\Lambda_a}w_a$ is the weight of atoms carrying both labels. On a pair of vertices, $V_t(\mathrm{mix}(\delta_a,\delta_c,x))\ge b_t+(1-x)\rho_a(t)+x\rho_c(t)-x(1-x)\,o_{ac}(t)$ (with equality in the terminal case used here).
--
--   The file proves, for the terminal stage $m$ and the level $\tfrac34P_m$, that exits to $\delta_m$ exist with few pieces:
--
--   - from a vertex $\delta_b$ with $V_m(\delta_b)\ge\tfrac34P_m$ and no "bad minimum" (the failure of $\rho_b(m)P_m<g_m^2\wedge g_m<2\rho_b(m)$), a safe path of at most one piece (`terminal_vertex_exit`);
--   - from a point $\mathrm{mix}(\delta_a,\delta_c,x)$ with $x\le\tfrac12$ and terminal value at least $\tfrac34P_m$, a safe path of at most two pieces to $\delta_m$, first for a monotone direction (`actual_terminal_exit_right`) and then for arbitrary partners (`actual_terminal_exit`);
--   - the same conclusion when the bad-minimum exclusion is replaced by an anchor budget $3\le g_a+2(b_m+\rho_a(m))$ together with the raw envelope inequality (`actual_terminal_exit_of_budget`), or, for $\tfrac14\le x\le\tfrac12$, by canonical persistence together with the envelope inequality (`actual_terminal_exit_of_canonical_budget`).
--
--   These exits supply the terminal half of the checkpoint certificates built from the actual-coverage constructor, and hence the exit path of the $(\tfrac34,m+3)$-certificates of Theorem 7 (Section 3 and Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/TerminalActual.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SafePaths
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_TerminalPairGeometry

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem terminal_vertex_exit (b : Fin (m + 1))
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤ P.value (Fin.last m) (vertex b))
    (hno : ¬ (P.residual b (Fin.last m) * P.benchmark (Fin.last m) <
      P.designated (Fin.last m) ^ 2 ∧
      P.designated (Fin.last m) < 2 * P.residual b (Fin.last m))) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = vertex b ∧ γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 1 := by
  by_cases hb : b = Fin.last m
  · subst b
    refine ⟨PolygonalPath.constant (vertex (Fin.last m)), rfl, rfl, ?_, by simp⟩
    exact (safePath_constant_iff _ _ _ _).2 ⟨simplex_vertex _, hgood⟩
  · refine ⟨PolygonalPath.segment (vertex b) (vertex (Fin.last m)), by simp,
      PolygonalPath.segment_terminal _ _, ?_, by simp⟩
    apply safePath_segment
    intro y hy hy'
    refine ⟨(simplex_vertex b).mix (simplex_vertex _) hy hy', ?_⟩
    rw [P.value_terminal_edge b hb]
    apply terminal_quadratic_safe_after _ _ _ 0 (P.residual_nonnegative _ _)
      (P.designated_nonnegative _) ?_ ?_ y hy
    · simpa only [benchmark, zero_mul, mul_zero, sub_zero, one_pow, one_mul, add_zero]
        using hgood.trans_eq (P.value_vertex _ _)
    · simpa only [benchmark, sub_zero, mul_one] using hno

theorem actual_terminal_exit_right (hP : P.Canonical)
    (a c : Fin (m + 1)) (hac : a ≠ c) (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1)
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.value (Fin.last m) (mix (vertex a) (vertex c) x))
    (hderiv : 0 ≤ P.residual c (Fin.last m) - P.residual a (Fin.last m) -
      (1 - 2 * x) * P.overlap a c (Fin.last m))
    (hno : ¬ (P.residual c (Fin.last m) * P.benchmark (Fin.last m) <
      P.designated (Fin.last m) ^ 2 ∧
      P.designated (Fin.last m) < 2 * P.residual c (Fin.last m) * x)) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex a) (vertex c) x ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  let L := P.baseline (Fin.last m)
  let G := P.designated (Fin.last m)
  let u := P.residual a (Fin.last m)
  let v := P.residual c (Fin.last m)
  let o := P.overlap a c (Fin.last m)
  have hgoodpoly : (3 : ℝ) / 4 * (L + G) ≤ pairPolynomial L u v o x := by
    rw [P.value_mix_vertices _ _ _ hac] at hgood
    exact hgood
  have hsafe : ∀ z : ℝ, x ≤ z → z ≤ 1 →
      (3 : ℝ) / 4 * (L + G) ≤ pairPolynomial L u v o z := by
    intro z hxz _
    exact hgoodpoly.trans (pairPolynomial_mono_right L u v o x z
      (P.overlap_nonnegative _ _ _) hderiv hxz)
  have hendno : ¬ (v * (L + G) < G ^ 2 ∧ G < 2 * v) :=
    terminal_pair_endpoint_no_bad_minimum L G u v o x
      (P.baseline_nonnegative _) (P.designated_nonnegative _) (P.residual_nonnegative _ _)
      (hP.2 _ c) (hP.2 _ a) (P.terminal_overlap_lower_bound a c) hno hsafe
  have hendgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.value (Fin.last m) (vertex c) := by
    rw [P.value_vertex]
    simpa [pairPolynomial, L, G, v, benchmark] using hsafe 1 hx' le_rfl
  obtain ⟨δ, hδinitial, hδterminal, hδsafe, hδpieces⟩ :=
    P.terminal_vertex_exit c hendgood hendno
  let γ := PolygonalPath.segment (mix (vertex a) (vertex c) x) (vertex c)
  have hγsafe : SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ := by
    apply safePath_segment
    intro y hy hy'
    rw [mix_mix_right]
    have hz : 0 ≤ (1 - y) * x + y :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr hy') hx) hy
    have hz' : (1 - y) * x + y ≤ 1 := by
      have := mul_nonneg (sub_nonneg.mpr hy') (sub_nonneg.mpr hx')
      nlinarith
    have hzx : x ≤ (1 - y) * x + y := by
      have := mul_nonneg hy (sub_nonneg.mpr hx')
      nlinarith
    refine ⟨(simplex_vertex a).mix (simplex_vertex c) hz hz', ?_⟩
    rw [P.value_mix_vertices _ _ _ hac]
    exact hsafe _ hzx hz'
  have hjoin : γ.node (Fin.last γ.pieces) = δ.node 0 :=
    (PolygonalPath.segment_terminal _ _).trans hδinitial.symm
  refine ⟨PolygonalPath.append γ δ, ?_, ?_, hγsafe.append hδsafe hjoin, ?_⟩
  · simp [γ]
  · rw [PolygonalPath.append_terminal γ δ hjoin, hδterminal]
  · simp only [PolygonalPath.append_pieces]
    change 1 + δ.pieces ≤ 2
    omega

/-- A terminal-good distinct pair of mass at most one half has a two-piece
exit when the anchor's terminal-partner quadratic excludes the bad minimum.
This is the geometric arbitrary-partner form of the actual exit lemma. -/
theorem actual_terminal_exit (hP : P.Canonical)
    (a c : Fin (m + 1)) (hac : a ≠ c) (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.value (Fin.last m) (mix (vertex a) (vertex c) x))
    (hno : ¬ (P.residual a (Fin.last m) * P.benchmark (Fin.last m) <
      P.designated (Fin.last m) ^ 2 ∧
      P.designated (Fin.last m) < 2 * P.residual a (Fin.last m) * (1 - x))) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex a) (vertex c) x ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  have hx' : x ≤ 1 := by linarith
  by_cases hd : 0 ≤ P.residual c (Fin.last m) - P.residual a (Fin.last m) -
      (1 - 2 * x) * P.overlap a c (Fin.last m)
  · apply P.actual_terminal_exit_right hP a c hac x hx hx' hgood hd
    rintro ⟨_, hbad⟩
    have h1 := mul_nonneg (P.residual_nonnegative c (Fin.last m))
      (show 0 ≤ 1 - 2 * x by linarith)
    have h2 := hP.2 (Fin.last m) c
    nlinarith
  · have hd' : 0 ≤ P.residual a (Fin.last m) - P.residual c (Fin.last m) -
        (1 - 2 * (1 - x)) * P.overlap c a (Fin.last m) := by
      rw [P.overlap_comm c a]
      linarith
    have hgood' : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
        P.value (Fin.last m) (mix (vertex c) (vertex a) (1 - x)) := by
      rw [← mix_swap]
      exact hgood
    obtain ⟨γ, hγinitial, hγterminal, hγsafe, hγpieces⟩ :=
      P.actual_terminal_exit_right hP c a (Ne.symm hac) (1 - x)
        (sub_nonneg.mpr hx') (by linarith) hgood' hd' hno
    refine ⟨γ, ?_, hγterminal, hγsafe, hγpieces⟩
    rw [hγinitial, ← mix_swap]

/-- The strong anchor budget and the raw envelope supply the actual
arbitrary-partner terminal exit. -/
theorem actual_terminal_exit_of_budget (hP : P.Canonical)
    (a c : Fin (m + 1)) (hac : a ≠ c) (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.value (Fin.last m) (mix (vertex a) (vertex c) x))
    (hbudget : 3 ≤ P.designated a +
      2 * (P.baseline (Fin.last m) + P.residual a (Fin.last m)))
    (henv : 4 * (1 - x) * (P.designated a - P.residual a (Fin.last m)) ≤
      3 - 3 * P.designated (Fin.last m) + P.baseline (Fin.last m)) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex a) (vertex c) x ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  apply P.actual_terminal_exit hP a c hac x hx hxhalf hgood
  exact actual_terminal_no_bad_minimum _ _ _ _ _
    (P.baseline_nonnegative _) (P.residual_nonnegative _ _) (hP.2 _ a)
    (P.designated_antitone hP (Fin.le_last a)) (by linarith) (by linarith) hbudget henv

/-- In the middle mass range, canonical persistence replaces the stronger
anchor budget in the actual terminal exit. -/
theorem actual_terminal_exit_of_canonical_budget (hP : P.Canonical)
    (a c : Fin (m + 1)) (hac : a ≠ c) (x : ℝ)
    (hxquarter : (1 : ℝ) / 4 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.value (Fin.last m) (mix (vertex a) (vertex c) x))
    (henv : 4 * (1 - x) * (P.designated a - P.residual a (Fin.last m)) ≤
      3 - 3 * P.designated (Fin.last m) + P.baseline (Fin.last m)) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex a) (vertex c) x ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  apply P.actual_terminal_exit hP a c hac x (by linarith) hxhalf hgood
  have hbudget : 1 ≤ P.baseline (Fin.last m) + P.residual a (Fin.last m) :=
    (P.one_le_benchmark hP a).trans (P.baseline_add_residual_monotone a (Fin.le_last a))
  exact actual_terminal_no_bad_minimum_canonical _ _ _ _ _
    (P.baseline_nonnegative _) (P.residual_nonnegative _ _) (hP.2 _ a)
    (P.designated_antitone hP (Fin.le_last a)) (by linarith) (by linarith) hbudget henv

end AtomicProfile

end ConsistentSubmodular

end


