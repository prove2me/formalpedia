-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_TerminalSuff
-- name    : ConsistentSubmodular_Deterministic_Certificates_TerminalSuff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:10:08.102209+00:00
-- url     : https://prove2.me/theorems/56e61575-2099-4408-a2ab-598fe4d4b3f9
-- title:
--   Terminal exits of atomic profiles from sufficient minimum-overlap rows
-- statement:
--   An atomic profile $P$ with stages $0,\dots,m$ consists of finitely many atoms $a$, each with a pool $\pi(a)\in\{0,\dots,m\}$, a nonempty label set $\Lambda_a\subseteq\{0,\dots,m\}$ with $i\le\pi(a)$ for every $i\in\Lambda_a$, and a weight $w_a\ge 0$. Its derived quantities at stage $t$ are the baseline $b_t=\sum_{\pi(a)<t}w_a$, the residual $\rho_i(t)=\sum_{\pi(a)\ge t,\ i\in\Lambda_a}w_a$, the designated value $g_t=\rho_t(t)$, the benchmark $P_t=b_t+g_t$, and, for a point $p$ of the simplex, the value $V_t(p)=b_t+\sum_{\pi(a)\ge t}w_a\bigl(1-\prod_{i\in\Lambda_a}(1-p_i)\bigr)$.
--
--   This file introduces no definitions. With $\delta_i$ the vertex of the simplex, $\mathrm{mix}$ the affine interpolation, `SafePath` a polygonal path all of whose nodes and segment points lie in the simplex with $V_t\ge$ a given level, and $P$ canonical when $g_0=1$ and $\rho_i(t)\le g_t$, the file proves existence of short safe exits at the terminal stage $m$ at level $\tfrac34P_m$, where $L=b_m$, $G=g_m$ and $u=\rho_a(m)$, $v=\rho_c(m)$ are residuals.
--
--   - `suff_terminal_vertex_exit`: if $w\ge0$, $G\le L+w$, and $\tfrac34P_m\le L+\rho_b(m)-w/4$, then there is a safe path from $\delta_b$ to $\delta_m$ with at most one piece (constant if $b=m$, a single segment otherwise).
--   - `suff_terminal_exit_ordered`: for $a\ne c$, mass $x\in[0,1]$, $\rho_a(m)\le\rho_c(m)$ and $\tfrac34P_m\le L+(1-x)u+xv-u/4$, a safe path of at most two pieces from $\mathrm{mix}(\delta_a,\delta_c,x)$ to $\delta_m$: first a segment to $\delta_c$, then the vertex exit.
--   - `suff_terminal_exit`: the same conclusion for arbitrary $a,c$ and $x\in[0,1]$ under the minimum-overlap row $\tfrac34P_m\le L+(1-x)u+xv-\min(u,v)/4$, with no positivity or distinctness assumption on the endpoints.
--
--   The terminal exit is the second path of every certificate; these lemmas supply it for the sufficient constructor, and hence for the certificates behind Theorem 7 (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/TerminalSuff.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SafePaths
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ScalarGeometry

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

/-- The scalar exit criterion lifts to a safe path from a type vertex, including
the case that the vertex is already the terminal anchor. -/
theorem suff_terminal_vertex_exit (b : Fin (m + 1)) (w : ℝ) (hw : 0 ≤ w)
    (hpersist : P.designated (Fin.last m) ≤ P.baseline (Fin.last m) + w)
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.baseline (Fin.last m) + P.residual b (Fin.last m) - w / 4) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = vertex b ∧ γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 1 := by
  by_cases hb : b = Fin.last m
  · subst b
    refine ⟨PolygonalPath.constant (vertex (Fin.last m)), rfl, rfl, ?_, by simp⟩
    apply (safePath_constant_iff _ _ _ _).2
    refine ⟨simplex_vertex _, ?_⟩
    rw [P.value_designated_vertex]
    have := P.benchmark_nonnegative (Fin.last m)
    linarith
  · refine ⟨PolygonalPath.segment (vertex b) (vertex (Fin.last m)), by simp,
      PolygonalPath.segment_terminal _ _, ?_, by simp⟩
    apply safePath_segment
    intro y hy hy'
    refine ⟨(simplex_vertex b).mix (simplex_vertex _) hy hy', ?_⟩
    rw [P.value_terminal_edge b hb]
    exact suff_terminal_vertex_edge _ _ _ _ (P.baseline_nonnegative _)
      (P.designated_nonnegative _) (P.residual_nonnegative _ _) hw hpersist hgood y hy hy'

theorem suff_terminal_exit_ordered (hP : P.Canonical)
    (a c : Fin (m + 1)) (hac : a ≠ c) (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1)
    (horder : P.residual a (Fin.last m) ≤ P.residual c (Fin.last m))
    (hrow : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.baseline (Fin.last m) + (1 - x) * P.residual a (Fin.last m) +
        x * P.residual c (Fin.last m) - P.residual a (Fin.last m) / 4) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex a) (vertex c) x ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  have hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.baseline (Fin.last m) + P.residual c (Fin.last m) -
        P.residual a (Fin.last m) / 4 := by
    have := mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr horder)
    nlinarith
  obtain ⟨δ, hδinitial, hδterminal, hδsafe, hδpieces⟩ :=
    P.suff_terminal_vertex_exit c (P.residual a (Fin.last m))
      (P.residual_nonnegative _ _) (P.terminal_persistence_budget hP a) hgood
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
    have hlow := P.value_mix_vertices_sufficient (Fin.last m) a c hac hz hz'
      (P.overlap_le_left a c (Fin.last m))
    have hmove := mul_nonneg (sub_nonneg.mpr hzx) (sub_nonneg.mpr horder)
    nlinarith
  have hjoin : γ.node (Fin.last γ.pieces) = δ.node 0 := by
    exact (PolygonalPath.segment_terminal _ _).trans hδinitial.symm
  refine ⟨PolygonalPath.append γ δ, ?_, ?_, hγsafe.append hδsafe hjoin, ?_⟩
  · simp [γ]
  · rw [PolygonalPath.append_terminal γ δ hjoin, hδterminal]
  · simp only [PolygonalPath.append_pieces]
    change 1 + δ.pieces ≤ 2
    omega

/-- A minimum-overlap sufficient row at the terminal stage supplies a safe exit
with at most two pieces. The mass is arbitrary in `[0,1]`; no positive residual
or distinct endpoint assumption is imposed. -/
theorem suff_terminal_exit (hP : P.Canonical)
    (a c : Fin (m + 1)) (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1)
    (hrow : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.baseline (Fin.last m) + (1 - x) * P.residual a (Fin.last m) +
        x * P.residual c (Fin.last m) -
        min (P.residual a (Fin.last m)) (P.residual c (Fin.last m)) / 4) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex a) (vertex c) x ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  by_cases hac : a = c
  · subst c
    have hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
        P.baseline (Fin.last m) + P.residual a (Fin.last m) -
          P.residual a (Fin.last m) / 4 := by
      simp only [min_self] at hrow
      nlinarith
    obtain ⟨γ, hγinitial, hγterminal, hγsafe, hγpieces⟩ :=
      P.suff_terminal_vertex_exit a (P.residual a (Fin.last m))
        (P.residual_nonnegative _ _) (P.terminal_persistence_budget hP a) hgood
    exact ⟨γ, by simpa using hγinitial, hγterminal, hγsafe, by omega⟩
  · by_cases horder : P.residual a (Fin.last m) ≤ P.residual c (Fin.last m)
    · apply P.suff_terminal_exit_ordered hP a c hac x hx hx' horder
      simpa only [min_eq_left horder] using hrow
    · have horder' : P.residual c (Fin.last m) ≤ P.residual a (Fin.last m) :=
        le_of_not_ge horder
      have hrow' : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
          P.baseline (Fin.last m) + (1 - (1 - x)) * P.residual c (Fin.last m) +
            (1 - x) * P.residual a (Fin.last m) - P.residual c (Fin.last m) / 4 := by
        rw [min_eq_right horder'] at hrow
        nlinarith
      obtain ⟨γ, hγinitial, hγterminal, hγsafe, hγpieces⟩ :=
        P.suff_terminal_exit_ordered hP c a (Ne.symm hac) (1 - x)
          (sub_nonneg.mpr hx') (by linarith) horder' hrow'
      refine ⟨γ, ?_, hγterminal, hγsafe, hγpieces⟩
      rw [hγinitial, ← mix_swap]

end AtomicProfile

end ConsistentSubmodular

end


