-- Prove2me | Definitions.Def_TabooRegen_Supplement_Classical
-- name    : TabooRegen_Supplement_Classical
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:41:58.400287+00:00
-- url     : https://prove2.me/theorems/96a466a1-5d9d-406d-8ceb-8143d5379848
-- title:
--   The post-$t$ process $X_t$, classical regeneration (Definition 1) over the taboo model, and the forward taboo limit of Theorem 1
-- statement:
--   Let $S$ be a complete separable metric space, $A\subseteq S$, and let $X$, the regeneration times $T(n)$ (under the taboo convention $T(n)=\infty$ on $\{\Gamma<T(n)\}$) and the cycles $W_n$ be as in the published model of this mission. This module adds three objects.
--
--   1. **The post-$t$ process.** For $t\ge0$,
--   $$
--   X_t=(X(t+s):s\ge0)\in D_{\tilde S}[0,\infty),
--   $$
--   the whole path shifted by $t$ (not the state $X(t)$).
--
--   2. **Classical regeneration (Definition 1).** $X$ is *classically regenerative* if there are finite random times $0\le T'(0)<T'(1)<\cdots$, continuing after an exit from $A$, whose cycles
--   $$
--   W'_n(t)=\begin{cases}X(T'(n-1)+t), & 0\le t<T'(n)-T'(n-1),\\ \Delta, & \text{otherwise},\end{cases}\qquad T'(-1)=0,
--   $$
--   satisfy (i) $(W'_j:j\ge0)$ are independent and (ii) $(W'_j:j\ge1)$ are identically distributed, and the model's times are their killed version: $T(n)=T'(n)$ on $\{T'(n)\le\Gamma\}$ and $T(n)=\infty$ otherwise.
--
--   3. **The forward taboo limit of Theorem 1.** For $\alpha\ge0$, $s\ge0$ and a measurable set $B$ of paths,
--   $$
--   \frac{E\int_0^{\tau_1}e^{\alpha(u+s)}\,I(X_u\in B,\ \Gamma>u+s)\,du}{E\int_0^{\tau_1\wedge\Gamma}e^{\alpha u}\,du}.
--   $$
--
--   Definition 1 is the classical notion that Remark 2 compares with taboo regeneration and that Theorem 3 assumes; the post-$t$ process and the forward limit are the objects of Theorem 1.
--
--   **Formalization Note** The post-$t$ process is built as an element of the published path type (a shift of a càdlàg path is càdlàg; the module proves this structural fact). Independence and identical distribution are imposed on the unkilled cycles $W'_j$, never on the model's cycles, which are constantly $\Delta$ after an exit; for every classical process the killed times satisfy every field of the published model, so the predicate covers every classically regenerative process. The numerator of the forward limit is an extended non-negative integral ($\tau_1=\infty$ is allowed), and the denominator is the published `cycleWeight` $E\int_0^{\gamma_1\wedge\tau_1}e^{\alpha u}du$, which equals $E\int_0^{\tau_1\wedge\Gamma}e^{\alpha u}du$ when $T(0)=0$.
-- source:
--   Glynn & Thorisson, Limit Theory for Taboo-Regenerative Processes, Queueing Systems 46 (2004) 271–294, DOI 10.1023/B:QUES.0000027987.00421.80, §2, p.273 (Definition 1), p.275 (taboo convention), §3, p.280 (post-$t$ process; limit of Theorem 1)

import Mathlib
import Definitions.Def_TabooRegen_Assumptions

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace TabooRegen.Supplement

open TabooRegen TabooRegen.Model
open KurtzProtter91.Integrals (IsCadlag)

/-- A shift `s ↦ x(t + s)` of a càdlàg path, embedded in `S̃ = S ⊕ Unit` by `Sum.inl`, is càdlàg.
(Structural lemma used to build the post-`t` process as an element of `D_S̃[0, ∞)`.) -/
theorem isCadlag_shift {S : Type*} [TopologicalSpace S] {x : ℝ≥0 → S} (hx : IsCadlag x)
    (t : ℝ≥0) : IsCadlag (fun s : ℝ≥0 => (Sum.inl (x (t + s)) : S ⊕ Unit)) := by
  have hmap : Continuous fun s : ℝ≥0 => t + s := continuous_const.add continuous_id
  constructor
  · intro s
    have h1 : ContinuousWithinAt x (Set.Ici (t + s)) (t + s) := hx.1 (t + s)
    have h2 : ContinuousWithinAt (fun s : ℝ≥0 => x (t + s)) (Set.Ici s) s := by
      refine h1.comp hmap.continuousWithinAt ?_
      intro u hu
      simp only [Set.mem_Ici] at hu ⊢
      exact add_le_add_right hu t
    exact continuous_inl.continuousAt.comp_continuousWithinAt h2
  · intro s hs
    obtain ⟨a, ha⟩ := hx.2 (t + s) (lt_of_lt_of_le hs (le_add_self))
    refine ⟨Sum.inl a, (continuous_inl.tendsto a).comp (ha.comp ?_)⟩
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((hmap.tendsto s).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact add_lt_add_right hu t

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] {A : Set S}
  {Ω : Type*} [MeasurableSpace Ω]

/-- The **post-`t` process** `X_t = (X(t + s) : s ⩾ 0)` (Glynn & Thorisson, Limit Theory for
Taboo-Regenerative Processes, Queueing Systems 46 (2004), §3, p.280), as an element of the path space
`D_S̃[0, ∞)` of the published `TabooRegen.Path` (values embedded by `Sum.inl`). It is the whole
shifted path, not the state `X(t)`. -/
noncomputable def post (M : Model S A Ω) (t : ℝ≥0) (ω : Ω) : Path S :=
  ⟨fun s => Sum.inl (M.X ω (t + s)), isCadlag_shift (M.cadlag ω) t⟩

/-- **Definition 1** (Queueing Systems 46 (2004), p.273), stated for a published `TabooRegen.Model`
whose regeneration times already carry the taboo convention `T(n) = ∞` on `{Γ < T(n)}` (p.275).
`X` is *classically regenerative* if there are finite measurable random times
`0 ⩽ T′(0) < T′(1) < ⋯` (which continue after an exit) whose cycles
`W′ₙ(t) = X(T′(n − 1) + t)` for `t < T′(n) − T′(n − 1)`, `= Δ` afterwards (`T′(−1) = 0`), satisfy
(i) `(W′_j : j ⩾ 0)` are independent and (ii) `(W′_j : j ⩾ 1)` are identically distributed, and
the model's times are the killed version of the `T′`: `T(n) = T′(n)` on `{T′(n) ⩽ Γ}` and
`T(n) = ∞` otherwise.

**Formalization Note.** Independence and identical distribution are imposed on the unkilled cycles
`W′`, never on the model's `W`: after an exit the killed cycles are constantly `Δ`, and asking them
to be i.i.d. would force `P(I₁ = 0) = 0`. For every classical process `(X, T′)` the killed times
satisfy every field of `Model`, so this predicate covers every classically regenerative process. The
cycles `W′` are carried as measurable path-valued random elements with their defining equation;
both properties hold automatically for càdlàg `X` and measurable `T′`. The delay cycle `W′₀` may have
a different law. -/
def IsClassicallyRegen (M : Model S A Ω) : Prop :=
  ∃ T' : ℕ → Ω → ℝ≥0, (∀ n, Measurable (T' n)) ∧ (∀ n ω, T' n ω < T' (n + 1) ω) ∧
    (∀ n ω, M.T n ω = if (T' n ω : ℝ≥0∞) ≤ M.Γ ω then (T' n ω : ℝ≥0∞) else ⊤) ∧
    ∃ W' : ℕ → Ω → Path S, (∀ n, Measurable (W' n)) ∧
      (∀ n ω, (W' n ω).1 = cycleOf M.X (fun k ω => (T' k ω : ℝ≥0∞)) n ω) ∧
      ProbabilityTheory.iIndepFun W' M.P ∧
      ∀ j : ℕ, ProbabilityTheory.IdentDistrib (W' (j + 1)) (W' 1) M.P M.P

/-- The numerator of the limit in **Theorem 1** (Queueing Systems 46 (2004), p.280):
`E ∫₀^{τ₁} e^{α(u+s)} I(X_u ∈ B, Γ > u + s) du`, an extended non-negative real. `X_u` is the post-`u`
process, `τ₁` may be `∞` (then the indicator of `Γ > u + s` restricts the range). -/
noncomputable def forwardNum (M : Model S A Ω) (α : ℝ) (s : ℝ≥0) (B : Set (Path S)) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ u in {u : ℝ | 0 ≤ u ∧ ENNReal.ofReal u < M.τ 1 ω},
    ENNReal.ofReal (Real.exp (α * (u + s))) *
      Set.indicator {u : ℝ | post M u.toNNReal ω ∈ B ∧ ENNReal.ofReal (u + s) < M.Γ ω}
        (fun _ => (1 : ℝ≥0∞)) u) ∂M.P

/-- The **forward taboo limit** of Theorem 1 (Queueing Systems 46 (2004), p.280):
`E ∫₀^{τ₁} e^{α(u+s)} I(X_u ∈ B, Γ > u + s) du / E ∫₀^{τ₁∧Γ} e^{αu} du`. The denominator is the
published `cycleWeight α` (`γ₁ ∧ τ₁ = Γ ∧ τ₁` when `T(0) = 0`, p.276). -/
noncomputable def forwardLimit (M : Model S A Ω) (α : ℝ) (s : ℝ≥0) (B : Set (Path S)) : ℝ :=
  (forwardNum M α s B).toReal / (M.cycleWeight α).toReal

end TabooRegen.Supplement


