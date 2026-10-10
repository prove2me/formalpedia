-- Prove2me | Definitions.Def_MasterVisc_Ito_Discretization
-- name    : MasterVisc_Ito_Discretization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:36.431983+00:00
-- url     : https://prove2.me/theorems/17855d3a-1b8f-45e9-8123-b463f2d4c74b
-- title:
--   Proof of Theorem 2.7, p. 945 — the partition t_i = iT/n, X̃ⁿ, X̃^{n,θ}, μⁿ and μ^{n,θ}
-- statement:
--   This module defines the discretizations used in the proof of Theorem 2.7 of Wu and Zhang.
--
--   Fix $n\ge1$ and the uniform partition $t_i=iT/n$ of $[0,T]$. For $t\in[0,T)$ let $i=i(n,t)=\lfloor nt/T\rfloor$, the index with $t_i\le t<t_{i+1}$. For a continuous path $\tilde X$ write $\tilde X_{t_i,t_{i+1}}=\tilde X_{t_{i+1}}-\tilde X_{t_i}$ as in (2.4), and define the càdlàg paths
--   $$
--   \tilde X^n:=\sum_{i=0}^{n-1}\tilde X_{t_i}\mathbf 1_{[t_i,t_{i+1})}+\tilde X_T\mathbf 1_{\{T\}},\qquad
--   \tilde X^{n,\theta}:=\tilde X^n_{t_i\wedge\cdot}+\theta\,\tilde X_{t_i,t_{i+1}}\mathbf 1_{[t_{i+1},T]},\quad\theta\in[0,1],
--   $$
--   the second one built on the $i$-th interval. Given a representation $(\tilde\Omega,\tilde{\mathbb P},\tilde X)$ of a law, $\mu^n:=\tilde{\mathbb P}\circ(\tilde X^n)^{-1}$ and $\mu^{n,\theta}:=\tilde{\mathbb P}\circ(\tilde X^{n,\theta})^{-1}$ are laws on $\widehat\Omega$.
--
--   These are the objects of the identity (2.21) and the limits (2.22) and after.
--
--   **Formalization Note** The dependence of $\tilde X^{n,\theta}$ and $\mu^{n,\theta}$ on the interval index $i$, implicit on the page, is an explicit argument. The value of $\tilde X^n$ at $r$ is $\tilde X$ at the grid point $t_{\lfloor nr/T\rfloor}$, capped at $T$; this is the page's step path, extended flat after $T$.
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), proof of Theorem 2.7, p. 945, definitions of X̃ⁿ, μⁿ, X̃^{n,θ}, μ^{n,θ}; (2.4), p. 940

import Mathlib
import Definitions.Def_MasterVisc_Ito_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.Ito

open EthierKurtz

/-! ### The discretizations of the proof of Theorem 2.7 (p. 945) -/

/-- The uniform partition of [0, T]: t_i = iT/n. -/
noncomputable def grid (T : ℝ≥0) (n i : ℕ) : ℝ≥0 := T * i / n

/-- The index i = i(n, t) with t_i ≤ t < t_{i+1}, i.e. ⌊nt/T⌋ (for 0 ≤ t < T). -/
noncomputable def gridIdx (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) : ℕ := ⌊(n : ℝ≥0) * t / T⌋₊

lemma isCadlag_comp_floor {d : ℕ} (h : ℝ≥0 → ℝ≥0) (hc : Continuous h) (hm : Monotone h)
    (g : ℕ → SDEState d) : IsCadlag (fun r => g ⌊h r⌋₊) := by
  refine ⟨fun r => ?_, fun r hr => ?_⟩
  · refine (continuousWithinAt_const (b := g ⌊h r⌋₊)).congr_of_eventuallyEq ?_ rfl
    have hlt : h r < (⌊h r⌋₊ : ℝ≥0) + 1 := Nat.lt_floor_add_one _
    have hev : ∀ᶠ s in 𝓝 r, h s < (⌊h r⌋₊ : ℝ≥0) + 1 :=
      (hc.tendsto r).eventually (gt_mem_nhds hlt)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs hs'
    have hle : h r ≤ h s := hm (Set.mem_Ici.mp hs')
    rw [Nat.floor_eq_iff bot_le |>.mpr ⟨(Nat.floor_le bot_le).trans hle, hs⟩]
  · set S : Set ℕ := (fun s => ⌊h s⌋₊) '' Set.Iio r with hS
    have hne : S.Nonempty := ⟨_, 0, hr, rfl⟩
    have hbdd : BddAbove S := ⟨⌊h r⌋₊, by
      rintro _ ⟨s, hs, rfl⟩
      exact Nat.floor_le_floor (hm (Set.mem_Iio.mp hs).le)⟩
    obtain ⟨s₀, hs₀, hM⟩ := Nat.sSup_mem hne hbdd
    refine ⟨g (sSup S), tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hs₀] with s hs
    have h1 : ⌊h s⌋₊ ≤ sSup S := le_csSup hbdd ⟨s, hs.2, rfl⟩
    have h2 : sSup S ≤ ⌊h s⌋₊ := hM ▸ Nat.floor_le_floor (hm hs.1.le)
    rw [le_antisymm h1 h2]

/-- X̃ⁿ := Σ_{i<n} X̃_{t_i} 1_{[t_i, t_{i+1})} + X̃_T 1_{{T}} for a continuous path X̃ = ω:
the value at r is ω at the grid point t_{⌊nr/T⌋} (capped at T), extended flat after T. -/
noncomputable def stepD {d : ℕ} {T : ℝ≥0} (n : ℕ) (ω : MasterVisc.Comparison.Path d T) : DPath d T :=
  ⟨fun r => MasterVisc.Comparison.evalAt (grid T n (gridIdx T n r)) ω,
    isCadlag_comp_floor (fun r => (n : ℝ≥0) * r / T)
      ((continuous_const.mul continuous_id).div_const _)
      (fun _ _ hab => div_le_div_of_nonneg_right (mul_le_mul_right hab _) bot_le)
      (fun k => MasterVisc.Comparison.evalAt (grid T n k) ω), by
    intro r hr
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [grid, hn]
    · have key : ∀ s, T ≤ s → MasterVisc.Comparison.evalAt (grid T n (gridIdx T n s)) ω = MasterVisc.Comparison.evalAt T ω := by
        intro s hs
        rcases eq_or_ne T 0 with hT | hT
        · simp [grid, gridIdx, hT, MasterVisc.Comparison.evalAt]
        · have hidx : n ≤ gridIdx T n s := by
            apply Nat.le_floor
            rw [le_div_iff₀ (pos_iff_ne_zero.mpr hT)]
            exact mul_le_mul_right hs _
          have hg : T ≤ grid T n (gridIdx T n s) := by
            rw [grid, le_div_iff₀ (by exact_mod_cast hn)]
            exact mul_le_mul_right (by exact_mod_cast hidx) _
          simp only [MasterVisc.Comparison.evalAt, min_eq_right hg, min_self]
      exact (key r hr).trans (key T le_rfl).symm⟩

/-- The increment X̃_{t_i, t_{i+1}} = X̃_{t_{i+1}} − X̃_{t_i} of (2.4). -/
noncomputable def incr {d : ℕ} {T : ℝ≥0} (n i : ℕ) (ω : MasterVisc.Comparison.Path d T) : SDEState d :=
  MasterVisc.Comparison.evalAt (grid T n (i + 1)) ω - MasterVisc.Comparison.evalAt (grid T n i) ω

/-- X̃^{n,θ} := X̃ⁿ_{t_i∧·} + θ X̃_{t_i,t_{i+1}} 1_{[t_{i+1},T]}, built on the i-th interval. -/
noncomputable def thetaD {d : ℕ} {T : ℝ≥0} (n i : ℕ) (θ : ℝ) (ω : MasterVisc.Comparison.Path d T) : DPath d T :=
  bumpD (grid T n (i + 1)) (stopD (grid T n i) (stepD n ω)) (θ • incr n i ω)

/-- μⁿ := ℙ̃ ∘ (X̃ⁿ)⁻¹, the law on Ω̂ of the discretized process built from the representation `R`. -/
noncomputable def lawStep {d : ℕ} {T : ℝ≥0} (R : Rep d T) (n : ℕ) : Measure (DPath d T) :=
  R.P.map (fun ω => stepD n (R.Y ω))

/-- μ^{n,θ} := ℙ̃ ∘ (X̃^{n,θ})⁻¹ on the i-th interval. -/
noncomputable def lawTheta {d : ℕ} {T : ℝ≥0} (R : Rep d T) (n i : ℕ) (θ : ℝ) : Measure (DPath d T) :=
  R.P.map (fun ω => thetaD n i θ (R.Y ω))

end MasterVisc.Ito


