-- Prove2me | Definitions.Def_ABPOnline_IsFinalBlockFeedback
-- name    : ABPOnline_IsFinalBlockFeedback
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:30.156045+00:00
-- url     : https://prove2.me/theorems/4344c91c-d64a-4bea-a562-20c83566a2f0
-- title:
--   The Euler scheme (19) and the final-block confinement property of Lemma 4.5
-- statement:
--   For a feedback $v$, independent Brownian coordinates $B_1,\dots,B_M$ and $N\ge1$, the **Euler scheme** is
--   $$
--   \hat Z_{0,i}=0,\qquad \hat a_{k,i}=v(k/N,\hat Z_{k,i}),\qquad \hat Z_{k+1,i}=\hat Z_{k,i}+\frac{\hat a_{k,i}}{N}+B_i\big(\tfrac{k+1}{N}\big)-B_i\big(\tfrac kN\big).
--   $$
--   Fix an even integer $p>4$ and $c_F>0$. A triple $(h_0,s_p,(v_N))$ has the **final-block confinement property** if $h_0>0$; $s_p$ is continuous on $(0,h_0)$ and $s_p(h)\downarrow0$ as $h\downarrow0$; and for every compact $[h_1,h_2]\subset(0,h_0)$ there is $C$ such that, whenever $L_N\in\{1,\dots,N-1\}$ and $h_N=L_N/N\in[h_1,h_2]$, the feedback $v_N$ (measurable) satisfies, for every $M$ and all $M$ independent Brownian coordinates,
--   $$
--   \sup_{k<L_N}\|\hat a_{k,i}\|_{L^p}\le c_F\quad(20),\qquad \mathbb E\max_{i\le M}\operatorname{dist}\big(\hat Z_{L_N,i},[-s_p(h_N),s_p(h_N)]\big)\le C\,M^{1/p}N^{-1}\quad(21),
--   $$
--   and $C\,M^{1/p}N^{-1}\to0$ when $M=O(N)$.
--
--   Lemma 4.5 asserts that such a triple exists; Propositions 4.7 and 4.8 use any such triple as the final-block feedback of Algorithm 1.
--
--   **Formalization Note** The feedback is a family indexed by $(N,L_N)$, chosen before the compact range and the constant, as in the paper's single construction (97). "Explicit" is not formalized. $\operatorname{dist}(z,[-s,s])$ is written $\max(|z|-s,0)$ (equal for $s\ge0$, and $s_p\ge0$ follows from monotonicity and the limit $0$). The expectation is a lower integral in $[0,\infty]$, and the maximum over no rows is $0$. Probability spaces are in Lean's `Type`.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Lemma 4.5, (19)–(21), p.13 (PDF p.14)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianVec

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ABPOnline

variable {Ω : Type*} {M : ℕ}

/-- The Euler scheme (19) of arXiv:2609.02124 (Lemma 4.5, printed p.13, PDF p.14) driven by the
feedback `v` and the Brownian coordinates `B i`:
`Ẑ_{0,i} = 0`, `Ẑ_{k+1,i} = Ẑ_{k,i} + v(k/N, Ẑ_{k,i})/N + B_i((k+1)/N) − B_i(k/N)`. -/
noncomputable def eulerZ (N : ℕ) (v : ℝ → ℝ → ℝ) (B : Fin M → ℝ≥0 → Ω → ℝ) :
    ℕ → Fin M → Ω → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => fun i ω =>
      eulerZ N v B k i ω + v ((k : ℝ) / N) (eulerZ N v B k i ω) / N +
        (B i (((k + 1 : ℕ) : ℝ≥0) / N) ω - B i ((k : ℝ≥0) / N) ω)

/-- The drift `â_{k,i} = v(k/N, Ẑ_{k,i})` evaluated by the Euler scheme (19)
(arXiv:2609.02124, p.13). -/
noncomputable def eulerDrift (N : ℕ) (v : ℝ → ℝ → ℝ) (B : Fin M → ℝ≥0 → Ω → ℝ) (k : ℕ)
    (i : Fin M) (ω : Ω) : ℝ :=
  v ((k : ℝ) / N) (eulerZ N v B k i ω)

/-- The conclusion of Lemma 4.5 (Final-block confinement) of arXiv:2609.02124 (printed p.13,
PDF p.14) for an even integer `p > 4` and a budget `c_F`, made a property of the data
`(h₀, s_p, v)`: `h₀ > 0`; the radius `s_p` is continuous on `(0, h₀)` and decreases to `0` as
`h ↓ 0`; and for every compact `[h₁, h₂] ⊂ (0, h₀)` there is a constant `C` such that for all
`N` and `L_N ∈ {1, …, N−1}` with `h_N = L_N/N ∈ [h₁, h₂]`, the feedback `v_N = v N L_N` is
measurable and, for every `M` and all `M` independent Brownian coordinates, the Euler scheme (19)
satisfies the per-step drift bound (20) `sup_{k<L_N} ‖â_{k,i}‖_{L^p} ≤ c_F` and the terminal
confinement estimate (21) `E max_{i ≤ M} dist(Ẑ_{L_N,i}, [−s_p(h_N), s_p(h_N)]) ≤ C M^{1/p} N^{-1}`;
and ("in particular") if `M = M_N = O(N)` the right-hand side `C M^{1/p} N^{-1}` tends to `0`.

**Formalization Note** The feedback is a family indexed by `(N, L_N)`, fixed before the compact
range and the constant `C`, as in the paper, where `v_N = v_{h_N}` is one construction (97). The
word "explicit" is not formalized. `dist(z, [−s, s])` is written `max(|z| − s, 0)`, which is the
distance for `s ≥ 0`, and `s_p ≥ 0` follows from monotonicity and the limit `0`. The expectation of
the maximum is a lower Lebesgue integral in `ℝ≥0∞`, so it has no junk value; the maximum over the
empty set (`M = 0`) is `0`. The probability spaces quantified over live in `Type`. -/
def IsFinalBlockFeedback (p : ℕ) (cF h₀ : ℝ) (sp : ℝ → ℝ) (v : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop :=
  0 < h₀ ∧ ContinuousOn sp (Ioo 0 h₀) ∧ MonotoneOn sp (Ioo 0 h₀) ∧
    Tendsto sp (𝓝[>] 0) (𝓝 0) ∧
    ∀ h₁ h₂ : ℝ, 0 < h₁ → h₁ ≤ h₂ → h₂ < h₀ → ∃ C : ℝ,
      (∀ c : ℝ, ∀ Mseq : ℕ → ℕ, (∀ N, (Mseq N : ℝ) ≤ c * N) →
        Tendsto (fun N : ℕ => C * (Mseq N : ℝ) ^ (1 / (p : ℝ)) / N) atTop (𝓝 0)) ∧
      ∀ N L : ℕ, 1 ≤ L → L ≤ N - 1 → h₁ ≤ (L : ℝ) / N → (L : ℝ) / N ≤ h₂ →
        Measurable (Function.uncurry (v N L)) ∧
        ∀ (M : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : Fin M → ℝ≥0 → Ω → ℝ), IsBrownianVec B P →
          (∀ i : Fin M, ∀ k < L, eLpNorm (eulerDrift N (v N L) B k i) p P ≤ ENNReal.ofReal cF) ∧
          ∫⁻ ω, ⨆ i : Fin M,
              ENNReal.ofReal (max (|eulerZ N (v N L) B L i ω| - sp ((L : ℝ) / N)) 0) ∂P ≤
            ENNReal.ofReal (C * (M : ℝ) ^ (1 / (p : ℝ)) / N)

end ABPOnline


