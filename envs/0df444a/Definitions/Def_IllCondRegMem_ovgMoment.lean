-- Prove2me | Definitions.Def_IllCondRegMem_ovgMoment
-- name    : IllCondRegMem_ovgMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:38.176937+00:00
-- url     : https://prove2.me/theorems/19c1c392-16ee-46d6-9239-72e79301600f
-- title:
--   Game 1 — the orthogonal vector game and the moments $\mathbb E[\sigma_k^p]$ of its score
-- statement:
--   The **orthogonal vector game** has inputs: dimensions $d\ge d_E$, message size $M$, query size $m$, accuracy $\delta_{\max}\in(0,1]$ and target $k$.
--
--   1. The oracle samples $E\sim\mathrm{Unif}(\mathrm{Gr}(d_E,d))$ and $v_1,\dots,v_m$ i.i.d. $\mathcal N(0,P_E)$.
--   2. Stage 1 (full access): given $E,v_1,\dots,v_m$, the player writes a message in $\{0,1\}^M$.
--   3. Stage 2: the public explored subspace starts at $G=\{0\}$ and the score at $\sigma=1$. For $i=1,\dots,k$, the player, using the message, $v_1,\dots,v_m$ and the stage-2 history, submits $w\in S^{d-1}\cap G^\perp$ and $\delta\in(0,\delta_{\max}]$. If $\|P_Ew\|\ge\delta$ the player loses ($\sigma=0$); otherwise $G\leftarrow G+\mathrm{Span}(P_{E^\perp}w)$ and $\sigma\leftarrow\sigma/\delta$.
--
--   The final score $\sigma_k$ measures how many nearly-perpendicular directions to $E$ the player can produce from a short message. Lemma 10 bounds its moments $\mathbb E[\sigma_k^p]$.
--
--   **Formalization Note** $\mathrm{Unif}(\mathrm{Gr}(d_E,d))$ is realized as the column span of a $d\times d_E$ matrix with i.i.d. $\mathcal N(0,1)$ entries (a rotation-invariant subspace of dimension $d_E$ almost surely), and $v_i=P_Eg_i$ with $g_i\sim\mathcal N(0,I_d)$. The player's randomness is one uniform seed used in both stages; the stage-2 history given to the player is the list of earlier responses $P_{E^\perp}w_j$. A query outside $S^{d-1}\cap G^\perp$ or with $\delta\notin(0,\delta_{\max}]$ loses, like a rejected query (such strategies are dominated by valid ones). The score lies in $[0,\infty]$ and $\mathbb E[\sigma_k^p]$ is a lower Lebesgue integral.
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Game 1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_IllCondRegMem_Learner

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- A **strategy for the orthogonal vector game** (Game 1, p.10) with message size `M`, query
size `m` and `k` stage-2 rounds in dimension `d`. `message E v s` is the stage-1 message written
with full access to `E`, the vectors `v₁, …, v_m` and the private seed `s`; `query i msg v s resp`
is the `i`-th stage-2 submission `(w, δ)`, computed from the message, the vectors `v`, the seed
and the responses `P_{E⊥} w_j` of the earlier rounds `j < i`. -/
structure OVGStrategy (d M m k : ℕ) where
  /-- Stage 1: the message `Message ∈ {0,1}^M`. -/
  message : Submodule ℝ (Vec d) → (Fin m → Vec d) → unitInterval → Mem M
  /-- Stage 2: the `i`-th query `(w_i, δ_i)`. -/
  query : (i : Fin k) → Mem M → (Fin m → Vec d) → unitInterval → (Fin i → Vec d) → Vec d × ℝ

open Classical in
/-- The state (score `σ`, responses `P_{E⊥} w_j`) of stage 2 after `n` rounds; responses of
rounds not yet played are `0`. -/
noncomputable def ovgRun {d M m k : ℕ} (S : OVGStrategy d M m k) (δmax : ℝ)
    (E : Submodule ℝ (Vec d)) (v : Fin m → Vec d) (s : unitInterval) :
    ℕ → ENNReal × (Fin k → Vec d)
  | 0 => (1, fun _ => 0)
  | n + 1 =>
    if h : n < k then
      let st := ovgRun S δmax E v s n
      let q := S.query ⟨n, h⟩ (S.message E v s) v s
        (fun j => st.2 ⟨j.val, lt_trans j.isLt h⟩)
      let G := Submodule.span ℝ (Set.range st.2)
      if ‖q.1‖ = 1 ∧ q.1 ∈ Gᗮ ∧ 0 < q.2 ∧ q.2 ≤ δmax ∧ ‖E.starProjection q.1‖ < q.2 then
        (st.1 * (ENNReal.ofReal q.2)⁻¹, Function.update st.2 ⟨n, h⟩ (Eᗮ.starProjection q.1))
      else (0, st.2)
    else ovgRun S δmax E v s n

/-- **`p`-th moment of the final score of the orthogonal vector game** (Game 1).
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Game 1,
p.10: "Input: dimensions d ≥ d_E, message size M, query size m, accuracy δ_max ∈ (0,1], target k.
Oracle: Sample E ∼ Unif(Gr(d_E, d)) and v₁, …, v_m iid∼ N(0, P_E). Stage 1: full access. Player:
Given E, v₁, …, v_m, write Message ∈ {0,1}^M. Stage 2: Player produces orthogonal directions with
only Message and query access. Initialize public explored subspace G ← {0} and score σ ← 1.
for i = 1, …, k do: Player: Using Message, v₁, …, v_m, and all stage 2 history, submit
w ∈ S^{d−1} ∩ G⊥ and δ ∈ (0, δ_max] to oracle; if ‖P_E w‖ ≥ δ then Player loses: σ ← 0 break;
Update G ← G + Span(P_{E⊥} w) and score σ ← σ/δ."

`ovgMoment dE S δmax p = E[σ_k^p]`.

**Formalization Note.** `E ∼ Unif(Gr(d_E, d))` is realized as the column span of a `d × d_E`
matrix `X` with i.i.d. `N(0,1)` entries (a rotation-invariant subspace of dimension `d_E` almost
surely when `d_E ≤ d`), and `v_i = P_E g_i` with `g_i` i.i.d. `N(0, I_d)`; the player's private
randomness is one uniform seed in `[0,1]`, available in both stages. The stage-2 history given to
the player is the list of earlier responses `P_{E⊥} w_j` (its own earlier queries are functions
of the same data). A query outside `S^{d−1} ∩ G⊥` or with `δ ∉ (0, δ_max]` loses (`σ = 0`), like a
rejected query; such strategies are dominated by valid ones. The score is in `[0, ∞]` and the
moment is a lower Lebesgue integral. -/
noncomputable def ovgMoment {d M m k : ℕ} (dE : ℕ) (S : OVGStrategy d M m k) (δmax p : ℝ) :
    ENNReal :=
  ∫⁻ ζ : (Fin dE → Vec d) × (Fin m → Vec d) × unitInterval,
      (ovgRun S δmax (Submodule.span ℝ (Set.range ζ.1))
        (fun i => (Submodule.span ℝ (Set.range ζ.1)).starProjection (ζ.2.1 i)) ζ.2.2 k).1 ^ p
    ∂((Measure.pi fun _ : Fin dE => stdGaussian (Vec d)).prod
      ((Measure.pi fun _ : Fin m => stdGaussian (Vec d)).prod (volume : Measure unitInterval)))

end IllCondRegMem


