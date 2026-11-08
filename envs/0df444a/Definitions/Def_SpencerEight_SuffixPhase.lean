-- Prove2me | Definitions.Def_SpencerEight_SuffixPhase
-- name    : SpencerEight_SuffixPhase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:34.875568+00:00
-- url     : https://prove2.me/theorems/1e3f3900-add8-413f-a49a-9b82cd9439d8
-- title:
--   A suffix phase of Lemma 8.45
-- statement:
--   For a family $B$ on the active set $S_0$, the numbers $(v,c,q)$ form a **suffix phase** if $0<q<1$, $v,c>0$ and there are $a,\beta\ge0$, $\eta>0$ with
--   $$c^2s_+^2\eta\ge v,\qquad n\bigl(v(d_8(q)-\beta/2)-a\bigr)>0,$$
--   and, for every nonempty $S'\subseteq S_0$ of size $m\le vn$,
--   $$\gamma_m\Bigl[\bigl\|\sum_{i\in S'}x_iB_i\bigr\|\le\sqrt{vn/\eta}\Bigr]\ge\exp[-m(a/v+\beta/2)].$$
--
--   This spells out the source's phrase "phases satisfy Lemma 8.43 with $(w,L,q,b):=(v,c,q,0)$", with $K_0$ the norm body and $\theta=0$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.45, p.106 (PDF p.106); Lemma 8.43, p.105 (PDF p.105)

import Mathlib
import Definitions.Def_SpencerEight_gammaM
import Definitions.Def_SpencerEight_sPlus
import Definitions.Def_SpencerEight_d8
open scoped Matrix.Norms.L2Operator

namespace SpencerEight

/-- One suffix phase of Lemma 8.45 (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.106 (PDF p.106)): "phases satisfy Lemma 8.43 with `(w, L, q, b) := (v, c, q, 0)`", for the family `B` on the active set `S₀`. There are `a, β ≥ 0` and `η > 0` with the radius condition `c² s₊² η ≥ v`, the reserve `n(v(d₈(q) − β/2) − a) > 0`, and, at every active size, the Gaussian mass bound of Lemma 8.43 for `K₀` the norm body with `θ = 0`: for every nonempty subfamily `S' ⊆ S₀` of size `m ≤ vn`, `γ_m[‖∑_{i∈S'} xᵢBᵢ‖ ≤ √(vn/η)] ≥ exp[−m(a/v + β/2)]`.

**Formalization Note** This spells out the page's phrase, which is what the proof feeds to Lemma 8.43 ("Lemma 8.43 with no moment bodies performs the suffix phases, including skipped phases"). The suffix applies no congruence, so `B` is the family after the last prefix step. -/
def SuffixPhase {ι : Type*} {n : ℕ} (B : ι → Matrix (Fin n) (Fin n) ℝ) (S₀ : Finset ι)
    (v c q : ℝ) : Prop :=
  0 < q ∧ q < 1 ∧ 0 < v ∧ 0 < c ∧
  ∃ a β η : ℝ, 0 ≤ a ∧ 0 ≤ β ∧ 0 < η ∧
    v ≤ c ^ 2 * sPlus ^ 2 * η ∧
    0 < (n : ℝ) * (v * (d8 q - β / 2) - a) ∧
    ∀ S' : Finset ι, S' ⊆ S₀ → S'.Nonempty → (S'.card : ℝ) ≤ v * n →
      ENNReal.ofReal (Real.exp (-((S'.card : ℝ) * (a / v + β / 2)))) ≤
        gammaM S' {x | ‖∑ i : S', x i • B i‖ ≤ Real.sqrt (v * n / η)}

end SpencerEight


