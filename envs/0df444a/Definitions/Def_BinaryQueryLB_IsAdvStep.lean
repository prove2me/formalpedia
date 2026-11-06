-- Prove2me | Definitions.Def_BinaryQueryLB_IsAdvStep
-- name    : BinaryQueryLB_IsAdvStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:34.292997+00:00
-- url     : https://prove2.me/theorems/19c1d37d-9fa1-4c67-a4ab-9431258c4ab3
-- title:
--   One step of the adversary
-- statement:
--   Consider a query $(y,h)$ and write $\bar y/R=q=(x,z)$, $\ell_i(w)=a x_i+\langle w,z\rangle$. From the state $(P,j)$ the adversary answers in two steps.
--
--   1. **Commitment step.** If $y$ was queried before, $j(y)$ is kept and the sets do not change. Otherwise: if $z=0$, $j(y)$ is the least index maximizing $a x_i$ and the sets do not change; if $z\ne0$, let $\alpha=1/(2m)$, take levels $r_k$ with $\mu^*(P_k\cap\{\ell_k>r_k\})=\alpha\,\mu^*(P_k)$ for every $k$, let $i$ be the least index with $r_i=\max_k r_k$, replace
--   $$
--   P_i\leftarrow P_i\cap\{\ell_i>r_i\},\qquad P_k\leftarrow P_k\cap\{\ell_k\le r_i\}\quad(k\ne i),
--   $$
--   and set $j(y)=i$.
--   2. **Answer step.** With $j=j(y)$, for $w\in P_j$ let $\psi(w)=h(\phi,\gamma)$ where
--   $$
--   \phi=\frac{MR}{2}\big(a x_j+\langle w,z\rangle+b(\|q\|_2-1)_+\big),\qquad \gamma=\frac M2\big((ae_j,w)+r_{\mathrm{rad}}(q),0\big).
--   $$
--   Let $A_\beta=\{w\in P_j:\psi(w)=\beta\}$. For a bit $\beta$ with $\mu^*(A_\beta)\ge\frac12\mu^*(P_j)$, the adversary replaces $P_j\leftarrow A_\beta$ and answers $\beta$.
--
--   The step relation holds between the old state, the query, the answer $\beta$ and the new state when they follow these rules.
--
--   **Formalization Note** The levels and the bit are any admissible choices, so a step is a relation. $\mu^*$ is Lebesgue outer measure (`volume` on arbitrary sets); no set is assumed measurable.
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), §3.1, p.16, eq. (1)

import Mathlib
import Definitions.Def_BinaryQueryLB_AdvState
import Definitions.Def_BinaryQueryLB_LocalQuery
import Definitions.Def_BinaryQueryLB_ybar
import Definitions.Def_BinaryQueryLB_ellPiece
import Definitions.Def_BinaryQueryLB_embedQ
import Definitions.Def_BinaryQueryLB_slope
import Definitions.Def_BinaryQueryLB_rrad
import Definitions.Def_BinaryQueryLB_bConst
open Classical
open scoped ENNReal

namespace BinaryQueryLB

/-- **One step of the adversary (§3.1).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), §3.1, p.16. For a query `(y, h)` with
`ȳ/R = q = (x, z)`:

*Commitment step.* "If `y` was queried before, the committed index `j(y)` is kept and nothing
changes. Otherwise … If `z = 0` … the adversary sets `j(y)` to the least index maximizing `a x_i`
and leaves the sets unchanged. If `z ≠ 0`, let `α = 1/(2m)`. By Lemma 2.11, for each `k ∈ [m]` there
is a level `r_k` with `µ*(P_k ∩ {ℓ_k > r_k}) = α µ*(P_k)`, and we let `i` be the least index with
`r_i = max_k r_k`. The adversary replaces `P_i ← P_i ∩ {ℓ_i > r_i}`, `P_k ← P_k ∩ {ℓ_k ≤ r_i}`
(`k ≠ i`), (1) and sets `j(y) = i`."

*Answer step.* "Let `j = j(y)`, and for `w ∈ P_j` let `ψ(w)` be the bit `h(ϕ, γ)`, where
`ϕ = (MR/2)(a x_j + ⟨w, z⟩ + b(∥q∥₂ − 1)_+)`, `γ = (M/2)((a e_j, w) + r_rad(q), 0)`. … Let
`A_β = {w ∈ P_j : ψ(w) = β}` … some `β` satisfies `µ*(A_β) ≥ ½µ*(P_j)`, and the adversary replaces
`P_j ← A_β` and answers `β`."

`IsAdvStep d R M s (y, h) β s'` says that the adversary, in state `s`, may answer the query
`(y, h)` with the bit `β` and move to the state `s'` according to these rules (`Pc` are the sets
after the commitment step, `j` the committed index).

**Formalization Note.** The rules leave the levels `r_k` and the bit `β` free among the admissible
choices, so a step is a relation, not a function. `µ*` is `volume` on arbitrary (possibly
non-measurable) sets, i.e. Lebesgue outer measure; `α = (2m)⁻¹` in `ℝ≥0∞`. `m = d / 2`. -/
def IsAdvStep (d : ℕ) (R M : ℝ) (s : AdvState d) (qr : LocalQuery d) (β : Bool)
    (s' : AdvState d) : Prop :=
  ∃ (Pc : Fin (d / 2) → Set (EuclideanSpace ℝ (Fin (d / 2)))) (j : Fin (d / 2)),
    ((s.2 qr.1 = some j ∧ Pc = s.1) ∨
      (s.2 qr.1 = none ∧ zPart (R⁻¹ • ybar d qr.1) = 0 ∧ Pc = s.1 ∧
        (∀ k, aConst * xPart (R⁻¹ • ybar d qr.1) k ≤ aConst * xPart (R⁻¹ • ybar d qr.1) j) ∧
        (∀ k, aConst * xPart (R⁻¹ • ybar d qr.1) k = aConst * xPart (R⁻¹ • ybar d qr.1) j →
          j ≤ k)) ∨
      (s.2 qr.1 = none ∧ zPart (R⁻¹ • ybar d qr.1) ≠ 0 ∧
        ∃ r : Fin (d / 2) → ℝ,
          (∀ k, MeasureTheory.volume (s.1 k ∩ {w | r k < ellPiece (R⁻¹ • ybar d qr.1) k w}) =
            (2 * ((d / 2 : ℕ) : ℝ≥0∞))⁻¹ * MeasureTheory.volume (s.1 k)) ∧
          (∀ k, r k ≤ r j) ∧ (∀ k, r k = r j → j ≤ k) ∧
          Pc j = s.1 j ∩ {w | r j < ellPiece (R⁻¹ • ybar d qr.1) j w} ∧
          ∀ k, k ≠ j → Pc k = s.1 k ∩ {w | ellPiece (R⁻¹ • ybar d qr.1) k w ≤ r j})) ∧
    MeasureTheory.volume (Pc j) / 2 ≤
      MeasureTheory.volume {w | w ∈ Pc j ∧ qr.2
        (M * R / 2 * (aConst * xPart (R⁻¹ • ybar d qr.1) j + inner ℝ w (zPart (R⁻¹ • ybar d qr.1)) +
            bConst (d / 2) * max (‖R⁻¹ • ybar d qr.1‖ - 1) 0),
          (M / 2) • embedQ d (slope j w + rrad (R⁻¹ • ybar d qr.1))) = β} ∧
    s'.1 = Function.update Pc j {w | w ∈ Pc j ∧ qr.2
        (M * R / 2 * (aConst * xPart (R⁻¹ • ybar d qr.1) j + inner ℝ w (zPart (R⁻¹ • ybar d qr.1)) +
            bConst (d / 2) * max (‖R⁻¹ • ybar d qr.1‖ - 1) 0),
          (M / 2) • embedQ d (slope j w + rrad (R⁻¹ • ybar d qr.1))) = β} ∧
    s'.2 = Function.update s.2 qr.1 (some j)

end BinaryQueryLB


