-- Prove2me | Definitions.Def_ContinualCounting_medianMechanism
-- name    : ContinualCounting_medianMechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:17.448195+00:00
-- url     : https://prove2.me/theorems/df55a85f-5dc2-4541-bca2-f57e484c16e2
-- title:
--   The derived mechanism $\widehat M_s$
-- statement:
--   Let $\nu$ be the law of the oblivious noise, and let $z^{(1)},z^{(2)},z^{(3)}$ be three i.i.d. copies. For each node $u\in\mathcal T^s$ at even depth $2d<h$: if $s_{d+1}=r$,
--   $$q_u:=\mathrm{median}_{k=1,2,3}\{b^{(k)}_{r(u)}-m^u_\ell(\Delta^{<\ell(\ell(u))}(z^{(k)}),\Delta^{<\ell(r(u))}(z^{(k)}))\},\qquad \widehat m_u:=q_u+a_{r(u)},$$
--   and if $s_{d+1}=\ell$,
--   $$q_u:=\mathrm{median}_{k=1,2,3}\{b^{(k)}_{r(\ell(u))}-b^{(k)}_{r(u)}-b^{(k)}_{r(r(u))}-m^u_r(\Delta^{<r(\ell(u))}(z^{(k)}),\Delta^{<r(r(u))}(z^{(k)}))\},\qquad \widehat m_u:=q_u+a_{r(\ell(u))}-a_{r(u)}-a_{r(r(u))}.$$
--   $\widehat M_s(x)$ is the vector $(\widehat m_u)_u$. The restricted neighbouring relation of Lemma 4 consists of the neighbouring pairs $x,x'$ with $x_i=x'_i=0$ for $i\notin\mathcal L(\mathcal T^s)$.
--
--   This is the mechanism on which the privacy attack is run.
--
--   **Formalization Note** The paper's predictors $m^u_\ell,m^u_r$ are replaced by parameters `φL`, `φR`, arbitrary families of functions of the conditioning coefficients; theorems assume them measurable, and the paper's predictors are an instance. `medianMechanism` is the law of the output for input $x$.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §5, pp.23–24 (PDF pp.24–25), (14)–(15)

import Mathlib
import Definitions.Def_ContinualCounting_IsDP
import Definitions.Def_ContinualCounting_prefixSum
import Definitions.Def_ContinualCounting_median3
import Definitions.Def_ContinualCounting_InTs

set_option autoImplicit false

open MeasureTheory

namespace ContinualCounting

/-- The output coordinates of `M̂_s`: "one coordinate m̂_u for each node u ∈ T^s with an even depth
d(u) < h" (Bairaktari, Dahl, Larsen, arXiv:2607.00876, sha256 986e6426…, §5, p.23). -/
def outputNodes (h : ℕ) (s : Fin (h / 2) → Bool) : Finset Node :=
  (nodes h).filter fun u => InTs h s u ∧ 2 ∣ u.1 ∧ u.1 < h

/-- A predictor family of the coefficients `∆^{<ℓ(ℓ(u))}, ∆^{<ℓ(r(u))}`: the paper's `m^u_ℓ` is one. -/
abbrev PredictorsL (h : ℕ) := ∀ u : Node, (condSetL h u → ℝ) → ℝ

/-- A predictor family of the coefficients `∆^{<r(ℓ(u))}, ∆^{<r(r(u))}`: the paper's `m^u_r` is one. -/
abbrev PredictorsR (h : ℕ) := ∀ u : Node, (condSetR h u → ℝ) → ℝ

/-- The quantity inside the median of (14) (`s_{d+1} = r`, so `isRight = true`) and of (15)
(`s_{d+1} = ℓ`) for one noise copy `z`. -/
noncomputable def predictionError {h : ℕ} (φL : PredictorsL h) (φR : PredictorsR h)
    (isRight : Bool) (u : Node) (z : Fin (2 ^ h) → ℝ) : ℝ :=
  if isRight then targetL h u z - φL u (fun v => coef h v.1 z)
  else targetR h u z - φR u (fun v => coef h v.1 z)

/-- `q_u` of (14), (15), p.23–24: the median over the three noise copies. -/
noncomputable def medianNoise {h : ℕ} (φL : PredictorsL h) (φR : PredictorsR h) (isRight : Bool)
    (u : Node) (zz : Fin 3 → Fin (2 ^ h) → ℝ) : ℝ :=
  median3 (predictionError φL φR isRight u (zz 0)) (predictionError φL φR isRight u (zz 1))
    (predictionError φL φR isRight u (zz 2))

/-- **The derived mechanism `M̂_s`.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), §5,
pp.23–24, (14)–(15): `M̂_s` "draws three i.i.d. copies z^{(1)}, z^{(2)}, z^{(3)} of the noise z", and for
`u ∈ T^s` at depth `2d < h` sets `m̂_u := q_u + a_{r(u)}` if `s_{d+1} = r`, and
`m̂_u := q_u + a_{r(ℓ(u))} − a_{r(u)} − a_{r(r(u))}` if `s_{d+1} = ℓ`.

**Formalization Note.** The law of the output for input `x`, as the image of the product `ν^{⊗3}`. The
paper's `m^u_ℓ, m^u_r` are replaced by arbitrary predictor families `φL, φR`, and the theorems
assume these measurable, so the `Measure.map` is the true pushforward. `a_u = coef h u (A x)`, so the
signal is the target's linear form evaluated at `A x`. -/
noncomputable def medianMechanism {h : ℕ} (ν : Measure (Fin (2 ^ h) → ℝ))
    (s : Fin (h / 2) → Bool) (φL : PredictorsL h) (φR : PredictorsR h) (x : Fin (2 ^ h) → Bool) :
    Measure (outputNodes h s → ℝ) :=
  (Measure.pi fun _ : Fin 3 => ν).map fun zz u =>
    medianNoise φL φR (letter s (u.1.1 / 2)) u.1 zz +
      (if letter s (u.1.1 / 2) then targetL h u.1 (prefixSum (bitVec x))
        else targetR h u.1 (prefixSum (bitVec x)))

/-- The restricted neighbouring relation of Lemma 4: neighbouring `x, x′ ∈ {0, 1}^n` with
`x_i = x′_i = 0` for `i ∉ L(T^s)`. -/
def RestrictedNeighbor (h : ℕ) (s : Fin (h / 2) → Bool) (x x' : Fin (2 ^ h) → Bool) : Prop :=
  Neighbor x x' ∧ (∀ i, i ∉ leavesTs h s → x i = false) ∧ (∀ i, i ∉ leavesTs h s → x' i = false)

end ContinualCounting


