-- Prove2me | Definitions.Def_BorderDiffEq_InBorderSWS
-- name    : BorderDiffEq_InBorderSWS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:42.898695+00:00
-- url     : https://prove2.me/theorems/296750c1-70ff-4149-b829-3737dacc1511
-- title:
--   The border $\overline{\Sigma\wedge\Sigma(w,e)}$ (and $\overline{\Sigma^{[w]}\wedge\Sigma}$)
-- statement:
--   Let $K$ be a field, $f$ a polynomial over $K$, $w\in\mathbb N$ and $e\in\mathbb N\cup\{\infty\}$. Then $f\in\overline{\Sigma\wedge\Sigma(w,e)}$ if some $\Sigma\wedge\Sigma$ circuit with constants and forms over $K((\varepsilon))$, top fan-in at most $w$ and every exponent at most $e$ satisfies
--   $$
--   \sum_j c_j\ell_j^{\,e_j}=f+\varepsilon\,S\qquad\text{for some } S\in K[[\varepsilon]][x].
--   $$
--   With $e=\infty$ (no bound on the exponents) this is the class $\overline{\Sigma^{[w]}\wedge\Sigma}$ of Lemma 4.10.
--
--   **Formalization Note** The exponent bound lives in `ℕ∞`, with `⊤` for "no bound". Constants in $K((\varepsilon))$ and $S\in K[[\varepsilon]][x]$ contain the paper's $K(\varepsilon)$ constants and $g\in K[\varepsilon][x]$.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §4, p.23

import Mathlib
import Definitions.Def_BorderDiffEq_SigmaWedgeSigma
import Definitions.Def_BorderDiffEq_IsEpsApprox

namespace BorderDiffEq

/-- **The border of Σ∧Σ circuits, `cl(Σ∧Σ(w, e))` and `cl(Σ^{[w]}∧Σ)`** (Bhat–Dutta–Kaplan–Shpilka–
Shringi, *Demystifying Border of Structured Algebraic Circuits via Differential Equations*,
manuscript (STOC 2027 submission), §4, p.23): a polynomial `f` over the field `K` is in the border
if some Σ∧Σ circuit with constants in `K((ε))`, top fan-in at most `w` and every exponent at most
`e`, computes `f + ε·S` with `S` a polynomial with coefficients in `K[[ε]]`.

**Formalization Note.** The exponent bound `e` lives in `ℕ∞`: `e = ⊤` means no bound, which is the
class `cl(Σ^{[w]}∧Σ)` of Lemma 4.10. Constants in `K((ε))` (Mathlib `LaurentSeries K`) and
`S ∈ K[[ε]][x]` cover the paper's `K(ε)` constants and `g ∈ K[ε][x]`. -/
def InBorderSWS (K : Type) [Field K] (σ : Type) [Fintype σ] (w : ℕ) (e : ℕ∞)
    (f : MvPolynomial σ K) : Prop :=
  ∃ Φ : SigmaWedgeSigma (LaurentSeries K) σ,
    Φ.topFanIn ≤ w ∧ (∀ j, (Φ.e j : ℕ∞) ≤ e) ∧ IsEpsApprox Φ.eval f

end BorderDiffEq


