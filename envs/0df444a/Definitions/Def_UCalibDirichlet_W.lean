-- Prove2me | Definitions.Def_UCalibDirichlet_W
-- name    : UCalibDirichlet_W
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:23.273417+00:00
-- url     : https://prove2.me/theorems/f91e37ca-3afd-4407-8b38-dac45574799a
-- title:
--   Symmetric Bregman curvature $W^i_F(a)$
-- statement:
--   For a count vector $a\in\mathbb R^K_{\ge 0}$ and $i\in[K]$, let $a_{-i}$ be $a$ with its $i$-th coordinate replaced by $0$. Then
--   $$W^i_F(a)=\|a\|_1\,\mathbb E_{R\sim\mathrm{Dir}(a_{-i})}\Big[\mathrm{Cov}_{X\sim\mathrm{Beta}(a_i,\|a_{-i}\|_1)}\big(f'_{i,R}(X),X\big)\Big],$$
--   with $f_{i,R}$ the restriction of $F$ to the segment from $R$ to $e_i$. Equivalently (12), $W^i_F(a)=\frac{\|a\|_1}{2}\mathbb E_{R,X,Y}[(f'_{i,R}(X)-f'_{i,R}(Y))(X-Y)]$ with $X,Y$ independent. It is a symmetric Bregman curvature of $F$ averaged over the beta fluctuation of coordinate $i$ and the Dirichlet law of the others, and bounds the stability term (Lemma 1.6).
--
--   **Formalization Note** The value lies in $[0,+\infty]$ (symmetric form (12)), equal to (11) whenever the inner covariance is finite. $\mathrm{Dir}(a_{-i})$ uses the zero-parameter convention. The paper uses $W$ for $a_i>0$ and $\|a_{-i}\|_1>0$.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), displays (11)–(12), p.5

import Mathlib
import Definitions.Def_UCalibDirichlet_dir
import Definitions.Def_UCalibDirichlet_fRestr
import Definitions.Def_UCalibDirichlet_bregCov

open MeasureTheory

namespace UCalibDirichlet

/-- **The symmetric Bregman curvature `W^i_F(a)`, displays (11)–(12).** Frongillo, Luo, Mehta &
Schneider (manuscript, STOC 2027 submission), p.5: "For a count vector `a ∈ ℝ^K_+`, we also let
`a_{−i} ∈ ℝ^K_+` be the vector obtained by replacing the `i`-th coordinate of `a` by 0", and
"`W^i_F(a) = ‖a‖₁ E_{R∼Dir(a_{−i})}[Cov_{X∼Beta(a_i,‖a_{−i}‖₁)}(f′_{i,R}(X), X)]`. (11)"

`W F i a = ‖a‖₁ · ∫⁻ bregCov (f_{i,r}) (a_i) (‖a_{−i}‖₁) dDir(a_{−i})(r)`, in `[0, +∞]`, where
`a_{−i} = Function.update a i 0`, `‖a‖₁ = ∑_j a_j` and `‖a_{−i}‖₁ = ∑_j (a_{−i})_j`.

**Formalization Note.** The covariance is `bregCov`, the symmetric form (12) of the paper, valued
in `[0, +∞]`: it equals (11) whenever the inner covariance is finite and is `+∞` otherwise (no
junk `0`). `Dir(a_{−i})` uses the zero-parameter convention of p.2 (`dir`), so `R` lies on the face
`{r ∈ Δ_K : r_i = 0}` as (10) requires. The paper uses `W` for `a` with nonnegative coordinates,
`a_i > 0` and `‖a_{−i}‖₁ > 0` (so that `Beta(a_i, ‖a_{−i}‖₁)` is defined). -/
noncomputable def W {K : ℕ} (F : (Fin K → ℝ) → ℝ) (i : Fin K) (a : Fin K → ℝ) : ENNReal :=
  ENNReal.ofReal (∑ j, a j) *
    ∫⁻ r, bregCov (fRestr F i r) (a i) (∑ j, Function.update a i 0 j)
      ∂(dir (Function.update a i 0))

end UCalibDirichlet


