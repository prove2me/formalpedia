-- Prove2me | Definitions.Def_IterRoundKMedian_Main_SinglePivot
-- name    : IterRoundKMedian_Main_SinglePivot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:25:37.106613+00:00
-- url     : https://prove2.me/theorems/d4471ef3-b941-43ca-ba2a-6c09a1c41497
-- title:
--   Quantities of one iteration of the single-pivot rounding: V(U), D(U), w(U,i), u_{qi}, r_i, I and Γ
-- statement:
--   Fix a client $j$ and a finite set $U$ of facilities with openings $y_i$ and distances $d_i=d(i,j)$; let $w_{qi}$ be the weight with which a pivot $q$ deletes $i$. Define
--   $$y(U)=\sum_{i\in U}y_i,\quad V(U)=\sum_{i\in U}y_id_i,\quad D(U)=\sum_{i,i'\in U}y_iy_{i'}|d_i-d_{i'}|,\quad w(U,i)=\sum_{q\in U}w_{qi},\quad u_{qi}=y_q-w_{qi}.$$
--   Let $r_i=\min\{d_q: q\in U,\ u_{qi}>0\}$, with $\min\emptyset=\infty$, and interpret $(y(U)-w(U,i))\,r_i$ as $0$ when $r_i=\infty$. The saving terms are
--   $$I=\sum_{i,q\in U}y_iu_{qi}(d_q-2d_i)_+,\qquad \Gamma=V(U)-\sum_{i\in U}y_i\big(y(U)-w(U,i)\big)r_i+I.$$
--
--   **Formalization Note.** Namespace `SinglePivot`; `w q i` is $w_{qi}$; `r` takes values in `WithTop ℝ` (the infimum over the empty set is `⊤`), and `mulTopZero c r` is $c\cdot r$ with $c\cdot\infty:=0$.
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), pp. 30–31, §4.2–4.3

import Mathlib

namespace IterRoundKMedian.Main
namespace SinglePivot

/-! Quantities of one iteration of the single-pivot rounding (§4.2–4.3). Fix a client `j`;
for a set `U` of facilities, `y_i` is the opening of `i`, `d_i = d(i, j)` and `w q i` is the
weight `w_{qi}` with which pivot `q` deletes `i` (the nearest-unit weights of `i`). -/

variable {ι : Type*}

/-- `y(U) = Σ_{i∈U} y_i`. -/
def yU (U : Finset ι) (y : ι → ℝ) : ℝ := ∑ i ∈ U, y i

/-- `V(U) = Σ_{i∈U} y_i d_i`. -/
def V (U : Finset ι) (y d : ι → ℝ) : ℝ := ∑ i ∈ U, y i * d i

/-- `D(U) = Σ_{i,i'∈U} y_i y_{i'} |d_i − d_{i'}|`. -/
def D (U : Finset ι) (y d : ι → ℝ) : ℝ := ∑ i ∈ U, ∑ q ∈ U, y i * y q * |d i - d q|

/-- `w(U, i) = Σ_{q∈U} w_{qi}`. -/
def wU (U : Finset ι) (w : ι → ι → ℝ) (i : ι) : ℝ := ∑ q ∈ U, w q i

/-- `u_{qi} = y_q − w_{qi}`. -/
def u (y : ι → ℝ) (w : ι → ι → ℝ) (q i : ι) : ℝ := y q - w q i

/-- `r_i = min{d_q : q ∈ U, u_{qi} > 0}`, with `min ∅ = ∞` (`⊤`). -/
noncomputable def r (U : Finset ι) (y d : ι → ℝ) (w : ι → ι → ℝ) (i : ι) : WithTop ℝ := by
  classical
  exact (U.filter (fun q => 0 < u y w q i)).inf (fun q => ((d q : ℝ) : WithTop ℝ))

/-- `c · r` for `r ∈ ℝ ∪ {∞}`, with `c · ∞ := 0` (the paper interprets
`(y(U) − w(U,i)) r_i` as `0` when `r_i = ∞`, which happens exactly when
`y(U) = w(U,i)`). -/
def mulTopZero (c : ℝ) : WithTop ℝ → ℝ
  | ⊤ => 0
  | (x : ℝ) => c * x

/-- `I = Σ_{i,q∈U} y_i u_{qi} (d_q − 2 d_i)_+`. -/
def savingI (U : Finset ι) (y d : ι → ℝ) (w : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ U, ∑ q ∈ U, y i * u y w q i * max (d q - 2 * d i) 0

/-- `Γ = V(U) − Σ_{i∈U} y_i (y(U) − w(U,i)) r_i + I`. -/
noncomputable def Gamma (U : Finset ι) (y d : ι → ℝ) (w : ι → ι → ℝ) : ℝ :=
  V U y d - ∑ i ∈ U, y i * mulTopZero (yU U y - wU U w i) (r U y d w i) + savingI U y d w

end SinglePivot
end IterRoundKMedian.Main


