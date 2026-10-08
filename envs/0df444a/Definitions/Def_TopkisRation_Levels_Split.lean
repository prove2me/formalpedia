-- Prove2me | Definitions.Def_TopkisRation_Levels_Split
-- name    : TopkisRation_Levels_Split
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:17.051793+00:00
-- url     : https://prove2.me/theorems/fe367e8d-f39d-418e-a337-bca49dafb5c4
-- title:
--   (4), (5), p. 164 — the one-dimensional split f_t(w; z, B) and the priority vector u(z − w, B)
-- statement:
--   In the model of Topkis (1968, §1), fix an interval $t$, a stock level $z\ge0$ and an outstanding demand vector $B\ge0$, and write $B^{(j)}=\sum_{i\ge j}B^i$. For $w\in[(z-B^{(1)})^+,z]$, the stock left after exactly $z-w$ units are issued in interval $t$, the paper defines
--
--   $$
--   f_t(w;z,B)=\min_{0\le u\le B,\ \mathbf 1\cdot(B-u)=z-w}\big[p_t\cdot u+g_{t-1}(w,a_tu)\big]+h_t(w) \tag{4}
--   $$
--
--   and the vector $u(z-w,B)=(u^1(z-w,B),\dots,u^n(z-w,B))$ with
--
--   $$
--   u^j(z-w,B)=\big(B^{(j)}-z+w\big)^+\wedge B^j. \tag{5}
--   $$
--
--   $u(z-w,B)$ is the unsatisfied demand left when the $z-w$ issued units go to the classes in order of importance, class $n$ first.
--
--   These two objects reduce the $n$-dimensional minimization (1) to a one-dimensional one in $w$.
--
--   **Formalization Note.** $f_t(w;z,B)$ is defined with a real `sInf` over the constraint set; that it is a minimum is the content of (6) and Lemma 4 of the mission. `uVec s B` is $u(s,B)$ and is used with $s=z-w$.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 164, (4) and (5)

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

variable {n : ℕ}

/-- f_t(w; z, B) of (4): the cost of interval t onward when exactly z − w units of stock are
issued in interval t, i.e. the minimum over 0 ≤ u ≤ B with 1·(B − u) = z − w of
p_t·u + g_{t−1}(w, a_t u), plus h_t(w). -/
noncomputable def Model.fw (M : Model n) (t : ℕ) (w z : ℝ) (B : Fin n → ℝ) : ℝ :=
  sInf ((fun u => M.p t ⬝ᵥ u + M.g (t - 1) w (M.a t • u)) ''
      {u | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w}) + M.h t w

/-- u(s, B) of (5), called with s = z − w: u^j(z − w, B) = (B^{(j)} − z + w)⁺ ∧ B^j. -/
def uVec (s : ℝ) (B : Fin n → ℝ) : Fin n → ℝ :=
  fun j => min (max (tailSum B j - s) 0) (B j)

end TopkisRation.Levels


