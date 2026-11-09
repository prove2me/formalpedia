-- Prove2me | Definitions.Def_OnlineCarpoolingLei_Oblivious_Threshold
-- name    : OnlineCarpoolingLei_Oblivious_Threshold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:52.664689+00:00
-- url     : https://prove2.me/theorems/5350fca7-b7b7-4577-9db2-528943659cbb
-- title:
--   Backward-witness thresholds: $K=\lfloor D/40\rfloor$, $\ell=\lceil D^2/80\rceil$, $A(k)$, slack $\Lambda(t,S)$, $S^{\pm}$
-- statement:
--   For an integer $D\ge300$ put
--   $$K=\Big\lfloor\frac D{40}\Big\rfloor,\qquad \ell=\Big\lceil\frac{D^2}{80}\Big\rceil,\tag{4.1}$$
--   and for integers $k\ge0$
--   $$A(k)=\sum_{r=0}^{k-1}(D-30r)=kD-15k(k-1).\tag{4.2}$$
--   For a trajectory $(d_t)$ and $S\subseteq[n]$ the **slack** is $\Lambda(t,S)=d_t(S)-A(|S|)$. When the edge $e_t=\mathbf 1_{u_t}-\mathbf 1_{v_t}$ crosses $S$, write
--   $$S^0=S,\qquad S^+=S\cup\{u_t,v_t\},\qquad S^-=S\setminus\{u_t,v_t\}.$$
--
--   The threshold has $A(0)=0$, $A(1)=D$ and increments $A(k+1)-A(k)=D-30k$; the increments decrease by $30$, one more than the bound $29$ on the receiving gap. These quantities drive the backward-witness argument of Lemmas 4.1 and 4.2.
--
--   **Formalization Note** $D$ is a natural number. $K$ is natural-number division (rounding down) and $\ell$ is the natural ceiling of the real number $D^2/80$. $A(k)$ is computed in $\mathbb Z$, so $k-1$ is not truncated at $k=0$.
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Section 4.1, (4.1), (4.2), pp.6–7 (PDF pp.6–7)

import Mathlib
import Definitions.Def_OnlineCarpoolingLei_Oblivious_Model

/-!
Yuhao Lei, *Online carpooling against an oblivious adversary*, STOC 2027 submission #416
(October 2026), §4.1 (pp.6–7): (4.1) `K` and `ℓ`, (4.2) the threshold `A(k)`, the slack
`Λ(t, S)`, and the sets `S⁺`, `S⁻` at a crossing edge.
-/

namespace OnlineCarpoolingLei.Oblivious

/-- (4.1) `K = ⌊D / 40⌋` (natural-number division rounds down). -/
def Kc (D : ℕ) : ℕ := D / 40

/-- (4.1) `ℓ = ⌈D² / 80⌉`. -/
noncomputable def ellc (D : ℕ) : ℕ := ⌈((D : ℝ) ^ 2) / 80⌉₊

/-- (4.2) `A(k) = ∑_{r=0}^{k−1} (D − 30 r) = kD − 15 k (k − 1)`, computed in `ℤ`. -/
def Athr (D k : ℕ) : ℤ := (k : ℤ) * D - 15 * (k : ℤ) * ((k : ℤ) - 1)

/-- The slack `Λ(t, S) = d_t(S) − A(|S|)` of a trajectory `d`. -/
def slack {n : ℕ} (D : ℕ) (d : ℕ → Fin n → ℤ) (t : ℕ) (S : Finset (Fin n)) : ℤ :=
  setSum (d t) S - Athr D S.card

/-- `S⁺ = S ∪ {u, v}` for the edge `e = 1_u − 1_v`. -/
def splus {n : ℕ} (e : Edge n) (S : Finset (Fin n)) : Finset (Fin n) := S ∪ {e.u, e.v}

/-- `S⁻ = S \ {u, v}` for the edge `e = 1_u − 1_v`. -/
def sminus {n : ℕ} (e : Edge n) (S : Finset (Fin n)) : Finset (Fin n) := S \ {e.u, e.v}

end OnlineCarpoolingLei.Oblivious


