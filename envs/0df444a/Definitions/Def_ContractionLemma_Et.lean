-- Prove2me | Definitions.Def_ContractionLemma_Et
-- name    : ContractionLemma_Et
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:50.750394+00:00
-- url     : https://prove2.me/theorems/d3441767-5086-4d21-94e7-f92e9b16034d
-- title:
--   The easy points, orders $m_t$, $E_t$ of eq. (7), and $R_t$
-- statement:
--   The **easy points** are $\mathcal E=S\setminus\{0\}$. Given orders $q_0,q_1,\dots$, put $m_t=q_{v_2(t)}$, and
--
--   $$
--   E_t(T)=\prod_{t'\in\mathcal E\setminus\{t\}}\Big(\frac{T-t'}{t-t'}\Big)^{m_{t'}}.
--   $$
--
--   $R_t(z)$ is the polynomial formed by the terms of degree below $m_t$ of the power series $F(t+\alpha z)/E_t(t+\alpha z)$. The module also defines the same construction from given data in place of the first $m_t$ coefficients of $F(t+\alpha z)$, and congruence of rationals modulo $2^p$, where $x\equiv y$ means $x=y$ or $v_2(x-y)\ge p$.
--
--   **Formalization Note** The level $v_2(t)$ is `padicValInt 2 t`, used only at nonzero $t$. Mathlib's `padicValRat 2 0 = 0` is a junk value, so congruence states the case $x=y$ separately, which gives the paper's $v_2(0)=\infty$.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.4.2, p.58; App. A.5.4, eq. (7), pp.70–71

import Mathlib
import Definitions.Def_ContractionLemma_kernel
import Definitions.Def_ContractionLemma_zoom

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- The easy points `E = S \ {0}` (App. A.4.1, p.57). -/
noncomputable def easyPts (a : ℕ) : Finset ℤ := (gridS a).erase 0

/-- The order `m_t = q_{v₂(t)}` at an easy point (App. A.5.4, p.70): the number of Taylor
coefficients taken at `t`, depending only on the level `v₂(t)` (`padicValInt 2 t`). -/
def orderAt (q : ℕ → ℕ) (t : ℤ) : ℕ := q (padicValInt 2 t)

/-- **`E_t` (eq. (7))** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript, sha256
049caea1…), p.70 (PDF p.73): `E_t(T) = ∏_{t′ ∈ E \ {t}} ((T − t′)/(t − t′))^{m_{t′}}`. -/
noncomputable def Et (a : ℕ) (q : ℕ → ℕ) (t : ℤ) : ℚ[X] :=
  ∏ t' ∈ (easyPts a).erase t, (C ((t : ℚ) - t')⁻¹ * (X - C (t' : ℚ))) ^ orderAt q t'

/-- The power series `1/E_t(t + αz)` (Lemma A.13(b)). -/
noncomputable def invZoomEt (a : ℕ) (q : ℕ → ℕ) (t : ℤ) : PowerSeries ℚ :=
  ((zoom a t (Et a q t) : ℚ[X]) : PowerSeries ℚ)⁻¹

/-- **`R_t`** (Lemma A.13, p.71): the polynomial formed by the terms of degree below `m_t` of
the power series `F(t + αz)/E_t(t + αz)`. -/
noncomputable def Rt (a : ℕ) (q : ℕ → ℕ) (t : ℤ) (F : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc (orderAt q t) (((zoom a t F : ℚ[X]) : PowerSeries ℚ) * invZoomEt a q t)

/-- `R_t` built, exactly as `R_t` is built from `F`, from given values `y 0, …, y (m_t − 1)` in
place of the first `m_t` coefficients of `F(t + αz)` (Lemma A.13(d)). -/
noncomputable def RtOfData (a : ℕ) (q : ℕ → ℕ) (t : ℤ) (y : ℕ → ℚ) : ℚ[X] :=
  PowerSeries.trunc (orderAt q t)
    (((∑ k ∈ Finset.range (orderAt q t), C (y k) * X ^ k : ℚ[X]) : PowerSeries ℚ) *
      invZoomEt a q t)

/-- Congruence of rationals modulo `2^p` (App. A.5.2, p.64, with `v₂(0) = ∞`): `x − y = 0` or
`v₂(x − y) ≥ p`. -/
def ratCongr (p : ℤ) (x y : ℚ) : Prop := x - y = 0 ∨ p ≤ padicValRat 2 (x - y)

end ContractionLemma


