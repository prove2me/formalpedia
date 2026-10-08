-- Prove2me | Definitions.Def_StrategicQR_Game_CriticalLevels
-- name    : StrategicQR_Game_CriticalLevels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T19:38:41.84773+00:00
-- url     : https://prove2.me/theorems/1e12973a-af29-49a7-a159-ab894834badb
-- title:
--   Lemmas 2, 3, 5 — critical demand levels $D_l, D_m, D_h, D_r$, sale prices $s_l, s_m, s_h(D), s_r$, the price rules $s^*$ and the first-order conditions (2), (4)
-- statement:
--   Fix the strategic fraction $\alpha$, the order quantity $q$ and the belief $\hat v$, and let $\xi=1-\bar G(\hat v)\alpha$. The paper's sale prices are the **low price** $s_l=v_B$, the **medium price** $s_m=\arg\max_{s\ge\hat v}s(\bar v-s)=\max(\bar v/2,\hat v)$, the **high price**
--   $$s_h(D)=\frac{(\bar v-\underline v)(D-q)}{\alpha D}+\hat v,$$
--   and, with quick response at unit cost $c_2$, $s_r=\arg\max_{s\ge \hat v}(s-c_2)\bar G(s)=\max(\hat v,(\bar v+c_2)/2)$. The **critical demand levels** are
--   $$D_l=\frac{q}{\xi+s_m\bar G(s_m)\alpha/s_l},\quad D_m=\frac{q}{\xi+\bar G(s_m)\alpha},\quad D_h=\frac q\xi,\quad D_r=\frac{q}{\xi+\bar G(s_r)\alpha}.$$
--   The **price rule of Lemma 2** is $s^*(D)=s_l$ if $D\le D_l$, $s_m$ if $D_l<D\le D_m$, and $s_h(D)$ if $D>D_m$. The **price rule of Lemma 5** is $s_l$ if $D\le D_l$, $s_m$ if $D_l<D\le D_m$, $s_h(D)$ if $D_m<D\le D_r$, and $s_r$ if $D>D_r$.
--
--   The right sides of the first-order conditions are, for (2) (Lemma 3),
--   $$p-c-pF(D_h)+s_lF(D_l)+\int_{D_m}^{D_h}(2s_h(x)-\bar v)\,dF(x),$$
--   and for (4) (quick response, Technical Appendix p. 6),
--   $$c_2-c_1-c_2F(D_r)+s_lF(D_l)+\int_{D_m}^{D_r}(2s_h(x)-\bar v)\,dF(x).$$
--
--   These are the closed forms that Lemmas 2, 3 and 5 assert to be optimal prices and derivatives of the profit. They are defined here as formulas only; the optimal revenues and profits themselves are defined independently, as suprema and expectations.
--
--   **Formalization Note** $D_h=q/\xi$ is a real number only for $\xi>0$; at $\xi=0$ (every consumer strategic and every one waiting) the paper's $D_h$ is $+\infty$, and the statements that use $D_h$ require $\xi>0$ or avoid $D_h$. The appendix prints $F(D_h^r)$ in (4); the re-derived and numerically checked term is $F(D_r)$.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 12, Lemma 2; p. 13, Lemma 3 eq. (2); p. 19, Lemma 5; Technical Appendix p. 6 (PDF 38), eq. (4)

import Mathlib
import Definitions.Def_StrategicQR_Game_Model

namespace StrategicQR.Game

open MeasureTheory

/-- The medium sale price `s_m = argmax_{s ≥ v̂} s (v̄ - s) = max(v̄/2, v̂)` (Lemma 2, p. 12). -/
noncomputable def sm (M : Model) (vhat : ℝ) : ℝ :=
  max (M.vhi / 2) vhat

/-- The critical demand level `D_l = q / (ξ + s_m Ḡ(s_m) α / s_l)` with `s_l = vB` (Lemma 2). -/
noncomputable def Dl (M : Model) (α q vhat : ℝ) : ℝ :=
  q / (xi M α vhat + sm M vhat * Gbar M (sm M vhat) * α / M.vB)

/-- The critical demand level `D_m = q / (ξ + Ḡ(s_m) α)` (Lemma 2). -/
noncomputable def Dm (M : Model) (α q vhat : ℝ) : ℝ :=
  q / (xi M α vhat + Gbar M (sm M vhat) * α)

/-- The critical demand level `D_h = q / ξ` (Lemma 2); meaningful when `ξ > 0`. -/
noncomputable def Dh (M : Model) (α q vhat : ℝ) : ℝ :=
  q / xi M α vhat

/-- The high sale price `s_h(D) = (v̄ - v̲)(D - q) / (α D) + v̂` (Lemma 2). -/
noncomputable def sh (M : Model) (α q vhat D : ℝ) : ℝ :=
  (M.vhi - M.vlo) * (D - q) / (α * D) + vhat

/-- The quick-response sale price `s_r = argmax_{s ≥ v̂} (s - c₂) Ḡ(s) = max(v̂, (v̄ + c₂)/2)`
(Lemma 5, p. 19; for `c₂ ≤ v̄`). -/
noncomputable def sr (M : Model) (c₂ vhat : ℝ) : ℝ :=
  max vhat ((M.vhi + c₂) / 2)

/-- The critical demand level `D_r = q / (ξ + Ḡ(s_r) α)` (Lemma 5, p. 19). -/
noncomputable def Dr (M : Model) (α c₂ q vhat : ℝ) : ℝ :=
  q / (xi M α vhat + Gbar M (sr M c₂ vhat) * α)

/-- The sale-price rule `s*(D)` of Lemma 2 (p. 12): `s_l = vB` if `D ≤ D_l`, `s_m` if
`D_l < D ≤ D_m`, and `s_h(D)` if `D > D_m`. -/
noncomputable def salePriceStar (M : Model) (α q vhat D : ℝ) : ℝ :=
  if D ≤ Dl M α q vhat then M.vB
  else if D ≤ Dm M α q vhat then sm M vhat
  else sh M α q vhat D

/-- The sale-price rule `s*` of Lemma 5 (i) (p. 19): `s_l` if `D ≤ D_l`, `s_m` if
`D_l < D ≤ D_m`, `s_h(D)` if `D_m < D ≤ D_r`, and `s_r` if `D > D_r`. -/
noncomputable def qrSalePriceStar (M : Model) (α c₂ q vhat D : ℝ) : ℝ :=
  if D ≤ Dl M α q vhat then M.vB
  else if D ≤ Dm M α q vhat then sm M vhat
  else if D ≤ Dr M α c₂ q vhat then sh M α q vhat D
  else sr M c₂ vhat

/-- The right-hand side of the first-order condition (2) (Lemma 3, p. 13):
`p - c - p F(D_h) + s_l F(D_l) + ∫_{D_m}^{D_h} (2 s_h(x) - v̄) dF(x)`. -/
noncomputable def focProfit (M : Model) (α c q vhat : ℝ) : ℝ :=
  M.p - c - M.p * demandCdf M.f (Dh M α q vhat) + M.vB * demandCdf M.f (Dl M α q vhat) +
    ∫ x in (Dm M α q vhat)..(Dh M α q vhat), (2 * sh M α q vhat x - M.vhi) * M.f x

/-- The right-hand side of the quick-response first-order condition (Technical Appendix p. 6,
(4), with the printed `F(D_h^r)` read as `F(D_r)`):
`c₂ - c₁ - c₂ F(D_r) + s_l F(D_l) + ∫_{D_m}^{D_r} (2 s_h(x) - v̄) dF(x)`. -/
noncomputable def focQRProfit (M : Model) (α c₁ c₂ q vhat : ℝ) : ℝ :=
  c₂ - c₁ - c₂ * demandCdf M.f (Dr M α c₂ q vhat) + M.vB * demandCdf M.f (Dl M α q vhat) +
    ∫ x in (Dm M α q vhat)..(Dr M α c₂ q vhat), (2 * sh M α q vhat x - M.vhi) * M.f x

end StrategicQR.Game


