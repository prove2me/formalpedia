-- Prove2me | Definitions.Def_TightClock_Supplement_windowProg
-- name    : TightClock_Supplement_windowProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:17:26.7812+00:00
-- url     : https://prove2.me/theorems/ca61153a-e0c6-44b4-958f-f5870ba23277
-- title:
--   Auction 7 — $\mathrm{Window}(a,b;\mathcal F,U)$
-- statement:
--   **Auction 7 (Window$(a,b;\mathcal F',U)$)** for $0<a<b$, a downward-closed family $\mathcal F'$ and an available set $U$ of bidders active at price $0$. Let $\beta>1$ solve $\beta\log\beta-\beta+1=\log(b/a)$ (5.2) and
--
--   $$\lambda_1=\log\Big(\beta\frac ba\Big),\qquad\lambda_2=\beta-1-\log\beta,\qquad\lambda=\lambda_1+\lambda_2\quad(5.3).$$
--
--   Set $Z_i=0$ for $i\notin U$. Independently for each $i\in U$:
--
--   * **screening**, with probability $\lambda_1/\lambda$: draw $p_i\sim H_1$ and offer $\max\{a,p_i\}$; $Z_i=p_i$ if she accepts, $Z_i=0$ otherwise;
--   * **sampling**, otherwise: $v_i\leftarrow\mathrm{Reveal}(i)$; $Z_i=0$ if $v_i<a$, else $Z_i\sim H_2(\min\{v_i,b\})$.
--
--   Select $S\in\arg\max_{S'\in\mathcal F'}\sum_{i\in S'}Z_i$ (by the selection rule) and run $\mathrm{RetainOnly}(S)$, which serves $S\cap\{\text{active bidders}\}$.
--
--   **Formalization Note** Each bidder has two independent uniforms: one for the screening coin and one for the score draw (through the quantile functions of $H_1$, $H_2$). The screening price is a real price, not a grid price.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §5.1.3, Auction 7, p.25 (PDF p.28), with (5.2)–(5.4), p.24 (PDF p.27)

import Mathlib
import Definitions.Def_TightClock_Supplement_reveal
import Definitions.Def_TightClock_Supplement_retainOnly
import Definitions.Def_TightClock_Supplement_Selector
import Definitions.Def_TightClock_Supplement_betaRoot
import Definitions.Def_TightClock_Supplement_h1Quantile
import Definitions.Def_TightClock_Supplement_h2Quantile

set_option autoImplicit false

namespace TightClock.Supplement

/-- Auction 7, `Window(a, b; F′, U)`, started from the public state `st0` (the bidders of `U` active
at price `0`). `β > 1` solves `β log β − β + 1 = log(b/a)` (5.2); `λ₁ = log(βb/a)`,
`λ₂ = β − 1 − log β`, `λ = λ₁ + λ₂` (5.3). `Zᵢ = 0` for `i ∉ U`. Independently for each `i ∈ U`: with
probability `λ₁/λ` (iff `cᵢ < λ₁/λ`; screening) draw `pᵢ ~ H₁` and offer `max{a, pᵢ}`, with `Zᵢ = pᵢ`
if she accepts and `0` otherwise; else (sampling) `vᵢ ← Reveal(i)`, `Zᵢ = 0` if `vᵢ < a`, and otherwise
`Zᵢ ~ H₂(min{vᵢ, b})`. Finally select `S ∈ arg max_{S′∈F′} ∑_{i∈S′} Zᵢ` (chosen by the selection rule `sel`)
and run `RetainOnly(S)`, which serves `S ∩ active`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §5.1.3, Auction 7, p.25 (PDF 28), with
(5.2)–(5.4), p.24 (PDF 27).

**Formalization Note** The draws from `H₁` and `H₂(x)` use the uniform `dᵢ` through the quantile
functions. The screening price `max{a, pᵢ}` is a real price, not a grid price. -/
noncomputable def windowProg {n : ℕ} (δ a b : ℝ) (F' : Finset (Finset (Fin n))) (U : Finset (Fin n))
    (sel : Selector n) (c d : Fin n → unitInterval) (st0 : CState n) : ClockProg n (Finset (Fin n)) := do
  let β := betaRoot (Real.log (b / a))
  let lam1 := Real.log (β * b / a)
  let lam2 := β - 1 - Real.log β
  let lam := lam1 + lam2
  let (st, Z) ← (List.finRange n).foldlM (fun (acc : CState n × (Fin n → ℝ)) i => do
    if i ∈ U then
      if (c i : ℝ) < lam1 / lam then
        let p := h1Quantile a β lam1 (d i)
        let (acc', st') ← offerTo acc.1 i (max a p)
        return (st', Function.update acc.2 i (if acc' then p else 0))
      else
        let (x, st') ← reveal δ acc.1 i
        return (st', Function.update acc.2 i (if x < a then 0 else h2Quantile β lam2 (min x b) (d i)))
    else return acc) (st0, fun _ => 0)
  retainOnly δ st (sel.pick F' (fun S => ∑ i ∈ S, Z i))

end TightClock.Supplement


