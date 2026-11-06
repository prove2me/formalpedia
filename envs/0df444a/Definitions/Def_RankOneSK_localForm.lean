-- Prove2me | Definitions.Def_RankOneSK_localForm
-- name    : RankOneSK_localForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:21.864028+00:00
-- url     : https://prove2.me/theorems/4af5298c-7b3b-492d-9831-f8f0cea7e51b
-- title:
--   Local quadratic form of Theorem 3.1 and (36)
-- statement:
--   For parameters $d,s,\lambda$, the two-spin measure $\mu_{J,a,b}$ and $f:\{\pm1\}^2\to\mathbb R$,
--   $$\begin{aligned}Q(f)={}&\mathbb E[(L_Xf)(L_Yf)]+J\,\mathbb E[M(L_Xf)(L_Yf)]+\frac{(\lambda J)^2}2\,\mathbb E[(L_Xf)^2+(L_Yf)^2]\\&+\frac{dJ^2}2\,\mathbb E\big[\bar X(y)^2(L_Xf)^2+\bar Y(x)^2(L_Yf)^2\big],\end{aligned}$$
--   all expectations under $\mu_{J,a,b}$, with $M(x,y)=(x+s\bar X(y))(y+s\bar Y(x))$.
--
--   Theorem 3.1 states $Q(f)\ge0$ for small $|J|$ uniformly in $a,b$; Lemma 4.1 computes the matrix of $Q$ in the basis $\varphi(X),\varphi(Y),\varphi(X)\varphi(Y)$.
--
--   **Formalization Note** The two spins are Booleans read as $\pm1$; $J$ is the raw interaction (not $\bar J=\tanh J$) and $a,b$ are the fields.
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Theorem 3.1, p.19 and (36), p.24

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_twoSpinExp
import Definitions.Def_RankOneSK_twoSpinLX
import Definitions.Def_RankOneSK_twoSpinLY
import Definitions.Def_RankOneSK_magX
import Definitions.Def_RankOneSK_magY
import Definitions.Def_RankOneSK_rankOneM

open OAI.SKGap

namespace RankOneSK

/-- The local quadratic form of Theorem 3.1 and display (36):
`E[(L_X f)(L_Y f)] + J·E[M(L_X f)(L_Y f)] + ((λJ)²/2)·E[(L_X f)² + (L_Y f)²]
  + (dJ²/2)·E[X̄(y)²·(L_X f)² + Ȳ(x)²·(L_Y f)²]`,
all expectations under the two-spin Ising measure `µ_{J,a,b}`, with `M(x, y) = (x + sX̄(y))(y + sȲ(x))`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Theorem 3.1, p.19, and Lemma 4.1, display (36), p.24.

**Formalization Note** The two spins are `Bool` values read as ±1 through `OAI.SKGap.spinValue`
(`true ↦ 1`, `false ↦ −1`); the first is `x` (the paper's `X`), the second `y` (`Y`). `J` is the raw
interaction (not `J̄ = tanh J`), `a`, `b` are the fields. The parameter `λ` is written `lam` (`λ` is a Lean keyword). -/
noncomputable def localForm (d s lam J a b : ℝ) (f : Bool → Bool → ℝ) : ℝ :=
  twoSpinExp J a b (fun x y => twoSpinLX J a b f x y * twoSpinLY J a b f x y) +
    J * twoSpinExp J a b (fun x y => rankOneM J a b s x y * twoSpinLX J a b f x y * twoSpinLY J a b f x y) +
    (lam * J) ^ 2 / 2 * twoSpinExp J a b (fun x y => twoSpinLX J a b f x y ^ 2 + twoSpinLY J a b f x y ^ 2) +
    d * J ^ 2 / 2 * twoSpinExp J a b (fun x y =>
      magX J a b y ^ 2 * twoSpinLX J a b f x y ^ 2 + magY J a b x ^ 2 * twoSpinLY J a b f x y ^ 2)

end RankOneSK


