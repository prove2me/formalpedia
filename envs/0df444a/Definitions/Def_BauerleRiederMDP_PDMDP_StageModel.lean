-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_StageModel
-- name    : BauerleRiederMDP_PDMDP_StageModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:21.964193+00:00
-- url     : https://prove2.me/theorems/a6e359ec-1d0d-46f5-b153-4c809789cb00
-- title:
--   Stationary substochastic Markov Decision Model, its operators $L$, $T$, values $J_n$, $J_\infty$ and $\alpha_b$
-- statement:
--   A stationary discrete-time **substochastic Markov Decision Model** with all actions admissible and discount factor $1$ consists of a one-stage reward $r(x,a)\in[-\infty,\infty]$ and a substochastic transition law $Q(\cdot|x,a)$. For a function $v$,
--   $$
--   (Lv)(x,a):=r(x,a)+\int v(x')\,Q(dx'|x,a),\qquad (Tv)(x):=\sup_a(Lv)(x,a).
--   $$
--   For a policy $\pi=(f_n)$, $J_{n\pi}=T_{f_0}\cdots T_{f_{n-1}}0$ and $J_{\infty\pi}=\lim_nJ_{n\pi}$, and
--   $$
--   \alpha_b:=\sup_{(x,a)}\frac{\int b(x')\,Q(dx'|x,a)}{b(x)}
--   $$
--   with the convention $0/0:=0$.
--
--   This general object carries the three embedded models of the chapter: with control functions, with relaxed controls, and of the chain.
--
--   **Formalization Note** The limit $J_{\infty\pi}$ is a `limsup`; the book gets its existence from the Convergence Assumption (C), which an upper bounding function with $\alpha_b<1$ implies. The quotient in $\alpha_b$ is in `ℝ≥0∞`, where $0/0=0$ and $c/0=\infty$ for $c>0$. The cemetery state is skipped, as in the book.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.28, pp.196–197 and p.247

import Mathlib
import Definitions.Def_MDPFinance_PDMDP_Core

open MeasureTheory Filter
open MDPFinance.PDMDP (erealIntegral)

namespace BauerleRiederMDP.PDMDP

/-- A stationary discrete-time **substochastic** Markov Decision Model with discount factor `1`
and all actions admissible (`D = S × Act`): a one-stage reward `rew` with values in `[-∞, ∞]` and a
substochastic transition law `kern` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.1 and p.247, PDF 258, where the cemetery state `Δ` is
skipped). It is the shape of the embedded models `(E, A, D, Q', r')` of §8.2 and `(E, U, Q', r')`
of §8.3.

**Formalization Note** Rewards are `EReal` because `r'` may equal `-∞`. -/
structure StageModel (S Act : Type*) [MeasurableSpace S] where
  /-- The one-stage reward. -/
  rew : S → Act → EReal
  /-- The substochastic transition law. -/
  kern : S → Act → Measure S

namespace StageModel

variable {S Act : Type*} [MeasurableSpace S]

/-- `(Lv)(x,a) := r(x,a) + ∫ v(x') Q(dx'|x,a)`. -/
noncomputable def L (D : StageModel S Act) (v : S → EReal) (x : S) (a : Act) : EReal :=
  D.rew x a + erealIntegral (D.kern x a) v

/-- The maximal reward operator `(Tv)(x) := sup_a (Lv)(x,a)`. -/
noncomputable def T (D : StageModel S Act) (v : S → EReal) (x : S) : EReal :=
  ⨆ a, D.L v x a

/-- `J_{nπ} = T_{f_0} ⋯ T_{f_{n-1}} 0` for a policy `π = (f_n)` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.197, PDF 208). -/
noncomputable def J (D : StageModel S Act) : ℕ → (ℕ → S → Act) → S → EReal
  | 0, _, _ => 0
  | n + 1, f, x => D.L (D.J n fun k => f (k + 1)) x (f 0 x)

/-- `J_{∞π} = lim_n J_{nπ}` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.197, PDF 208).

**Formalization Note** The book obtains the limit from the Convergence Assumption (C), which an
upper bounding function with `α_b < 1` implies; `limsup` is that limit. -/
noncomputable def Jinf (D : StageModel S Act) (f : ℕ → S → Act) (x : S) : EReal :=
  limsup (fun n => D.J n f x) atTop

/-- `α_b := sup_{(x,a)} ∫ b(x') Q(dx'|x,a) / b(x)`, with the convention `0/0 := 0` (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.196,
PDF 207, and p.28, PDF 43).

**Formalization Note** The quotient is taken in `ℝ≥0∞`, where `0/0 = 0` and `c/0 = ∞` for `c > 0`;
the second case is the failure of `∫ b dQ ≤ α b(x)` at a state with `b(x) = 0`. -/
noncomputable def alphaB (D : StageModel S Act) (b : S → ℝ) : ENNReal :=
  ⨆ x, ⨆ a, (∫⁻ z, ENNReal.ofReal (b z) ∂(D.kern x a)) / ENNReal.ofReal (b x)

end StageModel

end BauerleRiederMDP.PDMDP


