-- Prove2me | Definitions.Def_BeatingGV42_HasCodeFamily
-- name    : BeatingGV42_HasCodeFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:10.621219+00:00
-- url     : https://prove2.me/theorems/cc1e0b40-af1c-4aad-a756-98059b9bb546
-- title:
--   Family of $q$-ary codes with relative distance $\ge\delta$ and asymptotic rate $\ge R$
-- statement:
--   For an alphabet size $q$, a real $\delta$ and a real $R$, there is a **family of $q$-ary codes with asymptotic relative distance at least $\delta$ and asymptotic rate at least $R$** if there are lengths $n_0,n_1,\dots$ with $n_i\to\infty$ and codes $C_i\subseteq[q]^{n_i}$ such that
--
--   1. every $C_i$ has minimum distance at least $\delta n_i$, and
--   2. the rates satisfy $\displaystyle\liminf_{i\to\infty}\frac{\log_q|C_i|}{n_i}\ge R$, that is, for every $\varepsilon>0$, eventually $\dfrac{\log_q|C_i|}{n_i}\ge R-\varepsilon$.
--
--   This is the paper's notion of "a family of codes … with asymptotic relative distance at least $\delta$ and asymptotic rate at least $R$" in Theorem 1.1 and Proposition 4.9. The requirement $n_i\to\infty$ excludes the trivial one-letter code $[q]^1$.
--
--   **Formalization Note** The paper does not define the phrase. The lengths are `n : ℕ → ℕ` with `Tendsto n atTop atTop`; the distance condition is pointwise in $i$ (it implies $\liminf d(C_i)/n_i\ge\delta$ and is what the construction gives, eq. (4.20)); the rate condition is the $\varepsilon$-form of the $\liminf$, so no `Filter.liminf` junk value enters. Lean's `Real.logb q 0 = 0` gives an empty code rate $0$; this is immaterial, since for $R\le 0$ a one-word code already has rate $0$.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), Theorem 1.1, p.3 (PDF p.5), and Proposition 4.9, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_BeatingGV42_MinDistAtLeast

set_option autoImplicit false

open Filter

namespace BeatingGV42

/-- **A family of `q`-ary codes with asymptotic relative distance at least `δ` and asymptotic rate
at least `R`** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), Theorem 1.1, p.3 (PDF p.5), and Proposition 4.9, p.20 (PDF p.22)).
The paper does not define the phrase; it is read as: codes `C_i ⊆ [q]^{n_i}` with lengths
`n_i → ∞`, every `C_i` of minimum distance at least `δ n_i`, and rate `log_q |C_i| / n_i`
with `liminf_i log_q |C_i| / n_i ≥ R`.

**Formalization Note**
- The family is indexed by `i : ℕ`, with lengths `n : ℕ → ℕ` and `Tendsto n atTop atTop`. Without
  this requirement the single code `[q]¹` (rate 1, relative distance 1) would qualify.
- The distance condition is pointwise (`MinDistAtLeast (C i) (δ * n i)` for every `i`), which
  implies `liminf d(C_i)/n_i ≥ δ`; it is what the paper's construction delivers (eq. (4.20)).
- The rate condition is `liminf ≥ R` written as "for every `ε > 0`, eventually
  `R − ε ≤ log_q |C_i| / n_i`", so no `Filter.liminf` junk value enters. `Real.logb q 0 = 0`, so
  an empty code has rate `0` in Lean (the paper's `−∞`); this changes nothing, since for
  `R ≤ 0` a one-word code already has rate `0 ≥ R`. -/
def HasCodeFamily (q : ℕ) (δ R : ℝ) : Prop :=
  ∃ (n : ℕ → ℕ) (C : ∀ i, Finset (Fin (n i) → Fin q)),
    Tendsto n atTop atTop ∧
    (∀ i, MinDistAtLeast (C i) (δ * n i)) ∧
    ∀ ε > 0, ∀ᶠ i in atTop, R - ε ≤ Real.logb q ((C i).card : ℝ) / (n i : ℝ)

end BeatingGV42


