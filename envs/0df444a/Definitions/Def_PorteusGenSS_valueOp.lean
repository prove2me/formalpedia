-- Prove2me | Definitions.Def_PorteusGenSS_valueOp
-- name    : PorteusGenSS_valueOp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:16:30.695477+00:00
-- url     : https://prove2.me/theorems/c507a113-3e7a-4b44-924e-11cb00df4472
-- title:
--   One-period minimization $\inf_{y\ge x}\{c(y-x)+h(y)\}$
-- statement:
--   For an ordering cost $c$ and a function $h$,
--
--   $$
--   f(x)=\inf_{y\ge x}\{c(y-x)+h(y)\},
--   $$
--
--   the optimal cost when starting from inventory $x$; with $h=h_n$ this is equation (4), $f_n$.
--
--   **Formalization Note** The infimum is Lean's real infimum, which equals $0$ for sets unbounded below; under the hypotheses of the mission's theorems the infimum is attained or assumed finite.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), eq. (4), p. 413

import Mathlib

namespace PorteusGenSS

/-- **One-period value operator, equation (4).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §III, eq. (4), p. 413: "fn(x) = inf_{y≥x} {c(y − x) + hn(y)}."

`valueOp c h x = inf_{w ≥ x} (c(w − x) + h(w))`; with `h = hₙ` it is the paper's `fₙ(x)`.

**Formalization Note.** This is the real infimum `⨅` over the subtype `[x, ∞)`, which is the
greatest lower bound when the values are bounded below, and `0` (a Lean default) when they are
not. Under the hypotheses of the mission's goal every such infimum is attained (Lemma 3:
`Yₙ(x)` is nonempty), so the default value is never reached there; Lemma 2 carries the
boundedness explicitly. -/
noncomputable def valueOp (c h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨅ w : Set.Ici x, c ((w : ℝ) - x) + h w

end PorteusGenSS


