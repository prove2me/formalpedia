-- Prove2me | Definitions.Def_ZeroExtensionGap_Supplement_GapYes
-- name    : ZeroExtensionGap_Supplement_GapYes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:23:41.190786+00:00
-- url     : https://prove2.me/theorems/4c480439-05f1-4d89-beae-7c8a5a5e7ab0
-- title:
--   The gap problem $\mathrm{Gap\text{-}0\text{-}Ext}(k,\alpha)$
-- statement:
--   Fix an integer $k$ and a real factor $\alpha$. For a code $c$ of a 0-Extension input with threshold $\tau$ and instance $I$:
--
--   1. $c$ is a **Yes instance** of $\mathrm{Gap\text{-}0\text{-}Ext}(k,\alpha)$ if $I$ is valid (nonnegative weights, $D$ a metric on $T$), $|T|=k$, and $\mathrm{OPT}(I)\le\tau$;
--   2. $c$ is a **No instance** if $I$ is valid, $|T|=k$, and $\mathrm{OPT}(I)>\alpha\tau$.
--
--   An $\alpha$-approximation algorithm, one returning a retraction of cost at most $\alpha\cdot\mathrm{OPT}(I)$, outputs cost at most $\alpha\tau$ on Yes instances and more than $\alpha\tau$ on No instances, so it separates the two. Gap NP-hardness of this pair is therefore the statement that it is NP-hard to approximate 0-Extension within $\alpha$ on instances with exactly $k$ terminals.
--
--   **Formalization Note.** The module defines `GapYes k` and `GapNo k α`. No sign condition on $\tau$ is imposed: on a valid instance $\mathrm{OPT}\ge0$, so a negative threshold makes the Yes condition unsatisfiable. For $\alpha\ge1$ the two sets are disjoint.
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), Theorem 2, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_ZeroExtensionGap_Supplement_Code

set_option autoImplicit false

namespace ZeroExtensionGap.Supplement

/-- The Yes instances of the promise problem `Gap-0-Ext(k, α)` behind Theorem 2 of Chen, Zhu,
*Almost Tight Hardness of Approximation for 0-Extension*, STOC 2027 submission (manuscript sha256
0cdea87b…), §1.1, p.3 (PDF p.5): the coded instance is valid (nonnegative weights, `D` a metric on
`T`), has exactly `k` terminals, and `OPT(I) ≤ τ`.
**Formalization Note.** An `α`-approximation algorithm (one returning a retraction of cost at most
`α · OPT`) separates `GapYes k` from `GapNo k α`: its cost is at most `α τ` on Yes inputs and above
`α τ` on No inputs. So gap NP-hardness of this pair is "NP-hard to approximate within `α` on
instances with exactly `k` terminals". A negative threshold makes the Yes condition unsatisfiable
(costs are nonnegative on valid instances), so no sign condition on `τ` is needed. -/
def GapYes (k : ℕ) (c : Code) : Prop :=
  c.toInstance.IsValid ∧ c.toInstance.T.card = k ∧ c.toInstance.OPT ≤ (c.τ : ℝ)

/-- The No instances of `Gap-0-Ext(k, α)` (§1.1, p.3, PDF p.5): the coded instance is valid, has
exactly `k` terminals, and `OPT(I) > α · τ`. See `GapYes`. -/
def GapNo (k : ℕ) (α : ℝ) (c : Code) : Prop :=
  c.toInstance.IsValid ∧ c.toInstance.T.card = k ∧ α * (c.τ : ℝ) < c.toInstance.OPT

end ZeroExtensionGap.Supplement


