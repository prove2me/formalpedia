-- Prove2me | Definitions.Def_OmniMix_Loss
-- name    : OmniMix_Loss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:16.763305+00:00
-- url     : https://prove2.me/theorems/dec5e8be-1be7-469d-9770-2ab1c81126eb
-- title:
--   Loss on binary outcomes $\ell:[0,1]\times\{0,1\}\to\mathbb R\cup\{+\infty\}$
-- statement:
--   A **loss** is a map $\ell:[0,1]\times\{0,1\}\to\mathbb R\cup\{+\infty\}$: $\ell(p,y)$ is the loss of the prediction $p\in[0,1]$ when the outcome is $y\in\{0,1\}$.
--
--   All objects of the paper (properness, mixability, regret) are properties of or quantities attached to such a loss.
--
--   **Formalization Note** The type is `unitInterval → Bool → EReal`; the outcome `true` is $1$. The value $-\infty$ is excluded by a separate hypothesis $\ell(p,y)\neq-\infty$ wherever a loss is assumed.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1

import Mathlib

namespace OmniMix

/-- **A loss on binary outcomes.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1: "a loss function
`ℓ : [0, 1] × {0, 1} → ℝ ∪ {+∞}`".

`Loss` is the type of maps `ℓ : [0,1] → {0,1} → EReal` (curried, prediction first).

**Formalization Note.** `[0,1]` is `unitInterval`; the outcome set `{0,1}` is `Bool`, with `true` the
outcome `1` (its real value is `outVal`). The codomain is `EReal`; the paper's codomain `ℝ ∪ {+∞}`
excludes `⊥`, so every theorem that assumes a loss states `∀ p y, ℓ p y ≠ ⊥` separately. -/
abbrev Loss : Type := unitInterval → Bool → EReal

end OmniMix


