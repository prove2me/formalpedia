-- Prove2me | Definitions.Def_Pr6453_Invoice
-- name    : Pr6453_Invoice
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T16:14:12.883963+00:00
-- url     : https://prove2.me/theorems/969fa771-d541-4af1-8d63-e44929348545
-- title:
--   PR #6453: the invoice from the word's events to the rank histograms
-- statement:
--   The invoice of the PR #6453 word: the map from the word's events to its productive-target and paid-call rank histograms, `controller.formula_invoice` of the source.
--
--   The word emits five kinds of events. Each of the $18$ native calls (`LOCAL`) contributes the whole local helper histogram to the targets and the whole local paid histogram to the paid calls. The $17$ binary queries (`QUERY`) contribute $104$ paid jobs at rank $1$. The $14$ whole idle jobs (`IDLE`) contribute $208$ paid jobs at rank $8s$ where $s$ is the number of idle leaves. The $2$ individual idle jobs (`IDLE_ONE`) contribute $104$ each at rank $16$. The $20$ normalisations (`LAMBDA`) are free. On the productive side the $34$ diagonal terms contribute $104$ fields at rank $1+8\sigma$, where $\sigma$ is the index sum of the term.
--
--   `assemble` is the same invoice computed the other way, by folding over the events; `toHist` turns a counter into a histogram sorted by rank. The definitions let a proof check that the two computations agree on a given word and that the resulting histograms are the ones the price inequality prices.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: research/mixed-projector-query-root/controller.py (formula_invoice) and research/p104-third-anchor-clean-mixed-root/pricing.py (assemble), with the local receipt from RESULT.json (local.helpers, local.paid).

/-
# PR #6453: the invoice function

`controller.formula_invoice` of the source,
`research/mixed-projector-query-root/controller.py` at the PR #6453 head
(`b1a3e525793eca35c56324aa7ffd0b714cf606d4`):

```python
def formula_invoice(local):
    targets = Counter({r: 18*n for r,n in local['helpers'].items()})
    paid = Counter({r: 18*n for r,n in local['paid'].items()})
    paid[1] += 17*104
    # Four child trees: 7, 2, 2 and 7 leaves.
    for size, count in {2:8, 3:2, 4:2, 7:2}.items():
        targets[1+8*size] += 208*count
        paid[8*size] += 208*count
    for rank, count in {145:1, 73:2, 1:1, 17:2}.items():
        targets[rank] += 104*count
    paid[16] += 208
    return targets, paid
```

The coefficients are the word's census: `18` native calls (`LOCAL`), `17` binary queries
(`QUERY`, at `104` paid jobs each), `14` whole idle jobs (`IDLE`, `208` jobs each at rank
`8·size` with `size = 2,2,2,2,2,2,2,2,3,3,4,4,7,7`), `2` individual idle jobs (`IDLE_ONE`,
`104` each at rank `16`), and `34` diagonal terms (`targets[1+8·sum] += 104`, with sums
`0,2,…,2,3,…,4,…,7,…,9`).

This file formalises the function and checks that, applied to the local receipt of the
PR #6453 word, it returns exactly the two histograms that `Pr6453.moment_kappa_gt` prices.
-/
import Definitions.Def_Pr6453_RankMoments

set_option autoImplicit false

namespace Pr6453

noncomputable section

/-! ## The local receipt of the word -/

/-- Native helper targets of the local receipt, `RESULT.json → local.helpers`. -/
def localHelpers : List (ℕ × ℕ) :=
  [(1, 14), (2, 8), (3, 4), (4, 107), (5, 15), (6, 3), (7, 9), (8, 39), (9, 363)]

/-- Paid calls of the local receipt, `RESULT.json → local.paid`. -/
def localPaid : List (ℕ × ℕ) :=
  [(1, 2236), (2, 453), (3, 491), (4, 109), (5, 151), (6, 8), (7, 9), (8, 1)]

/-! ## The invoice -/

/-- The multiplicity of rank `r` in a histogram. -/
def countIn (h : List (ℕ × ℕ)) (r : ℕ) : ℕ :=
  (h.map fun p => if p.1 = r then p.2 else 0).sum

/-- The productive-target invoice: each of the `18` native calls contributes the local helper
histogram, the fourteen whole idle jobs contribute `208` fields at rank `1 + 8·size`, and the
thirty-four diagonal terms contribute `104` fields at rank `1 + 8·sum`. -/
def invoiceTargets (helpers : List (ℕ × ℕ)) : ℕ → ℕ := fun r =>
  18 * countIn helpers r
    + (if r = 17 then 208 * 8 else 0)
    + (if r = 25 then 208 * 2 else 0)
    + (if r = 33 then 208 * 2 else 0)
    + (if r = 57 then 208 * 2 else 0)
    + (if r = 1 then 104 * 1 else 0)
    + (if r = 17 then 104 * 2 else 0)
    + (if r = 73 then 104 * 2 else 0)
    + (if r = 145 then 104 * 1 else 0)

/-- The paid-call invoice: the `18` native calls, the `17` binary queries at rank `1`
(`104` jobs each), the fourteen whole idle jobs at rank `8·size`, and the two individual idle
jobs at rank `16` (`104` each). -/
def invoicePaid (paid : List (ℕ × ℕ)) : ℕ → ℕ := fun r =>
  18 * countIn paid r
    + (if r = 1 then 17 * 104 else 0)
    + (if r = 16 then 208 * 8 else 0)
    + (if r = 24 then 208 * 2 else 0)
    + (if r = 32 then 208 * 2 else 0)
    + (if r = 56 then 208 * 2 else 0)
    + (if r = 16 then 208 else 0)

/-- A counter as a histogram, sorted by rank with the zero ranks dropped. -/
def toHist (f : ℕ → ℕ) (N : ℕ) : List (ℕ × ℕ) :=
  ((List.range N).map fun r => (r, f r)).filter fun p => p.2 ≠ 0


