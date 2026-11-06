-- Prove2me | Definitions.Def_DecodablePOMDP_DecodingTable
-- name    : DecodablePOMDP_DecodingTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:48.100268+00:00
-- url     : https://prove2.me/theorems/9202a1b8-d9fe-4a8d-9cc9-beba33cb6fa8
-- title:
--   Decoding tables, their probabilities and the policies they induce
-- statement:
--   A **decoding table** $d$ has one entry $d_h(y)\in\mathcal S$ for each stage $h\in\{2,\dots,H\}$ and observation $y\in\mathcal O$. Sampling the entries independently, $d_h(y)\sim D_h(\cdot\mid y)$, gives $d$ the probability
--
--   $$\prod_{h=2}^H\prod_{y\in\mathcal O}D_h(d_h(y)\mid y).$$
--
--   For a deterministic policy $\sigma$ of $\widehat{\mathcal P}$, the policy $\sigma\circ d$ of $\mathcal P$ runs $\sigma$ on the observations $(y_h,d_h(y_h))$ in place of $(y_h,\widehat X_h)$.
--
--   These are the objects of the derandomisation of App. A.10.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), App. A.10, p.20

import Mathlib
import Definitions.Def_DecodablePOMDP_Value

namespace DecodablePOMDP

/-- **Probability of a decoding table** (A.10, p.20). A decoding table `d` has one entry
`d_h(y) ∈ S` for each stage `h ∈ {2, …, H}` (index `h − 2`) and observation `y ∈ O`; sampling all
entries independently, `d_h(y) ∼ D_h(· | y)`, gives `d` the probability
`Π_{h=2}^{H} Π_{y∈O} D_h(d_h(y) | y)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.10, p.20: "The decoding table contains
one entry for each stage h ∈ {2, . . . , H} and observation y ∈ O, giving (H − 1)O entries in total.
… independently sampling all decoding-table entries in advance". -/
def tableWeight {S O : Type} [Fintype O] (H : ℕ) (D : ℕ → O → S → ℝ)
    (d : Fin (H - 1) → O → S) : ℝ :=
  ∏ i, ∏ y, D (i.val + 2) y (d i y)

/-- **Policy of the original POMDP that decodes with a fixed table** (A.10, p.20): run the
deterministic augmented policy `σ`, feeding it `(y, d_h(y))` in place of the sampled `(y, X̂_h)`.
In a `t`-step history (from stage 1, newest first) entry `i` carries the observation of stage
`t + 1 − i`, i.e. table index `t − 1 − i`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.10, p.20.

**Formalization Note.** Indices outside the table (never read for histories of length
`≤ H − 1`) use `default`. -/
def decodePolicy {S A O : Type} [Inhabited S] (H : ℕ) (d : Fin (H - 1) → O → S)
    (σ : DetPolicyFn A (O × S)) : DetPolicyFn A O :=
  fun t hist => σ t (fun i => ((hist i).1, ((hist i).2,
    if hlt : t - 1 - i.val < H - 1 then d ⟨t - 1 - i.val, hlt⟩ (hist i).2 else default)))

end DecodablePOMDP


