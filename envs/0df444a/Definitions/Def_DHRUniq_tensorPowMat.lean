-- Prove2me | Definitions.Def_DHRUniq_tensorPowMat
-- name    : DHRUniq_tensorPowMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:42.362348+00:00
-- url     : https://prove2.me/theorems/13fd55f9-e20f-4fed-8ebc-99491f6f6a94
-- title:
--   Tensor power $\varrho^{\otimes n}$ of a bipartite operator
-- statement:
--   For an operator $\varrho$ on $\mathbb C^a\otimes\mathbb C^b$, the **$n$-fold tensor power** $\varrho^{\otimes n}$ acts on $(\mathbb C^a)^{\otimes n}\otimes(\mathbb C^b)^{\otimes n}$, with
--
--   $$
--   \varrho^{\otimes n}\big((x,y),(x',y')\big)=\prod_{i=1}^n\varrho\big((x_i,y_i),(x'_i,y'_i)\big).
--   $$
--
--   Alice holds all first factors and Bob all second factors, which is the cut for conditions (E4) and (E4′).
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, (E4), p. 8

import Mathlib

namespace DHRUniq

/-- **The `n`-fold tensor power `ϱ^{⊗n}` of a bipartite operator** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, (E4), p. 8: "the
`n`-fold tensor product of `ϱ` by itself which acts on the tensor product
`(H^A)^{⊗n} ⊗ (H^B)^{⊗n}`"), with entries
`ϱ^{⊗n}((x, y), (x', y')) = ∏_i ϱ((x_i, y_i), (x'_i, y'_i))`.

**Formalization Note** Alice's `n` copies are grouped into `Fin n → a` and Bob's into
`Fin n → b`, as in the published `WildeQIT.EntManip.tensorPowVec`; the published
`RainsSep.Distill.pairPower` has the same entries but only for `a = b`, which is why it is not
reused. -/
def tensorPowMat {a b : Type} (ρ : Matrix (a × b) (a × b) ℂ) (n : ℕ) :
    Matrix ((Fin n → a) × (Fin n → b)) ((Fin n → a) × (Fin n → b)) ℂ :=
  Matrix.of fun z w => ∏ i, ρ (z.1 i, z.2 i) (w.1 i, w.2 i)

end DHRUniq


