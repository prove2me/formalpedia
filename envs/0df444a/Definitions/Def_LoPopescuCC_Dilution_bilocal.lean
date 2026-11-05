-- Prove2me | Definitions.Def_LoPopescuCC_Dilution_bilocal
-- name    : LoPopescuCC_Dilution_bilocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:13.380878+00:00
-- url     : https://prove2.me/theorems/4a3a23dc-2786-4829-9bd5-aa1ed5607499
-- title:
--   Local maps $(V_A\otimes V_B)w$
-- statement:
--   For matrices $V_A$ and $V_B$ acting on Alice's and Bob's side respectively, $(V_A\otimes V_B)w$ is the vector with amplitudes
--
--   $$
--   \big((V_A\otimes V_B)w\big)(i,j)=\sum_{p,q}(V_A)_{ip}(V_B)_{jq}\,w(p,q).
--   $$
--
--   It expresses the paper's "up to bi-local unitary transformations".
--
--   **Formalization Note** The matrices may be rectangular. The theorems assume $V_A^\dagger V_A=1$ and $V_B^\dagger V_B=1$, so the maps are local isometries, and local unitaries when square.
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, proof of the Lemma, p. 4

import Mathlib

namespace LoPopescuCC.Dilution

/-- **`(V_A ⊗ V_B) w`** (Lo, Popescu, arXiv:quant-ph/9902045v2, proof of the Lemma, p. 4: "up to
bi-local unitary transformations"): the vector obtained by applying the local map `V_A` on Alice's
side and `V_B` on Bob's side, with amplitude
`((V_A ⊗ V_B) w)(i, j) = Σ_{p,q} (V_A)_{ip} (V_B)_{jq} w(p, q)`.

**Formalization Note** The maps are rectangular matrices. The theorems assume `V_Aᴴ V_A = 1` and
`V_Bᴴ V_B = 1`, i.e. local isometries, which are local unitaries when the matrices are square. -/
noncomputable def bilocal {a b α β : Type} [Fintype α] [Fintype β] (VA : Matrix a α ℂ)
    (VB : Matrix b β ℂ) (w : EuclideanSpace ℂ (α × β)) : EuclideanSpace ℂ (a × b) :=
  WithLp.toLp 2 fun z => ∑ p, ∑ q, VA z.1 p * VB z.2 q * w (p, q)

end LoPopescuCC.Dilution


