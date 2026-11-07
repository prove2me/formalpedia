-- Prove2me | Definitions.Def_TargetedSamplers_origLayer
-- name    : TargetedSamplers_origLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:38.536417+00:00
-- url     : https://prove2.me/theorems/772a2cf3-e6e6-4a02-9522-c3efbcbf50ec
-- title:
--   The original, translation and auxiliary layers of the bootstrapping system
-- statement:
--   Fix a layered circuit $C_n$ of width $T$ and an input $x$. The construction in the proof of Theorem 4.23 defines strings indexed by $g\circ b=2g+b$, $g<T$, $b\in\{0,1\}$:
--
--   - $P_1$: $(P_1)_{g\circ b}$ is the value of gate $g$ of layer 1.
--   - $Q_i$: $(Q_i)_{g\circ b}=(\mathrm{OUT}_i(g,b),(P_i)_{g\circ b})$, pairs ordered lexicographically.
--   - $R_{i,\log 2T,0}$: the bitonic sorter applied to $Q_i$.
--   - $P_{i+1}$: $(P_{i+1})_{g\circ b}$ is the NAND of the second components of $R_{i,\log 2T,0}$ at positions $g\circ0$ and $g\circ1$.
--
--   These are the original layers $P_i$, the translation layers $Q_i$ and the auxiliary layers $R_{i,k,j}$ of the paper.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), proof of Theorem 4.23, pp.31–32 (pdf pp.33–34)

import Mathlib
import Definitions.Def_TargetedSamplers_LayeredCircuit
import Definitions.Def_TargetedSamplers_bitonicNet

namespace TargetedSamplers

namespace LayeredCircuit

variable {n : ℕ}

/-- The translation layer `Qᵢ` built on a string `P ∈ {0,1}^{2T}` (Chen, Doron, Ebtehaj, Tell,
Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, proof of Theorem 4.23, p.31):
`(Qᵢ)_{g∘b} = (OUTᵢ(g, b), P_{g∘b})`, where `g∘b = 2g + b`. Pairs are ordered lexicographically.
Positions `≥ 2T` are padding and are never read. -/
def translationLayer (c : LayeredCircuit n) (i : ℕ) (P : ℕ → Bool) : ℕ → ℕ ×ₗ Bool := fun j =>
  if h : j / 2 < c.width then toLex ((c.out i ⟨j / 2, h⟩ (decide (j % 2 = 1))).val, P j)
  else toLex (0, false)

/-- The original layers `Pᵢ ∈ {0,1}^{2T}` of the bootstrapping system of a circuit `C_n` of width
`T` on input `x` (proof of Theorem 4.23, pp.31–32): `P₁` replicates layer 1 of `C_n`,
`(P₁)_{g∘b} = ` value of gate `g` of layer 1; for `i ≥ 1`, `R_{i,log 2T,0}` is the bitonic sorter
applied to `Qᵢ`, and `(P_{i+1})_{g∘b}` is the NAND of the second components of
`R_{i,log 2T,0}` at `g∘0` and `g∘1`. -/
noncomputable def origLayer (c : LayeredCircuit n) (x : Fin n → Bool) : ℕ → ℕ → Bool
  | 0 => fun _ => false
  | 1 => fun j => if h : j / 2 < c.width then c.value x 1 ⟨j / 2, h⟩ else false
  | i + 2 => fun j =>
      let R := bitonicNet (Nat.log 2 (2 * c.width))
        (c.translationLayer (i + 1) (c.origLayer x (i + 1)))
      !((ofLex (R (2 * (j / 2)))).2 && (ofLex (R (2 * (j / 2) + 1))).2)

end LayeredCircuit

end TargetedSamplers


