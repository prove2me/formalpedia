-- Prove2me | Definitions.Def_MultiSelectPandora_Inst_Valid
-- name    : MultiSelectPandora_Inst_Valid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:06.610197+00:00
-- url     : https://prove2.me/theorems/b18558ef-7761-46e0-a541-c1e079d18b66
-- title:
--   Validity of an instance
-- statement:
--   An instance is valid when $c_i\ge0$ and $\mathrm{val}_{ij}\ge0$ for all $i,j$, and each $(\mathrm{prob}_{ij})_j$ is a probability vector: its entries are nonnegative and sum to $1$.
--
--   These are exactly the constraints of the model. A zero cost, a zero value, $n=0$ and $k>n$ are all allowed, and values need not be distinct.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst

namespace MultiSelectPandora

/-- **Validity of an instance.** Beyhaghi–Han–Luqman manuscript, §2.1, p.5 (PDF p.6): `c_i ≥ 0`, `v_i ≥ 0`, and each
`F_i` a probability law.

**Formalization Note.** A zero cost, zero values, `n = 0` and `k > n` are all allowed, as on the page; there is no
distinct-values condition. `∑ prob = 1` excludes an empty support. -/
def Inst.Valid (I : Inst) : Prop :=
  (∀ i, 0 ≤ I.c i) ∧ (∀ i j, 0 ≤ I.val i j) ∧ (∀ i j, 0 ≤ I.prob i j) ∧ ∀ i, ∑ j, I.prob i j = 1

end MultiSelectPandora


