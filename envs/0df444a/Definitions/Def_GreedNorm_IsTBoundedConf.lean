-- Prove2me | Definitions.Def_GreedNorm_IsTBoundedConf
-- name    : GreedNorm_IsTBoundedConf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:34.976314+00:00
-- url     : https://prove2.me/theorems/53fa66a3-dee5-4aaf-a6a8-102139580b78
-- title:
--   $t$-bounded configuration set
-- statement:
--   Given load functions $\mathrm{load}_i$ and a threshold vector $t$, a configuration set $\mathcal A$ is **$t$-bounded** if for every $\ell\in\mathrm{POS}$ the number of configurations $(i,S)\in\mathcal A$ with $\mathrm{load}_i(S)>t_\ell$ is at most $\ell-1$.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 3.7, p.8 (PDF 10)

import Mathlib
import Definitions.Def_GreedNorm_POS

namespace GreedNorm

/-- **`t`-bounded configuration set**: for every `ℓ ∈ POS`, at most `ℓ − 1` configurations
`(i, S) ∈ A` have load `load_i(S) > t_ℓ`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 3.7, p.8 (PDF 10): "we say that A is t-bounded if for every ℓ∈POS, the number of
configurations (i, S) with load loadi(S) > tℓ is at most ℓ−1".

**Formalization Note** `load : Fin m → Finset U → ℝ` gives the load functions; POS is
`POS m ε`. -/
def IsTBoundedConf {m : ℕ} {U : Type} (ε : ℝ) (load : Fin m → Finset U → ℝ) (t : ℕ → ℝ)
    (A : Finset (Fin m × Finset U)) : Prop :=
  ∀ ℓ ∈ POS m ε, (A.filter (fun c => t ℓ < load c.1 c.2)).card ≤ ℓ - 1

end GreedNorm


