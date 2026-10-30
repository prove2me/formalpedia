-- Prove2me | Definitions.Def_OnlineCRS_Combine_encSampler
-- name    : OnlineCRS_Combine_encSampler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:23:23.160981+00:00
-- url     : https://prove2.me/theorems/6ef95e53-248c-43c8-ba44-fc5a56de1c65
-- title:
--   Input encoding of the sampling algorithm
-- statement:
--   Consider a family of instances indexed by $i$, where instance $i$ has ground set $\{0,\dots,n_i-1\}$ and a description $\mathrm{code}_i$ (a bit string). The input $(i,x)$ of the sampling algorithm, with $x\in\mathbb Q^{n_i}$, is encoded as $\mathrm{code}_i$, the separator $3$, and the encoding of $x$.
--
--   **Formalization Note** Definition 1.7 speaks of "polynomial time"; it is read in Mathlib's Turing-machine model `Turing.TM2ComputableInPolyTime`, which measures time in the length of a fixed encoding of the input. This encoding is fixed once for the mission (never a parameter) and writes numbers in binary (Mathlib's `Computability.encodeNat`). Polynomial time is meaningful only as instances grow, so the instance description is part of the input; a single instance is the special case of a one-element index set.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 1.7 (auxiliary encoding), p. 4

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encVec

namespace OnlineCRS.Combine

/-- **Input encoding of the sampling algorithm.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 1.7, p. 4: "a polynomial time algorithm that, for a given input `x`, samples …".

For an instance family (instance `i` has ground set `Fin (n i)` and description
`code i : List Bool`), the sampler's input `(i, x)` is encoded as `code i`, the separator `3`, and
`encVec x`.

**Formalization Note.** Reading 6: Definition 1.7's "polynomial time" is read in Mathlib's
Turing-machine model `Turing.TM2ComputableInPolyTime`, which needs a fixed encoding of inputs as
lists of symbols. The encoding is fixed here (never a parameter); numbers are binary, via
Mathlib's `Computability.encodeNat`, so input length is the usual bit length. Instance families (Reading 6, generalization): polynomial time is measured as instances
grow, so the instance description is part of the input; a single instance is `ι = Unit`. -/
def encSampler {ι : Type} (n : ι → ℕ) (code : ι → List Bool) :
    (Σ i, Fin (n i) → ℚ) → List Sym :=
  fun p => (code p.1).map bit ++ [3] ++ encVec p.2

end OnlineCRS.Combine


