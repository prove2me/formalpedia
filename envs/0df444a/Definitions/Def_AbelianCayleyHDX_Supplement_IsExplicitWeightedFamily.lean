-- Prove2me | Definitions.Def_AbelianCayleyHDX_Supplement_IsExplicitWeightedFamily
-- name    : AbelianCayleyHDX_Supplement_IsExplicitWeightedFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:05:01.040041+00:00
-- url     : https://prove2.me/theorems/1696fa19-cc5a-421f-8cba-92a346c2dca9
-- title:
--   Explicit family of translation-invariant weighted Cayley complexes
-- statement:
--   A family $j\mapsto(n_j,S_j,X_j(d),\mu_j)$ of translation-invariant weighted Cayley complexes is **explicit** if a deterministic algorithm, given $j$, outputs the ambient dimension $n_j$, the generators in $\mathbb F_2^{n_j}$, one representative of each top-face translation orbit, and the exact rational weight of each face in that orbit, in time polynomial in $n_j$. Finite-field elements and rational weights are encoded in binary.
--
--   Precisely: there are one multi-stack Turing machine $M$ and one polynomial $p$ such that for every $j$ there are a duplicate-free list of the generators and a list containing exactly one representative of each translation orbit of top faces, for which $M$ on input $j$ (in binary) halts within $p(n_j)$ steps and outputs $n_j$, the generators, and for each representative its vertices followed by its weight $\mu_j$.
--
--   **Formalization Note** Same machine model and encodings as the base mission's `IsExplicitFamily` (published `HMBinPacking.OutputsWithin`, self-delimiting binary `encNat`, `encList`, `encVec`, `encRat`), with the uniform weight replaced by the weight of the representative.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9 (explicit families)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_ReplParity_Vec
import Definitions.Def_AbelianCayleyHDX_encRat
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement

open RSListDecodingCapacity.AllRates in
/-- **An explicit family of translation-invariant weighted Cayley complexes**
(Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9): "a deterministic algorithm, given the family index, outputs the ambient
dimension `n`, the generators in `𝔽₂ⁿ`, one representative of each top-face translation orbit, and
the exact rational weight of each face in that orbit, in time polynomial in `n` for fixed
parameters. Finite-field elements and rational weights are encoded in binary."

The family is `j ↦ (n_j, S_j, tops_j, μ_j)`. The predicate says: there are one multi-stack Turing
machine `M` and one polynomial `p` such that for every index `j` there are a duplicate-free list of
the generators and a duplicate-free list of top faces (each listed by its distinct vertices),
containing exactly one representative of each translation orbit of `tops_j`, for which `M`, started
on `j` in binary, halts within `p(n_j)` steps with output `n_j`, the generators, and for each
representative its vertices followed by its exact weight `μ_j(r)`.

**Formalization Note** Same machine model and encodings as the base mission's `IsExplicitFamily`
(the published `HMBinPacking.OutputsWithin`; `encNat`, `encList`, `encVec`, `encRat`; index `j` in
binary; time polynomial in `n_j`), with the uniform weight `1/|T_j|` replaced by the weight
`μ_j(r)` of the representative, which is the weight of every face of its orbit when the complex
is translation invariant. -/
def IsExplicitWeightedFamily (n : ℕ → ℕ) (S : ∀ j, Finset (Vec (n j)))
    (tops : ∀ j, Finset (Finset (Vec (n j)))) (μ : ∀ j, Finset (Vec (n j)) → ℚ) : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial ℕ, ∀ j : ℕ,
    ∃ gens : List (Vec (n j)), ∃ reps : List (List (Vec (n j))),
      gens.Nodup ∧ gens.toFinset = S j ∧ reps.Nodup ∧
      (∀ r ∈ reps, r.Nodup ∧ r.toFinset ∈ tops j) ∧
      (∀ τ ∈ tops j, ∃! r, r ∈ reps ∧ ∃ g : Vec (n j), τ = r.toFinset.image (· + g)) ∧
      HMBinPacking.OutputsWithin M (encNat j)
        (encNat (n j) ++ encList encVec gens ++
          encList (fun r => encList encVec r ++ AbelianCayleyHDX.encRat (μ j r.toFinset)) reps)
        (p.eval (n j))

end AbelianCayleyHDX.Supplement


