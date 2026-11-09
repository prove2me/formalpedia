-- Prove2me | Definitions.Def_AbelianCayleyHDX_IsExplicitFamily
-- name    : AbelianCayleyHDX_IsExplicitFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:29:40.324222+00:00
-- url     : https://prove2.me/theorems/86939b56-12ef-4245-8d90-6d1ec5a0fbad
-- title:
--   Explicit family of translation-invariant unweighted two-dimensional Cayley complexes
-- statement:
--   Let $(n_j, S_j, T_j)_{j \ge 0}$ be a family of translation-invariant unweighted two-dimensional Cayley complexes over $\mathbb F_2^{n_j}$ (generators $S_j$, triangle set $T_j$). Following p.9, the family is **explicit** if one deterministic algorithm, given the family index $j$, outputs the ambient dimension $n_j$, the generators, one representative of each top-face translation orbit, and the exact rational weight of each face in that orbit, in time polynomial in $n_j$; field elements and rational weights are in binary.
--
--   Precisely: there are one multi-stack Turing machine $M$ and one polynomial $p$ such that for every $j$ there are a duplicate-free list of the elements of $S_j$ and a duplicate-free list of triangles of $T_j$, each listed by its three distinct vertices, containing exactly one triangle from each translation orbit of $T_j$, for which $M$ started on $j$ (in binary) halts within $p(n_j)$ steps with output: $n_j$; the generator list; and for each listed triangle its vertices followed by its weight $1/|T_j|$.
--
--   **Formalization Note** The machine model is the published `HMBinPacking.OutputsWithin` (Mathlib's `TM2OutputsInTime`, Boolean alphabets); numbers and lists use the published self-delimiting binary encodings `encNat`, `encList`; a vector of $\mathbb F_2^n$ is its $n$ coordinates (`encVec`) and a rational is `encRat`. Under the uniform distribution every face of $T_j$ has weight $1/|T_j|$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_ReplParity_Vec
import Definitions.Def_AbelianCayleyHDX_encRat
open ReplParity (Vec)

namespace AbelianCayleyHDX

open RSListDecodingCapacity.AllRates in
/-- **An explicit family of translation-invariant unweighted two-dimensional Cayley complexes**
(Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9): "a deterministic algorithm, given the family index, outputs the ambient
dimension `n`, the generators in `𝔽₂ⁿ`, one representative of each top-face translation orbit, and
the exact rational weight of each face in that orbit, in time polynomial in `n` for fixed
parameters. Finite-field elements and rational weights are encoded in binary."

The family is `j ↦ (n_j, S_j, T_j)` (generators `S_j`, triangle set `T_j`, uniform weight). The
predicate says: there are one multi-stack Turing machine `M` and one polynomial `p` such that for
every index `j` there are a duplicate-free list of the generators and a duplicate-free list of
triangles of `T_j` (each listed by its three distinct vertices), containing exactly one
representative of each translation orbit of `T_j`, for which `M`, started on `j` in binary, halts
within `p(n_j)` steps with output
`n_j`, the generators, and for each representative its vertices followed by its weight `1/|T_j|`.

**Formalization Note** The machine model is the published `HMBinPacking.OutputsWithin`
(Mathlib's `TM2OutputsInTime` with Boolean alphabets); numbers and lists use the published
self-delimiting binary encodings `encNat`, `encList`, a vector of `𝔽₂ⁿ` its `n` coordinates
(`encVec`), and a rational `encRat`. The family index `j` is given in binary. The weight of every
face of the uniform distribution on `T_j` is `1/|T_j|`. The time bound is polynomial in `n_j`, as on
p.9. -/
def IsExplicitFamily (n : ℕ → ℕ) (S : ∀ j, Finset (Vec (n j))) (T : ∀ j, Finset (Finset (Vec (n j)))) :
    Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ p : Polynomial ℕ, ∀ j : ℕ,
    ∃ gens : List (Vec (n j)), ∃ reps : List (List (Vec (n j))),
      gens.Nodup ∧ gens.toFinset = S j ∧ reps.Nodup ∧
      (∀ r ∈ reps, r.Nodup ∧ r.toFinset ∈ T j) ∧
      (∀ τ ∈ T j, ∃! r, r ∈ reps ∧ ∃ g : Vec (n j), τ = r.toFinset.image (· + g)) ∧
      HMBinPacking.OutputsWithin M (encNat j)
        (encNat (n j) ++ encList encVec gens ++
          encList (fun r => encList encVec r ++ encRat (1 / ((T j).card : ℚ))) reps)
        ((p.eval (n j)))

end AbelianCayleyHDX


