-- Prove2me | Definitions.Def_PPSLattice_PPS_Efficient
-- name    : PPSLattice_PPS_Efficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:34:30.645534+00:00
-- url     : https://prove2.me/theorems/da6e6ec4-447b-4471-95bc-615aff9434e7
-- title:
--   The algorithms of a PPS scheme run in polynomial time
-- statement:
--   A PPS scheme is **efficient** if $\mathrm{GSetup},\mathrm{MSKGen},\mathrm{pkEnc},\mathrm{KGen},\mathrm{skEnc}$ are probabilistic polynomial-time algorithms and Decode is a deterministic polynomial-time algorithm, on inputs written as $(1^\lambda, N\text{ in binary},\mathrm{crs},\dots)$, with indices in binary and a set $S$ by its description.
--
--   Running time is therefore polynomial in $\lambda$, $\log N$, the lengths of the strings received and $|S|\log N$, matching "none of our algorithms have running times growing with $N$ (beyond the set description $|S|$) and are all efficient".
--
--   **Formalization Note** Each law must equal the image of fair coins under one polynomial-time machine, on every input (`PPTSampler`). Efficiency is kept separate from the four properties of Definition 4.1.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.1, Syntax, p.17; §4.4, p.24

import Mathlib
import Definitions.Def_PPSLattice_PPS
import Definitions.Def_PPSLattice_PPTSampler
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_PPSLattice_encBin
import Definitions.Def_PPSLattice_encSet
import Definitions.Def_RestrictedDec_encOpt
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- A PPS scheme consists of **polynomial-time algorithms**: GSetup, MSKGen, pkEnc, KGen and skEnc
are probabilistic polynomial-time samplers (`PPTSampler`) and Decode is a deterministic
polynomial-time map (its output `µ′ ∈ M_λ ∪ {⊥}` written by `RestrictedDec.encOpt`: `⊥ ↦ 1`, `µ ↦ 0µ`), on inputs written as `tup [1^λ, N in binary, crs, …]`, with indices in binary
and a set `S` by its description `encSet S` (its elements in binary).
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.1, Syntax, p.17 ("consists of the following polynomial time algorithms", "number of indices N
(in binary)"); p.24 ("none of our algorithms have running times growing with N (beyond the set
description |S|) and are all efficient").

**Formalization Note.** Running time is polynomial in the length of the input code, so in `λ`,
`log N`, the lengths of the strings received and `|S| · log N`. The condition covers every input,
and each law must equal the image of fair coins exactly (see `PPTSampler`). It is kept separate from
the four properties of Definition 4.1. -/
def PPS.Efficient (E : PPS) : Prop :=
  PPTSampler (fun a : ℕ × ℕ => BeyondDS.tup [encNat a.1, encBin a.2])
      (fun a => E.gsetup a.1 a.2) ∧
    PPTSampler (fun a : ℕ × ℕ × Str => BeyondDS.tup [encNat a.1, encBin a.2.1, a.2.2])
      (fun a => E.mskgen a.1 a.2.1 a.2.2) ∧
    PPTSampler (fun a : ℕ × ℕ × Str × ℕ =>
        BeyondDS.tup [encNat a.1, encBin a.2.1, a.2.2.1, encBin a.2.2.2])
      (fun a => E.pkEnc a.1 a.2.1 a.2.2.1 a.2.2.2) ∧
    PPTSampler (fun a : ℕ × ℕ × Str × Str × Finset ℕ =>
        BeyondDS.tup [encNat a.1, encBin a.2.1, a.2.2.1, a.2.2.2.1, encSet a.2.2.2.2])
      (fun a => E.kgen a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) ∧
    PPTSampler (fun a : ℕ × ℕ × Str × Str × ℕ × Str =>
        BeyondDS.tup [encNat a.1, encBin a.2.1, a.2.2.1, a.2.2.2.1, encBin a.2.2.2.2.1,
          a.2.2.2.2.2])
      (fun a => E.skEnc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2) ∧
    PolyTimeOn (fun a : ℕ × ℕ × Str × Finset ℕ × Str × ℕ × Str =>
        BeyondDS.tup [encNat a.1, encBin a.2.1, a.2.2.1, encSet a.2.2.2.1, a.2.2.2.2.1,
          encBin a.2.2.2.2.2.1, a.2.2.2.2.2.2])
      (fun a => RestrictedDec.encOpt
        (E.decode a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2))

end PPSLattice


