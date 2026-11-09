-- Prove2me | Definitions.Def_AbelianCayleyHDX_MinDistAtLeast3
-- name    : AbelianCayleyHDX_MinDistAtLeast3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:29:54.990516+00:00
-- url     : https://prove2.me/theorems/61eba606-9a01-4695-95cb-9e1ab418932a
-- title:
--   Binary linear code of minimum distance at least three
-- statement:
--   A binary linear code $W \subseteq \mathbb F_2^M$ has **minimum distance at least three** if every nonzero codeword has Hamming weight at least $3$ (for a linear code, Hamming distance and weight agree).
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9; Section 2.1, p.8

import Mathlib

namespace AbelianCayleyHDX

/-- **Minimum distance at least three** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9; Section 2.1: "code distances
refer to Hamming distance"): every nonzero vector of the binary linear code `W` has Hamming weight
at least `3`. -/
def MinDistAtLeast3 {κ : Type*} [Fintype κ] (W : Submodule (ZMod 2) (κ → ZMod 2)) : Prop :=
  ∀ v ∈ W, v ≠ 0 → 3 ≤ (Finset.univ.filter fun i => v i ≠ 0).card

end AbelianCayleyHDX


