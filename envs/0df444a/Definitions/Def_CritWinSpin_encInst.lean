-- Prove2me | Definitions.Def_CritWinSpin_encInst
-- name    : CritWinSpin_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:38:27.790518+00:00
-- url     : https://prove2.me/theorems/a19412f4-12bf-43ce-8658-7128a0457d3f
-- title:
--   Binary encoding of an instance $(J,h)$, its bit length $B$, configuration codes and decoders
-- statement:
--   An **instance** on $N$ sites is a pair $(J,h)\in\mathbb Q^{N\times N}\times\mathbb Q^N$. Its code is $N$ in unary followed by the entries of $J$ in row-major order and of $h$, each in a self-delimiting rational code; the **bit length** $B$ is the length of that string. Configurations $x\in A^N$ and sample tuples $X_{1:k}$ have analogous codes. Each decoder returns the object whose code is the given string, and $\bot$ when there is none; this implements the rule of Definition 2.2 that any other output is replaced by $\bot$.
--
--   **Formalization Note** The paper fixes no encoding. Two reasonable encodings have polynomially related lengths, which the polynomial factors of the theorems absorb.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), §2.1, p.9; Definition 2.2, p.9

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_CritWinSpin_gibbs
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian
set_option autoImplicit false

namespace CritWinSpin

/-- A rational instance `(J, h)` on `N` sites. -/
abbrev Inst (N : ℕ) : Type := Matrix (Fin N) (Fin N) ℚ × (Fin N → ℚ)

/-- **Binary encoding of an instance** `(J, h) ∈ ℚ^{N×N} × ℚ^N` (§2.1, p.9): `encNat N`, then the
entries `J_ij` in row-major order, then `h_1, …, h_N`, each rational as `encRat`.

Source: Liu–Zhang–Ren, STOC 2027 submission (manuscript sha256 f77584da…), §2.1, p.9 ("whose
binary encoding length we refer to as the bit length `B` of `(J, h)`").

**Formalization Note.** The paper fixes no encoding; any two reasonable encodings have
polynomially related lengths, which the polynomial factor of (2) absorbs. `encRat` is
self-delimiting, so `encInst` is injective on each `Inst N`. -/
def encInst {N : ℕ} (M : Inst N) : Str :=
  encNat N ++ (List.ofFn fun i => (List.ofFn fun j => encRat (M.1 i j)).flatten).flatten ++
    (List.ofFn fun i => encRat (M.2 i)).flatten

/-- The bit length `B` of `(J, h)` (p.9). -/
def bitLen {N : ℕ} (M : Inst N) : ℕ := (encInst M).length

/-- Encoding of a configuration `x ∈ A^N`: the rationals `x_1, …, x_N` as `encRat`. -/
def encConfig {S : SpinLaw} {N : ℕ} (x : Config S (Fin N)) : Str :=
  (List.ofFn fun i => encRat ((x i : ℚ))).flatten

/-- Encoding of a sample tuple `X_{1:k}`: `encNat k`, then every configuration. -/
def encSamples {S : SpinLaw} {N k : ℕ} (xs : Fin k → Config S (Fin N)) : Str :=
  encNat k ++ (List.ofFn fun j => encConfig (xs j)).flatten

open Classical in
/-- Decoding of an instance on `N` sites: `some M` when the string is `encInst M`, else `none`. -/
noncomputable def decInst (N : ℕ) (s : Str) : Option (Inst N) :=
  if h : ∃ M : Inst N, encInst M = s then some (Classical.choose h) else none

open Classical in
/-- Decoding of an output configuration in `A^N`: `some x` when the string is `encConfig x`, and
`none` (the paper's `⊥`) otherwise (Definition 2.2, p.9: "any other output is replaced by `⊥`"). -/
noncomputable def decConfig (S : SpinLaw) (N : ℕ) (s : Str) : Option (Config S (Fin N)) :=
  if h : ∃ x : Config S (Fin N), encConfig x = s then some (Classical.choose h) else none

open Classical in
/-- Decoding of an output tuple in `(A^N)^k`: `some xs` when the string is `encSamples xs`, else
`none` (`⊥`). -/
noncomputable def decTuple (S : SpinLaw) (N k : ℕ) (s : Str) : Option (Fin k → Config S (Fin N)) :=
  if h : ∃ xs : Fin k → Config S (Fin N), encSamples xs = s then some (Classical.choose h) else none

end CritWinSpin


