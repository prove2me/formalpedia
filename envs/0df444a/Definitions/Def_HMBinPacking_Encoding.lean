-- Prove2me | Definitions.Def_HMBinPacking_Encoding
-- name    : HMBinPacking_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:15.44154+00:00
-- url     : https://prove2.me/theorems/85e406ee-2954-4c1c-a55d-9d017f3ac98e
-- title:
--   Binary encodings: instance code $\mathrm{enc}(I)$, input length $L$, $\mathrm{enc}(q)$ of rationals and vectors
-- statement:
--   All numbers are written in **binary** with the published self-delimiting code `encodeNat` (the bit length of $m$ in unary, a separator, then the bits of $m$), which spends $2\lceil\log_2(m+1)\rceil+1$ symbols on $m$. Integers carry a sign bit, and a rational $q=p/r$ in lowest terms is written as the codes of $p$ and $r$.
--
--   1. The **instance code** is the concatenation of the codes of $B$, $d$, $s_1,\dots,s_d$, $a_1,\dots,a_d$, $b$, in this order, and the **binary input length** $L$ is its length. Every code has length at least one, so $L\ge 2d+3\ge5$.
--   2. For a rational number $q$, $\mathrm{enc}(q)$ is the length of its code; a rational vector is written as the concatenation of the codes of its entries, and its encoding length $\ell$ is the length of that word.
--   3. A residue $r\in\{0,\dots,d-1\}^d$ and natural or integer vectors are written entrywise in the same way.
--
--   These codes fix what "binary input length" and "encoding length" mean in every time bound of the mission. Sizes and multiplicities are written in binary, as the paper requires: no number is listed in unary.
--
--   **Formalization Note** The codes `encodeNat`, `encodeInt`, `encodeRat` are reused from the published module `ExponomialAssortment_FPTAS_Machine`. The dimension of a vector is not part of its code; it is known from the context.
-- source:
--   Koana, Kumabe, High-Multiplicity Bin Packing is FPT, arXiv:2609.16923v2, abstract (PDF p.1), §1 p.1 and footnote 1 p.1 (binary encoding, L); §3, p.5 (enc(q), ℓ)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_HMBinPacking_Instance
open ExponomialAssortment.FPTAS (encodeNat encodeInt encodeRat)

namespace HMBinPacking

/-- **Binary encoding of a vector of naturals.**
Koana, Kumabe, arXiv:2609.16923v2, abstract (PDF p.1) and footnote 1, p.1: sizes and multiplicities
are "encoded in binary".

The concatenation of the self-delimiting binary codes `encodeNat (v 0), …, encodeNat (v (n−1))`.

**Formalization Note.** `encodeNat` is the published `ExponomialAssortment.FPTAS.encodeNat`: the bit
length in unary, a separator, then the bits. It spends `2·size(m) + 1` symbols on `m`, so no number
is written in unary. The dimension `n` is not part of the code; it is known from the context. -/
def encodeNatVec {n : ℕ} (v : Fin n → ℕ) : List Bool :=
  (List.ofFn fun i => encodeNat (v i)).flatten

/-- **Binary encoding of an integer vector**: the concatenation of `encodeInt (v i)`.
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5 (the integer point returned by Lemma 5).

**Formalization Note.** `encodeInt` is the published `ExponomialAssortment.FPTAS.encodeInt` (a sign
bit, then `encodeNat` of the absolute value). -/
def encodeIntVec {n : ℕ} (v : Fin n → ℤ) : List Bool :=
  (List.ofFn fun i => encodeInt (v i)).flatten

/-- **Binary encoding of a rational vector**, the `enc` of a vector.
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5: "For a rational number or vector q, let enc(q) denote its
total binary encoding length, including numerators and denominators."

**Formalization Note.** `encodeRat q` (published) is `encodeInt q.num ++ encodeNat q.den`, with `q`
in lowest terms. The encoding length of a vector `v` is `(encVec v).length`; it is the `ℓ` of the
paper when `v` is a query. -/
def encVec {n : ℕ} (v : Fin n → ℚ) : List Bool :=
  (List.ofFn fun i => encodeRat (v i)).flatten

/-- **The encoding length `enc(q)` of a rational number.**
Koana, Kumabe, arXiv:2609.16923v2, §3, p.5: "let enc(q) denote its total binary encoding length,
including numerators and denominators".

**Formalization Note.** `enc q` is the length of the published code `encodeRat q`. -/
def enc (q : ℚ) : ℕ :=
  (encodeRat q).length

/-- **The binary encoding of a Bin Packing instance.**
Koana, Kumabe, arXiv:2609.16923v2, abstract (PDF p.1), §1 p.1 and footnote 1, p.1: "both the item
sizes and the number of items of each size are encoded in binary"; "the binary input length".

The concatenation of the binary codes of `B`, `d`, `s₁, …, s_d`, `a₁, …, a_d`, `b`, in this order.

**Formalization Note.** Every number is written with `encodeNat`, which is self-delimiting and uses
`2·size(m) + 1` bits, so the code is injective and its length is the binary input length up to a
constant factor. -/
def encodeInstance (I : Instance) : List Bool :=
  encodeNat I.B ++ encodeNat I.d ++ encodeNatVec I.s ++ encodeNatVec I.a ++ encodeNat I.b

/-- **The binary input length `L`.**
Koana, Kumabe, arXiv:2609.16923v2, §1, p.1: "L denotes the binary encoding length of the input".

**Formalization Note.** `L I` is the length of `encodeInstance I`. Every `encodeNat` has length at
least 1, so `L I ≥ 2d + 3 ≥ 5`. -/
def inputLength (I : Instance) : ℕ :=
  (encodeInstance I).length

/-- **Binary encoding of a residue index `r ∈ {0, …, d − 1}^d`.**
Koana, Kumabe, arXiv:2609.16923v2, §2, p.3: "All residue indices r range over {0, . . . , d − 1}^d."

**Formalization Note.** A residue is a map `Fin d → Fin d`; it is written as the binary codes of its
`d` entries. -/
def encodeResidue {d : ℕ} (r : Fin d → Fin d) : List Bool :=
  encodeNatVec fun i => (r i : ℕ)

end HMBinPacking


