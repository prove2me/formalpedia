-- Prove2me | Definitions.Def_UniformSubpower_Supplied_Encoding
-- name    : UniformSubpower_Supplied_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:20:38.064412+00:00
-- url     : https://prove2.me/theorems/50729aad-7f1b-436b-96ff-bbb30e363cc3
-- title:
--   Length-faithful bitstring encodings of instances, queries and relative-transport inputs
-- statement:
--   Every natural number $k$ is coded by its binary digits (least significant first; no digits for $0$) inside one **self-delimiting block**: each payload bit $b$ is written as the two bits $1, b$ and the block ends with a $0$, so $\ell$ payload bits take $2\ell + 1$ bits (the block code of the published `PvsNP_bitstring_encoding`).
--
--   The argument tuples of an $r$-ary operation on $\{0, \dots, s-1\}$ are listed in **lexicographic order** (first argument most significant); a full table is the list of its $s^r$ values in that order, each coded as above. The **encoding of an instance** is the concatenation of the codes of
--   $$n,\ k,\ r_0, \dots, r_{k-1},\ d,\ \big(s_i,\ \text{the full tables of } f_0, \dots, f_{k-1} \text{ on } A_i\big)_{i < n},\ |G|,\ \big(g_0, \dots, g_{n-1}\big)_{g \in G}.$$
--   Its length is the input length $N$ of the paper up to the constant factors of the block code: every table is listed in full, numbers are in binary, and nothing is padded. The **encoding of a query** is the concatenation of the codes of $i$ and $a$ for each prescription $(i, a)$, in order; its length is the query length $R$.
--
--   For Lemma 6.1, a binary relation on $\{0, \dots, s-1\}$ is encoded by its $s^2$ truth values in lexicographic order, and the **transport input** $(\sigma, S, \mu, \rho, x, y, z)$ is the concatenation of the signature, the full-table encoding of $S$, the tables of $\mu$ and $\rho$, and the codes of $x, y, z$.
--
--   **Formalization Note.** These encodings are injective on well-formed data and are the inputs on which the polynomial-time claims are made through `PvsNP.IsPolyTime` of the published `PvsNP_complexity_classes`.
-- source:
--   Gkantzounis, Uniform Subpower Membership for Finite Mal'tsev Algebras, STOC 2027 submission (manuscript sha256 149e66b1…), p. 3, §1.1; p. 59, Appendix A

import Mathlib
import Definitions.Def_PvsNP_bitstring_encoding
import Definitions.Def_UniformSubpower_Supplied_Algebra

namespace UniformSubpower.Supplied

/-!
Length-faithful bitstring encodings of instances and queries (Gkantzounis, §1.1, p. 3; the
paper's own encoding, Appendix A, p. 59): every natural number is written in binary inside a
self-delimiting block (`b` bits become `2b + 1` bits), and every table is listed in full.
-/

/-- The code of a natural number: its binary digits (least significant first, `Nat.bits`; the
empty list for `0`) inside one self-delimiting block. -/
def natCode (k : ℕ) : List Bool := PvsNP.BitstringEncoding.delimit (Nat.bits k)

/-- All argument tuples `Fin r → Fin s`, in lexicographic order (the first argument is the
most significant). The list has exactly `s ^ r` entries. -/
def allTuples : (r s : ℕ) → List (Fin r → Fin s)
  | 0, _ => [Fin.elim0]
  | r + 1, s => (List.finRange s).flatMap
      (fun a => (allTuples r s).map (fun t => (Fin.cons a t : Fin (r + 1) → Fin s)))

/-- A full value table of an `r`-ary operation on `Fin s`: its `s ^ r` values in the
lexicographic order of the argument tuples. -/
def encodeTable (r s : ℕ) (f : (Fin r → Fin s) → Fin s) : List Bool :=
  ((allTuples r s).map (fun t => natCode (f t))).flatten

/-- A signature: the number of symbols, then each arity. -/
def encodeSignature (σ : Signature) : List Bool :=
  natCode σ.length ++ (σ.map natCode).flatten

/-- A full-table algebra: its carrier size, then the full table of every symbol in order. -/
def encodeTableAlg (σ : Signature) (T : TableAlg σ) : List Bool :=
  natCode T.size ++
    ((List.finRange σ.length).map (fun j => encodeTable (σ.ar j) T.size (T.table j))).flatten

/-- A tuple of a product: its entries, coordinate by coordinate. -/
def encodeTuple (n : ℕ) (sz : Fin n → ℕ) (g : (i : Fin n) → Fin (sz i)) : List Bool :=
  ((List.finRange n).map (fun i => natCode (g i : ℕ))).flatten

/-- The encoding of an instance: `n`, the signature, the index of the designated symbol, every
coordinate algebra by its full tables, the number of generators, and every generator entry by
entry. Its length is the input length `N` (up to the constant factors of the block code). -/
def encodeInstance (I : Instance) : List Bool :=
  natCode I.n ++ encodeSignature I.sig ++ natCode (I.mal : ℕ) ++
    ((List.finRange I.n).map (fun i => encodeTableAlg I.sig (I.coord i))).flatten ++
    natCode I.gens.length ++
    (I.gens.map (encodeTuple I.n (fun i => (I.coord i).size))).flatten

/-- The encoding of a query: each prescription `(i, a)` as the two blocks of `i` and `a`. Its
length is the query length `R`. -/
def encodeQuery (Q : Query) : List Bool :=
  (Q.map (fun p => natCode p.1 ++ natCode p.2)).flatten

/-- The full table of a binary relation on `Fin s`: its `s ^ 2` truth values in lexicographic
order, one bit each. -/
def encodeRel (s : ℕ) (r : Fin s → Fin s → Bool) : List Bool :=
  (allTuples 2 s).map (fun t => r (t 0) (t 1))

/-- The input of the relative transport of Lemma 6.1: the signature, the full tables of the
algebra `S`, the full tables of the congruences `μ` and `ρ`, and a triple `(x, y, z)`. -/
def encodeTransportInput (σ : Signature) (T : TableAlg σ) (μ ρ : Fin T.size → Fin T.size → Bool)
    (x y z : Fin T.size) : List Bool :=
  encodeSignature σ ++ encodeTableAlg σ T ++ encodeRel T.size μ ++ encodeRel T.size ρ ++
    natCode (x : ℕ) ++ natCode (y : ℕ) ++ natCode (z : ℕ)

end UniformSubpower.Supplied


