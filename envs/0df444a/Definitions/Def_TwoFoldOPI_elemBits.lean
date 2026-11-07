-- Prove2me | Definitions.Def_TwoFoldOPI_elemBits
-- name    : TwoFoldOPI_elemBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:40.818235+00:00
-- url     : https://prove2.me/theorems/001fbe43-f21e-4202-9292-8a1ad86e96a8
-- title:
--   Bit encoding of an explicitly represented finite field $\mathbb F_p[X]/(f)$
-- statement:
--   The field is given by a published presentation: a prime $p$ and a monic irreducible $f\in\mathbb F_p[X]$ of degree $e$, with
--   $$K=\mathbb F_p[X]/(f),\qquad q=|K|=p^e .$$
--   Every finite field is isomorphic to one of these. This definition adds what an algorithm needs to read and write field elements.
--
--   An element $a\in K$ is written by its $e$ coordinates in the power basis $1,X,\dots,X^{e-1}$; each coordinate $0\le v<p$ takes $\lceil\log_2 p\rceil$ bits, most significant bit first, coordinate $0$ first. A symbol therefore takes $b=e\lceil\log_2 p\rceil$ bits. Reading a block of $b$ bits back is total: each coordinate block is read as a natural number and reduced modulo $p$. The public description of the field is $p$, $e$ and the coefficients $f_0,\dots,f_e$ of $f$, each in self-delimiting binary.
--
--   This is the field model of every statement of the mission: the paper's codes are "given by explicit generator or parity-check matrices over an explicitly represented finite field".
--
--   **Formalization Note** The presentation is the published `AvgCaseTI.FieldPres` (carrier `AdjoinRoot f`). This module also provides the carrier's `Fintype` and `DecidableEq` instances and its power basis.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Computational conventions, p. 26; Notation, p. 20

import Mathlib
import Definitions.Def_AvgCaseTI_FieldPres
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

namespace TwoFoldOPI

/-! **Bit encoding of an explicitly represented finite field.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, "Computational
conventions", p.26: "Codes are given by explicit generator or parity-check matrices over an
explicitly represented finite field"; notation p.20: "Over F_q, write p = char(F_q)".

The field is a published presentation `AvgCaseTI.FieldPres` (`p` prime, `f ∈ F_p[X]` monic
irreducible, carrier `F_p[X]/(f)` = `AdjoinRoot f`, `q = p^{deg f}`); every finite field is
isomorphic to one. This module adds what an algorithm needs to read and write field elements:
finiteness and decidable equality of the carrier, the power basis, and the bit encoding.

**Formalization Note.** An element `a` is written by its `e = deg f` coordinates in the power basis
`1, X, …, X^{e−1}`, each coordinate `0 ≤ v < p` in `⌈log₂ p⌉` bits, most significant bit first,
coordinate `0` first (`elemBits`; the `fieldBits` convention of the published `QAlgorithms.OPI`
field layer). Reading bits back (`decodeElem`) is total: each block of `⌈log₂ p⌉` bits is read as a
natural number and reduced modulo `p`. `fieldEncode` writes `p`, `e` and the `e + 1` coefficients
of `f` in self-delimiting binary (`QAlgorithms.LocalHamiltonian.encBin`). The module holds this one
encoding layer (instances, basis, width, encoder, decoder, field description) as a unit. -/

noncomputable instance instFintypeFieldPres (F : AvgCaseTI.FieldPres) : Fintype F.F :=
  haveI : Module.Finite (ZMod F.p) F.F :=
    PowerBasis.finite (AdjoinRoot.powerBasis F.hirr.ne_zero)
  haveI : Finite F.F := Module.finite_of_finite (ZMod F.p)
  Fintype.ofFinite F.F

noncomputable instance instDecidableEqFieldPres (F : AvgCaseTI.FieldPres) : DecidableEq F.F :=
  Classical.decEq _

/-- The power basis `1, X, …, X^{e−1}` of `F_p[X]/(f)` over `F_p`. -/
noncomputable def fieldBasis (F : AvgCaseTI.FieldPres) : PowerBasis (ZMod F.p) F.F :=
  AdjoinRoot.powerBasis F.hirr.ne_zero

/-- The number `e · ⌈log₂ p⌉` of bits per field symbol (`e = deg f`). -/
def bitsPerSymbol (F : AvgCaseTI.FieldPres) : ℕ := F.f.natDegree * Nat.clog 2 F.p

/-- The bit encoding of `a`: bit `j·⌈log₂ p⌉ + k` is bit `k` (most significant first) of the
`j`-th power-basis coordinate of `a`. -/
noncomputable def elemBits (F : AvgCaseTI.FieldPres) (a : F.F) : Fin (bitsPerSymbol F) → Bool :=
  fun i =>
    let jk := finProdFinEquiv.symm i
    QAlgorithms.natToBits (Nat.clog 2 F.p) ((fieldBasis F).basis.repr a jk.1).val jk.2

/-- Total decoding of a block of `e · ⌈log₂ p⌉` bits: coordinate `j` is the number written by its
`⌈log₂ p⌉` bits (most significant first), reduced modulo `p`. -/
noncomputable def decodeElem (F : AvgCaseTI.FieldPres) (bits : Fin (bitsPerSymbol F) → Bool) :
    F.F :=
  (fieldBasis F).basis.equivFun.symm fun j =>
    ((QAlgorithms.bitsToNat fun k : Fin (Nat.clog 2 F.p) =>
      bits (finProdFinEquiv (j, k)) : ℕ) : ZMod F.p)

/-- The public description of the field: `p`, `e` and the coefficients `f_0, …, f_e` of `f`, each
in self-delimiting binary. -/
def fieldEncode (F : AvgCaseTI.FieldPres) : List Bool :=
  QAlgorithms.LocalHamiltonian.encBin F.p ++ QAlgorithms.LocalHamiltonian.encBin F.f.natDegree ++
    (List.ofFn fun j : Fin (F.f.natDegree + 1) =>
      QAlgorithms.LocalHamiltonian.encBin (F.f.coeff j).val).flatten

end TwoFoldOPI


