-- Prove2me | Definitions.Def_TwoFoldOPI_Input
-- name    : TwoFoldOPI_Input
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:31.511831+00:00
-- url     : https://prove2.me/theorems/bb38da16-94cb-40d8-b924-41eb6d85ac1e
-- title:
--   An instance of $\mathrm{CIP}_{C,A}$ for Theorem 7.4, with its encoding and size
-- statement:
--   An instance of the problem of Theorem 7.4 consists of:
--   1. a field presentation $F$ ($K=\mathbb F_p[X]/(f)$, $q=|K|$);
--   2. a length $m$, a number of rows $r$, a tag $\mathrm{gen}$ and a matrix $H\in K^{r\times m}$, defining the code $C$ (row space of $H$ if $\mathrm{gen}$, else $\ker H$);
--   3. forbidden values $\beta\in K^m$, defining $A=\prod_i(K\setminus\{\beta_i\})$;
--   4. a precision $t$ (the algorithm is run with $t=\lceil\log_2(1/\epsilon)\rceil$).
--
--   The algorithm reads the bit encoding: the field's description, then $m$ and $r$ in self-delimiting binary, the bit $\mathrm{gen}$, the entries of $H$ row by row and the entries of $\beta$ ($b$ bits each), and $t$ in self-delimiting binary. The encoding is injective. The size parameter of polynomial bounds is
--   $$\mathrm{scale}=m+r+q+t ,$$
--   matching the paper's $\mathrm{poly}(m,q,\log(1/\epsilon))$ (for basis matrices $r\le m$).
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.3, Theorem 7.4, p. 40; §5.2, p. 26

import Mathlib
import Definitions.Def_TwoFoldOPI_elemBits

namespace TwoFoldOPI

/-- **An instance of the code intersection problem `CIP_{C,A}` of Theorem 7.4.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7, Theorem 7.4, p.40: "Let C ⊆ F_q^m be given by a generator or parity-check matrix, let
β_1, …, β_m ∈ F_q be arbitrary … For every ϵ ∈ (0, 1/4) there is a quantum algorithm … running in
poly(m, q, log(1/ϵ)) time"; §5.2, p.26: "Codes are given by explicit generator or parity-check
matrices over an explicitly represented finite field."

An instance is a field presentation `F`, a length `m`, a matrix `H ∈ K^{r×m}` with a tag `gen`
(generator matrix if `gen`, parity-check matrix otherwise), the forbidden values `β ∈ K^m`, and a
precision `t` (the algorithm is run with `t = ⌈log₂(1/ϵ)⌉`).

* `encode x`: the public bit string the algorithm reads: the field (`fieldEncode`),
  then `m` and `r` in self-delimiting binary, the bit `gen`, the entries of `H` row by row and
  the entries of `β`, each by `elemBits`, and `t` in self-delimiting binary.
* `scale x = m + r + q + t`, the size parameter of the polynomial bounds.

**Formalization Note.** The encoding is injective, so an algorithm reading `encode x` sees exactly
the instance. `q` itself (not `log q`) enters `scale`, as in the paper's `poly(m, q, log(1/ϵ))`;
`t` enters linearly, i.e. `log(1/ϵ)`. -/
structure Input where
  /-- The field. -/
  F : AvgCaseTI.FieldPres
  /-- The code length. -/
  m : ℕ
  /-- The number of rows of the matrix. -/
  r : ℕ
  /-- Generator matrix (`true`) or parity-check matrix (`false`). -/
  gen : Bool
  /-- The matrix. -/
  H : Matrix (Fin r) (Fin m) F.F
  /-- The forbidden value of each coordinate. -/
  β : Fin m → F.F
  /-- The precision parameter, `⌈log₂(1/ϵ)⌉`. -/
  t : ℕ

namespace Input

/-- The public bit encoding of an instance (see `Input`). -/
noncomputable def encode (x : Input) : List Bool :=
  fieldEncode x.F ++ QAlgorithms.LocalHamiltonian.encBin x.m ++
    QAlgorithms.LocalHamiltonian.encBin x.r ++ [x.gen] ++
    (List.ofFn fun i : Fin x.r => (List.ofFn fun j : Fin x.m =>
      List.ofFn (elemBits x.F (x.H i j))).flatten).flatten ++
    (List.ofFn fun i : Fin x.m => List.ofFn (elemBits x.F (x.β i))).flatten ++
    QAlgorithms.LocalHamiltonian.encBin x.t

/-- The size parameter `m + r + q + t`. -/
def scale (x : Input) : ℕ := x.m + x.r + x.F.q + x.t

end Input

end TwoFoldOPI


