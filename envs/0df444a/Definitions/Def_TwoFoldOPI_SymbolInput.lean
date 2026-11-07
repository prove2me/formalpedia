-- Prove2me | Definitions.Def_TwoFoldOPI_SymbolInput
-- name    : TwoFoldOPI_SymbolInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:35.750892+00:00
-- url     : https://prove2.me/theorems/33775d29-f904-42fe-9ed0-461428135231
-- title:
--   Input of the single-symbol measurement's implementation
-- statement:
--   An input of the implementation clause of Lemma 7.2 is a field presentation $F$ ($q=|K|$), a forbidden value $\beta\in K$ and a precision $t$ (run with $t=\lceil\log_2(1/\delta)\rceil$). The algorithm reads the field's description, then the $b$ bits of $\beta$, then $t$ in self-delimiting binary; the encoding is injective. The size parameter is
--   $$\mathrm{scale}=q+t,$$
--   matching the paper's $\mathrm{poly}(q,\log(1/\delta))$.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.1, Lemma 7.2, p. 38

import Mathlib
import Definitions.Def_TwoFoldOPI_elemBits

namespace TwoFoldOPI

/-- **The input of the single-symbol measurement's implementation.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.1, Lemma 7.2, p.38: "Since it acts on one qudit of dimension q, it can be implemented to
operator-norm error δ in time poly(q, log(1/δ))."

An input is a field presentation `F`, the forbidden value `β ∈ K`, and a precision `t` (run with
`t = ⌈log₂(1/δ)⌉`).

* `encode x`: `fieldEncode`, then `elemBits β`, then `t` in self-delimiting binary.
* `scale x = q + t`.

**Formalization Note.** The encoding is injective; `q` itself and `t ≈ log₂(1/δ)` enter the size
parameter, as in `poly(q, log(1/δ))`. -/
structure SymbolInput where
  /-- The field. -/
  F : AvgCaseTI.FieldPres
  /-- The forbidden value. -/
  β : F.F
  /-- The precision parameter, `⌈log₂(1/δ)⌉`. -/
  t : ℕ

namespace SymbolInput

/-- The public bit encoding (see `SymbolInput`). -/
noncomputable def encode (x : SymbolInput) : List Bool :=
  fieldEncode x.F ++ List.ofFn (elemBits x.F x.β) ++ QAlgorithms.LocalHamiltonian.encBin x.t

/-- The size parameter `q + t`. -/
def scale (x : SymbolInput) : ℕ := x.F.q + x.t

end SymbolInput

end TwoFoldOPI


