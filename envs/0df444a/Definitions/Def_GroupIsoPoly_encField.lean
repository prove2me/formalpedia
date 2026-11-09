-- Prove2me | Definitions.Def_GroupIsoPoly_encField
-- name    : GroupIsoPoly_encField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:46.930401+00:00
-- url     : https://prove2.me/theorems/936d938c-1445-45cc-885e-dbc011986797
-- title:
--   Binary code of a presented finite field and of its elements
-- statement:
--   A finite field is given by a **presentation** $\mathbb F_q=\mathbb F_p[x]/(f)$ with $p$ prime and $f$ monic irreducible of degree $e$, so $q=p^e$. Its **code** is the self-delimiting code of $p$, of $e$, and of the $e$ coefficients of $f$ below the leading one. A field element is written as its $e$ coordinates in the basis $1,x,\dots,x^{e-1}$, each a number below $p$; a matrix is written entry by entry, row by row.
--
--   An algorithm over an arbitrary finite field receives the field this way; every finite field has a presentation.
--
--   **Formalization Note** The presentation is the published `AvgCaseTI.FieldPres`; numbers use the published `encodeNat`. `elemNats`, `matNats`, `encElem` give the coordinates.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.2, p.2 (PDF p.6); Theorem 8.1, p.71 (PDF p.75)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_AvgCaseTI_FieldPres

set_option autoImplicit false

namespace GroupIsoPoly

open ExponomialAssortment.FPTAS (encodeNat)
open AvgCaseTI (FieldPres)

/-- The `deg f` power-basis coordinates of a field element, as natural numbers below `p`. -/
noncomputable def elemNats (P : FieldPres) (x : P.F) : List ℕ :=
  List.ofFn fun i : Fin P.f.natDegree => (P.coords x i).val

/-- The coordinates of an `r × c` matrix over the presented field, row by row. -/
noncomputable def matNats (P : FieldPres) {r c : ℕ} (A : Matrix (Fin r) (Fin c) P.F) : List ℕ :=
  (List.ofFn fun i : Fin r => (List.ofFn fun j : Fin c => elemNats P (A i j)).flatten).flatten

/-- The binary code of a field element: its coordinates, each by `encodeNat`. -/
noncomputable def encElem (P : FieldPres) (x : P.F) : List Bool :=
  ((elemNats P x).map encodeNat).flatten

/-- **The binary code of a presented finite field** `F_q = F_p[x]/(f)`.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.2, p.2 (PDF p.6): "Let A, B be two ℓ × m × n
3-way arrays over Fq"; Theorem 8.1, p.71 (PDF p.75): "InSize is the total input bit length". An
algorithm over an arbitrary `F_q` receives the field as part of its input.

The code is `encodeNat p`, `encodeNat (deg f)`, then the `deg f` coefficients of `f` below its leading
coefficient (the monic `f` is determined by them).

**Formalization Note.** The field presentation is the published `AvgCaseTI.FieldPres`; every finite
field has one. Numbers use the published `ExponomialAssortment.FPTAS.encodeNat`. -/
noncomputable def encField (P : FieldPres) : List Bool :=
  encodeNat P.p ++ encodeNat P.f.natDegree ++
    (List.ofFn fun i : Fin P.f.natDegree => encodeNat (P.f.coeff i).val).flatten

end GroupIsoPoly


