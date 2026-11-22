-- Prove2me | Definitions.Def_PreservePast_Supplement_singList
-- name    : PreservePast_Supplement_singList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:30:10.325329+00:00
-- url     : https://prove2.me/theorems/585b3687-0bb3-465f-a1d7-01287bc27900
-- title:
--   The singleton list $X_S$ of a labelled sample
-- statement:
--   For a labelled sample $D=((A_i,X_i))_{i=1}^n$ with labels in $[n]$, the **singleton list** $X_S$ consists of the labelled observations whose label occurs exactly once in the sample, in training order.
--
--   **Formalization Note** The list has random length $K\le n$. It is stored in a fixed carrier with $n$ positions: position $j<K$ holds the $j$-th singleton observation, and every later position holds a padding value whose label is the extra value $n$ (not a class label). This encodes the list bijectively; the positions of the singletons inside the sample are not recorded.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), §K.1, p.56 (PDF p.58); §K.3, p.58 (PDF p.60)

import Mathlib

namespace PreservePast.Supplement

/-- **The singleton list `X_S`** of a labelled sample `D = ((A_i, X_i))_{i<n}` with labels in
`[n]`: the labelled observations whose label occurs exactly once in the sample, in training
order. P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held
version, PDF sha256 48013ceb…d00fa), §K.1, p.56 (PDF p.58): "let X_S = (L, F) contain the
singleton labels in training order and their features"; §K.3, p.58 (PDF p.60): "Let X_S list the
singleton labeled observations in training order."

**Formalization Note.** The list has random length `K ≤ n`. It is stored in the fixed carrier
`Fin n → Fin (n + 1) × F`: position `j < K` holds the `j`-th singleton observation, with its label
embedded by `Fin.castSucc`, and every position `j ≥ K` holds the padding value
`(Fin.last n, default)`, whose label `n` is not a class label. This is a bijective encoding of
the list (the positions of the singletons inside the sample are not recorded). -/
def singList {n : ℕ} {F : Type} [Inhabited F] (D : Fin n → Fin n × F) : Fin n → Fin (n + 1) × F :=
  fun j =>
    match ((List.ofFn D).filter fun p =>
        decide ((Finset.univ.filter fun i => (D i).1 = p.1).card = 1))[j.1]? with
    | some p => (p.1.castSucc, p.2)
    | none => (Fin.last n, default)

end PreservePast.Supplement


