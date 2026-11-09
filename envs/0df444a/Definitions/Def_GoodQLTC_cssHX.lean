-- Prove2me | Definitions.Def_GoodQLTC_cssHX
-- name    : GoodQLTC_cssHX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:50:38.232229+00:00
-- url     : https://prove2.me/theorems/ab87721b-84e8-4b4d-8470-9d025dc1de4d
-- title:
--   The CSS check matrices $H_X=R_\beta(\delta^k)$, $H_Z=R_\beta(\delta^{k-1})^{\top}$ (Equation (4.5))
-- statement:
--   Choose stalk bases and an ordered $\mathbb F_2$-basis $\beta=\{\beta_a\}_{a\in[s]}$ of $F=\mathbb F_{2^s}$. For an $F$-linear map $B$ let $R_\beta(B)$ be its binary matrix after writing each field coordinate in $\beta$. For $1\le k<t$,
--   $$
--   H_X=R_\beta(\delta^k),\qquad H_Z=R_\beta(\delta^{k-1})^{\top}. \tag{4.5}
--   $$
--   The check list includes every row, including dependent and zero rows.
--
--   **Formalization Note** An ordered $\mathbb F_2$-basis is the coordinate isomorphism $F\cong\mathbb F_2^s$ (`F ≃+ (Fin s → ZMod 2)`); qubits are triples (face of dimension $k$, stalk coordinate, $a\in[s]$).
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.4, Equation (4.5), p.18 (PDF p.21)

import Mathlib
import Definitions.Def_GoodQLTC_cobdMat
open Matrix

namespace GoodQLTC

/-- The binary matrix `R_β(B)` of an `F`-matrix `B`, obtained by writing each field coordinate in
an ordered `F_2`-basis `β = {β_a}_{a∈[s]}` of `F`, Gay–Jeronimo, arXiv:2609.20780 (held version),
§4.4, p.18.

**Formalization Note.** An ordered `F_2`-basis of `F` is the coordinate isomorphism
`β : F ≃+ (Fin s → ZMod 2)` (every additive isomorphism of `F_2`-spaces is `F_2`-linear). The
`((i, p), (j, q))` entry is the `p`-th coordinate of `B_{ij} β_q`. -/
def binMatrix {F : Type} [Field F] {s : ℕ} (β : F ≃+ (Fin s → ZMod 2)) {m n : Type}
    (B : Matrix m n F) : Matrix (m × Fin s) (n × Fin s) (ZMod 2) :=
  Matrix.of fun ip jq => β (B ip.1 jq.1 * β.symm (Pi.single jq.2 1)) ip.2

/-- The X check matrix `H_X := R_β(δ^k)` of Equation (4.5), Gay–Jeronimo, arXiv:2609.20780 (held
version), p.18. Its columns are the qubits `(f, a, p)` (`f ∈ X(k)`, `a` a stalk coordinate,
`p ∈ [s]`). -/
noncomputable def cssHX {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) {F : Type} [Field F] (Fs : Cosheaf X F) {s : ℕ}
    (β : F ≃+ (Fin s → ZMod 2)) (k : ℕ) :=
  binMatrix β (cobdMat φ Fs k (k + 1))

/-- The Z check matrix `H_Z := R_β(δ^{k−1})^⊺` of Equation (4.5), Gay–Jeronimo,
arXiv:2609.20780 (held version), p.18. **Formalization Note.** Used for `1 ≤ k < t`; the check
list consists of all rows, including dependent and zero rows. -/
noncomputable def cssHZ {X : Type} [PartialOrder X] [Fintype X] {t : ℕ}
    (φ : X → Fin t → Option Bool) {F : Type} [Field F] (Fs : Cosheaf X F) {s : ℕ}
    (β : F ≃+ (Fin s → ZMod 2)) (k : ℕ) :=
  (binMatrix β (cobdMat φ Fs (k - 1) k))ᵀ

end GoodQLTC


