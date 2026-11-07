-- Prove2me | Definitions.Def_QMAPlusGap_swapF
-- name    : QMAPlusGap_swapF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:06:15.411318+00:00
-- url     : https://prove2.me/theorems/8a104cd6-fd60-4afb-91bc-dd7c6cc98a2a
-- title:
--   Cross-copy swap $F_{ij}$
-- statement:
--   On two copies $\mathcal H^{\otimes m}\otimes\mathcal H^{\otimes m}$, $F_{ij}$ swaps register $i$ of the first copy with register $j$ of the second copy: on basis vectors it exchanges the $i$-th symbol of the first string with the $j$-th symbol of the second.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), App. A.1, p.31

import Mathlib

set_option autoImplicit false

namespace QMAPlusGap

/-- The swap **`F_{ij}`** on two copies of `H^{⊗m}`, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), App. A.1, p.31: "F_{ij} swaps register i of the first
copy with register j of the second copy". It maps the basis vector `|y₁⟩|y₂⟩` to `|y₁'⟩|y₂'⟩` with
`y₁' = y₁[i ↦ y₂ j]` and `y₂' = y₂[j ↦ y₁ i]`; as a matrix, the entry at `(x, y)` is `1` exactly when `x` is
that image of `y`. -/
def swapF {ι : Type} [DecidableEq ι] {m : ℕ} (i j : Fin m) :
    Matrix ((Fin m → ι) × (Fin m → ι)) ((Fin m → ι) × (Fin m → ι)) ℂ :=
  Matrix.of fun x y =>
    if x.1 = Function.update y.1 i (y.2 j) ∧ x.2 = Function.update y.2 j (y.1 i) then 1 else 0

end QMAPlusGap


