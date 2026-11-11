-- Prove2me | Definitions.Def_PermInvCC_hg
-- name    : PermInvCC_hg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:25:36.412256+00:00
-- url     : https://prove2.me/theorems/8dbfcb2d-9cd1-486d-8bfd-9b60db251831
-- title:
--   Separation parameter $h_g$ of a partial function
-- statement:
--   For a permutation-invariant partial function $g$ whose promised inputs have fixed margins, $h_g$ is the minimum of $h(T,U)$ over promised types $T,U$ with opposite labels; if no such pair exists, $h_g:=1$.
--
--   Theorem 3.1 bounds the classical cost by $h_g^{-2}$ and Theorem 4.1 bounds the quantum cost below by $h_g^{-1}$.
--
--   **Formalization Note** The minimum is taken over pairs of promised inputs with values $+1$ and $-1$; since $h$ is symmetric this is the minimum over oppositely labelled promised types. The formula is evaluated for every $g$; the theorems add the hypotheses.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.4, p.10

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_hE

namespace PermInvCC

open Classical in
/-- The **separation parameter `h_g`** of a partial function (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, Definition 2.4, p.10): the minimum of `h(T, U)`
over promised types `T, U` with opposite labels; `h_g := 1` if no such pair exists.

**Formalization Note.** The minimum is taken over all promised input pairs `(x, y)` with value
`+1` and `(x', y')` with value `−1`, of `h(jointType x y, jointType x' y')`; since `h` is symmetric
this is the minimum over oppositely labelled promised types. The paper uses `h_g` for
permutation-invariant `g` whose promised inputs have fixed margins; the formula is evaluated for
every `g`. -/
noncomputable def hg {n q : ℕ} (g : PartialFn n q) : ℝ :=
  let S := (Finset.univ : Finset ((Fin n → Fin q) × (Fin n → Fin q) × (Fin n → Fin q) ×
      (Fin n → Fin q))).filter fun p => g p.1 p.2.1 = some true ∧ g p.2.2.1 p.2.2.2 = some false
  if h : S.Nonempty then
    S.inf' h fun p => hTU (jointType p.1 p.2.1) (jointType p.2.2.1 p.2.2.2)
  else 1

end PermInvCC


