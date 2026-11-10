-- Prove2me | Definitions.Def_PPSLattice_iidVec
-- name    : PPSLattice_iidVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:17.190207+00:00
-- url     : https://prove2.me/theorems/da694171-b630-4e03-b8dc-911d71f162c3
-- title:
--   Independent samples: the law $p^{\otimes k}$ on vectors
-- statement:
--   For a law $p$ and $k\in\mathbb N$, the law of $(x_0,\dots,x_{k-1})$ with $x_j\leftarrow p$ independent, e.g. $\mathbf e\leftarrow D^m_{\mathbb Z,\chi}$ or $\tilde{\mathbf e}\leftarrow[-\sqrt m\tilde\chi,\sqrt m\tilde\chi]^\lambda$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17; Construction 4.6, p.21

import Mathlib
set_option autoImplicit false

namespace PPSLattice

/-- The law of a vector of `k` **independent samples** of `p`: `iidVec p k` is the product law
`p^{⊗k}` on `Fin k → α`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Assumption 3.4, p.17 ("e ← D^m_{Z,χ}") and Construction 4.6, p.21
("e ← D^{⌈log N⌉·m}_{Z,χ}", "ẽ ← [−√m χ̃, √m χ̃]^λ"). -/
noncomputable def iidVec {α : Type} (p : PMF α) : (k : ℕ) → PMF (Fin k → α)
  | 0 => PMF.pure Fin.elim0
  | k + 1 => p.bind fun a => (iidVec p k).map fun v => Fin.cons a v

end PPSLattice


