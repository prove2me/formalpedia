-- Prove2me | Definitions.Def_MantriCVQ_CodeDeg
-- name    : MantriCVQ_CodeDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:35.487928+00:00
-- url     : https://prove2.me/theorems/b77a4905-5cf3-43dc-8bef-b0778f55b438
-- title:
--   The degree condition of a code family
-- statement:
--   A family of maps $C_m:\mathbb F_2^m\times\mathbb F_2^m\to\mathbb F_2$ of **degree $d\ge1$**: for every positive multiple $m$ of eight and every $x\in\mathbb F_2^m$, the coordinate $s\mapsto C_m(s,x)$ is a multilinear polynomial over $\mathbb F_2$ of degree at most $d$. Section 6 and Theorem 1.7 use a code family only through this property (p. 6).
--
--   **Formalization Note** $C$ is total in $m$; its values at other $m$ are never used.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Definition 3.1 (ii), p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace MantriCVQ

/-- The degree part of a code family of degree `d` (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), Definition 3.1 (ii), p. 15 (PDF p. 17)): `d ≥ 1`, and for every positive multiple
`m` of eight and every `x ∈ F₂^m` the coordinate `s ↦ C_m(s, x)` is a multilinear polynomial over `F₂`
of degree at most `d`. §6 and Theorem 1.7 use a code family only through this property.

**Formalization Note** `C` is total in `m`; its values at other `m` are never used. -/
structure CodeDeg (d : ℕ) where
  /-- the maps `C_m` -/
  code : (m : ℕ) → Bits m → Bits m → Bool
  one_le_d : 1 ≤ d
  multilinear : ∀ m : ℕ, 0 < m → 8 ∣ m → ∀ x : Bits m,
    ∃ P : MvPolynomial (Fin m) (ZMod 2),
      P.totalDegree ≤ d ∧ (∀ e ∈ P.support, ∀ i, e i ≤ 1) ∧
        ∀ s : Bits m, MvPolynomial.eval (fun i => if s i then (1 : ZMod 2) else 0) P =
          if code m s x then 1 else 0

end MantriCVQ


