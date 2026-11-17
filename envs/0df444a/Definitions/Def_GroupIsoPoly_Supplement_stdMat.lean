-- Prove2me | Definitions.Def_GroupIsoPoly_Supplement_stdMat
-- name    : GroupIsoPoly_Supplement_stdMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:26:37.195501+00:00
-- url     : https://prove2.me/theorems/4a40ba53-2c64-41a0-8aac-e0926ff2d0d1
-- title:
--   Natural, dual and Frobenius-twisted modules
-- statement:
--   For $g\in\mathrm{GL}(n,K)$, $K$ of characteristic $p$, and a **module kind** $\kappa$ (dual or not, and a twist exponent $r\ge0$), the matrix of $g$ on the module of kind $\kappa$ is
--
--   $$\big(g \text{ or } (g^{-1})^{\mathsf T}\big)^{[p^r]},$$
--
--   where $X^{[p^r]}$ raises every entry of $X$ to the power $p^r$. With $r=0$ and no dual this is the **natural module** $K^n$; $(g^{-1})^{\mathsf T}$ is the **dual** (contragredient) module in the dual basis; the entrywise power is a **Frobenius twist**.
--
--   These are the modules from which the tensor and Hom modules of Theorems 6.3 and C.9 are built.
--
--   **Formalization Note** On a finite field $a\mapsto a^{p^r}$ is a field automorphism, so each kind gives a representation of $\mathrm{GL}(n,K)$.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Definitions 5–7, p.17 (PDF p.21); Definition 16, p.48 (PDF p.52)

import Mathlib

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

/-- The kind of a standard module of a classical factor: dual or not, and a Frobenius twist
exponent `r` (`r = 0`: no twist). -/
structure ModKind where
  dual : Bool
  twist : ℕ

/-- **The matrix of `g ∈ GL(n, K)` on a natural, dual or Frobenius-twisted module.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Definitions 5–7, p.17 (PDF p.21), and Definition 16,
p.48 (PDF p.52): "each Ti is a natural, dual, or Frobenius-twisted module of one factor of D".

On the natural module `K^n` the element `g` acts by its own matrix; on the dual module (the
contragredient, in the dual basis) by `(g⁻¹)ᵀ`; a Frobenius twist by `r` raises every entry of the
action matrix to the power `p^r`, `p = char K`. So the matrix is
`(g or (g⁻¹)ᵀ)` with every entry `a ↦ a^(p^r)`.

**Formalization Note.** For a finite field `K` of characteristic `p`, `a ↦ a^(p^r)` is a field
automorphism, so `stdMat κ` is a representation of `GL(n, K)`. -/
noncomputable def stdMat {K : Type*} [Field K] {n : ℕ} (κ : ModKind) (g : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K :=
  (if κ.dual then (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).transpose
    else (g : Matrix (Fin n) (Fin n) K)).map fun a => a ^ (ringChar K ^ κ.twist)

end Supplement

end GroupIsoPoly


