-- Prove2me | Definitions.Def_ContractionLemma_kernel
-- name    : ContractionLemma_kernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:25.068921+00:00
-- url     : https://prove2.me/theorems/ccacf241-ec54-4e32-9b82-7a2c0ef70e7b
-- title:
--   The kernel $K_\delta$, eq. (6), on the grid $S=\{-L,\dots,L-1\}$
-- statement:
--   Fix $L=2^a$. The grid is $S=\{-L,\dots,L-1\}$, and $C(T)=\prod_{s\in S}(T-s)$. The **kernel** is
--
--   $$
--   K_\delta(T)=\frac{C(T)}{C'(0)\,(T-\delta)}=\frac{1}{C'(0)}\prod_{s\in S,\ s\ne\delta}(T-s),
--   $$
--
--   the Lagrange basis polynomial of the point $\delta$ on the grid, normalized so that $K_0(0)=1$. The constants $c_t=C'(t)/C'(0)$ scale the shifts on the curve built from it.
--
--   **Formalization Note** The kernel is defined by the product formula, for every integer $\delta$. Only slot differences, which lie in $S$, are used.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.4.1, eq. (6), pp.57–58

import Mathlib

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- The grid `S = {−L, …, L − 1}` with `L = 2^a` (App. A.4.1, p.57). -/
noncomputable def gridS (a : ℕ) : Finset ℤ := Finset.Ico (-(2 ^ a : ℤ)) (2 ^ a)

/-- `C(T) = ∏_{s ∈ S} (T − s)` (p.57). -/
noncomputable def Cpoly (a : ℕ) : ℚ[X] := ∏ s ∈ gridS a, (X - C (s : ℚ))

/-- `C′(0)`. -/
noncomputable def Cder0 (a : ℕ) : ℚ := (derivative (Cpoly a)).eval 0

/-- **The kernel `K_δ` (eq. (6))** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.58 (PDF p.61):
`K_δ(T) = C(T)/(C′(0)(T − δ)) = (1/C′(0)) ∏_{s ∈ S, s ≠ δ} (T − s)`, the Lagrange basis
polynomial of the point `δ` on the grid `S`, normalized by `C′(0)`.

**Formalization Note.** Defined by the product formula, for every integer `δ` (the paper uses
it for slot differences `δ ∈ S`; for `δ ∉ S` the product runs over all of `S`). -/
noncomputable def kernel (a : ℕ) (δ : ℤ) : ℚ[X] :=
  C (Cder0 a)⁻¹ * ∏ s ∈ (gridS a).erase δ, (X - C (s : ℚ))

/-- `c_t = C′(t)/C′(0)` (Lemma A.7, p.58). -/
noncomputable def shiftConst (a : ℕ) (t : ℤ) : ℚ := (derivative (Cpoly a)).eval (t : ℚ) / Cder0 a

end ContractionLemma


