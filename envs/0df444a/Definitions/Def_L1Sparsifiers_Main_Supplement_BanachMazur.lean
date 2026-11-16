-- Prove2me | Definitions.Def_L1Sparsifiers_Main_Supplement_BanachMazur
-- name    : L1Sparsifiers_Main_Supplement_BanachMazur
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:15:40.949135+00:00
-- url     : https://prove2.me/theorems/5209e5fa-5cb9-42c8-85ff-5d8c68985969
-- title:
--   The Banach–Mazur distance $d_{BM}(X,Y)$
-- statement:
--   Let $X$ and $Y$ be real normed spaces. The **Banach–Mazur distance** between them is
--   $$d_{BM}(X,Y)=\inf\big\{\|T\|\,\|T^{-1}\|:\ T:X\to Y\ \text{a linear isomorphism}\big\},$$
--   the infimum over all bounded linear bijections with bounded inverse, valued in $[0,\infty]$. It equals $+\infty$ when no isomorphism exists, for instance when $\dim X\ne\dim Y$. For isomorphic nonzero spaces $d_{BM}(X,Y)\ge1$, and $d_{BM}(X,Y)\le1+\varepsilon$ says that, up to rescaling, $X$ embeds onto $Y$ with distortion at most $1+\varepsilon$.
--
--   This is the distance in which Theorem 3 measures how well an $n$-dimensional subspace of $\ell_1$ is approximated by a subspace of $\ell_1^N$.
--
--   **Formalization Note** The infimum is over continuous linear equivalences `X ≃L[ℝ] Y` and is computed in `ℝ≥0∞`, so it is never a junk value $0$ on an empty index set. Between finite-dimensional spaces every linear bijection is continuous, so this is the infimum over all linear isomorphisms. For two zero spaces the only map is $0$, and the value is $0$ rather than the conventional $1$; both are at most $1+\varepsilon$.
-- source:
--   Victor Reis, Thomas Rothvoss, Linear-size ℓ1 sparsifiers, STOC 2027 submission #162 (October 2026; PDF SHA-256 5137e7dee3cd303bd508f90f5f42c955632af5dc2ec978d9ef575bae4ce23710), §1.1, Theorem 3 and the sentence after it, p.4

import Mathlib

namespace L1Sparsifiers.Main.Supplement

open scoped NNReal ENNReal

/-- **Banach–Mazur distance** (Reis–Rothvoss, STOC 2027 submission #162, §1.1, p.4):
for real normed spaces `X` and `Y`,
`d_BM(X, Y) = inf { ‖T‖ · ‖T⁻¹‖ : T : X → Y a linear isomorphism }`.

The infimum ranges over **all** continuous linear isomorphisms `T : X ≃L[ℝ] Y` and is taken in
`[0, ∞]`, so it is `∞` when `X` and `Y` are not isomorphic (for instance when their dimensions
differ); it is never a junk `0`. Between finite-dimensional spaces every linear bijection is
continuous, so this is the infimum over all linear isomorphisms. -/
noncomputable def banachMazur (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : ℝ≥0∞ :=
  ⨅ T : X ≃L[ℝ] Y, (((‖(T : X →L[ℝ] Y)‖₊ * ‖(T.symm : Y →L[ℝ] X)‖₊ : ℝ≥0)) : ℝ≥0∞)

end L1Sparsifiers.Main.Supplement


