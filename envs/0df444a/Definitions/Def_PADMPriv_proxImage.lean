-- Prove2me | Definitions.Def_PADMPriv_proxImage
-- name    : PADMPriv_proxImage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:04.887221+00:00
-- url     : https://prove2.me/theorems/f3bf988b-a63e-4a1b-ad66-8ba53d58b4f2
-- title:
--   Image $A\circ P_{\beta,F,A}(u)$ of a proximal minimizer
-- statement:
--   For $F$, $A$, $\beta$ and $u$ as in (13), let
--   $$
--   A\circ P_{\beta,F,A}(u) := A\hat x, \qquad \hat x \in P_{\beta,F,A}(u).
--   $$
--   The proximal set $P_{\beta,F,A}(u)$ may contain many points, but for convex $F$ all of them have the same image under $A$ (proof of Proposition 3.1), so this operator is single-valued. PADM only ever uses this image.
--
--   **Formalization Note** A minimizer is picked by choice; if (13) has no minimizer at $u$ the value is the placeholder $0$. Every statement using this operator assumes, or has hypotheses that imply, that the minimizers exist.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Eqs. (13)–(15), p.7; proof of Proposition 3.1, p.22

import Mathlib
import Definitions.Def_PADMPriv_IsProxMin

namespace PADMPriv

open Classical in
/-- The image `A ∘ P_{β,F,A}(u) = A x̂` of a proximal minimizer `x̂ ∈ P_{β,F,A}(u)` of (13)
(Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), (13)–(15), p.7). For convex `F` every minimizer has the same image
(proof of Proposition 3.1, p.22), so the value does not depend on which minimizer is chosen.

**Formalization Note** A minimizer is chosen by `Classical.choose`. If (13) has no minimizer the
value is the junk `0`; every statement using it assumes (or its hypotheses imply) that the
minimizers exist. -/
noncomputable def proxImage {m p : ℕ} (β : ℝ) (F : EuclideanSpace ℝ (Fin p) → ℝ)
    (A : Matrix (Fin m) (Fin p) ℝ) (u : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  if h : ∃ x, IsProxMin β F A u x then Matrix.toEuclideanLin A h.choose else 0

end PADMPriv


