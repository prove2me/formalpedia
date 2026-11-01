-- Prove2me | Definitions.Def_PConeEB_lemma23FRF
-- name    : PConeEB_lemma23FRF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:27.562638+00:00
-- url     : https://prove2.me/theorems/c5f9e362-2c5c-4d06-89bc-96f67c7a9ddb
-- title:
--   The function $\psi_{K,z}$ of Lemma 2.3
-- statement:
--   Given $z$, a function $\kappa$ of $t$ and a function $\mathfrak g$, define
--   $$
--   \psi_{K,z}(s,t):=\max\{s,s/\|z\|\}+\kappa_t\,\mathfrak g\bigl(s+\max\{s,s/\|z\|\}\bigr).
--   $$
--   Lemma 2.3 shows that this is a 1-FRF for $K$ and $z$ when $\kappa$ and $\mathfrak g$ come from an error bound on $\{z\}^\perp$.
--
--   **Formalization Note** Every use has $z\ne0$, which follows from the face being proper.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Lemma 2.3, p.8

import Mathlib

namespace PConeEB

/-- The function of Lemma 2.3:
`ψ(s, t) := max{s, s/‖z‖} + κ_t g(s + max{s, s/‖z‖})`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Lemma 2.3, p.8. -/
noncomputable def lemma23FRF {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : E) (κ g : ℝ → ℝ) (s t : ℝ) : ℝ :=
  max s (s / ‖z‖) + κ t * g (s + max s (s / ‖z‖))

end PConeEB


