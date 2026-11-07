-- Prove2me | Definitions.Def_GeoSemialgCSP_CousinsHom
-- name    : GeoSemialgCSP_CousinsHom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:13.329956+00:00
-- url     : https://prove2.me/theorems/c6523133-e4e9-4e51-bf56-22f7cf43515f
-- title:
--   Cousins homomorphism of a complete tree
-- statement:
--   For a domain $X\subseteq\mathbb R^d$, a predicate $P$, and the complete ordered $k$-ary tree of height $h$, a **cousins homomorphism** is a map $\psi$ from the leaves to $X$ such that
--   $$\mathrm{cousins}(l_1,\dots,l_k)=1\ \Longrightarrow\ P(\psi(l_1),\dots,\psi(l_k))=1 .$$
--
--   It turns every constraint of the multiscale instance into a satisfied constraint of $P$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 Assumptions, p.7 (PDF p.8); Eq. (2), p.9 (PDF p.10)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_cousinsW

namespace GeoSemialgCSP

/-- **Cousins homomorphism of a complete tree.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 Assumptions,
printed p.7 (PDF p.8), and (2), printed p.9 (PDF p.10): a map `ψ` from the leaves of the tree to
`X` such that `cousins(l₁, …, l_k) = 1` implies `P(ψ(l₁), …, ψ(l_k)) = 1`.

**Formalization Note.** For the complete ordered `k`-ary tree of height `h` (leaves = words
`Fin h → Fin k`). -/
def CousinsHom {k d : ℕ} (X : Set (E d)) (S : Set (Fin k → E d)) (h : ℕ)
    (ψ : (Fin h → Fin k) → E d) : Prop :=
  (∀ w, ψ w ∈ X) ∧ ∀ l : Fin k → (Fin h → Fin k), cousinsW l → ψ ∘ l ∈ S

end GeoSemialgCSP


