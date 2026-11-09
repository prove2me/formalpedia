-- Prove2me | Definitions.Def_ProxGapTight_Um
-- name    : ProxGapTight_Um
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:52:45.063881+00:00
-- url     : https://prove2.me/theorems/c89d6d4c-53a4-4543-b0ce-68d7ebf05d7b
-- title:
--   Ambient code $U_m=\mathrm{span}_{\mathbb F_p}\{u_W\}$
-- statement:
--   Let $p$ be a prime, $Q=p^a$, and $X$ the set of lines of $\mathbb F_Q^m$. The **ambient code** is
--   $$
--   U_m=\mathrm{span}_{\mathbb F_p}\{u_W:\ W\in\mathrm{Gr}(m-2,\mathbb F_Q^m)\}\subseteq\mathbb F_p^X,
--   $$
--   the $\mathbb F_p$-span of the incidence vectors of the codimension-two subspaces.
--
--   This is the code of points and codimension-two spaces of a projective space studied by Adriaensen and Denaux; its low-weight words are combinations of at most two incidence vectors, which is the base of the counterexample.
--
--   **Formalization Note** $\mathbb F_Q$ is any field $K$ and $\mathbb F_p$ is $\mathbb Z/p\mathbb Z$.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §3.1, p.7, display

import Mathlib
import Definitions.Def_ProxGapTight_incVec

namespace ProxGapTight

/-- The **ambient code** `U_m := span_{F_p}{u_W : W ∈ Gr(m − 2, F_Q^m)} ⊆ F_p^X`, Kominers, Thaler,
Zheng, manuscript (Sept. 2026), §3.1, p.7, display.

**Formalization Note.** `F_Q` is any field `K` (in the statements, of order `Q = p^a`), `F_p` is
`ZMod p`, and `X = Lines K m`. -/
def Um (K : Type) [Field K] (m p : ℕ) : Submodule (ZMod p) (Lines K m → ZMod p) :=
  Submodule.span (ZMod p) (Set.range (fun W : Codim2 K m => incVec (ZMod p) W))

end ProxGapTight


