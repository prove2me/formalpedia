-- Prove2me | Definitions.Def_AlonMilman_PropertyT_regularRep
-- name    : AlonMilman_PropertyT_regularRep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:31:12.673185+00:00
-- url     : https://prove2.me/theorems/ccbeb275-8a3e-4a4c-a25b-481ae00a3912
-- title:
--   The left regular representation of a finite group as permutation matrices
-- statement:
--   Let $T$ be a finite group and $R$ a semiring (in this mission $\mathbb{R}$ or $\mathbb{C}$). For $t \in T$, $\pi(t)$ is the $|T| \times |T|$ permutation matrix, with rows and columns indexed by $T$, given by
--
--   $$\big(\pi(t)\big)_{w,u} = \begin{cases} 1 & \text{if } w\,u^{-1} = t,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   Acting on a vector $v = (v_u)_{u\in T}$, it gives $(\pi(t) v)_w = v_{t^{-1} w}$. This is the regular (left) representation used in the proof of Alon and Milman's Lemma 4.8; composed with a homomorphism $\phi : H \to T$ it gives the representation $\pi \cdot \phi$ of $H$ whose restriction to the zero-sum vectors is fed to Lemma 4.7.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 85, proof of Lemma 4.8

import Mathlib

namespace AlonMilman.PropertyT

/-- The (left) regular representation of a finite group `T` as permutation matrices
(Alon–Milman 1985, proof of Lemma 4.8, p. 85): `(π(t))_{w,u} = 1` if `w · u⁻¹ = t` and `0`
otherwise, with entries in a semiring `R`. -/
def regularRep (R : Type) [Semiring R] {T : Type} [Group T] [DecidableEq T] (t : T) :
    Matrix T T R :=
  fun w u => if w * u⁻¹ = t then 1 else 0

end AlonMilman.PropertyT


