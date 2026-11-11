-- Prove2me | Definitions.Def_UPPIntersection_Halfspaces_Polynomials
-- name    : UPPIntersection_Halfspaces_Polynomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:26:55.790836+00:00
-- url     : https://prove2.me/theorems/88416551-5393-4151-8928-c8654d963bb7
-- title:
--   §2, §4 — $I_\eta$, the orthant function $Q_k$, signed AND and shifted Legendre polynomials $L_i$
-- statement:
--   1. For $\eta\in(0,1)$, $I_\eta=[-1,-\eta]\cup[\eta,1]$.
--   2. The orthant function $Q_k:\mathbb R^k\to\mathbb R$ is $Q_k(s)=\bigwedge_{i=1}^k\operatorname{sgn} s_i$ when every $s_i\ne0$ and $0$ otherwise: it is $-1$ on the open negative orthant, $+1$ at every other point with nonzero coordinates, and $0$ on the coordinate hyperplanes.
--   3. The signed AND of values $v_1,\dots,v_k\in\{-1,1\}$ is $-1$ if all $v_i=-1$ and $+1$ otherwise.
--   4. The shifted Legendre polynomials are
--   $$L_i(t)=\sum_{a=0}^{i}\binom ia^2(t-1)^a(t-2)^{i-a},$$
--   equal to $P_i(2t-3)$ for the Legendre polynomial $P_i$ with $P_i(1)=1$.
--
--   These objects carry the polynomial branch of the argument (Section 4): degree lower bounds for sign representations of $Q_k$ on $I_\eta^k$, and coefficient control through the orthogonal family $L_i$ on $[1,2]$.
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 13 (definitions of I_η and Q_k), p. 12 (∧), p. 22 (definition of L_i); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib

namespace UPPIntersection.Halfspaces

open Polynomial

/-- `I_η = [-1, -η] ∪ [η, 1]`. -/
def bandI (η : ℝ) : Set ℝ := {x | η ≤ |x| ∧ |x| ≤ 1}

open Classical in
/-- The orthant function `Q_k(s) = ⋀_i sgn s_i` if every `s_i ≠ 0`, and `0` otherwise (p.13):
it equals `-1` on the open negative orthant, `+1` at every other point with all coordinates
nonzero, and `0` if some coordinate vanishes. -/
noncomputable def orthantQ {k : ℕ} (s : Fin k → ℝ) : ℝ :=
  if ∃ i, s i = 0 then 0 else if ∀ i, s i < 0 then -1 else 1

open Classical in
/-- Signed Boolean AND of `±1` values: `-1` if every value is `-1`, and `+1` otherwise. -/
noncomputable def signedAnd {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  if ∀ i, v i = -1 then -1 else 1

/-- The shifted Legendre polynomial `L_i(t) = ∑_{a=0}^{i} C(i,a)² (t-1)^a (t-2)^{i-a}` (§4.2). -/
noncomputable def shiftedL (i : ℕ) : ℝ[X] :=
  ∑ a ∈ Finset.range (i + 1), C ((i.choose a : ℝ) ^ 2) * (X - C 1) ^ a * (X - C 2) ^ (i - a)

end UPPIntersection.Halfspaces


