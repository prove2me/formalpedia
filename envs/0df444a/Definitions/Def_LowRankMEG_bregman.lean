-- Prove2me | Definitions.Def_LowRankMEG_bregman
-- name    : LowRankMEG_bregman
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:15.020259+00:00
-- url     : https://prove2.me/theorems/79b94905-2a5f-40a1-aa1b-80b9acd1286c
-- title:
--   The von Neumann Bregman distance $B(X,Y)$
-- statement:
--   On the spectrahedron, the Bregman distance of the von Neumann entropy is
--   $$
--   B(X,Y)=\operatorname{Tr}\bigl(X\log(X)-X\log(Y)\bigr),
--   $$
--   with the convention $0\log(0):=0$, which lets $X$ be singular. This is the quantum relative entropy. It is the distance in which the iterates of Matrix Exponentiated Gradient are measured.
--
--   **Formalization Note** `mlog` carries the convention. Every statement of the mission takes a positive definite second argument, since $\log(Y)$ is undefined on the page otherwise.
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Eq. (2), p.5

import Mathlib
import Definitions.Def_LowRankMEG_mlog

namespace LowRankMEG

/-- **The Bregman distance of the von Neumann entropy on the spectrahedron**,
`B(X, Y) = Tr(X log(X) − X log(Y))`.
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Eq. (2), p.5.

**Formalization Note.** The first argument may be singular: `mlog` carries the convention
`0 log(0) := 0` of p.5. Every statement of this mission takes a positive definite second argument. -/
noncomputable def bregman {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (X * mlog X - X * mlog Y).trace

end LowRankMEG


