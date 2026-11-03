-- Prove2me | Definitions.Def_EnvelopeMSLP_basisMatrix
-- name    : EnvelopeMSLP_basisMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:51.23874+00:00
-- url     : https://prove2.me/theorems/1c85de00-14cf-4b91-a6fc-91e6a4e72c69
-- title:
--   The basis matrix $D_\beta$
-- statement:
--   For an $m\times n$ matrix $D$ and $\beta\subseteq[n]$ with $|\beta|=m$, the matrix $D_\beta$ is the square matrix obtained from $D$ by removing the columns $[n]\setminus\beta$.
--
--   **Formalization Note** $\beta$ is an injection `Fin m ↪ Fin n`, which also fixes the order of the columns. The sign of $\det D_\beta$ depends on this order.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), proof of Lemma 1, p.9

import Mathlib
open Matrix

namespace EnvelopeMSLP

/-- **The square matrix `D_β`.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), proof of Lemma 1, p.9: `D` with the columns outside `β`
removed.

**Formalization Note.** The paper's `β ⊆ [n]`, `|β| = m`, is an injection `Fin m ↪ Fin n`, which
also fixes an order of the columns; the sign of `det D_β` depends on that order. -/
def basisMatrix {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) (β : Fin m ↪ Fin n) :
    Matrix (Fin m) (Fin m) ℝ :=
  D.submatrix id β

end EnvelopeMSLP


