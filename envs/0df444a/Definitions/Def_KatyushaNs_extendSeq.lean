-- Prove2me | Definitions.Def_KatyushaNs_extendSeq
-- name    : KatyushaNs_extendSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:47:49.125991+00:00
-- url     : https://prove2.me/theorems/d91564fc-d3d8-4387-99b1-e76d8e422b8e
-- title:
--   Padding a finite index sequence
-- statement:
--   For $n \ge 1$ and a finite index sequence $w = (w_0, \dots, w_{N-1})$ with values in $\{1,\dots,n\}$, the padded sequence agrees with $w$ on $0,\dots,N-1$ and takes the first index at every $k \ge N$.
--
--   It is an auxiliary device for the expectations of Theorem 4.1 and Appendix C.1: an expectation over the first $N$ iterations only reads indices $0,\dots,N-1$, so the padding is never used.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Theorem 4.1, p. 15; Appendix C.1, pp. 26–27 (auxiliary)

import Mathlib

namespace KatyushaNs

/-- **A finite index sequence padded to an infinite one.**
Auxiliary for the expectations of Allen-Zhu, *Katyusha: The First Direct Acceleration of
Stochastic Gradient Methods*, arXiv:1603.05953v6, Theorem 4.1, p. 15 (PDF p. 16) and
Appendix C.1, pp. 26–27 (PDF pp. 27–28).

`extendSeq hn w k = w k` for `k < N` and `= 0` (the first index) for `k ≥ N`.

**Formalization Note.** The padded values are never read by the averaged quantities: an
expectation over `N` iterations only involves indices `0, …, N − 1`. -/
def extendSeq {n : ℕ} (hn : 0 < n) {N : ℕ} (w : Fin N → Fin n) : ℕ → Fin n :=
  fun k => if h : k < N then w ⟨k, h⟩ else ⟨0, hn⟩

end KatyushaNs


