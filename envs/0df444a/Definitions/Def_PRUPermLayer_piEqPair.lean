-- Prove2me | Definitions.Def_PRUPermLayer_piEqPair
-- name    : PRUPermLayer_piEqPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:04.646199+00:00
-- url     : https://prove2.me/theorems/5a36b8e1-3ac9-4b18-ac59-a9fd76b79694
-- title:
--   Equality projector $\Pi^{\mathrm{eq}}_{ij}$ on registers $i$ and $j$
-- statement:
--   On $t$ registers with $N$ basis labels each, $\Pi^{\mathrm{eq}}_{ij}$ is the diagonal projector onto the basis states $|x_1,\dots,x_t\rangle$ with $x_i = x_j$: the event that registers $i$ and $j$ give equal outcomes.
--
--   **Formalization Note** Registers are numbered from $0$ in Lean: register $i$ is the paper's register $i+1$.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 4.1, p.17 (PDF p.19)

import Mathlib

namespace PRUPermLayer

/-- The equality projector `Π^eq_{ij}` on registers `i` and `j` of `t` registers with `N`
labels: the diagonal projector onto the basis states with `x_i = x_j` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Lemma 4.1, p.17
(PDF p.19)).

**Formalization Note** Registers are indexed by `Fin t` (0-based): `i : Fin t` is the source's
register `i + 1`. -/
def piEqPair (N t : ℕ) (i j : Fin t) : Matrix (Fin t → Fin N) (Fin t → Fin N) ℂ :=
  Matrix.diagonal fun x => if x i = x j then 1 else 0

end PRUPermLayer


