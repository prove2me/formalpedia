-- Prove2me | Definitions.Def_ChanTomoNB_Proj
-- name    : ChanTomoNB_Proj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:10.800416+00:00
-- url     : https://prove2.me/theorems/fb7b14cd-67ee-4c3d-8ab5-7cf4bb2c0839
-- title:
--   Rank-$k$ orthogonal projectors $\mathrm{Proj}_k$, $P_0=\mathrm{diag}(I_k,0)$ and $W_0=[I_k;0]$
-- statement:
--   $\mathrm{Proj}_k(\mathbb C^X)$ is the set of rank-$k$ orthogonal projectors $P$ on $\mathbb C^X$: $P^\dagger=P$, $P^2=P$, $\operatorname{rank}P=k$. On $\mathbb C^m$ the coordinate projector is $P_0=\mathrm{diag}(I_k,0_{m-k})$ and the coordinate isometry $W_0=\begin{pmatrix}I_k\\0\end{pmatrix}:\mathbb C^k\to\mathbb C^m$, so that $W_0W_0^\dagger=P_0$ for $k\le m$.
--
--   A Haar-random element of $\mathrm{Proj}_k(m)$ is $UP_0U^\dagger$ with $U$ Haar on $\mathbb U_m$; these objects parametrize the hidden signal ranges of the hard instances.
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, §4, p.21 and p.24; §5.1, p.26; Lemma 5.14, p.32

import Mathlib

open Matrix

namespace ChanTomoNB

/-- `Proj_k`: the rank-`k` orthogonal projectors on `ℂ^X` (Hermitian, idempotent, rank `k`).
Chen, Oufkir, *Quantum channel tomography: optimal bounds in the near-boundary regime*,
arXiv:2611.03639v1, §4, p.21 (`Proj_{d′}(d′+α)`) and §5.1, p.26 (`Proj_{d′}(im Π)`). -/
def Proj (k : ℕ) (X : Type) [Fintype X] [DecidableEq X] : Set (Matrix X X ℂ) :=
  {P | Pᴴ = P ∧ P * P = P ∧ P.rank = k}

/-- The coordinate projector `P₀ = diag(I_k, 0)` on `ℂ^m` (arXiv:2611.03639v1, p.24 and
Lemma 5.14, p.32: `P₀ := diag(I_{d′}, 0_α)`). -/
def P0 (k m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) < k then 1 else 0

/-- The coordinate isometry `W₀ = [I_k; 0] : ℂ^k → ℂ^m`, with `W₀ W₀† = P₀` (for `k ≤ m`). Used to
parametrize `P ∼ Proj_k(m)` by a Haar unitary `U ∼ U_m` as `P = U P₀ U†` with isometry `U W₀`
(arXiv:2611.03639v1, p.24). -/
def W0 (k m : ℕ) : Matrix (Fin m) (Fin k) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

end ChanTomoNB


