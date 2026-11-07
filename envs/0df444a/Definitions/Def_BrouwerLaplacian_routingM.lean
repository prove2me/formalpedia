-- Prove2me | Definitions.Def_BrouwerLaplacian_routingM
-- name    : BrouwerLaplacian_routingM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:07.668199+00:00
-- url     : https://prove2.me/theorems/4bca837b-4594-42e5-9cea-9d995cdda7b2
-- title:
--   The matrices $M$, $N=CMC$ and the vector $v=CM\mathbf 1$ of a projection
-- statement:
--   Let $P$ be a real $n\times n$ matrix, and let $C$ be the centering matrix. The **matrix $M$** of $P$ has entries
--
--   $$M_{ii}=0,\qquad M_{ij}=P_{ii}+P_{jj}-2P_{ij}-1\quad(i\ne j).$$
--
--   From it the paper forms the vector $v=CM\mathbf 1$ (the centered row sums of $M$) and the matrix $N=CMC$.
--
--   For an orthogonal projection $P$, the quantity $P_{ii}+P_{jj}-2P_{ij}=\|P(e_i-e_j)\|^2$ is the squared length of the projected edge vector $e_i-e_j$, so $M_{ij}$ measures how much a potential edge $\{i,j\}$ contributes beyond $1$ to the trace $\operatorname{tr}(PL)$. These objects carry the paper's reduction of Brouwer's conjecture to a nuclear norm bound for split graphs.
--
--   **Formalization Note** Indices are $\mathrm{Fin}\,n$. The module defines `routingM P` ($M$), `routingV P` ($v$) and `routingN P` ($N$).
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Lemma 5.3, p.5; Lemma 5.5, p.6

import Mathlib
import Definitions.Def_BrouwerLaplacian_centering

namespace BrouwerLaplacian

open Matrix

/-- **The matrix `M` of a projection.**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Lemma 5.3, p.5 (also
Lemma 5.5, p.6, and the proof of Lemma 5.6, p.8): "Define the matrix M with diagonal entries
Mᵢᵢ = 0 and off-diagonal entries Mᵢⱼ = Pᵢᵢ + Pⱼⱼ − 2Pᵢⱼ − 1." -/
def routingM {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then 0 else P i i + P j j - 2 * P i j - 1

/-- **The vector `v = CM𝟙`.**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Lemma 5.3, p.5 and
Lemma 5.5, p.6: "Let v = CM1", with `C` the centering matrix and `𝟙` the all-ones vector. -/
noncomputable def routingV {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  centering n *ᵥ (routingM P *ᵥ fun _ => 1)

/-- **The matrix `N = CMC`.**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Lemma 5.5, p.6:
"Let N = CMC". -/
noncomputable def routingN {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  centering n * routingM P * centering n

end BrouwerLaplacian


