-- Prove2me | Definitions.Def_OnlineCAP_linkPoint
-- name    : OnlineCAP_linkPoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:35.124074+00:00
-- url     : https://prove2.me/theorems/676cf2bf-3dd0-4499-b222-b9d7fb117bcc
-- title:
--   The point p_ℓ = (i, j) of a link
-- statement:
--   Each link $\ell=\{v_i,v_j\}$ of the cycle with $i<j$ is represented by the point
--   $$p_\ell=(i,j)\in\mathbb Z^2\subseteq\mathbb R^2 ,$$
--   and a link set $L$ by the point set $P_L=\{p_\ell:\ell\in L\}$. In general $p_{\{v_i,v_j\}}=(\min(i,j),\max(i,j))$; distinct links without loops give distinct points.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §3.1, p.11

import Mathlib

namespace OnlineCAP

/-- **The point of a link.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §3.1, p.11 (PDF p.11): "For each link ℓ = (vi, vj), we create a
point pℓ = (i, j) ∈ Z2", with the convention `i < j` of Proposition 3.2.

`linkPoint {v_i, v_j} = (min(i, j), max(i, j)) ∈ ℝ²`. -/
def linkPoint {n : ℕ} : Sym2 (Fin n) → ℝ × ℝ :=
  Sym2.lift ⟨fun i j => (((min i j : Fin n) : ℕ), ((max i j : Fin n) : ℕ)), fun i j => by
    simp only [min_comm, max_comm]⟩

/-- **The point set of a link set.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §3.1, p.11: `P_L = {p_ℓ : ℓ ∈ L}`. -/
noncomputable def linkPoints {n : ℕ} (L : Finset (Sym2 (Fin n))) : Finset (ℝ × ℝ) := by
  classical
  exact L.image linkPoint

end OnlineCAP


