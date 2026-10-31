-- Prove2me | Definitions.Def_TractableComposite_alphaPi
-- name    : TractableComposite_alphaPi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:30.131999+00:00
-- url     : https://prove2.me/theorems/1856dc3a-f1f6-4f71-ad8c-c7891d815a79
-- title:
--   The coefficients $\alpha^\pi$ of (15)
-- statement:
--   $$\alpha^\pi_{ij}=\begin{cases}0 & j=0,\\ \vartheta(\pi,i,j)-\vartheta(\pi,i,j+1) & 1\le j<n,\\ \vartheta(\pi,i,n) & j=n.\end{cases}$$
--
--   Together with $b^\pi$ they give the affine function that interpolates $\bar\phi$ on the staircase simplex $\Upsilon_\pi$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (15), p.11

import Mathlib
import Definitions.Def_TractableComposite_theta

namespace TractableComposite

/-- **The coefficients α^π**, (15), p.11: `α^π_ij = 0` if `j = 0`, `ϑ(π,i,j) − ϑ(π,i,j+1)` if `1 ≤ j < n`,
and `ϑ(π,i,n)` if `j = n`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (15), p.11. -/
noncomputable def alphaPi {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) (φ : (Fin d → ℝ) → ℝ) (π : Fin (d * n) → Fin d) :
    Fin d → Fin (n + 1) → ℝ :=
  fun i j => if j.val = 0 then 0 else
    if h : j.val < n then theta a φ π i j - theta a φ π i ⟨j.val + 1, by omega⟩ else theta a φ π i j

end TractableComposite


