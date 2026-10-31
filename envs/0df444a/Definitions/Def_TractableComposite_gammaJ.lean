-- Prove2me | Definitions.Def_TractableComposite_gammaJ
-- name    : TractableComposite_gammaJ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:50.159982+00:00
-- url     : https://prove2.me/theorems/d0be535c-eb9d-49e3-8c24-00728182be7c
-- title:
--   The linear map $\Gamma_J$
-- statement:
--   For $J\in\mathcal J$, $\Gamma_J$ maps $u$ to $\tilde u$ with $\tilde u_{ij}=u_{ij}$ for $j\in J_i$ and
--
--   $$\tilde u_{ij}=(1-\gamma_{ij})u_{i\,l(i,j)}+\gamma_{ij}u_{i\,r(i,j)}\qquad(j\notin J_i),$$
--
--   where $l(i,j)=\max\{j'\in J_i\mid j'\le j\}$, $r(i,j)=\min\{j'\in J_i\mid j'\ge j\}$ and $\gamma_{ij}=(a_{ij}-a_{i\,l(i,j)})/(a_{i\,r(i,j)}-a_{i\,l(i,j)})$. It replaces the coordinates outside $J_i$ by linear interpolation of those in $J_i$.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), (6), p.5

import Mathlib

namespace TractableComposite

/-- **The linear map Γ_J**, (6), p.5: `ũᵢⱼ = uᵢⱼ` for `j ∈ Jᵢ` and
`ũᵢⱼ = (1 − γᵢⱼ) u_{i l(i,j)} + γᵢⱼ u_{i r(i,j)}` for `j ∉ Jᵢ`, where `l(i,j) = max{j' ∈ Jᵢ | j' ≤ j}`,
`r(i,j) = min{j' ∈ Jᵢ | j' ≥ j}` and `γᵢⱼ = (aᵢⱼ − a_{i l(i,j)})/(a_{i r(i,j)} − a_{i l(i,j)})`. He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), (6), p.5.

**Formalization Note.** `l` and `r` are `Finset.sup`/`Finset.inf` of the filtered `Jᵢ` in `Fin (n+1)`;
for `J ∈ 𝒥` (`0, n ∈ Jᵢ`) these are the max and min of nonempty sets. The same map with `s` in
place of `u` is used in (18) and in Theorem 2's proof. -/
noncomputable def gammaJ {d n : ℕ} (a : Fin d → Fin (n + 1) → ℝ) (J : Fin d → Finset (Fin (n + 1))) (u : Fin d → Fin (n + 1) → ℝ) : Fin d → Fin (n + 1) → ℝ :=
  fun i j =>
    if j ∈ J i then u i j else
      let l := ((J i).filter (· ≤ j)).sup id
      let r := ((J i).filter (j ≤ ·)).inf id
      let γ := (a i j - a i l) / (a i r - a i l)
      (1 - γ) * u i l + γ * u i r

end TractableComposite


