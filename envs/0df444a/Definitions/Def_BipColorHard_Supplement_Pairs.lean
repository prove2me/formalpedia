-- Prove2me | Definitions.Def_BipColorHard_Supplement_Pairs
-- name    : BipColorHard_Supplement_Pairs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:43:52.046689+00:00
-- url     : https://prove2.me/theorems/b2a09da1-6a12-49c2-9e54-935fd8957e74
-- title:
--   The vectors $\alpha^S$, $\beta^S$ of Theorem 27
-- statement:
--   Let $q=2k+1$ with $k\ge1$, let $S\subseteq[q]$ with $|S|=k$, and let $\delta,\hat\delta$ be reals. Define $\alpha^S,\beta^S\in\mathbb R^q$ by
--   $$\alpha^S_i=\begin{cases}\frac1q+\delta,& i\in S,\\[2pt] \frac1q-\frac{k}{k+1}\delta,& i\notin S,\end{cases}\qquad \beta^S_i=\begin{cases}\frac1q-\frac{k+1}{k}\hat\delta,& i\in S,\\[2pt] \frac1q+\hat\delta,& i\notin S.\end{cases}$$
--   Since $|S|=k$ and $|S^c|=k+1$, both vectors have coordinate sum $1$ for every $\delta,\hat\delta$.
--
--   These are the color-frequency vectors of the global maximizers of $\Psi$ in Theorem 27.
--
--   **Formalization Note** Colors are `Fin (2k+1)` and $S$ ranges over the published `Omega k` (the $k$-subsets). The definitions are used only for $k\ge1$, where $(k+1)/k$ involves no division by zero.
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Theorem 27, p.31 (PDF p.33)

import Definitions.Def_BipColorHard_PhaseLabeling

set_option autoImplicit false

namespace BipColorHard.Supplement

/-- The vector `α` of Theorem 27, p.31 (PDF p.33), Galanis, Guo, He, Štefankovič, Vigoda, manuscript of
Nov. 3, 2026 (sha256 78a66d1f…), for `q = 2k + 1`, a `k`-subset `S ⊆ [q]` and `δ`:
`α_i = 1/q + δ` for `i ∈ S` and `α_i = 1/q − (k/(k+1)) δ` for `i ∉ S`. -/
noncomputable def alphaS (k : ℕ) (δ : ℝ) (S : Omega k) (i : Fin (2 * k + 1)) : ℝ :=
  if i ∈ S.1 then 1 / ((2 * k + 1 : ℕ) : ℝ) + δ
  else 1 / ((2 * k + 1 : ℕ) : ℝ) - ((k : ℝ) / ((k : ℝ) + 1)) * δ

/-- The vector `β` of Theorem 27, p.31 (PDF p.33), manuscript sha256 78a66d1f…, for `q = 2k + 1`, a
`k`-subset `S ⊆ [q]` and `δ̂`: `β_i = 1/q − ((k+1)/k) δ̂` for `i ∈ S` and `β_i = 1/q + δ̂` for `i ∉ S`.

**Formalization Note.** Used only for `k ≥ 1`, so the factor `(k+1)/k` involves no division by zero. -/
noncomputable def betaS (k : ℕ) (δh : ℝ) (S : Omega k) (i : Fin (2 * k + 1)) : ℝ :=
  if i ∈ S.1 then 1 / ((2 * k + 1 : ℕ) : ℝ) - (((k : ℝ) + 1) / (k : ℝ)) * δh
  else 1 / ((2 * k + 1 : ℕ) : ℝ) + δh

end BipColorHard.Supplement


