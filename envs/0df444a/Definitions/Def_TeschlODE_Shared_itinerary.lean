-- Prove2me | Definitions.Def_TeschlODE_Shared_itinerary
-- name    : TeschlODE_Shared_itinerary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:09:20.463993+00:00
-- url     : https://prove2.me/theorems/8794759e-0462-4451-a5d4-3a3f2f04977a
-- title:
--   The itinerary map $\varphi : \Lambda \to \Sigma_2$ of the tent map (11.23)
-- statement:
--   Fix $\mu > 2$ and set $I_0 = [0, \mu^{-1}]$, $I_1 = [1 - \mu^{-1}, 1]$. The **itinerary map** sends $x \in \Lambda$ to the sequence $\varphi(x) = (x_n)_{n \in \mathbb{N}_0} \in \Sigma_2 = \{0,1\}^{\mathbb{N}_0}$ with
--   $$x_n = j \quad\text{if}\quad T_\mu^n(x) \in I_j .$$
--   It records which of the two intervals the $n$-th iterate visits.
--
--   This one definition serves chunk 09-interval-maps and chunk 11-horseshoe (in both, Theorem 11.5, p. 301; in 11 it was called `tentItinerary`).
--
--   **Formalization Note.** For $x \in \Lambda$ every iterate lies in $\Lambda \subseteq I_0 \cup I_1$, and $I_0 \cap I_1 = \emptyset$ for $\mu > 2$, so the rule "$x_n = 0$ if $T_\mu^n(x) \in I_0$, and $x_n = 1$ otherwise" is the book's. The Lean function is defined on all of $\mathbb{R}$; its values off $\Lambda$ carry no meaning and every theorem only uses $x \in \Lambda$. Sequences are functions $\mathbb{N} \to \mathrm{Fin}\,2$, indexed from $0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 300, §11.4, Eq. (11.23)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap

namespace TeschlODE.Shared

/-- Teschl, §11.4, p. 300, (11.23): the itinerary map `ϕ : Λ → Σ₂`, `ϕ(x)ₙ = j` if
`T_µⁿ(x) ∈ I_j`, where `I₀ = [0, 1/µ]` and `I₁ = [1 − 1/µ, 1]`. For `µ > 2` and `x ∈ Λ` every
iterate lies in `Λ ⊆ I₀ ∪ I₁` and `I₀ ∩ I₁ = ∅`, so `ϕ(x)ₙ = 0` iff `T_µⁿ(x) ∈ I₀`, which is how it
is written here. Values at points outside `Λ` carry no meaning. -/
noncomputable def itinerary (μ : ℝ) (x : ℝ) : ℕ → Fin 2 :=
  fun n => if (tentMap μ)^[n] x ∈ Set.Icc (0 : ℝ) (1 / μ) then 0 else 1

end TeschlODE.Shared


