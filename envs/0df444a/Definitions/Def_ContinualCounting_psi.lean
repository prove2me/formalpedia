-- Prove2me | Definitions.Def_ContinualCounting_psi
-- name    : ContinualCounting_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:45:20.549503+00:00
-- url     : https://prove2.me/theorems/9f209dba-eccf-4ee3-8f1c-6b631f27ab3f
-- title:
--   The attack vectors $\psi^i$ and $\mu^i$
-- statement:
--   The attack vectors have one coordinate for each node of $\mathcal T^s$ at even depth $<h$, and a dummy coordinate $\Lambda$. For $i\in\mathcal L(\mathcal T^s)$: $\psi^i_\Lambda=2^{-h/4}$, and for $u$ at depth $2d$,
--   $$\psi^i_u=\begin{cases}0&i\notin\mathcal L(\mathcal T^u),\\-2^{-(h/2-d)/2}&i\in\mathcal L(\mathcal T^{\ell(u)}),\\2^{-(h/2-d)/2}&i\in\mathcal L(\mathcal T^{r(u)}).\end{cases}$$
--   For a selection $\mathcal J,\{J_d\}$: $\mu^i_\Lambda=0$, and for $d\in\mathcal J$, $u\in J_d$,
--   $$\mu^i_u=\begin{cases}2^{-d/2}\mathbf 1\{i\in\mathcal L(\mathcal T^{r(\ell(u))})\}&s_{d+1}=r,\\-2^{-d/2}\mathbf 1\{i\in\mathcal L(\mathcal T^{\ell(r(u))})\}&s_{d+1}=\ell,\end{cases}$$
--   while $\mu^i_u=0$ for every other $u$.
--
--   These are the Haar-type linear measurement and the signal vector of the adversary.
--
--   **Formalization Note** The zero clause of $\psi^i$ is taken from p.12 and from App. C; the loop of Algorithm 1, p.26, omits it, and without it $\|\psi^i\|_2^2\neq1$. Coordinates are `Option Node`, with `none` for $\Lambda$.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), p.12 (PDF p.13), Algorithm 1, p.26 (PDF p.27), and App. C, p.41 (PDF p.42)

import Mathlib
import Definitions.Def_ContinualCounting_InTs
import Definitions.Def_ContinualCounting_medianMechanism

set_option autoImplicit false

namespace ContinualCounting

/-- **The attack vector `ψ^i`.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), p.12 and
App. C, p.41: `ψ^i_Λ = 2^{−h/4}` on the dummy coordinate `Λ`; for `u` at depth `2d`, `ψ^i_u = 0` if
`i ∉ L(T^u)`, `−2^{−(h/2−d)/2}` if `i ∈ L(T^{ℓ(u)})` and `2^{−(h/2−d)/2}` if `i ∈ L(T^{r(u)})`.

**Formalization Note.** `Option Node` is the coordinate type, `none` being `Λ`. The ancestor-only
vector is the one of p.12 and of App. C's proof of Lemma 6; the loop of Algorithm 1, p.26, omits the
clause `ψ^i_u = 0` for `i ∉ L(T^u)`, and with that omission `∥ψ^i∥₂² ≠ 1`. Exponents are real. -/
noncomputable def psi (h : ℕ) (i : Fin (2 ^ h)) : Option Node → ℝ
  | none => (2 : ℝ) ^ (-(h : ℝ) / 4)
  | some u =>
    if IsUnder h (left u) i then -(2 : ℝ) ^ (-((h : ℝ) / 2 - ((u.1 / 2 : ℕ) : ℝ)) / 2)
    else if IsUnder h (right u) i then (2 : ℝ) ^ (-((h : ℝ) / 2 - ((u.1 / 2 : ℕ) : ℝ)) / 2)
    else 0

open Classical in
/-- **The signal vector `µ^i`.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…),
Algorithm 1, p.26: `µ^i_Λ = 0`; for `d ∈ J` and `u ∈ J_d`, `µ^i_u = 2^{−d/2} 1{i ∈ L(T^{r(ℓ(u))})}` if
`s_{d+1} = r` and `µ^i_u = −2^{−d/2} 1{i ∈ L(T^{ℓ(r(u))})}` otherwise; `µ^i_u = 0` for every other `u`.
The depth of `u` is `2d`, so `d = u.1 / 2`. -/
noncomputable def mu (h : ℕ) (s : Fin (h / 2) → Bool) (J : Finset ℕ) (Js : ℕ → Finset Node)
    (i : Fin (2 ^ h)) : Option Node → ℝ
  | none => 0
  | some u =>
    if u.1 / 2 ∈ J ∧ u ∈ Js (u.1 / 2) then
      if letter s (u.1 / 2) then
        (2 : ℝ) ^ (-((u.1 / 2 : ℕ) : ℝ) / 2) * (if IsUnder h (right (left u)) i then 1 else 0)
      else
        -(2 : ℝ) ^ (-((u.1 / 2 : ℕ) : ℝ) / 2) * (if IsUnder h (left (right u)) i then 1 else 0)
    else 0

/-- The inner product over the coordinates of the attack: the nodes of `T^s` at even depth `< h`, and
the dummy `Λ` (p.27). -/
noncomputable def attackInner (h : ℕ) (s : Fin (h / 2) → Bool) (f g : Option Node → ℝ) : ℝ :=
  ∑ c ∈ Finset.insertNone (outputNodes h s), f c * g c

end ContinualCounting


