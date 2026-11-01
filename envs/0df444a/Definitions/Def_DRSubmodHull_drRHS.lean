-- Prove2me | Definitions.Def_DRSubmodHull_drRHS
-- name    : DRSubmodHull_drRHS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:09.177539+00:00
-- url     : https://prove2.me/theorems/bbd1d1de-9cf6-4578-b31b-19a4d5fa316c
-- title:
--   The coefficients $t(\delta,z)$ of (26)–(29) and the right-hand side of the DR inequality (38)
-- statement:
--   For $\psi\in\Psi$ let (eq. (26))
--   $$
--   \eta_\psi(z)=\frac{z_\psi-(u_\psi-\lfloor u_\psi\rfloor)\,z_{\mathrm{ch}(\psi)}}{u_{\mathrm{ch}(\psi)}-u_\psi}.
--   $$
--   Let $z_0=u_0=0$. For a permutation $\delta$, $k\in\{1,\dots,|\mathcal V|\}$, $i=\delta(k)$ and $i^\triangle=i^\triangle(\mathcal T^{\delta,k-1})$ (eqs. (27)–(29)):
--   $$
--   t(\delta,z)_k=\begin{cases}\dfrac{\eta_\psi(z)-z_{i^\triangle}}{\lfloor u_\psi\rfloor-u_{i^\triangle}}, & i=\psi\in\Psi,\ \mathrm{ch}(\psi)\notin\mathcal T^{\delta,k-1},\\[2mm] \dfrac{z_i-\eta_\psi(z)}{u_i-\lfloor u_\psi\rfloor}, & \text{else if } i^\triangle=\psi\in\Psi,\\[2mm] \dfrac{z_i-z_{i^\triangle}}{u_i-u_{i^\triangle}}, & \text{otherwise,}\end{cases}
--   $$
--   and $t(\delta,z)_0=1$, $t(\delta,z)_{|\mathcal V|+1}=0$ (p.16). The value $t(\delta,z)_k$ depends only on $(\delta(1),\dots,\delta(k))$; the module defines it as a function of the set of earlier vertices and the new vertex.
--
--   The **DR inequality** associated with $\delta$ is (eq. (38))
--   $$
--   w\;\ge\;\sum_{k=1}^{|\mathcal V|} t(\delta,z)_k\,\big[f(P(\delta,k))-f(P(\delta,k-1))\big],
--   $$
--   which is linear in $(z,w)$; the module defines its right-hand side.
--
--   **Formalization Note** Lean's $x/0=0$; for a valid permutation every denominator is positive (Observation 5.9), which is the only case any statement uses. The index $k$ is the paper's 1-based index; $t$ is $0$ beyond $|\mathcal V|+1$.
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, §5, pp.15–16, eqs. (26)–(29); §6, p.22, eq. (38)

import Mathlib
import Definitions.Def_DRSubmodHull_Ppt
import Definitions.Def_DRSubmodHull_IsValidPerm

set_option autoImplicit false

open Classical

noncomputable section

namespace DRSubmodHull

/-- **`η_ψ`** (arXiv:2211.07726v2, §5, p.15, eq. (26)):
`η_ψ(z) = (z_ψ − (u_ψ − ⌊u_ψ⌋) z_{ch(ψ)}) / (u_{ch(ψ)} − u_ψ)`. -/
def eta {V : Type*} (A : V → V → Prop) (u : V → ℝ) (ψ : V) (z : V → ℝ) : ℝ :=
  (z ψ - (u ψ - (Int.floor (u ψ) : ℝ)) * z (child A ψ)) / (u (child A ψ) - u ψ)

/-- `z₀ = 0` (p.15): the coordinate of `z` at an `Option V`, with `none` (index `0`) giving `0`. -/
def zAt {V : Type*} (z : V → ℝ) : Option V → ℝ
  | some j => z j
  | none => 0

/-- **The `t`-value of a vertex `i` placed after the set `S` of earlier vertices**
(arXiv:2211.07726v2, §5, p.15, eqs. (27)–(29)). Writing `i△ = i△(S)`, with `z₀ = u₀ = 0`:
* (27) if `i = ψ ∈ Ψ` and `ch(ψ) ∉ S`: `(η_ψ(z) − z_{i△}) / (⌊u_ψ⌋ − u_{i△})`;
* (28) else if `i△ = ψ ∈ Ψ`: `(z_i − η_ψ(z)) / (u_i − ⌊u_ψ⌋)`;
* (29) otherwise: `(z_i − z_{i△}) / (u_i − u_{i△})`.

With `S = 𝒯^{δ,k−1}` and `i = δ(k)` this is the paper's `t(δ, z)_k`; as the paper notes (p.16),
it depends only on the partial permutation `(δ(1), …, δ(k))`.

**Formalization Note.** Lean's `x / 0 = 0`; by Observation 5.9 every denominator is positive
when `(…, i)` is a prefix of a valid permutation, which is the only case any statement uses. -/
def tCore {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) (S : Finset V) (i : V)
    (z : V → ℝ) : ℝ :=
  if i ∈ Psi A N u ∧ child A i ∉ S then
    (eta A u i z - zAt z (tri A S i)) / ((Int.floor (u i) : ℝ) - uAt u (tri A S i))
  else
    match tri A S i with
    | some ψ =>
      if ψ ∈ Psi A N u then (z i - eta A u ψ z) / (u i - (Int.floor (u ψ) : ℝ))
      else (z i - z ψ) / (u i - u ψ)
    | none => z i / u i

/-- **`t(δ, z)_k`** (arXiv:2211.07726v2, §5, pp.15–16, eqs. (27)–(29)) for every `k ∈ ℕ`, with the
paper's 1-based index `k`: `t(δ, z)₀ = 1`, `t(δ, z)_k = tCore(𝒯^{δ,k−1}, δ(k), z)` for
`1 ≤ k ≤ |𝒱|`, and `t(δ, z)_{|𝒱|+1} = 0` (also `0` beyond).

**Formalization Note.** The paper's `δ(k)` is `δ ⟨k − 1, _⟩` in Lean. -/
def tval {V : Type*} [Fintype V] (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (δ : Fin (Fintype.card V) ≃ V) (z : V → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1
  else if h : k - 1 < Fintype.card V then tCore A N u (Tset δ (k - 1)) (δ ⟨k - 1, h⟩) z
  else 0

/-- **The right-hand side of the DR inequality associated with `δ`** (arXiv:2211.07726v2, §6,
p.22, eq. (38)): `∑_{k=1}^{|𝒱|} t(δ, z)_k [f(P(δ, k)) − f(P(δ, k − 1)))]`, where
`P(δ, k) = P(𝒯^{δ,k})`. The DR inequality is `w ≥ drRHS δ z`. -/
def drRHS {V : Type*} [Fintype V] (A : V → V → Prop) (N : Set V) (u : V → ℝ)
    (f : (V → ℝ) → ℝ) (δ : Fin (Fintype.card V) ≃ V) (z : V → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (Fintype.card V),
    tval A N u δ z k * (f (Ppt A N u (Tset δ k)) - f (Ppt A N u (Tset δ (k - 1))))

end DRSubmodHull


