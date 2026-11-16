-- Prove2me | Definitions.Def_OptHedgeGames_Supplement_Cascade
-- name    : OptHedgeGames_Supplement_Cascade
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:20:50.279167+00:00
-- url     : https://prove2.me/theorems/cb8ab66a-18e0-4bc2-a430-991905420443
-- title:
--   The cascade with a shared normalizer — actions $(j,w)$, utilities, $g_j$ (63) and the recurrence (64)
-- statement:
--   Fix $k\ge1$ blocks and $n\ge8k+1$ actions. A player has the actions $(j,w)$ with $1\le j\le k$ and $w\in V=\{\pm1,\pm i,\pm1\pm i\}$, and $n-8k$ neutral actions. With scores $z=(z_1,\dots,z_k)\in\mathbb C^k$ the strategy is
--   $$
--   p(j,w)=\frac{e^{\mathrm{Re}(\overline wz_j)}}{Z(z)},\qquad Z(z_1,\dots,z_k)=\sum_{j=1}^k\sum_{w\in V}e^{\mathrm{Re}(\overline wz_j)}+(n-8k).
--   $$
--
--   The coefficient $c$ is as in the single block, and $q(\pm1)=1$, $q(\pm i)=-1$, $q(1+i)=q(-1-i)=i/2$, $q(1-i)=q(-1+i)=-i/2$. Let $\kappa=\nu=1/64$, $\delta_1=\delta$ and $\delta_j=0$ for $j\ge2$. The utility of the own action $(j,v)$ against the opponent's action $(j',w)$ is
--   1. $\mathrm{Re}(\overline v\,\mu\,c(w)\,e^{-\mathrm{Re}(\overline w\delta)})$ (the table (47)) if $j=j'=1$;
--   2. $\mathrm{Re}(\overline v[-\kappa c(w)])$ if $j=j'\ge2$;
--   3. $\mathrm{Re}(\overline v\,\nu\,q(w)\,e^{-\mathrm{Re}(\overline w\delta_{j-1})})$ if $j'=j-1$;
--   4. $0$ otherwise; neutral actions have utility $0$.
--
--   With $S(u)=\sinh u_1+i\sinh u_2$ and $\Psi(u)=\sum_{w\in V}q(w)e^{\mathrm{Re}(\overline wu)}$,
--   $$
--   g_1(z)=\frac{2\mu S(z_1-\delta)}{Z(z)},\qquad g_j(z)=\frac{-2\kappa S(z_j)+\nu\Psi(z_{j-1}-\delta_{j-1})}{Z(z)}\quad(2\le j\le k),
--   $$
--   and the joint state $s=(z_j,\varrho_j)_{j\le k}\in\mathbb C^{2k}$ evolves by
--   $$
--   z_{j,t+1}=z_{j,t}+\eta[2g_j(z_t)-\varrho_{j,t}],\qquad \varrho_{j,t+1}=g_j(z_t),\qquad s_0=0,
--   $$
--   with one-step map $\Phi_{\mu,\delta}$. States are compared in the Euclidean norm of $\mathbb C^{2k}\cong\mathbb R^{4k}$.
--
--   These are the objects of Theorem 6.23, the construction behind the three-player lower bound.
--
--   **Formalization Note** Blocks are `Fin k`, 0-based: block `j` is the paper's block $j+1$. The actions are `(Fin k × Fin 8) ⊕ Fin (n - 8 * k)`, with $n$ elements for $n\ge8k$; $Z$ is the sum over all of them, each neutral action contributing $1$. `qCoef` lists $q$ in the order of `vtx`. The Euclidean distance is written out as `cascDist`.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), §6.4, (63)–(64), pp.39–40; q from §6.2, p.32 and Figure 5, p.26; Euclidean norm convention p.27

import Mathlib
import Definitions.Def_OptHedgeGames_Supplement_Block

namespace OptHedgeGames

namespace Supplement

/-- The **quadratic coefficient** `q`: `q(±1) = 1`, `q(±i) = −1`, `q(1+i) = q(−1−i) = i/2`,
`q(1−i) = q(−1+i) = −i/2`, indexed like `vtx` (Dagan, Eisen, Erez & Koren, *Optimistic Hedge in
General-Sum Games*, STOC 2027 submission manuscript (sha256 383e3793…), §6.2, p.32; Figure 5,
p.26). -/
noncomputable def qCoef : Fin 8 → ℂ :=
  ![1, 1, -1, -1, Complex.I / 2, Complex.I / 2, -Complex.I / 2, -Complex.I / 2]

/-- The self-interaction constant `κ = 1/64`
(manuscript sha256 383e3793…, §6.4, p.39, "κ = ν = 1/64 as in Lemma 6.15"). -/
noncomputable def kappa : ℝ := 1 / 64

/-- The coupling constant `ν = 1/64` (manuscript sha256 383e3793…, §6.4, p.39). -/
noncomputable def nu : ℝ := 1 / 64

/-- The **actions of player 1 (and of player 2) in the cascade** with `k` blocks and `n` actions:
the actions `(j, w)`, `1 ≤ j ≤ k`, `w ∈ V` (`Sum.inl (j, w)`, `w` indexing `vtx`), and the `n − 8k`
neutral actions (`Sum.inr`) (manuscript sha256 383e3793…, §6.4, p.39).

**Formalization Note** Blocks are `Fin k`, 0-based: the block `j : Fin k` is the paper's block
`j + 1`. For `n ≥ 8k + 1` (the hypothesis of Theorem 6.23) this type has exactly `n` elements. -/
abbrev CascadeAction (n k : ℕ) : Type := (Fin k × Fin 8) ⊕ Fin (n - 8 * k)

/-- The exponent `Re(w̄ z_j)` of the action `(j, w)` at the scores `z = (z₁, …, z_k)`; `0` for a
neutral action (manuscript sha256 383e3793…, §6.4, p.39). -/
def cascScore {n k : ℕ} (z : Fin k → ℂ) : CascadeAction n k → ℝ
  | Sum.inl (j, w) => pair (vtx w) (z j)
  | Sum.inr _ => 0

/-- The **shared normalizer** `Z(z₁, …, z_k) = Σ_{j=1}^k Σ_{w∈V} e^{Re(w̄z_j)} + (n − 8k)`, written as
a sum over all `n` actions, each neutral one contributing `e⁰ = 1`
(manuscript sha256 383e3793…, §6.4, p.39). -/
noncomputable def cascZ (n k : ℕ) (z : Fin k → ℂ) : ℝ :=
  ∑ τ : CascadeAction n k, Real.exp (cascScore z τ)

/-- The shift `δ_j` of block `j`: `δ₁ = δ` and `δ_j = 0` for `j ≥ 2`
(manuscript sha256 383e3793…, §6.4, p.39). Block `j : Fin k` is the paper's block `j + 1`. -/
def cascShift {k : ℕ} (δ : ℂ) (j : Fin k) : ℂ := if j.val = 0 then δ else 0

/-- The **utility in the cascade** of the own action `τ` against the opponent's action `σ`
(manuscript sha256 383e3793…, §6.4, p.39), for own action `(j, v)` and opponent action `(j′, w)`:
* `(47)`, `Re(v̄ µ c(w) e^{−Re(w̄δ)})`, if `j = j′ = 1`;
* the self-interaction `Re(v̄[−κc(w)])` if `j = j′ ≥ 2`;
* the coupling `Re(v̄ ν q(w) e^{−Re(w̄δ_{j−1})})` if `j′ = j − 1`;
* `0` otherwise; neutral actions have utility `0`, and an action against a neutral one gets `0`.

**Formalization Note** Blocks are 0-based: paper block `1` is `j.val = 0`, and `j′ = j − 1` reads
`j′.val + 1 = j.val`. -/
noncomputable def cascU {n k : ℕ} (μ δ : ℂ) : CascadeAction n k → CascadeAction n k → ℝ
  | Sum.inl (j, v), Sum.inl (j', w) =>
    if j = j' then
      (if j.val = 0 then
        ((starRingEnd ℂ) (vtx v) * μ * cCoef w * (Real.exp (-pair (vtx w) δ) : ℂ)).re
      else
        ((starRingEnd ℂ) (vtx v) * (-(kappa : ℂ) * cCoef w)).re)
    else if j'.val + 1 = j.val then
      ((starRingEnd ℂ) (vtx v) * (nu : ℂ) * qCoef w *
        (Real.exp (-pair (vtx w) (cascShift δ j')) : ℂ)).re
    else 0
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, _ => 0

/-- `S(u) = sinh u₁ + i sinh u₂` for `u = u₁ + iu₂` (manuscript sha256 383e3793…, §6.4, p.39). -/
noncomputable def sFun (u : ℂ) : ℂ := (Real.sinh u.re : ℂ) + Complex.I * (Real.sinh u.im : ℂ)

/-- `Ψ(u) = Σ_{w∈V} q(w) e^{Re(w̄u)}` (manuscript sha256 383e3793…, §6.4, p.39). -/
noncomputable def psiFun (u : ℂ) : ℂ := ∑ w : Fin 8, qCoef w * (Real.exp (pair (vtx w) u) : ℂ)

/-- The **block coefficients (63)**, for `z = (z₁, …, z_k)`:
`g₁(z) = 2µS(z₁ − δ)/Z(z)` and `g_j(z) = (−2κS(z_j) + νΨ(z_{j−1} − δ_{j−1}))/Z(z)` for `2 ≤ j ≤ k`
(manuscript sha256 383e3793…, (63), p.39).

**Formalization Note** Block `j : Fin k` is the paper's block `j + 1`; for `j.val ≥ 1` the previous
block is `⟨j.val − 1, _⟩`. -/
noncomputable def cascG (n k : ℕ) (μ δ : ℂ) (z : Fin k → ℂ) (j : Fin k) : ℂ :=
  if j.val = 0 then 2 * μ * sFun (z j - δ) / (cascZ n k z : ℂ)
  else
    let j' : Fin k := ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
    (-2 * (kappa : ℂ) * sFun (z j) + (nu : ℂ) * psiFun (z j' - cascShift δ j')) / (cascZ n k z : ℂ)

/-- The **one-step map `Φ_{µ,δ}` of (64)** on the joint state `s = (z_j, ϱ_j)_{j≤k} ∈ ℂ^{2k}`:
`z_j ↦ z_j + η[2g_j(z) − ϱ_j]`, `ϱ_j ↦ g_j(z)` (manuscript sha256 383e3793…, (64), p.40). -/
noncomputable def cascStep (n k : ℕ) (η : ℝ) (μ δ : ℂ) (s : (Fin k → ℂ) × (Fin k → ℂ)) :
    (Fin k → ℂ) × (Fin k → ℂ) :=
  (fun j => s.1 j + (η : ℂ) * (2 * cascG n k μ δ s.1 j - s.2 j), fun j => cascG n k μ δ s.1 j)

/-- The **trajectory of (64) from `s₀ = 0`** (the uniform start): `cascTraj n k η μ δ t = s_t`
(manuscript sha256 383e3793…, (64), p.40). -/
noncomputable def cascTraj (n k : ℕ) (η : ℝ) (μ δ : ℂ) (t : ℕ) : (Fin k → ℂ) × (Fin k → ℂ) :=
  (cascStep n k η μ δ)^[t] (0, 0)

/-- The **Euclidean distance** on `ℂ^{2k} ≅ ℝ^{4k}` between two joint states,
`∥s − s′∥ = (Σ_j |z_j − z′_j|² + |ϱ_j − ϱ′_j|²)^{1/2}` (manuscript sha256 383e3793…, p.27: "We use
the Euclidean norm on ℂ² ≅ ℝ⁴ unless another norm is specified", applied blockwise in §6.4). -/
noncomputable def cascDist {k : ℕ} (s s' : (Fin k → ℂ) × (Fin k → ℂ)) : ℝ :=
  Real.sqrt (∑ j, (‖s.1 j - s'.1 j‖ ^ 2 + ‖s.2 j - s'.2 j‖ ^ 2))

end Supplement

end OptHedgeGames


