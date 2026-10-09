-- Prove2me | Definitions.Def_KAdaptability_Bilinear_Program7
-- name    : KAdaptability_Bilinear_Program7
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:05:02.915296+00:00
-- url     : https://prove2.me/theorems/e3593ddb-b654-4426-9e41-08ee54e7c7ab
-- title:
--   The mixed-integer bilinear program (7) and the set Δ_K(ℓ)
-- statement:
--   Fix an instance of the two-stage robust binary program with constraint uncertainty, $\epsilon>0$ and a decision $(x,\{y^k\}_{k\in\mathcal K})$. For $\ell\in\mathcal L=\{0,\dots,L\}^K$ the paper defines, in the proof of Theorem 5 (p. ec8),
--   $$\Delta_K(\ell)=\{\lambda\in\mathbb R^K_+:\ e^\top\lambda=1,\ \lambda_k=0\ \ \forall k\in\mathcal K:\ell_k\neq 0\},$$
--   and writes $H_{\ell_k}$ for the $\ell_k$-th row of $H$ as a column vector.
--
--   Problem (7) minimizes $\tau$ over $x\in\mathcal X$, $y^k\in\mathcal Y$, $\tau\in\mathbb R$ and, **separately for every** $\ell\in\mathcal L$, auxiliary variables $\lambda(\ell)$, $\alpha(\ell)$, $\beta^k(\ell)$, $\gamma(\ell)$, subject to:
--
--   1. for every $\ell\in\partial\mathcal L$: $\lambda(\ell)\in\Delta_K(\ell)$, $\alpha(\ell)\in\mathbb R^R_+$, $\beta^k(\ell)\in\mathbb R^L_+$ ($k\in\mathcal K$), $\gamma(\ell)\in\mathbb R^K_+$ and
--   $$b^\top\alpha(\ell)-\sum_{k:\ \ell_k=0}(Tx+Wy^k)^\top\beta^k(\ell)+\sum_{k:\ \ell_k\neq0}\big([Tx+Wy^k]_{\ell_k}-\epsilon\big)\gamma_k(\ell)\le\tau,$$
--   $$A^\top\alpha(\ell)-\sum_{k:\ \ell_k=0}H^\top\beta^k(\ell)+\sum_{k:\ \ell_k\neq0}H_{\ell_k}\gamma_k(\ell)=Cx+\sum_{k\in\mathcal K}\lambda_k(\ell)Qy^k;$$
--   2. for every $\ell\in\mathcal L_+$: $\alpha(\ell)\in\mathbb R^R_+$, $\gamma(\ell)\in\mathbb R^K_+$ and
--   $$b^\top\alpha(\ell)+\sum_{k\in\mathcal K}\big([Tx+Wy^k]_{\ell_k}-\epsilon\big)\gamma_k(\ell)\le-1,\qquad A^\top\alpha(\ell)+\sum_{k\in\mathcal K}H_{\ell_k}\gamma_k(\ell)=0.$$
--
--   The definition also records the value of (7) at a fixed decision, the infimum of the feasible $\tau$, and the optimal value of (7), the infimum of $\tau$ over all decisions and feasible auxiliary variables, together with the vector $Cx+\sum_k\lambda_kQy^k$ and the weighted cost $\xi^\top Cx+\sum_k\lambda_k\,\xi^\top Qy^k$ used in the proof of Theorem 5.
--
--   **Formalization Note** Values are in the extended reals: the infimum of an empty set of $\tau$ is $+\infty$, and if every real $\tau$ is feasible the infimum is $-\infty$. Because $\ell_k=0$ names no row, $H_{\ell_k}$ and $[Tx+Wy^k]_{\ell_k}$ are given the placeholder value $0$ when $\ell_k=0$; program (7) only reads them for $\ell_k\neq 0$. The auxiliary variables are functions of $\ell$, so each $\ell$ has its own copy.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 19, Theorem 5, problem (7); p. ec8 (PDF p. 42), Proof of Theorem 5, definition of Δ_K(ℓ)

import Definitions.Def_KAdaptability_Bilinear_Problem

open Matrix

namespace KAdaptability.Bilinear

namespace Problem

variable {N M L nQ R : ℕ} (P : Problem N M L nQ R)

/-- `Δ_K(ℓ) = {λ ∈ ℝ^K_+ : e⊤λ = 1, λ_k = 0 ∀k ∈ 𝒦 : ℓ_k ≠ 0}`, the set defined in the proof of
Theorem 5 (p. ec8) and used in the statement of problem (7). -/
def DeltaK {K : ℕ} (ℓ : Fin K → Fin (L + 1)) : Set (Fin K → ℝ) :=
  {lam | (∀ k, 0 ≤ lam k) ∧ ∑ k, lam k = 1 ∧ ∀ k, ℓ k ≠ 0 → lam k = 0}

/-- `H_{ℓ_k}`, the `ℓ_k`-th row of `H` as a column vector (p. 19), for `ℓ_k ≠ 0`. The value `0`
at `ℓ_k = 0` is a placeholder that problem (7) never reads: every occurrence of `H_{ℓ_k}`
in (7) is in a sum over `k` with `ℓ_k ≠ 0`, or for `ℓ ∈ ℒ₊`. -/
def Hrow {K : ℕ} (ℓ : Fin K → Fin (L + 1)) (k : Fin K) : Fin nQ → ℝ :=
  if h : ℓ k = 0 then 0 else P.H ((ℓ k).pred h)

/-- `[Tx + Wy^k]_{ℓ_k}`, the `ℓ_k`-th component of `Tx + Wy^k`, for `ℓ_k ≠ 0`. The value `0` at
`ℓ_k = 0` is a placeholder that problem (7) never reads (see `Hrow`). -/
def lhsRow {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (ℓ : Fin K → Fin (L + 1))
    (k : Fin K) : ℝ :=
  if h : ℓ k = 0 then 0 else P.lhs x (y k) ((ℓ k).pred h)

/-- The objective of the dual LP for `ℓ ∈ ∂ℒ` (p. 19, p. ec9):
`b⊤α − Σ_{k : ℓ_k = 0} (Tx + Wy^k)⊤β^k + Σ_{k : ℓ_k ≠ 0} ([Tx + Wy^k]_{ℓ_k} − ε) γ_k`. -/
def dualObjBdry (ε : ℝ) {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ)
    (ℓ : Fin K → Fin (L + 1)) (α : Fin R → ℝ) (β : Fin K → Fin L → ℝ) (γ : Fin K → ℝ) : ℝ :=
  P.b ⬝ᵥ α - ∑ k ∈ Finset.univ.filter (fun k => ℓ k = 0), P.lhs x (y k) ⬝ᵥ β k
    + ∑ k ∈ Finset.univ.filter (fun k => ℓ k ≠ 0), (P.lhsRow x y ℓ k - ε) * γ k

/-- The left-hand side of the dual equality constraint for `ℓ ∈ ∂ℒ` (p. 19, p. ec9):
`A⊤α − Σ_{k : ℓ_k = 0} H⊤β^k + Σ_{k : ℓ_k ≠ 0} H_{ℓ_k} γ_k`. -/
def dualLhsBdry {K : ℕ} (ℓ : Fin K → Fin (L + 1)) (α : Fin R → ℝ) (β : Fin K → Fin L → ℝ)
    (γ : Fin K → ℝ) : Fin nQ → ℝ :=
  P.Aᵀ *ᵥ α - ∑ k ∈ Finset.univ.filter (fun k => ℓ k = 0), P.Hᵀ *ᵥ β k
    + ∑ k ∈ Finset.univ.filter (fun k => ℓ k ≠ 0), γ k • P.Hrow ℓ k

/-- The cost vector `Cx + Σ_{k∈𝒦} λ_k Qy^k` of the inner maximization over `ξ` (p. ec9). -/
def costVec {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (lam : Fin K → ℝ) : Fin nQ → ℝ :=
  P.C *ᵥ x + ∑ k, lam k • (P.Q *ᵥ y k)

/-- The weighted cost `ξ⊤Cx + Σ_{k∈𝒦} λ_k · ξ⊤Qy^k` of the reformulations in the proof of
Theorem 5 (p. ec8); it equals `(Cx + Σ_{k∈𝒦} λ_k Qy^k)⊤ξ`. -/
def lagCost {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (lam : Fin K → ℝ)
    (ξ : Fin nQ → ℝ) : ℝ :=
  P.firstCost ξ x + ∑ k, lam k * P.secondCost ξ (y k)

/-- Dual feasibility with objective value at most `τ`, for `ℓ ∈ ∂ℒ` and weights `λ`
(the dual LP on p. ec9, and the `∂ℒ` block of (7) apart from `λ(ℓ) ∈ Δ_K(ℓ)`):
`α ∈ ℝ^R_+`, `β^k ∈ ℝ^L_+` (`k ∈ 𝒦`), `γ ∈ ℝ^K_+`,
`b⊤α − Σ_{k : ℓ_k = 0} (Tx + Wy^k)⊤β^k + Σ_{k : ℓ_k ≠ 0} ([Tx + Wy^k]_{ℓ_k} − ε) γ_k ≤ τ` and
`A⊤α − Σ_{k : ℓ_k = 0} H⊤β^k + Σ_{k : ℓ_k ≠ 0} H_{ℓ_k} γ_k = Cx + Σ_{k∈𝒦} λ_k Qy^k`. -/
def DualBdry (ε : ℝ) {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ)
    (ℓ : Fin K → Fin (L + 1)) (lam : Fin K → ℝ) (τ : ℝ)
    (α : Fin R → ℝ) (β : Fin K → Fin L → ℝ) (γ : Fin K → ℝ) : Prop :=
  0 ≤ α ∧ (∀ k, 0 ≤ β k) ∧ 0 ≤ γ ∧
    P.dualObjBdry ε x y ℓ α β γ ≤ τ ∧
    P.dualLhsBdry ℓ α β γ = P.costVec x y lam

/-- The `ℒ₊` block of (7) (p. 19) for one `ℓ`: `α ∈ ℝ^R_+`, `γ ∈ ℝ^K_+`,
`b⊤α + Σ_{k∈𝒦} ([Tx + Wy^k]_{ℓ_k} − ε) γ_k ≤ −1` and `A⊤α + Σ_{k∈𝒦} H_{ℓ_k} γ_k = 0`. -/
def PlusBlock (ε : ℝ) {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ)
    (ℓ : Fin K → Fin (L + 1)) (α : Fin R → ℝ) (γ : Fin K → ℝ) : Prop :=
  0 ≤ α ∧ 0 ≤ γ ∧
    P.b ⬝ᵥ α + ∑ k, (P.lhsRow x y ℓ k - ε) * γ k ≤ -1 ∧
    P.Aᵀ *ᵥ α + ∑ k, γ k • P.Hrow ℓ k = 0

/-- Feasibility in the mixed-integer bilinear program (7) (p. 19) of the decision
`(x, {y^k})` with epigraph value `τ ∈ ℝ`: there are variables `λ(ℓ), α(ℓ), β^k(ℓ), γ(ℓ)`,
**one copy for every `ℓ ∈ ℒ`**, such that the `∂ℒ` block holds for every `ℓ ∈ ∂ℒ`
(including `λ(ℓ) ∈ Δ_K(ℓ)`) and the `ℒ₊` block holds for every `ℓ ∈ ℒ₊`.
The constraints `x ∈ 𝒳`, `y^k ∈ 𝒴` are not part of this predicate (see `IsDecision`). -/
def Feasible7 (ε : ℝ) {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) (τ : ℝ) : Prop :=
  ∃ (lam : (Fin K → Fin (L + 1)) → Fin K → ℝ) (α : (Fin K → Fin (L + 1)) → Fin R → ℝ)
    (β : (Fin K → Fin (L + 1)) → Fin K → Fin L → ℝ) (γ : (Fin K → Fin (L + 1)) → Fin K → ℝ),
    (∀ ℓ ∈ LBdry K L, lam ℓ ∈ DeltaK ℓ ∧
      P.DualBdry ε x y ℓ (lam ℓ) τ (α ℓ) (β ℓ) (γ ℓ)) ∧
    (∀ ℓ ∈ LPlus K L, P.PlusBlock ε x y ℓ (α ℓ) (γ ℓ))

/-- The value of problem (7) at a fixed decision `(x, {y^k})`: the infimum of the feasible
`τ`, in `EReal` (`⊤ = +∞` if no `τ` is feasible, `⊥ = −∞` if every `τ` is). -/
noncomputable def val7 (ε : ℝ) {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) : EReal :=
  sInf ((fun τ : ℝ => (τ : EReal)) '' {τ | P.Feasible7 ε x y τ})

/-- The optimal value of problem (7) (p. 19): the infimum of `τ` over all `(x, {y^k}) ∈ 𝒳 × 𝒴^K`
and all feasible auxiliary variables, in `EReal`. -/
noncomputable def opt7 (ε : ℝ) (K : ℕ) : EReal :=
  sInf ((fun τ : ℝ => (τ : EReal)) ''
    {τ | ∃ (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ), P.IsDecision x y ∧ P.Feasible7 ε x y τ})

end Problem

end KAdaptability.Bilinear


