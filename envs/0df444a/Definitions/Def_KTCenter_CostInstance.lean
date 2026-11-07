-- Prove2me | Definitions.Def_KTCenter_CostInstance
-- name    : KTCenter_CostInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:26:47.66369+00:00
-- url     : https://prove2.me/theorems/60e8ac07-1d9c-4f6a-971f-14538b256c53
-- title:
--   Cost instance: tables $A_i,u_{iv},q_i,\lambda_v,W$ with the requirements of (6)–(7)
-- statement:
--   A **cost instance** consists of $n\ge1$ inputs, a finite set $U$ of variables, for each $v\in U$ a nonempty allowed-key set $P_v$ of at most $K$ rationals, a partition $\mathcal B$ of $U$ into nonempty blocks, constants $A_i$, single-key costs $u_{iv}$, pair costs $q_i$, change bounds $\lambda_v$ and a rational $W$. Its surrogate cost is (6):
--
--   $$\tilde C_i(p)=A_i+\sum_{v\in U}u_{iv}(p_v)+\sum_{B\in\mathcal B}\sum_{\substack{u,v\in B\\u<v}}q_i(u,p_u,v,p_v)\qquad(p\in\mathcal P(U)).$$
--
--   The requirements are: $A_i$ and $u_{iv}$ are nonnegative rationals; $q_i$ is symmetric, takes values in $[0,1]$, and vanishes on a repeated candidate and across blocks; $\lambda_v\ge0$ and $|\tilde C_i(p)-\tilde C_i(p')|\le\lambda_v$ whenever $p,p'$ agree outside $v$; $W\ge1$; and, for fixed positive rationals $C_0,C_1$, (7):
--
--   $$Q_0:=\sum_{B\in\mathcal B}|B|^2\le C_0W,\qquad \Lambda:=\sum_{v\in U}\lambda_v\le C_1W.$$
--
--   This is the input of the joint optimization of Sections 5.3–6 (Theorem 6.1).
--
--   **Formalization Note** All data are finite tables: variables are `Fin N`, keys are listed increasingly as `key v : Fin (k v) → ℚ`, and the cost tables take key indices, so they have no values off the allowed keys. Blocks are the nonempty fibres of a labelling `blk`. $K$, $C_0$, $C_1$ are parameters of the type.
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), "Surrogate cost", eqs. (6)–(7), p.15 (PDF p.17)

import Mathlib

namespace KTCenter

/-- **The tables of a cost instance**, "Surrogate cost", p.15 (PDF p.17).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…), §3.

**Formalization Note.** All data are finite tables. The variables `U` are `Fin N`, in increasing
label order, and `P_v` is listed increasingly as `key v : Fin (k v) → ℚ`. The tables `u` and `q`
take key *indices*, so a table has no values off the allowed keys. `blk` names the block of each
variable, so `ℬ` is the family of nonempty fibres of `blk`. -/
structure CostData where
  /-- the number of inputs -/
  n : ℕ
  /-- the number of variables `|U|` -/
  N : ℕ
  /-- `k v = |P_v|` -/
  k : Fin N → ℕ
  /-- the allowed keys -/
  key : (v : Fin N) → Fin (k v) → ℚ
  /-- the block of a variable -/
  blk : Fin N → ℕ
  /-- the constants `Aᵢ` -/
  A : Fin n → ℚ
  /-- the single-key costs `uᵢᵥ` -/
  u : Fin n → (v : Fin N) → Fin (k v) → ℚ
  /-- the pair costs `qᵢ` -/
  q : Fin n → (u : Fin N) → Fin (k u) → (v : Fin N) → Fin (k v) → ℚ
  /-- the change bounds `λ_v` -/
  lam : Fin N → ℚ
  /-- the rational `W` -/
  W : ℚ

namespace CostData

variable (D : CostData)

/-- The partition `ℬ`: the nonempty fibres of `blk`. -/
def blocks : Finset (Finset (Fin D.N)) :=
  Finset.univ.image fun v => Finset.univ.filter fun u => D.blk u = D.blk v

/-- An allowed assignment `p ∈ 𝒫(U)`, as key indices. -/
abbrev Assign : Type := (v : Fin D.N) → Fin (D.k v)

/-- **Surrogate cost**, eq. (6), p.15:
`C̃ᵢ(p) = Aᵢ + Σ_{v∈U} uᵢᵥ(p_v) + Σ_{B∈ℬ} Σ_{u<v in B} qᵢ(u, p_u, v, p_v)`. -/
def cost (i : Fin D.n) (p : D.Assign) : ℚ :=
  D.A i + ∑ v, D.u i v (p v) +
    ∑ B ∈ D.blocks, ∑ x ∈ (B ×ˢ B).filter (fun x => x.1 < x.2),
      D.q i x.1 (p x.1) x.2 (p x.2)

/-- `Q₀ = Σ_{B∈ℬ} |B|²`, eq. (7). -/
def Q0 : ℕ := ∑ B ∈ D.blocks, B.card ^ 2

/-- `Λ = Σ_{v∈U} λ_v`, eq. (7). -/
def Lam : ℚ := ∑ v, D.lam v

end CostData

/-- **Cost instance**, "Surrogate cost", p.15 (PDF p.17), with the size bound `K` and constants
`C₀`, `C₁` of eq. (7): the tables of `CostData` and the requirements of pp.15.

Verbatim requirements: "Here Aᵢ and the single-key cost values are nonnegative rationals. The pair
costs qᵢ are symmetric and take rational values in [0, 1]; they are zero when both arguments refer
to the same candidate or when the candidates belong to different subsets of ℬ."

**Formalization Note.** `1 ≤ n` is Theorem 1.1's standing assumption, `1 ≤ k v` is "finite nonempty
set" (p.14) and `key v` lists `P_v` strictly increasingly. `K`, `C₀`, `C₁` are type parameters, so
that a machine for fixed `K, C₀, C₁` is a function on one type. -/
structure CostInstance (K : ℕ) (C₀ C₁ : ℚ) extends CostData where
  one_le_n : 1 ≤ n
  one_le_k : ∀ v, 1 ≤ k v
  k_le : ∀ v, k v ≤ K
  key_strictMono : ∀ v, StrictMono (key v)
  A_nonneg : ∀ i, 0 ≤ A i
  u_nonneg : ∀ i v a, 0 ≤ u i v a
  q_nonneg : ∀ i u a v b, 0 ≤ q i u a v b
  q_le_one : ∀ i u a v b, q i u a v b ≤ 1
  q_symm : ∀ i u a v b, q i u a v b = q i v b u a
  q_self : ∀ i v a b, q i v a v b = 0
  q_cross : ∀ i u a v b, blk u ≠ blk v → q i u a v b = 0
  lam_nonneg : ∀ v, 0 ≤ lam v
  lam_bound : ∀ (i : Fin n) (v : Fin N) (p p' : toCostData.Assign),
    (∀ u, u ≠ v → p u = p' u) → |toCostData.cost i p - toCostData.cost i p'| ≤ lam v
  one_le_W : 1 ≤ W
  Q0_le : (toCostData.Q0 : ℚ) ≤ C₀ * W
  Lam_le : toCostData.Lam ≤ C₁ * W

namespace CostInstance

variable {K : ℕ} {C₀ C₁ : ℚ} (I : CostInstance K C₀ C₁)

instance : Nonempty (Fin I.n) := ⟨⟨0, I.one_le_n⟩⟩

instance (v : Fin I.N) : Nonempty (Fin (I.k v)) := ⟨⟨0, I.one_le_k v⟩⟩

/-- `max_{i∈[n]} C̃ᵢ(p)`. -/
def maxCost (p : I.Assign) : ℚ := Finset.univ.sup' Finset.univ_nonempty fun i => I.cost i p

/-- `min_{q∈𝒫(U)} max_{i∈[n]} C̃ᵢ(q)`, eq. (75). -/
def minMaxCost : ℚ := Finset.univ.inf' Finset.univ_nonempty I.maxCost

end CostInstance

end KTCenter


