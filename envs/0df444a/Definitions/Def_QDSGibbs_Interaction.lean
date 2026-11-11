-- Prove2me | Definitions.Def_QDSGibbs_Interaction
-- name    : QDSGibbs_Interaction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:13.443477+00:00
-- url     : https://prove2.me/theorems/60155897-4e9f-4079-9bc3-9a7db0406087
-- title:
--   Labelled interactions, restricted Hamiltonians $H_\Omega$, crossing interaction $W_{\partial B}$, $J_{\mathrm{int}}$, Gibbs states, and the nearest-neighbour chain
-- statement:
--   A **labelled interaction** is a finite family of on-site terms $V_i=V_i^*$ supported on $\{i\}$ and interaction terms $h_\alpha=h_\alpha^*$ supported on specified sets $X_\alpha$; its Hamiltonian is $H=\sum_iV_i+\sum_\alpha h_\alpha$. For a region $\Omega$, the **restricted Hamiltonian** keeps exactly the terms supported inside $\Omega$,
--
--   $$
--   H_\Omega=\sum_{i\in\Omega}V_i+\sum_{\alpha:\,X_\alpha\subseteq\Omega}h_\alpha,
--   $$
--
--   and for a block $B$ the **crossing interaction** is $W_{\partial B}=H-H_B-H_{B^c}$. The **interaction strength** is
--
--   $$
--   J_{\mathrm{int}}=\sup_{i\in\Lambda}\sum_{\alpha:\,i\in X_\alpha}\|h_\alpha\|,
--   $$
--
--   which excludes the on-site terms; $J_{\mathrm{int}}(H_\Omega)$ is the same quantity for the terms inside $\Omega$. The **Gibbs state** of an operator $K$ is $e^{-\beta K}/\mathrm{Tr}\,e^{-\beta K}$. The **nearest-neighbour chain** $H=\sum_{i=1}^NV_i+\sum_{i=1}^{N-1}W_i$ is the labelled interaction whose bond $i$ has support $\{i,i+1\}$ and term $W_i$; its standing assumptions are $V_i=V_i^*$ on site $i$ (any norm) and $W_i=W_i^*$ on sites $i,i+1$.
--
--   **Formalization Note** The structure holds data only; the Hermiticity and support conditions are `Interaction.IsValid` (general) and `IsChainHam` (chain). The bookkeeping bounds of (2.1) ($|X_\alpha|\le k$, diameter $\le r$, multiplicity $\le\nu$) are not imposed. $H_\Omega$ and its Gibbs state are full-space operators ($\sigma^\Omega_\beta\otimes\mathbb 1/\dim$). Chain sites and bonds are 0-based; at $N=1$ there are no bonds and $J_{\mathrm{int}}=0$.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), (2.1)–(2.4), pp.10–11; (5.1), p.39

import Mathlib
import Definitions.Def_QDSGibbs_traceNorm

open scoped Matrix

namespace QDSGibbs

/-- A **labelled interaction** on `N` sites with on-site terms (arXiv:2610.03578, held file sha256
ede55815…, (2.1), p.10): `H = Σ_{i ∈ Λ} V_i + Σ_{α ∈ A} h_α` with labels `α ∈ Fin m`, specified
supports `X_α` and terms `h_α`. Distinct labels may have the same support.

**Formalization Note** The data only; the conditions `V_i = V_i^*`, `supp V_i ⊆ {i}`,
`h_α = h_α^*`, `supp h_α ⊆ X_α` are `Interaction.IsValid`. The bookkeeping bounds of (2.1)
(`2 ≤ |X_α| ≤ k`, `diam X_α ≤ r`, each site in at most `ν` supports) are not imposed. -/
structure Interaction {N : ℕ} (d : Fin N → ℕ) where
  /-- number of labelled interaction terms -/
  m : ℕ
  /-- the specified support `X_α` of the term `h_α` -/
  X : Fin m → Finset (Fin N)
  /-- the interaction terms `h_α` (full-space operators) -/
  h : Fin m → Op d
  /-- the on-site terms `V_i` (full-space operators) -/
  V : Fin N → Op d

/-- The conditions of (2.1) (arXiv:2610.03578, p.10): `V_i = V_i^*` supported on `{i}`, and
`h_α = h_α^*` supported on `X_α`. The on-site terms may have arbitrary norms. -/
def Interaction.IsValid {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) : Prop :=
  (∀ i, (I.V i).IsHermitian ∧ SupportedOn {i} (I.V i)) ∧
  (∀ α, (I.h α).IsHermitian ∧ SupportedOn (I.X α) (I.h α))

/-- The Hamiltonian `H = Σ_i V_i + Σ_α h_α` (arXiv:2610.03578, (2.1), p.10). -/
def ham {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) : Op d :=
  ∑ i, I.V i + ∑ α, I.h α

open Classical in
/-- The **restricted Hamiltonian** `H_Ω = Σ_{i ∈ Ω} V_i + Σ_{α : X_α ⊆ Ω} h_α` (arXiv:2610.03578,
(2.3), p.11): exactly the labelled terms whose specified supports lie inside `Ω`.

**Formalization Note** As a full-space operator `H_Ω ⊗ 1_{Λ ∖ Ω}` (p.11: "When used as an operator on
`H_Λ`, it is extended by the identity"). -/
noncomputable def hamOn {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) (Ω : Finset (Fin N)) : Op d :=
  ∑ i ∈ Ω, I.V i + ∑ α ∈ Finset.univ.filter (fun α => I.X α ⊆ Ω), I.h α

/-- The **crossing interaction** `W_∂B = H − H⁰_B`, `H⁰_B = H_B + H_{B^c}` (arXiv:2610.03578, (2.4),
p.11). -/
noncomputable def cross {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) (B : Finset (Fin N)) : Op d :=
  ham I - hamOn I B - hamOn I Bᶜ

open Classical in
/-- The **interaction strength** `J_int = sup_{i ∈ Λ} Σ_{α : i ∈ X_α} ‖h_α‖` (arXiv:2610.03578, (2.2),
p.11). It excludes the on-site terms `V_i`.

**Formalization Note** A supremum of finitely many reals (a maximum for `N ≥ 1`); `‖·‖` is the
operator norm `opNorm`. -/
noncomputable def jint {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) : ℝ :=
  ⨆ i : Fin N, ∑ α ∈ Finset.univ.filter (fun α => i ∈ I.X α), opNorm (I.h α)

open Classical in
/-- The interaction strength `J_int(H_Ω) = sup_{i ∈ Ω} Σ_{α : i ∈ X_α ⊆ Ω} ‖h_α‖` of the restricted
Hamiltonian `H_Ω` (arXiv:2610.03578, (2.2) applied to (2.3), p.11).

**Formalization Note** The supremum is over all sites; for `i ∉ Ω` the sum is empty, so this is the
supremum over `Ω` (and `0` for `Ω = ∅`). `jintOn I univ = jint I`. -/
noncomputable def jintOn {N : ℕ} {d : Fin N → ℕ} (I : Interaction d) (Ω : Finset (Fin N)) : ℝ :=
  ⨆ i : Fin N, ∑ α ∈ Finset.univ.filter (fun α => i ∈ I.X α ∧ I.X α ⊆ Ω), opNorm (I.h α)

/-- The **Gibbs state** `e^{−βK} / Tr e^{−βK}` of an operator `K` (arXiv:2610.03578, (2.2), (2.3),
p.11). `σ_{β,H} = gibbs β (ham I)`.

**Formalization Note** For a restricted Hamiltonian, `gibbs β (hamOn I Ω)` is the full-space operator
`σ^Ω_β ⊗ 1_{Λ∖Ω} / dim H_{Λ∖Ω}`; it has the same marginals on `Ω` and the same expectations of
observables supported in `Ω` as `σ^Ω_β`. The matrix exponential is Mathlib's `NormedSpace.exp`. -/
noncomputable def gibbs {n : Type} [Fintype n] [DecidableEq n] (β : ℝ) (K : Matrix n n ℂ) :
    Matrix n n ℂ :=
  (NormedSpace.exp ((-β) • K)).trace⁻¹ • NormedSpace.exp ((-β) • K)

/-- The bond `{b, b+1}` of a chain (0-based sites; paper bond `i` joins paper sites `i, i+1`). -/
def bond {N : ℕ} (b : Fin (N - 1)) : Finset (Fin N) :=
  {⟨b.val, by omega⟩, ⟨b.val + 1, by omega⟩}

/-- The **nearest-neighbour chain** `H = Σ_{i=1}^N V_i + Σ_{i=1}^{N−1} W_i` (arXiv:2610.03578, (5.1),
p.39) as a labelled interaction: label `b` has support `{b, b+1}` and term `W_b`.

**Formalization Note** 0-based: bond `b : Fin (N−1)` is the paper's `W_{b+1}`. Then
`jint (chain V W) = max_i (‖W_{i−1}‖ + ‖W_i‖)` (missing bonds count as `0`); for `N = 1` there are
no bonds and `J_int = 0`. -/
def chain {N : ℕ} {d : Fin N → ℕ} (V : Fin N → Op d) (W : Fin (N - 1) → Op d) : Interaction d where
  m := N - 1
  X := bond
  h := W
  V := V

/-- The standing assumptions of §5 on the chain terms (arXiv:2610.03578, (5.1), p.39): `V_i = V_i^*`
acts on site `i` (arbitrary norm) and `W_i = W_i^*` acts on sites `i, i+1`. -/
def IsChainHam {N : ℕ} {d : Fin N → ℕ} (V : Fin N → Op d) (W : Fin (N - 1) → Op d) : Prop :=
  (∀ i, (V i).IsHermitian ∧ SupportedOn {i} (V i)) ∧
  (∀ b, (W b).IsHermitian ∧ SupportedOn (bond b) (W b))

end QDSGibbs


