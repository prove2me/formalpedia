-- Prove2me | Definitions.Def_DRSubmodHull_CZ
-- name    : DRSubmodHull_CZ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:20.727985+00:00
-- url     : https://prove2.me/theorems/8f69180b-b261-49f9-ad61-c387bc127a2a
-- title:
--   $\Psi$, Assumptions 1 and 2, Property 4.2, and the polyhedron $\mathcal{CZ}$ with the MIR inequalities (6a)–(6c)
-- statement:
--   Let $(\mathcal G,N,u)$ be as in `DRSubmodHull.Zset`. Write $\lfloor\cdot\rfloor,\lceil\cdot\rceil$ for floor and ceiling.
--
--   1. $\Psi=\{\psi\in\mathcal V: u_\psi\notin\mathbb Z,\ R^+(\psi)\cap N\neq\emptyset\}$, the vertices with fractional upper bound and an integer descendant (p.6).
--   2. **Assumption 1** (p.6): no two elements of $\Psi$ lie on a common directed path (no element of $\Psi$ is a proper descendant of another), and every child of every $\psi\in\Psi$ is an integer variable.
--   3. **Property 4.2** (p.6): every $\psi\in\Psi$ has exactly one child $\rho$, and $\rho\in N$ with $u_\rho=\lceil u_\psi\rceil$. The child is written $\mathrm{ch}(\psi)$.
--   4. **Assumption 2** (p.26): for every $\psi\in\Psi$ with $u_\psi>1$, $u_i=\lceil u_\psi\rceil$ for all $i\in R^+(\psi)\setminus\{\psi\}$.
--   5. The polyhedron (6a)–(6c) (p.8)
--   $$
--   \mathcal{CZ}=\Big\{z\ge 0:\ z_i\le u_i\ \forall i,\quad z_i-z_j\le 0\ \forall (i,j)\in\mathcal A,\quad -z_{\mathrm{ch}(\psi)}+\frac{z_\psi}{u_\psi-\lfloor u_\psi\rfloor}\le\frac{\lfloor u_\psi\rfloor(\lceil u_\psi\rceil-u_\psi)}{u_\psi-\lfloor u_\psi\rfloor}\ \forall\psi\in\Psi\Big\}.
--   $$
--   The last family are the **mixed-integer rounding (MIR) inequalities**.
--
--   $\mathcal{CZ}$ is the paper's candidate for $\mathrm{conv}(\mathcal Z(\mathcal G,u))$ (Theorem 4.21); the assumptions are the standing hypotheses of §§4–7.
--
--   **Formalization Note** $\mathrm{ch}(\psi)$ is a chosen out-neighbour of $\psi$ (and $\psi$ itself if there is none); every statement that uses it assumes Property 4.2, under which it is the unique child. The paper's convention $\lfloor\alpha\rfloor=\alpha-1$ for integer $\alpha$ (p.4) never applies: floors are taken only of $u_\psi$, $\psi\in\Psi$, which are not integers.
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, §4, p.6 (Ψ, Assumption 1, Property 4.2), p.8 ((6a)–(6c), ch(ψ)), p.26 (Assumption 2)

import Mathlib
import Definitions.Def_DRSubmodHull_Zset

set_option autoImplicit false

open Classical

noncomputable section

namespace DRSubmodHull

/-- `Ψ := {ψ ∈ 𝒱 : u_ψ ∉ ℤ, R⁺(ψ) ∩ N ≠ ∅}` (arXiv:2211.07726v2, §4, p.6): the vertices with a
fractional upper bound that have at least one integer descendant. -/
def Psi {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) : Set V :=
  {ψ | (¬ ∃ k : ℤ, u ψ = k) ∧ ∃ j ∈ N, Relation.ReflTransGen A ψ j}

/-- **Assumption 1** (arXiv:2211.07726v2, p.6): "There can be at most one `ψ ∈ Ψ` in any directed
path of `𝒢`. For any `ψ ∈ Ψ`, `ch(ψ) ⊆ N`."

**Formalization Note.** In a directed rooted forest two vertices lie on a common directed path iff
one is a descendant of the other, so the first clause says that no element of `Ψ` is a proper
descendant of another. -/
def Assumption1 {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) : Prop :=
  (∀ ψ ∈ Psi A N u, ∀ ψ' ∈ Psi A N u, Relation.ReflTransGen A ψ ψ' → ψ = ψ') ∧
    (∀ ψ ∈ Psi A N u, ∀ j : V, A ψ j → j ∈ N)

/-- **Property 4.2** (arXiv:2211.07726v2, p.6): "For any `ψ ∈ Ψ`, `ch(ψ) = {ρ}` such that `ρ ∈ N`
and `u_ρ = ⌈u_ψ⌉`." -/
def Property42 {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) : Prop :=
  ∀ ψ ∈ Psi A N u, ∃ ρ : V, (∀ j : V, A ψ j ↔ j = ρ) ∧ ρ ∈ N ∧ u ρ = (Int.ceil (u ψ) : ℝ)

/-- **Assumption 2** (arXiv:2211.07726v2, p.26): "When there exists a fractionally upper bounded
continuous variable `ψ ∈ Ψ` with `u_ψ > 1`, we assume that `u_i = ⌈u_ψ⌉` for all
`i ∈ R⁺(ψ) \ {ψ}`" (for every such `ψ`). -/
def Assumption2 {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) : Prop :=
  ∀ ψ ∈ Psi A N u, 1 < u ψ → ∀ i : V, Relation.ReflTransGen A ψ i → i ≠ ψ →
    u i = (Int.ceil (u ψ) : ℝ)

/-- **The child `ch(ψ)`** (arXiv:2211.07726v2, p.8: "Every `ψ ∈ Ψ` has exactly one child, so by
slightly abusing notation, we denote the index of the child of `ψ` by `ch(ψ)`").

**Formalization Note.** A chosen out-neighbour of `ψ` (and `ψ` itself if it has none). Under
Property 4.2, which is a hypothesis of every statement of this mission, every `ψ ∈ Ψ` has exactly
one child, and `child A ψ` is that child. -/
def child {V : Type*} (A : V → V → Prop) (ψ : V) : V :=
  if h : ∃ j, A ψ j then h.choose else ψ

/-- **The set `𝒞𝒵`** (arXiv:2211.07726v2, §4, p.8, (6a)–(6c)):
`𝒞𝒵 := {z ∈ ℝ₊^{n+m} : z_i ≤ u_i ∀ i (6a); z_i − z_j ≤ 0 ∀ (i, j) ∈ 𝒜 (6b);
−z_{ch(ψ)} + z_ψ/(u_ψ − ⌊u_ψ⌋) ≤ ⌊u_ψ⌋(⌈u_ψ⌉ − u_ψ)/(u_ψ − ⌊u_ψ⌋) ∀ ψ ∈ Ψ (6c)}`.
The rows (6c) are the mixed-integer rounding (MIR) inequalities.

**Formalization Note.** `⌊·⌋`, `⌈·⌉` are `Int.floor`, `Int.ceil`. The paper's convention
`⌊α⌋ = α − 1` for integer `α` (p.4) is never triggered: the floor is applied only to `u_ψ`, `ψ ∈ Ψ`,
which is not an integer, so the denominators `u_ψ − ⌊u_ψ⌋` are positive. -/
def CZ {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) : Set (V → ℝ) :=
  {z | 0 ≤ z ∧ z ≤ u ∧ (∀ i j : V, A i j → z i - z j ≤ 0) ∧
    ∀ ψ ∈ Psi A N u,
      -z (child A ψ) + z ψ / (u ψ - (Int.floor (u ψ) : ℝ)) ≤
        (Int.floor (u ψ) : ℝ) * ((Int.ceil (u ψ) : ℝ) - u ψ) / (u ψ - (Int.floor (u ψ) : ℝ))}

end DRSubmodHull


