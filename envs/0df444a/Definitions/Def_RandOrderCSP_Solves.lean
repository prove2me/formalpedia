-- Prove2me | Definitions.Def_RandOrderCSP_Solves
-- name    : RandOrderCSP_Solves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:09:19.425909+00:00
-- url     : https://prove2.me/theorems/471dc66d-dd30-4a1a-bf39-d7c6a0e9126a
-- title:
--   Solving $\text{MAX-CSP}_{\beta,\gamma}(\Gamma)$ in the random-order model
-- statement:
--   A family $A$ of randomized algorithms **solves** $\text{MAX-CSP}_{\beta',\gamma'}(\Gamma)$ on instances with at most $\mathrm{bound}(n)$ constraints, with failure function $\delta$, if for all $n$, all $1\le m\le\mathrm{bound}(n)$ and all instances $\Phi$ of $\mathrm{CSP}(\Gamma)$ on $[n]$ with $m$ constraints:
--
--   1. if $\mathrm{opt}_\Phi\ge\gamma'$ then $\mathbb P_\pi\big[\mathbb P_{\mathcal R}[A\text{ outputs YES}]\ge 2/3\big]\ge 1-\delta(n)$;
--   2. if $\mathrm{opt}_\Phi\le\beta'$ then $\mathbb P_\pi\big[\mathbb P_{\mathcal R}[A\text{ outputs NO}]\ge 2/3\big]\ge 1-\delta(n)$.
--
--   Here $\pi$ is a uniform permutation of the constraints and $\mathcal R$ is the internal randomness.
--
--   **Formalization Note** The paper's $1-o(1)$ is the explicit $1-\delta(n)$, and theorems require $\delta\to0$. The family is indexed by $(n,m)$ because a lower-bound algorithm may depend on $m$ (p.1); an upper-bound algorithm ignores it.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), pp.1–2

import Mathlib
import Definitions.Def_RandOrderCSP_StreamAlg

namespace RandOrderCSP

/-- `P_ℛ[ALG answers b on the stream l]`: the probability over the internal randomness. -/
noncomputable def probAnswer {U : Type} {s : ℕ} (A : RandAlg U s) (l : List U) (b : Bool) : ℝ :=
  (A.toOuterMeasure {D | D.answer l = b}).toReal

/-- `P_𝒪[P_ℛ[ALG answers b] ≥ 2/3]`: the fraction of the `m!` orders `π` of the instance `Φ` for
which the algorithm answers `b` with probability at least `2/3` over its internal randomness. -/
noncomputable def goodOrderFrac {U : Type} {s m : ℕ} (A : RandAlg U s) (Φ : Fin m → U)
    (b : Bool) : ℝ := by
  classical
  exact ((Finset.univ.filter
      (fun π : Equiv.Perm (Fin m) => (2 : ℝ) / 3 ≤ probAnswer A (streamOf Φ π) b)).card : ℝ) /
    (Fintype.card (Equiv.Perm (Fin m)) : ℝ)

/-- **Solving MAX-CSP_{β′,γ′}(Γ) in the random-order model** (pp.1–2).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), pp.1–2: "If 𝒪 denotes the randomness in the
order of the constraints, and ℛ denotes the internal randomness of the algorithm ALG, we say that ALG
solves the problem MAX-CSP_{β,γ}(Γ) if for every instance Φ satisfying either the YES case with
opt^CSP(Φ) ≥ γ, or the NO case with opt^CSP(Φ) ≤ β, we have
P_𝒪[P_ℛ[ALG correctly outputs YES/NO] ≥ 2/3] ≥ 1 − o(1)."

`Solves Γ β' γ' bound s A δ`: for every `n` and every `m` with `1 ≤ m ≤ bound n`, the randomized
`s n`-space algorithm `A n m` is correct on every instance of `CSP(Γ)` on `[n]` with `m` constraints
in the YES case (`opt ≥ γ'`, answer `true`) and in the NO case (`opt ≤ β'`, answer `false`), for a
fraction at least `1 - δ n` of the `m!` stream orders.

**Formalization Note.** The `o(1)` is the explicit failure function `δ` (the theorems require
`δ → 0` as `n → ∞`, uniformly over instances). The algorithm family is indexed by `(n, m)` (p.1:
"the algorithm is allowed to depend on n and (for the purpose of lower bounds) we also allow it to
depend on m"); an algorithm that depends on `n` only is the family `fun n _ => A n`. Instances have
`m ≥ 1` constraints (p.13); the random order is a uniform permutation of the `m` indexed constraints,
i.e. a uniformly random ordering of the multiset. -/
def Solves {k : ℕ} {Sig : Type} (Γ : Set ((Fin k → Sig) → Bool)) (β' γ' : ℝ) (bound : ℕ → ℕ)
    (s : ℕ → ℕ) (A : (n m : ℕ) → RandAlg (Constraint k Sig n) (s n)) (δ : ℕ → ℝ) : Prop :=
  ∀ (n m : ℕ), 1 ≤ m → m ≤ bound n → ∀ Φ : Fin m → Constraint k Sig n,
    (toCSP Φ).IsInstanceOf Γ →
      (γ' ≤ (toCSP Φ).opt → 1 - δ n ≤ goodOrderFrac (A n m) Φ true) ∧
      ((toCSP Φ).opt ≤ β' → 1 - δ n ≤ goodOrderFrac (A n m) Φ false)

end RandOrderCSP


