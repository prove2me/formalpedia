-- Prove2me | Definitions.Def_LaconicBarrier_SecureHonest
-- name    : LaconicBarrier_SecureHonest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:28.911225+00:00
-- url     : https://prove2.me/theorems/23ce692e-b934-4b1d-a102-92490d8523cf
-- title:
--   Security against the honest-prover reduction $\mathcal R \circ \mathcal P$
-- statement:
--   Let $\Pi = (\mathcal V, \mathcal P)$ be a two-message argument for an NP relation $\mathcal R$ with witness bound $q$, and $\mathcal R$ a $k$-query, $T$-time reduction to $(\mathcal C, c)$. For a statement $x$ and a string $w$, $\widetilde{\mathcal P}_{x,w}$ answers each query $pk$ with $\mathcal P(pk, x, w)$ if $(x, w) \in \mathcal R$, and with a fixed dummy response otherwise.
--
--   The **honest-prover reduction** $\mathcal R \circ \mathcal P$ takes auxiliary input $(x, z, w_1, \dots, w_k)$, runs $\mathcal R(1^\lambda, x, z)$ and answers its $j$-th query with $\widetilde{\mathcal P}_{x, w_j}$. Its allowed auxiliary inputs at $(\lambda, n)$ are those with $|x| = n$, $|z| \le T(\lambda, n)$ and $|w_j| \le q(n)$. The game $(\mathcal C, c)$ is **$\Gamma$-secure against $\mathcal R \circ \mathcal P$** at the reduction's target-parameter map if it is $\Gamma$-secure against this algorithm; with $\Gamma = T$, **secure against $\mathcal R \circ \mathcal P$**.
--
--   **Formalization Note** The dummy response is a parameter; the witness list has exactly $k(\lambda, n)$ entries.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 6.1, p.37

import Mathlib
import Definitions.Def_LaconicBarrier_LaconicArg
import Definitions.Def_LaconicBarrier_Reduction_winProb
import Definitions.Def_LaconicBarrier_SecureAgainst

namespace LaconicBarrier

open Classical in
/-- The oracle `P̃_{x, w_j}` answering the `j`-th query `pk` of the honest-prover reduction (Jain,
Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), Definition 6.1, p.37: "answer
each query `pk` with `P(pk, x, w)` if `(x, w) ∈ R`, and with a fixed dummy response otherwise"),
with `w = w_j` the `j`-th string of `ws` (the empty string beyond its end). -/
noncomputable def honestOracle (A : LaconicArg) (Rel : List Bool → List Bool → Prop)
    (dummy x : List Bool) (ws : List (List Bool)) : ℕ → List Bool → PMF (List Bool) :=
  fun j pk => if Rel x (ws.getD j []) then A.proverPMF pk x (ws.getD j []) else PMF.pure dummy

/-- **Security against the honest-prover reduction** `R ∘ P` (Jain, Mathialagan, Roy, STOC 2027
submission (manuscript sha256 1af78662…), Definition 6.1, p.37): `R ∘ P` takes the auxiliary input
`(x, z, w₁, …, w_k)`, runs `R(1^λ, x, z)` and answers its `j`-th query with `P̃_{x, w_j}`; its allowed
auxiliary inputs at `(λ, n)` are those with `|x| = n`, `|z| ≤ T(λ, n)` and `|w_j| ≤ q(n)`. The game
`(C, c)` is Γ-secure against `R ∘ P` at `f` (the reduction's target-parameter map) if it is Γ-secure
against this algorithm (`SecureAgainst`, Definition 4.14); with `Γ = T` this is "secure against
`R ∘ P`".

**Formalization Note** The dummy response is a parameter. The witness list has exactly
`k(λ, n)` entries. -/
def SecureHonest (G : Game) (A : LaconicArg) (Rel : List Bool → List Bool → Prop)
    (q : ℕ → ℕ) (R : Reduction) (k T : ℕ → ℕ → ℕ) (dummy : List Bool) (p : ℕ → ℕ)
    (Γ : ℕ → ℕ → ℕ) : Prop :=
  SecureAgainst (α := List Bool × List Bool × List (List Bool)) G
    (fun lam a => R.winProb G (honestOracle A Rel dummy a.1 a.2.2) lam a.1 (PMF.pure a.2.1))
    (fun lam n => {a | a.1.length = n ∧ a.2.1.length ≤ T lam n ∧ a.2.2.length = k lam n ∧
      ∀ w ∈ a.2.2, w.length ≤ q n})
    p Γ

end LaconicBarrier


