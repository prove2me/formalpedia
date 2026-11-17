-- Prove2me | Definitions.Def_LaconicBarrier_Supplement_SecureHonestAd
-- name    : LaconicBarrier_Supplement_SecureHonestAd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:30:44.266803+00:00
-- url     : https://prove2.me/theorems/0a1a7ddd-ed0d-4651-a7bf-7f2c80d5456c
-- title:
--   Security against the honest-prover reduction $\mathcal R\circ\mathcal P$, adaptive form
-- statement:
--   Let $\Pi = (G, P, V)$ be a SNARG for $\mathcal R$ with witness bound $q$, and let $(\mathcal R, F)$ be a $k$-query, $T$-time black-box reduction from its adaptive soundness to a game $(\mathcal C, c)$ with target-parameter map $f$. For a pair $(x_j, w_j)$, let $\tilde P_{x_j, w_j}$ answer a proving key $\mathsf{pk}$ with $P(\mathsf{pk}, x_j, w_j)$ if $(x_j, w_j) \in \mathcal R$ and with a fixed dummy response otherwise.
--
--   The **honest-prover reduction** $\mathcal R \circ P$, adaptive form, takes the auxiliary input $(1^n, z, (x_1, w_1), \dots, (x_k, w_k))$, runs $\mathcal R(1^\lambda, 1^n, z)$, and answers its $j$-th query $\mathsf{pk}$ with
--   $$
--   \bigl(x_j,\ \tilde P_{x_j, w_j}(\mathsf{pk})\bigr).
--   $$
--   Its allowed auxiliary inputs at $(\lambda, n)$ have $|z| \le T(\lambda, n)$, exactly $k(\lambda, n)$ pairs, $|x_j| = n$ and $|w_j| \le q(n)$. The game $(\mathcal C, c)$ is **$\Gamma$-secure against $\mathcal R\circ P$ at $f$** if it is $\Gamma$-secure against this algorithm in the sense of Definition 4.14 (the published `SecureAgainst`); with $\Gamma = T$ this is "secure against $\mathcal R \circ P$".
--
--   This is the only hardness hypothesis of Theorems 6.8 and 6.10; it is implied by $T$-hardness of $(\mathcal C, c)$ at $f$.
--
--   **Formalization Note** It is built on the published `SecureAgainst` exactly as the published non-adaptive `SecureHonest`. The reply pair is the tuple code used by the adaptive-soundness game. The dummy response is a parameter.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 6.1, p.37 (last paragraph)

import Mathlib
import Definitions.Def_LaconicBarrier_Supplement_SNARG
import Definitions.Def_LaconicBarrier_Reduction_winProb
import Definitions.Def_LaconicBarrier_SecureAgainst

namespace LaconicBarrier.Supplement

open Classical in
/-- The oracle answering the `j`-th query `pk` of the honest-prover reduction in the **adaptive**
form (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and
SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Definition 6.1, p.37: "the `j`th query
is answered with `(x_j, P̃_{x_j,w_j}(pk))`", where `P̃_{x,w}` answers with `P(pk, x, w)` if
`(x, w) ∈ R` and with a fixed dummy response otherwise). The pair `(x_j, w_j)` is the `j`-th entry of
`ps` (the pair of empty strings beyond its end); the reply is the tuple code `tup [x_j, π]`, as in
`SNARG.adaptiveSource`. -/
noncomputable def honestOracleAd (S : SNARG) (Rel : List Bool → List Bool → Prop)
    (dummy : List Bool) (ps : List (List Bool × List Bool)) : ℕ → List Bool → PMF (List Bool) :=
  fun j pk =>
    if Rel (ps.getD j ([], [])).1 (ps.getD j ([], [])).2 then
      (S.proverPMF pk (ps.getD j ([], [])).1 (ps.getD j ([], [])).2).map
        (fun π => QAdvFew.PoQOracle.tup [(ps.getD j ([], [])).1, π])
    else PMF.pure (QAdvFew.PoQOracle.tup [(ps.getD j ([], [])).1, dummy])

/-- **Security against the honest-prover reduction `R ∘ P`, adaptive form** (Jain, Mathialagan, Roy,
STOC 2027 submission (manuscript sha256 1af78662…), Definition 6.1, p.37, last paragraph: "For
adaptive soundness, `x` is replaced by `1ⁿ` and each `w_j` by a pair `(x_j, w_j)` with `|x_j| = n`").
`R ∘ P` takes the auxiliary input `(1ⁿ, z, (x₁, w₁), …, (x_k, w_k))`, runs `R(1^λ, 1ⁿ, z)` and answers
its `j`-th query with `honestOracleAd`; its allowed auxiliary inputs at `(λ, n)` have `|z| ≤ T(λ, n)`,
exactly `k(λ, n)` pairs, `|x_j| = n` and `|w_j| ≤ q(n)`. The game `(C, c)` is `Γ`-secure against
`R ∘ P` if it is `Γ`-secure against this algorithm (`SecureAgainst`, Definition 4.14); with `Γ = T`
this is "secure against `R ∘ P` at `f`".

**Formalization Note** Built on the published `SecureAgainst` exactly as the published
non-adaptive `SecureHonest`; the dummy response is a parameter. -/
def SecureHonestAd (G : Game) (S : SNARG) (Rel : List Bool → List Bool → Prop) (q : ℕ → ℕ)
    (R : Reduction) (k T : ℕ → ℕ → ℕ) (dummy : List Bool) (p : ℕ → ℕ) (Γ : ℕ → ℕ → ℕ) : Prop :=
  SecureAgainst (α := List Bool × List Bool × List (List Bool × List Bool)) G
    (fun lam a => R.winProb G (honestOracleAd S Rel dummy a.2.2) lam a.1 (PMF.pure a.2.1))
    (fun lam n => {a | a.1 = unary n ∧ a.2.1.length ≤ T lam n ∧ a.2.2.length = k lam n ∧
      ∀ xw ∈ a.2.2, xw.1.length = n ∧ xw.2.length ≤ q n})
    p Γ

end LaconicBarrier.Supplement


