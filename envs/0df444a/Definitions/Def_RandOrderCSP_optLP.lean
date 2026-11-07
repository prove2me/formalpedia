-- Prove2me | Definitions.Def_RandOrderCSP_optLP
-- name    : RandOrderCSP_optLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:59.988708+00:00
-- url     : https://prove2.me/theorems/f13e040c-4ee3-40bb-b141-60f10aa0fe1f
-- title:
--   The basic LP value $\mathrm{opt}^{LP}_\Phi$
-- statement:
--   Let $\Phi=(H,f)$ be a CSP. A **distribution-labeling** assigns to each edge $j$ a distribution $D(j)$ on $\Sigma^k$. It is **1-consistent** if for all $j,j'\in\mathcal E_H$ and $\ell,\ell'\in[k]$ with $M_H(j,\ell)=M_H(j',\ell')$, the $\ell$-th marginal of $D(j)$ equals the $\ell'$-th marginal of $D(j')$. The LP value is
--
--   $$\mathrm{opt}^{LP}_\Phi=\max_{D\text{ 1-consistent}}\ \mathbb E_{j\in\mathcal E_H,\,x\sim D(j)}\big[f(j)(x)\big].$$
--
--   This is the relaxation whose power decides the random-order streaming complexity in the mission's goal. The distributions need not be products.
--
--   **Formalization Note** The maximum is written as a supremum over a set that is nonempty for a nonempty alphabet and bounded by $1$, so it equals the paper's maximum.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.3, p.14

import Mathlib
import Definitions.Def_RandOrderCSP_CSP

namespace RandOrderCSP

/-- A probability vector on a finite set: nonnegative entries summing to one (`Δ(S)`, p.11). -/
def IsDistr {S : Type} [Fintype S] (p : S → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- The `ℓ`-th coordinate marginal of a distribution `p` on `Σ^k`. -/
noncomputable def marginal {k : ℕ} {Sig : Type} [Fintype Sig] [DecidableEq Sig]
    (p : (Fin k → Sig) → ℝ) (ℓ : Fin k) (σ : Sig) : ℝ :=
  ∑ x : Fin k → Sig, if x ℓ = σ then p x else 0

/-- **The basic LP** (§3.3, p.14).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.3, p.14: "Let D : ℰ_H → Δ(Σ^k) be an
edge-coloring of H, which assigns to each edge a distribution on Σ^k. We say D is 1-consistent if …
for every j, j′ ∈ ℰ_H and ℓ, ℓ′ ∈ [k], if M_H(j, ℓ) = M_H(j′, ℓ′), then the ℓ-th marginal of D(j)
and the ℓ′-th marginal of D(j′) are identical. … val_Φ(D) := E_{j∈ℰ_H, x∈D(j)}[(f(j))(x)], and
correspondingly opt^LP_Φ := max_{D 1-consistent} val_Φ(D)."

`IsOneConsistent Φ D` says that every `D j` is a distribution on `Σ^k` and any two incidences of the
same vertex (in the same or in different edges) have equal marginals.

**Formalization Note.** `opt^LP` is the supremum of `val_Φ(D)` over all 1-consistent `D`. The set
is nonempty when `Σ` is nonempty (point masses of an assignment, Proposition 3.9) and bounded above
by `1`, so the supremum is the paper's maximum (which is attained, the feasible set being compact). The
distributions `D j` are arbitrary, not product distributions. -/
def IsOneConsistent {k : ℕ} {Sig V E : Type} [Fintype Sig] [DecidableEq Sig]
    (Φ : CSP k Sig V E) (D : E → (Fin k → Sig) → ℝ) : Prop :=
  (∀ j, IsDistr (D j)) ∧
    ∀ j j' ℓ ℓ', Φ.H.M j ℓ = Φ.H.M j' ℓ' → ∀ σ, marginal (D j) ℓ σ = marginal (D j') ℓ' σ

/-- `val_Φ(D) := E_{j ∈ ℰ_H} E_{x ∼ D(j)} [f(j)(x)]`. -/
noncomputable def valLP {k : ℕ} {Sig V E : Type} [Fintype Sig] [Fintype E]
    (Φ : CSP k Sig V E) (D : E → (Fin k → Sig) → ℝ) : ℝ :=
  (1 / (Fintype.card E : ℝ)) * ∑ j, ∑ x : Fin k → Sig, D j x * (if Φ.f j x then (1 : ℝ) else 0)

/-- `opt^LP_Φ := max_{D 1-consistent} val_Φ(D)` (p.14). -/
noncomputable def optLP {k : ℕ} {Sig V E : Type} [Fintype Sig] [DecidableEq Sig] [Fintype E]
    (Φ : CSP k Sig V E) : ℝ :=
  sSup {t | ∃ D, IsOneConsistent Φ D ∧ valLP Φ D = t}

end RandOrderCSP


