-- Prove2me | Definitions.Def_NoMenuRevenue186_TrustedXOS_Scores
-- name    : NoMenuRevenue186_TrustedXOS_Scores
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:56.456001+00:00
-- url     : https://prove2.me/theorems/a1a8a3e9-a1bd-4e2c-8854-12448793941d
-- title:
--   Simulated outcomes, tested scores, and planted conditional laws
-- statement:
--   Fix a protocol $\Pi$, seller seed $(A,u)$, and any $R$-element buyer collection $B\subseteq\mathcal F$, allowing unsupported and disjoint pairs. For every $j=0,\ldots,K$, run the same seller strategy at the actual prior $D_{A,u}$ against the buyer strategy at $v_{B,2^j}$, yielding $(X_j,p_j)$ and quality $q_j=w_B(X_j)$.
--
--   The test $E_j$ requires $p_j\ge0$, $p_j\le2^j q_j$, and $2^j q_j-p_j\ge2^j q_\ell-p_\ell$ for every $\ell=0,\ldots,K$. Define
--
--   $$\tau_j=\frac{p_j}{2^j}\mathbf1[E_j],\qquad
--   \mu_j=\mathbb E_{\pi_j}[\tau_j],\quad
--   \mu'_j=\mathbb E_{\pi'}[\tau_j],\quad
--   \Delta=\frac{1-\epsilon}{\alpha}-\frac2{K+1}.$$
--
--   Here $\pi_j$ is the uniform law of balanced-labeled pairs having a unique intersection of label $j$, whereas $\pi'$ is the uniform disjoint law with the same balanced labels. Each planted expectation uses its own conditional law. Both are implemented by finite uniform sampling, with the construction's validity conditions guaranteeing nonempty domains.
--
--   The tests give a meaningful score without strengthening supported buyer-PIC into global incentive compatibility.
-- source:
--   Aggarwal, Dang, Rubinstein, Zhao, STOC 2027 submission #186 (October 2026), printed p.17–18, PDF p.19–20, Sections 4.3–4.4

import Mathlib
import Definitions.Def_NoMenuRevenue186_TrustedXOS_Construction

namespace NoMenuRevenue186.TrustedXOS
namespace Construction
variable {n : ℕ}

noncomputable def simulated (C : Construction n) (P : Protocol n) (a : C.Seed)
    (B : Finset (Bundle n)) (j : Fin (C.K + 1)) : Outcome n :=
  P.outcome (C.prior a) (C.value B j)

noncomputable def quality (C : Construction n) (P : Protocol n) (a : C.Seed)
    (B : Finset (Bundle n)) (j : Fin (C.K + 1)) : ℝ :=
  C.base B (C.simulated P a B j).bundle

/-- E_j tests all K+1 simulated outcomes, also on unsupported type pairs. -/
def Passes (C : Construction n) (P : Protocol n) (a : C.Seed)
    (B : Finset (Bundle n)) (j : Fin (C.K + 1)) : Prop :=
  0 ≤ (C.simulated P a B j).payment ∧
  (C.simulated P a B j).payment ≤ (2 : ℝ) ^ j.val * C.quality P a B j ∧
  ∀ l : Fin (C.K + 1),
    (2 : ℝ) ^ j.val * C.quality P a B l - (C.simulated P a B l).payment ≤
    (2 : ℝ) ^ j.val * C.quality P a B j - (C.simulated P a B j).payment

noncomputable def score (C : Construction n) (P : Protocol n) (a : C.Seed)
    (B : Finset (Bundle n)) (j : Fin (C.K + 1)) : ℝ := by
  classical
  exact if C.Passes P a B j then (C.simulated P a B j).payment / (2 : ℝ) ^ j.val else 0

abbrev ScoreInput (C : Construction n) := C.Seed × Finset (Bundle n)

/-- Uniform planted conditional law at the specified true label, not a common
    law for all j. Balanced labels make this exactly the source conditioning. -/
noncomputable def planted (C : Construction n) (j : Fin (C.K + 1)) : FiniteLaw C.ScoreInput := by
  classical
  exact FiniteLaw.uniform (Finset.univ.filter (fun x : C.ScoreInput =>
    x.1 ∈ C.seeds ∧ x.2 ⊆ C.F ∧ x.2.card = C.R ∧
    ∃ S, x.1.1 ∩ x.2 = {S} ∧ x.1.2 S = j)) ((∅, fun _ => 0), ∅)

/-- The disjoint law has the same balanced-label law as every planted law. -/
noncomputable def disjointLaw (C : Construction n) : FiniteLaw C.ScoreInput := by
  classical
  exact FiniteLaw.uniform (Finset.univ.filter (fun x : C.ScoreInput =>
    x.1 ∈ C.seeds ∧ x.2 ⊆ C.F ∧ x.2.card = C.R ∧ Disjoint x.1.1 x.2))
    ((∅, fun _ => 0), ∅)

noncomputable def mu (C : Construction n) (P : Protocol n) (j : Fin (C.K + 1)) : ℝ :=
  (C.planted j).expect (fun x => C.score P x.1 x.2 j)

noncomputable def muDisjoint (C : Construction n) (P : Protocol n) (j : Fin (C.K + 1)) : ℝ :=
  C.disjointLaw.expect (fun x => C.score P x.1 x.2 j)

noncomputable def gap (C : Construction n) (α : ℝ) : ℝ := (1 - C.ε) / α - 2 / (C.K + 1 : ℝ)

end Construction
end NoMenuRevenue186.TrustedXOS


