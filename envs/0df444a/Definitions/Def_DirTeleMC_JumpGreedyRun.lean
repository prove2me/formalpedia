-- Prove2me | Definitions.Def_DirTeleMC_JumpGreedyRun
-- name    : DirTeleMC_JumpGreedyRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:35:48.952332+00:00
-- url     : https://prove2.me/theorems/1b44dcef-63d8-4aa8-9642-e842203590f9
-- title:
--   JUMPGREEDY (Algorithm 2) as a run relation
-- statement:
--   For an integer $\ell \ge 2$, JUMPGREEDY on an instance $(G, s, K, k)$ sets $\eta = 2\ell - 1$ and $\rho = \lceil k^{1/\ell}\rceil$ and:
--   1. sets best to the fallback schedule (line 2);
--   2. for $\theta = 1, \dots, k - 1$: sets $\Lambda = \ell(\theta + \rho + 1)$, $\mu = 20\eta\Lambda$, $\Gamma = 1/\ln(1 + 1/\mu)$; lets $J$ be the union of the structures returned by GREEDY(root of $\mathcal U_{\eta,\theta}$, $k$, $0$, $K$); if $J$ covers at least $k$ terminals, keeps $k$ of them and sets best to the shorter of best and SCHEDULE$(J)$;
--   3. returns best.
--
--   The relation contains every run of the algorithm: every way of resolving the choices left open in GREEDY, SCHEDULE, the fallback, the kept terminals, and "the shorter of" on equal lengths.
--
--   **Formalization Note** With $\Gamma = 1/\ln(1+1/\mu)$, $e^{y/\Gamma} = (1 + 1/\mu)^y$, so an exact rational implementation makes exactly the comparisons of this real relation.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Algorithm 2, p.24 (PDF p.25); §B.4 "The main algorithm", p.22 (PDF p.23)

import Mathlib
import Definitions.Def_DirTeleMC_GreedyLoop
import Definitions.Def_DirTeleMC_ScheduleRun
import Definitions.Def_DirTeleMC_FallbackRun
import Definitions.Def_DirTeleMC_rho

namespace DirTeleMC

open JTree

/-- **The scale of Algorithm 2 for the guess `θ`** (line 5, p.24): `Λ = ℓ(θ + ⌈k^{1/ℓ}⌉ + 1)`, `µ = 20ηΛ` with
`η = 2ℓ − 1`, and `Γ = 1/ln(1 + 1/µ)`.

**Formalization Note.** `Real.log` is the natural logarithm (p.8). Then `e^{y/Γ} = (1 + 1/µ)^y`, so an exact
rational implementation of Algorithm 1 makes exactly the comparisons of this real relation (p.22). -/
noncomputable def jgScale (ℓ k θ : ℕ) : ℝ :=
  1 / Real.log (1 + 1 / ((20 * (2 * ℓ - 1) * (ℓ * (θ + rho k ℓ + 1)) : ℕ) : ℝ))

/-- **A run of JUMPGREEDY (Algorithm 2) with parameter `ℓ`.**
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Algorithm 2, p.24, and §B.4 "The main algorithm", p.22.

`JumpGreedyRun ℓ I S` says that Algorithm 2 on the instance `I` can return `S`. There is a sequence
`best 0, best 1, …, best (k − 1)` of the values of the variable `best`:

1. `best 0` is a fallback schedule (line 2);
2. for every guess `θ = 1, …, k − 1` (line 4), the top call `GREEDY(root of U_{η,θ}, k, 0, K)` with
   `η = 2ℓ − 1` and the scale `Γ = jgScale ℓ k θ` (lines 5–6) returns some list `out`, and `J` is the union of
   the returned structures (they share the root, labelled `s`);
3. if `J` covers at least `k` terminals (line 7), some `k` of the covered terminals `Y` are kept, SCHEDULE(J)
   returns some `S_θ`, and `best θ` is the shorter of `best (θ − 1)` and `S_θ` (line 8), either one when their
   lengths are equal; otherwise `best θ = best (θ − 1)`;
4. `S = best (k − 1)` (line 11).

**Formalization Note.** All the choices the page leaves open (in GREEDY, SCHEDULE, the fallback, which `k`
covered terminals to keep, and "the shorter of" on equal lengths) are left open: the relation contains every
run, and every deterministic tie-breaking is one of them. For DTM (`k = |K|`) the kept set is `K`. -/
def JumpGreedyRun (ℓ : ℕ) (I : Inst) (S : Schedule I.n) : Prop :=
  ∃ best : ℕ → Schedule I.n,
    FallbackRun I (best 0) ∧
    (∀ θ, 1 ≤ θ → θ ≤ I.k - 1 →
      ∃ out : List (JTree I.n),
        GreedyRun I.adj θ (jgScale ℓ I.k θ) I.s (2 * ℓ - 1) I.k 0 I.K out ∧
        (I.k ≤ (I.K ∩ cov (2 * ℓ - 1) (join I.s out)).card →
          ∃ (Y : Finset (Fin I.n)) (Sθ : Schedule I.n),
            Y ⊆ I.K ∩ cov (2 * ℓ - 1) (join I.s out) ∧ Y.card = I.k ∧
            ScheduleRun I.s (join I.s out) Y Sθ ∧
            ((best θ = best (θ - 1) ∧ (best (θ - 1)).length ≤ Sθ.length) ∨
              (best θ = Sθ ∧ Sθ.length ≤ (best (θ - 1)).length))) ∧
        (¬ I.k ≤ (I.K ∩ cov (2 * ℓ - 1) (join I.s out)).card → best θ = best (θ - 1))) ∧
    S = best (I.k - 1)

end DirTeleMC


