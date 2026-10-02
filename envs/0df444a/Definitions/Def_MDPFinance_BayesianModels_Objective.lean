-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_Objective
-- name    : MDPFinance_BayesianModels_Objective
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:22:52.784005+00:00
-- url     : https://prove2.me/theorems/17d87f22-ca08-47d7-9586-96be9eea2c82
-- title:
--   The Bayesian Model's expected total reward $J_N$
-- statement:
--   This definition gives the Bayesian Model's own optimization objective, following
--   Bäuerle and Rieder's Eq. (5.2) specialized to a fixed unknown parameter $\theta$.
--
--   For a policy $\pi$ and $k$ stages to go, the expected reward-to-go from history $(xs,as,zs)$ at
--   absolute time $n$, holding $\theta$ fixed, is
--   $$
--   V_k^\pi(\theta) = \mathbb E\Big[\sum_{j=n}^{n+k-1} r(X_j,\theta,A_j) + g(X_{n+k},\theta)\Big],
--   $$
--   where the expectation integrates the continuation over the disturbance $Z_{n+1}$ against its
--   density $q_Z(x_n,\theta,a_n,\cdot)$, and the observable state advances deterministically via
--   $T^X$.
--
--   The value of $\pi$ over the whole $N$-stage problem from $x \in E_X$ integrates this out over
--   the prior:
--   $$
--   J_N^\pi(x) := \int_\Theta V_N^\pi(\theta)\, Q_0(\mathrm d\theta),
--   \qquad
--   J_N(x) := \sup_{\pi \in \tilde\Pi_N} J_N^\pi(x).
--   $$
--
--   **Formalization Note.** This mirrors `MDPFinance.POMDP.PartiallyObservableMDM.JNpi`/`JN`
--   (chunk `05a`) specialized to the Bayesian Model's explicit disturbance machinery.
--
--   **Moderation note.** The values $V^\pi$, $J_N^\pi$, $J_N$ are in $[-\infty,\infty]$ (`erealIntegral`, Lebesgue integrals of positive and negative parts), and the chapter's standing **Integrability Assumption** (p. 151) is `IntegrabilityAssumption`, stated through the positive-part recursion `VposPi`. With real Bochner integrals a stage with expectation $-\infty$ was recorded as $0$, and the two sides of Theorem 5.4.7 could differ.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 150, Eq. (5.2) (specialized)

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Policy
import Definitions.Def_MDPFinance_BayesianModels_Operators

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.BayesianModels

variable {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace Z] [Nonempty A] [Nonempty Z]

/-- The value `V_{k,n}^π(xs,as,zs,θ) := 𝔼[Σ_{j=n}^{n+k-1} r(X_j,θ,A_j) + g(X_{n+k},θ)]` of policy
`π` over the next `k` stages, from history `(xs,as,zs)`, fixed (unknown) parameter `θ`, at
absolute time `n` (Bäuerle–Rieder, p. 150, PDF 163, `V_n^π` specialized to the Bayesian Model:
`θ` is never updated, and the state advances deterministically via `T^X` driven by `Z_{n+1}`,
whose law given `(x_n,θ,a_n)` has density `q_Z(x_n,θ,a_n,\cdot)` w.r.t. `ν`). Values are in
`[-∞,∞]` through `erealIntegral`, so that under the chapter's Integrability Assumption (finite
expected positive parts) they are the book's expectations in `[-∞,∞)`. -/
noncomputable def BayesModel.Vpi (M : BayesModel EX Θ A Z) (π : Policy EX A Z) :
    (k : ℕ) → (n : ℕ) → (xs : ℕ → EX) → (as : ℕ → A) → (zs : ℕ → Z) → (θ : Θ) → EReal
  | 0, n, xs, _, _, θ => (M.g (xs n, θ) : EReal)
  | (k + 1), n, xs, as, zs, θ =>
      let a := π n xs as zs
      (M.r (xs n, θ, a) : EReal) + (M.β : EReal) *
        erealIntegral (M.nu.withDensity (fun z => ENNReal.ofReal (M.qZ (xs n) θ a z)))
          (fun z => M.Vpi π k (n + 1) (Function.update xs (n + 1) (M.TX (xs n) a z))
            (Function.update as n a) (Function.update zs (n + 1) z) θ)

/-- `𝔼[Σ_{j=n}^{n+k-1} β^{j-n} r⁺(X_j,θ,A_j) + β^k g⁺(X_{n+k},θ)] ∈ [0,∞]`, the same recursion for
the positive parts `r⁺`, `g⁺` (Lebesgue integrals). -/
noncomputable def BayesModel.VposPi (M : BayesModel EX Θ A Z) (π : Policy EX A Z) :
    (k : ℕ) → (n : ℕ) → (xs : ℕ → EX) → (as : ℕ → A) → (zs : ℕ → Z) → (θ : Θ) → ℝ≥0∞
  | 0, n, xs, _, _, θ => ENNReal.ofReal (M.g (xs n, θ))
  | (k + 1), n, xs, as, zs, θ =>
      let a := π n xs as zs
      ENNReal.ofReal (M.r (xs n, θ, a)) + ENNReal.ofReal M.β *
        ∫⁻ z, M.VposPi π k (n + 1) (Function.update xs (n + 1) (M.TX (xs n) a z))
            (Function.update as n a) (Function.update zs (n + 1) z) θ
          ∂(M.nu.withDensity (fun z => ENNReal.ofReal (M.qZ (xs n) θ a z)))

/-- `J_N^π(x) := ∫ V_{N,0}^π((x,\dots),(\dots),(\dots),θ) Q_0(dθ) ∈ [-∞,∞]` (Bäuerle–Rieder,
p. 150, PDF 163, Eq. (5.2) specialized to the Bayesian Model). -/
noncomputable def BayesModel.JNpi (M : BayesModel EX Θ A Z) (π : Policy EX A Z) (N : ℕ)
    (x : EX) : EReal :=
  erealIntegral M.Q0 (fun θ => M.Vpi π N 0 (fun _ => x) (fun _ => Classical.arbitrary A)
    (fun _ => Classical.arbitrary Z) θ)

/-- `J_N(x) := sup_{π ∈ Π̃_N} J_N^π(x)` (Bäuerle–Rieder, p. 150, PDF 163, Eq. (5.2)). -/
noncomputable def BayesModel.JN (M : BayesModel EX Θ A Z) (N : ℕ) (x : EX) : EReal :=
  ⨆ π ∈ {π : Policy EX A Z | M.IsPolicy N π}, M.JNpi π N x

/-- The Integrability Assumption of Section 5.1 (Bäuerle–Rieder, p. 151, PDF 164), assumed
throughout Chapter 5, specialized to the Bayesian Model: for all `x ∈ E_X`,
`sup_π ∫ 𝔼^π_{xθ}[Σ_{n=0}^{N-1} β^n r⁺(X_n,θ,A_n) + β^N g⁺(X_N,θ)] Q_0(dθ) < ∞`. -/
def BayesModel.IntegrabilityAssumption (M : BayesModel EX Θ A Z) (N : ℕ) : Prop :=
  ∀ x : EX, (⨆ π ∈ {π : Policy EX A Z | M.IsPolicy N π},
    ∫⁻ θ, M.VposPi π N 0 (fun _ => x) (fun _ => Classical.arbitrary A)
      (fun _ => Classical.arbitrary Z) θ ∂M.Q0) < ⊤

end MDPFinance.BayesianModels


