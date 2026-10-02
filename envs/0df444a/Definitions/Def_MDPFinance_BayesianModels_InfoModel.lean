-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_InfoModel
-- name    : MDPFinance_BayesianModels_InfoModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:10.975272+00:00
-- url     : https://prove2.me/theorems/5828b38b-8f0d-4ae6-9910-fbba88d704dc
-- title:
--   The information-based Markov Decision Model (Definition 5.4.6)
-- statement:
--   **Definition 5.4.6.** Given a Bayesian Model with a sequential sufficient statistic $(t_n)$,
--   the **information-based Markov Decision Model** replaces the parameter $\theta$ (never directly
--   observed) by the information state $i \in I$ as the model's second state coordinate, giving an
--   ordinary (fully observed) Markov Decision Model over $E := E_X \times I$:
--
--   - $D(x,i) := D(x)$, the same feasible actions as the original model;
--   - $\hat T(x,i,a,z) := (T^X(x,a,z), \hat\Phi(x,i,a,z))$, the joint transition of the observable
--     state and the information state;
--   - $\hat Q^Z(B\mid x,i,a) := \int_\Theta Q^Z(B\mid x,\theta,a)\,\hat\mu(\mathrm d\theta\mid i)$,
--     the disturbance law averaged over the current posterior;
--   - $\hat r(x,i,a) := \int_\Theta r(x,\theta,a)\,\hat\mu(\mathrm d\theta\mid i)$ and
--     $\hat g(x,i) := \int_\Theta g(x,\theta)\,\hat\mu(\mathrm d\theta\mid i)$, the reward and
--     terminal reward averaged the same way;
--   - the same discount factor $\beta$.
--
--   This is a genuine Markov Decision Model as in Chapter 2, and its value function
--   $\hat J_k$ (with $k$ stages remaining) is the sup, over feasible Markov policies of the reduced
--   model, of the corresponding policy value — the same "true value function" convention as
--   Chapter 2's $V_n$.
--
--   Also bundled here: `InfoModel.VpiHat`/`JNpiHat`, the value of an *original* (history-dependent,
--   Bayesian-Model) policy $\pi$ computed by running it through the information-based model's own
--   reward/transition data — the object Theorem 5.4.7 calls $\hat J_N^\pi$.
--
--   **Formalization Note.** The disturbance/transition kernel $\hat Q^Z$ composed with $\hat T$ is
--   bundled as `Qhat`, a `Kernel`, characterized by its defining mixture formula (`hQhat`) rather
--   than literally constructed via measurable pushforward/bind combinators — the same "data
--   satisfying a defining formula" pattern as `MDPFinance.POMDP.FilteredModel.Qprime`/`hQprime`
--   (chunk `05a`); see `MODERATION_NOTES.md`.
--
--   **Moderation note.** $\hat r$, $\hat g$ and the policy values $\hat V^\pi$, $\hat J^\pi_N$ are in $[-\infty,\infty]$ (`erealIntegral`): the book defines $\hat r$, $\hat g$ "whenever the integral exists", and a real Bochner integral would silently return $0$ otherwise.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 162-163, Definition 5.4.6

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior
import Definitions.Def_MDPFinance_BayesianModels_SuffStat
import Definitions.Def_MDPFinance_BayesianModels_Policy
import Definitions.Def_MDPFinance_BayesianModels_Operators
import Definitions.Def_MDPFinance_BayesianModels_ValueFunction

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

variable {EX Θ A Z I : Type*} [MeasurableSpace EX] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace Z] [MeasurableSpace I] {M : BayesModel EX Θ A Z} {Pf : M.Posterior}
  {S : SuffStat M Pf I} {Phihat : EX → I → A → Z → I}

/-- `D̂(x,i) := D(x)`, the feasible actions of the information-based model (Bäuerle–Rieder,
Definition 5.4.6, p. 162, PDF 175: "`D(x,i) := D(x)` is the set of feasible actions"). -/
def InfoDx (M : BayesModel EX Θ A Z) (e : EX × I) : Set A :=
  M.Dx e.1

/-- `D̂ ⊆ (E_X × I) × A`, the feasible state-action pairs of the information-based model. -/
def InfoD (M : BayesModel EX Θ A Z) : Set ((EX × I) × A) :=
  {p | p.2 ∈ M.Dx p.1.1}

/-- `T̂(x,i,a,z) := (T^X(x,a,z), Φ̂(x,i,a,z))`, the state-transition function of the
information-based model (Bäuerle–Rieder, Definition 5.4.6, p. 162, PDF 175). -/
def InfoT (M : BayesModel EX Θ A Z) (Phihat : EX → I → A → Z → I) (x : EX) (i : I) (a : A)
    (z : Z) : EX × I :=
  (M.TX x a z, Phihat x i a z)

/-- `r̂(x,i,a) := ∫ r(x,θ,a) μ̂(dθ|i) ∈ [-∞,∞]` (Bäuerle–Rieder, Definition 5.4.6, p. 162, PDF 175,
"whenever the integral exists": an `erealIntegral`, so that a reward without finite expectation
is `±∞`, never a default real). -/
noncomputable def InfoR (S : SuffStat M Pf I) (x : EX) (i : I) (a : A) : EReal :=
  erealIntegral (S.muHat i) (fun θ => (M.r (x, θ, a) : EReal))

/-- `ĝ(x,i) := ∫ g(x,θ) μ̂(dθ|i) ∈ [-∞,∞]` (Bäuerle–Rieder, Definition 5.4.6, p. 163, PDF 176). -/
noncomputable def InfoG (S : SuffStat M Pf I) (e : EX × I) : EReal :=
  erealIntegral (S.muHat e.2) (fun θ => (M.g (e.1, θ) : EReal))

/-- Definition 5.4.6 (Bäuerle–Rieder, p. 162, PDF 175): the **information-based Markov Decision
Model** `(E,A,D,Z,T̂,Q̂^Z,r̂,ĝ,β)` with `E := E_X × I`. Its disturbance kernel `Q̂^Z(B|x,i,a) :=
∫ Q^Z(B|x,θ,a) μ̂(dθ|i)` is genuine *data* here (bundled as `Qhat`, a `Kernel`), characterized by
its defining mixture formula `hQhat` — the same "data satisfying a defining formula" pattern as
`MDPFinance.POMDP.FilteredModel.Qprime`/`hQprime` (chunk `05a`), since constructing the kernel
literally from `μ̂` and `q_Z` via measurable pushforward/mixture combinators inside a `def` would
otherwise force discharging non-trivial measurability side-conditions with no placeholder
available to a definition. -/
structure InfoModel (M : BayesModel EX Θ A Z) (Pf : M.Posterior) (S : SuffStat M Pf I)
    (Phihat : EX → I → A → Z → I) where
  Qhat : Kernel ((EX × I) × A) (EX × I)
  hQhat : ∀ x i a, Qhat ((x, i), a) =
    ((S.muHat i).bind fun θ => M.nu.withDensity fun z => ENNReal.ofReal (M.qZ x θ a z)).map
      fun z => InfoT M Phihat x i a z

/-- `Ĵ_k(x,i) := sup_{\hat π \text{ feasible}} \hat V_k^{\hat π}(x,i)`, the *true* value function
of the information-based model with `k` stages remaining (Bäuerle–Rieder, p. 157, PDF 171 /
Theorem 5.4.8, sup-over-Markov-policies convention, via `MDPFinance.BayesianModels.Vsup` applied
to the info-model's own raw data `(D̂,Q̂,r̂,ĝ,β)`). Theorem 5.4.8a's Bellman equation (`Ĵ_0 = ĝ`,
`Ĵ_n = T̂Ĵ_{n-1}`) is then a genuine, non-definitional consequence of Theorem 2.3.8 applied to
this instance, exactly as for `MDPFinance.Bellman.structure_theorem` (chunk `02a`). -/
noncomputable def InfoModel.Jhat (Im : InfoModel M Pf S Phihat) (k : ℕ) : EX × I → EReal :=
  Vsup (InfoD M) (fun ea => Im.Qhat ea) (fun ea => InfoR S ea.1.1 ea.1.2 ea.2) (InfoG S) M.β k

/-- `V̂_{k,n}^π(xs,as,zs) := r̂(x_n,t_n(h̃_n),a_n) + β ∫ V̂_{k-1,n+1}^π(\dots) Q̂^Z(dz|x_n,t_n(h̃_n),
a_n)`, the value-to-go of a (Bayesian Model) policy `π` computed through the information-based
model's own reward/transition data, with base case `ĝ(x_{n+k}, t_{n+k}(h̃_{n+k}))`. Restated for
Theorem 5.4.7's `Ĵ_N^π` (Bäuerle–Rieder, p. 162, PDF 176), matching
`MDPFinance.POMDP.FilteredModel.ExPrime`/`JprimeNpi` (chunk `05a`)'s pattern of running the
*original* policy `π` through the *reduced* model's machinery. -/
noncomputable def InfoModel.VpiHat (Im : InfoModel M Pf S Phihat) (π : Policy EX A Z) :
    (k : ℕ) → (n : ℕ) → (xs : ℕ → EX) → (as : ℕ → A) → (zs : ℕ → Z) → EReal
  | 0, n, xs, as, zs => InfoG S (xs n, S.t n xs as zs)
  | (k + 1), n, xs, as, zs =>
      let a := π n xs as zs
      let i := S.t n xs as zs
      InfoR S (xs n) i a + (M.β : EReal) *
        erealIntegral
          ((S.muHat i).bind fun θ => M.nu.withDensity fun z => ENNReal.ofReal (M.qZ (xs n) θ a z))
          (fun z => Im.VpiHat π k (n + 1) (Function.update xs (n + 1) (M.TX (xs n) a z))
            (Function.update as n a) (Function.update zs (n + 1) z))

/-- `Ĵ_N^π(x,t_0) := V̂_{N,0}^π((x,\dots),(\dots),(\dots))` (Bäuerle–Rieder, Theorem 5.4.7, p. 162,
PDF 176). -/
noncomputable def InfoModel.JNpiHat [Nonempty A] [Nonempty Z] (Im : InfoModel M Pf S Phihat)
    (π : Policy EX A Z) (N : ℕ) (x : EX) : EReal :=
  Im.VpiHat π N 0 (fun _ => x) (fun _ => Classical.arbitrary A) (fun _ => Classical.arbitrary Z)

end MDPFinance.BayesianModels


