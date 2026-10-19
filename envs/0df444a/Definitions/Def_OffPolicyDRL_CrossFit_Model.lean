-- Prove2me | Definitions.Def_OffPolicyDRL_CrossFit_Model
-- name    : OffPolicyDRL_CrossFit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:36.820802+00:00
-- url     : https://prove2.me/theorems/31d094d9-3034-489a-bff7-af566f1d152b
-- title:
--   Off-policy evaluation model M3 under transition sampling: w, η, ψ, φ_eff, EB(M3), L(w′, f), L² norms (Sec. 1.2, Def. 3, Thm 3, Sec. 4.1, Lemma 1)
-- statement:
--   An **off-policy evaluation model** consists of the following data.
--
--   1. A time-invariant MDP with transition kernel $p(s'\mid s,a)$ and reward kernel $p(r\mid s,a)$.
--   2. A discount factor $\gamma$ and a reward bound $R_{\max}$.
--   3. A known target (evaluation) policy $\pi_e$ with its known initial state law $p^{(0)}_{\pi_e}$.
--   4. A behavior policy $\pi_b$.
--   5. The marginal law $p^{(0)}_{\pi_b}$ of the state $s$ of one observed transition.
--
--   The **standing assumptions** are the following:
--   - both MDP kernels and both policies are Markov;
--   - rewards lie in $[0,R_{\max}]$ and $0\le\gamma<1$;
--   - $p^{(0)}_{\pi_e}$ and $p^{(0)}_{\pi_b}$ are probability measures;
--   - overlap holds: $\pi_e(\cdot\mid s)\ll\pi_b(\cdot\mid s)$ for every $s$, and $p^{(\infty)}_{\pi_e,\gamma}\ll p^{(0)}_{\pi_b}$.
--
--   From the target policy one has $q$, $v$, the estimand $\rho^{\pi_e}$ and the discounted visitation $p^{(\infty)}_{\pi_e,\gamma}$. In addition:
--
--   1. the stationary density ratio $w(s)=p^{(\infty)}_{\pi_e,\gamma}(s)/p^{(0)}_{\pi_b}(s)$ and the policy ratio $\eta(s,a)=\pi_e(a\mid s)/\pi_b(a\mid s)$ (Radon–Nikodym derivatives);
--   2. the law $p_{\pi_b}$ of one observation $(s,a,r,s')$: $s\sim p^{(0)}_{\pi_b}$, $a\sim\pi_b(\cdot\mid s)$, and, given $(s,a)$, independently $r\sim p(\cdot\mid s,a)$ and $s'\sim p(\cdot\mid s,a)$ (Definition 3, model $\mathcal M_3$);
--   3. for any $w'$, $q'$ (with $v'(s)=\int q'(s,a)\pi_e(da\mid s)$), the estimating function
--   $$\psi(s,a,r,s';w',q')=(1-\gamma)\,\mathbb E_{p^{(0)}_{\pi_e}}[v'(s_0)]+w'(s)\eta(s,a)\big(r+\gamma v'(s')-q'(s,a)\big);$$
--   4. the efficient influence function $\phi_{\rm eff}(s,a,r,s')=w(s)\eta(s,a)(r+\gamma v(s')-q(s,a))$ and the efficiency bound $\mathrm{EB}(\mathcal M_3)=\mathbb E[\phi_{\rm eff}^2]$ (Eq. (3));
--   5. $L(w',f)=\mathbb E[\gamma w'(s)\eta(s,a)f(s')-w'(s)f(s)]+(1-\gamma)\mathbb E_{p^{(0)}_{\pi_e}}[f(s)]$ (Eq. (11));
--   6. the norms $\|f\|_2=\mathbb E[f(s)^2]^{1/2}$ and $\|g\|_2=\mathbb E[g(s,a)^2]^{1/2}$ under the behavior data.
--
--   Unsubscripted expectations are under $p_{\pi_b}$.
--
--   These are the objects of Theorem 6 and of its proof.
--
--   **Formalization Note** $w$ is `toReal` of the Radon–Nikodym derivative of the discounted visitation with respect to $p^{(0)}_{\pi_b}$, so it is determined only $p^{(0)}_{\pi_b}$-a.e. $\eta$ is `toReal` of Mathlib's jointly measurable kernel Radon–Nikodym derivative `Kernel.rnDeriv` (this needs a countably generated action σ-algebra); for each $s$ it agrees $\pi_b(\cdot\mid s)$-a.e. with $d\pi_e(\cdot\mid s)/d\pi_b(\cdot\mid s)$. Off the supports these ratios take junk values that no statement depends on. $\mathrm{EB}$ and the $L^2$ norms are Bochner integrals, which are $0$ for non-integrable integrands. Every theorem that uses them assumes the bounds ($w\le C_w$, $\eta\le C_\eta$, bounded nuisances) that make the integrands bounded. The paper's base measures $\lambda_S,\lambda_A,\lambda_R$ are not needed: densities are Radon–Nikodym derivatives of the measures themselves. The overlap assumption $\pi_e(\cdot\mid s)\ll\pi_b(\cdot\mid s)$ is implicit in the paper's $\eta=\pi_e/\pi_b$. $p^{(\infty)}_{\pi_e,\gamma}\ll p^{(0)}_{\pi_b}$ is what Definition 3's "the base measure is absolutely continuous wrt the distribution of $s$" guarantees.
-- source:
--   Kallus & Uehara, Efficiently Breaking the Curse of Horizon in Off-Policy Evaluation with Double Reinforcement Learning, arXiv:1909.05850v6, Section 1.2 pp. 4–7 (transition sampling, η, w, L^p norm), Definition 3 and Theorem 3 Eq. (3) p. 16, Section 4.1 p. 21 (ψ), Lemma 1 Eq. (11) p. 32

import Mathlib
import Definitions.Def_OffPolicyDRL_CrossFit_MDP

open MeasureTheory ProbabilityTheory Filter Topology

namespace OffPolicyDRL.CrossFit

/-- The off-policy evaluation model of Kallus–Uehara (Sec. 1.2 and Def. 3): an MDP together with
the discount factor `γ`, the reward bound `Rmax`, the known target (evaluation) policy `πe` with its
known initial distribution `ν0e = p^{(0)}_{πe}`, the behavior policy `πb`, and the marginal law
`ν0b = p^{(0)}_{πb}` of the state `s` of one observed transition `(s, a, r, s′)`. -/
structure Model (S A : Type*) [MeasurableSpace S] [MeasurableSpace A] extends MDP S A where
  /-- discount factor -/
  γ : ℝ
  /-- reward bound -/
  Rmax : ℝ
  /-- target (evaluation) policy `πe(a | s)` -/
  πe : Kernel S A
  /-- behavior policy `πb(a | s)` -/
  πb : Kernel S A
  /-- initial state distribution `p^{(0)}_{πe}` of the target policy -/
  ν0e : Measure S
  /-- marginal law `p^{(0)}_{πb}` of `s` in the transition data -/
  ν0b : Measure S

namespace Model

variable {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : Model S A)

/-- The discounted visitation `p^{(∞)}_{πe,γ}` of the target policy from `p^{(0)}_{πe}`. -/
noncomputable def occ : Measure S := M.discVisitation M.γ M.ν0e M.πe

/-- The q-function `q` of the target policy. -/
noncomputable def q : S × A → ℝ := M.qFun M.γ M.πe

/-- The v-function `v` of the target policy. -/
noncomputable def v : S → ℝ := M.vFun M.γ M.πe

/-- `v′(s) = E_{a ∼ πe(· | s)}[q′(s, a)]` for an arbitrary `q′`. -/
noncomputable def vOf' (q' : S × A → ℝ) : S → ℝ := MDP.vOf M.πe q'

/-- The estimand `ρ^{πe} = lim_T ρ^{πe}_T` (p. 5). -/
noncomputable def ρ : ℝ := M.policyValue M.γ M.ν0e M.πe

/-- Standing assumptions: Markov kernels, rewards in `[0, Rmax]`, `γ ∈ [0, 1)`, probability initial
laws, and overlap — `πe(· | s) ≪ πb(· | s)` for every `s` (so that `η = πe/πb` exists) and
`p^{(∞)}_{πe,γ} ≪ p^{(0)}_{πb}` (so that `w` exists; Def. 3: the base measure is absolutely
continuous wrt the distribution of `s`). -/
structure Standing : Prop where
  bounded : M.toMDP.IsBounded M.Rmax
  γ_nonneg : 0 ≤ M.γ
  γ_lt_one : M.γ < 1
  markov_πe : IsMarkovKernel M.πe
  markov_πb : IsMarkovKernel M.πb
  prob_ν0e : IsProbabilityMeasure M.ν0e
  prob_ν0b : IsProbabilityMeasure M.ν0b
  policy_ac : ∀ s, M.πe s ≪ M.πb s
  visitation_ac : M.occ ≪ M.ν0b

/-- The stationary density ratio `w(s) = p^{(∞)}_{πe,γ}(s) / p^{(0)}_{πb}(s)`, as a
Radon–Nikodym derivative (real-valued; determined `p^{(0)}_{πb}`-a.e.). -/
noncomputable def w (s : S) : ℝ := (M.occ.rnDeriv M.ν0b s).toReal

/-- The policy density ratio `η(s, a) = πe(a | s) / πb(a | s)`, as the jointly measurable kernel
Radon–Nikodym derivative (for each `s`, determined `πb(· | s)`-a.e.). -/
noncomputable def η [MeasurableSpace.CountablyGenerated A] (s : S) (a : A) : ℝ :=
  (Kernel.rnDeriv M.πe M.πb s a).toReal

/-- The law `p_{πb}(J_{s1})` of one observed transition `(s, a, r, s′)`: `s ∼ p^{(0)}_{πb}`,
`a ∼ πb(· | s)`, and, given `(s, a)`, independently `r ∼ p(· | s, a)` and `s′ ∼ p(· | s, a)`. -/
noncomputable def obsLaw : Measure (S × A × ℝ × S) :=
  ((M.ν0b ⊗ₘ M.πb) ⊗ₘ (M.Rw ×ₖ M.P)).map (fun p => (p.1.1, p.1.2, p.2.1, p.2.2))

/-- The estimating function
`ψ(s, a, r, s′; w′, q′) = (1 - γ) E_{p^{(0)}_{πe}}[v′(s₀)] + w′(s) η(s, a) (r + γ v′(s′) - q′(s, a))`
(p. 21). -/
noncomputable def ψ [MeasurableSpace.CountablyGenerated A] (w' : S → ℝ) (q' : S × A → ℝ)
    (o : S × A × ℝ × S) : ℝ :=
  (1 - M.γ) * ∫ s, M.vOf' q' s ∂M.ν0e +
    w' o.1 * M.η o.1 o.2.1 * (o.2.2.1 + M.γ * M.vOf' q' o.2.2.2 - q' (o.1, o.2.1))

/-- The efficient influence function `φ_eff(s, a, r, s′) = w(s) η(s, a) (r + γ v(s′) - q(s, a))`
(Theorem 3, p. 16). -/
noncomputable def φeff [MeasurableSpace.CountablyGenerated A] (o : S × A × ℝ × S) : ℝ :=
  M.w o.1 * M.η o.1 o.2.1 * (o.2.2.1 + M.γ * M.v o.2.2.2 - M.q (o.1, o.2.1))

/-- The efficiency bound `EB(M3) = E[w²(s) η²(s, a) (r + γ v(s′) - q(s, a))²]` (Eq. (3), p. 16). -/
noncomputable def EB [MeasurableSpace.CountablyGenerated A] : ℝ := ∫ o, (M.φeff o) ^ 2 ∂M.obsLaw

/-- `L(w′, f) = E[γ w′(s) η(s, a) f(s′) - w′(s) f(s)] + (1 - γ) E_{p^{(0)}_{πe}}[f(s)]`
(Eq. (11), p. 32). -/
noncomputable def Lfun [MeasurableSpace.CountablyGenerated A] (w' f : S → ℝ) : ℝ :=
  (∫ o, (M.γ * w' o.1 * M.η o.1 o.2.1 * f o.2.2.2 - w' o.1 * f o.1) ∂M.obsLaw) +
    (1 - M.γ) * ∫ s, f s ∂M.ν0e

/-- The `L²(p^{(0)}_{πb})` norm `‖f‖₂ = (E[f(s)²])^{1/2}` of a function of the state. -/
noncomputable def normS (f : S → ℝ) : ℝ := √(∫ s, f s ^ 2 ∂M.ν0b)

/-- The `L²(p^{(0)}_{πb} ⊗ πb)` norm `‖g‖₂ = (E[g(s, a)²])^{1/2}` of a function of `(s, a)`. -/
noncomputable def normSA (g : S × A → ℝ) : ℝ := √(∫ x, g x ^ 2 ∂(M.ν0b ⊗ₘ M.πb))

end Model

end OffPolicyDRL.CrossFit


