-- Prove2me | Definitions.Def_RelaxedEqMDP_Discrete_Supplement_ContinuousTime
-- name    : RelaxedEqMDP_Discrete_Supplement_ContinuousTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:04:23.309804+00:00
-- url     : https://prove2.me/theorems/55eff805-4c3a-41a3-99b3-a1e677c9e5e9
-- title:
--   §3, (3.1)–(3.11), Definition 3.1, Assumption 3.1, pp. 10–13 — continuous-time MDP with rate matrices: values, concatenation, equilibria, Gibbs and argmax operators
-- statement:
--   Continuous-time version of the time-inconsistent MDP of the base mission. The state space is $\mathcal S=\{1,\dots,d\}$ and the action space is a compact set $U\subset\mathbb R^\ell$ with $\mathrm{Leb}(U)>0$. Each action $u\in U$ carries a **rate matrix** $q^u$: $q^u_{ij}\ge0$ for $j\ne i$ and $q^u_{ii}=-\sum_{j\ne i}q^u_{ij}$. A relaxed control $\pi\in\Pi$ assigns to every state a probability measure $\pi(i)$ on $U$ (base `IsRelaxed`); $\pi\in\Pi_r$ if each $\pi(i)$ has a density with finite differential entropy $\mathcal H(\pi(i))$ (base `IsRegular`, `ent`). The **relaxed rate matrix** of $\mu$ is $Q^\mu_{ij}=\int_U q^u_{ij}\,\mu(du)$, and under $\pi$ the chain jumps from $i$ according to the row $Q^{\pi(i)}_i$; its transition matrix is $P_i(X_s=j)=\big(e^{sQ^\pi}\big)_{ij}$.
--
--   With $f^\mu(s,i)=\int_U f(s,i,u)\,\mu(du)$ and a discount $\delta:[0,\infty)\to[0,1]$ (nonincreasing, $\delta(0)=1$), the file defines:
--
--   1. the values (3.1)–(3.2) and the auxiliary values (3.4)–(3.5),
--   $$\widetilde J^\pi(i)=\int_0^\infty\big(e^{sQ^\pi}r^\pi(s)\big)_i\,ds,\qquad \widetilde V^\pi_\lambda(t,i)=\int_0^\infty\big(e^{sQ^\pi}r^\pi_\lambda(t+s)\big)_i\,ds,$$
--   where $r^\pi(s)_j=f^{\pi(j)}(s,j)$ and $r^\pi_\lambda(s)_j=f^{\pi(j)}(s,j)+\lambda\delta(s)\mathcal H(\pi(j))$ ($\widetilde J^\pi_\lambda$ and $\widetilde V^\pi$ likewise);
--   2. the values of the concatenation $\pi'\otimes_\varepsilon\pi$ ($\pi'$ on $[0,\varepsilon)$, $\pi$ afterwards), through the Markov property at time $\varepsilon$:
--   $$\widetilde J^{\pi'\otimes_\varepsilon\pi}(i)=\int_0^\varepsilon\big(e^{sQ^{\pi'}}r^{\pi'}(s)\big)_i\,ds+\big(e^{\varepsilon Q^{\pi'}}\widetilde V^\pi(\varepsilon)\big)_i,$$
--   and $\widetilde J^{\pi'\otimes_\varepsilon\pi}_\lambda$ with $r_\lambda$, $\widetilde V_\lambda$;
--   3. Definition 3.1: $\pi\in\Pi_r$ is a **regular relaxed equilibrium** for (3.2) if $\limsup_{\varepsilon\downarrow0}\big(\widetilde J^{\pi'\otimes_\varepsilon\pi}_\lambda(i)-\widetilde J^\pi_\lambda(i)\big)/\varepsilon\le0$ for all $\pi'\in\Pi_r$ and $i$; $\pi\in\Pi$ is a **relaxed equilibrium** for (3.1) if the same holds with $\widetilde J$ and all $\pi'\in\Pi$;
--   4. the Gibbs density (3.8) $\widetilde\Gamma_\lambda(y,i)(u)=e^{(f(0,i,u)+q^u_i\cdot y)/\lambda}\big/\int_Ue^{(f(0,i,v)+q^v_i\cdot y)/\lambda}dv$, the control $\widetilde\Gamma_\lambda(y,\cdot)$, $\widetilde\Psi_\lambda(y)=\widetilde J^{\widetilde\Gamma_\lambda(y,\cdot)}_\lambda$ and $\widetilde\Phi_\lambda(\pi)=\widetilde\Gamma_\lambda(\widetilde J^\pi_\lambda,\cdot)$;
--   5. (3.9)–(3.11): $\widetilde E(y,i)=\arg\max_{u\in U}\{f(0,i,u)+q^u_i\cdot y\}$, $\widetilde\Gamma(y)=\{\pi\in\Pi:\operatorname{supp}\pi(i)\subseteq\widetilde E(y,i)\ \forall i\}$, $\widetilde\Psi(y)=\{\widetilde J^\pi:\pi\in\widetilde\Gamma(y)\}$ and $\widetilde\Phi(\pi)=\widetilde\Gamma(\widetilde J^\pi)$;
--   6. the hypotheses: the standing setup, measurability, Assumption 3.1 ($\int_0^\infty(\sup_{i,u}|f(s,i,u)|+\delta(s))\,ds<\infty$), Assumption 2.2 with $q$ for $p$, boundedness of the rates, and right continuity of $t\mapsto f(t,i,u)$ at zero uniformly in $u$.
--
--   These objects carry the continuous-time results of §3 and the limit theorem of §5.
--
--   **Formalization Note** The Gibbs objects reuse the base mission's `gibbsDensity`, `gibbsCtrl`, `argmaxSet` and `GammaSet` with $q$ for $p$ and the time-$0$ reward $f(0,\cdot,\cdot)$. The relaxed generator is the base averaged matrix `Pbar` applied to $q$. The matrix exponential is Mathlib's `NormedSpace.exp`. Integrals over $[0,\infty)$ are over $(0,\infty)$, which is the same Lebesgue integral. The page prints $E(y,i)$ in (3.10); it is read as $\widetilde E(y,i)$. The lim sup in Definition 3.1 is written as "for every $\eta>0$ the quotient is eventually $\le\eta$". Measurability of $(s,u)\mapsto f(s,i,u)$ on $[0,\infty)\times U$ and $u\mapsto q^u_{ij}$ on $U$ is the standing convention implicit in the integrals. The rate bound `RatesBdd` is what makes $Q^\mu$ defined for every $\mu\in\mathcal P(U)$. `TimeContAtZeroUnif` is the repaired time-continuity hypothesis (see the theorems that use it).
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, pp. 10–13, (3.1)–(3.11), Definition 3.1, Assumption 3.1; p. 8, Assumption 2.2 (with q for p, p. 12)

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete.Supplement

/-- A `d × d` rate matrix (generator) (p. 10): `Q_{ij} ≥ 0` for `j ≠ i` and
`Q_{ii} = −∑_{j≠i} Q_{ij}`, i.e. every row sums to `0`. -/
structure IsRateMatrix {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) : Prop where
  offdiag_nonneg : ∀ i j, i ≠ j → 0 ≤ Q i j
  row_sum : ∀ i, ∑ j, Q i j = 0

/-- Standing setup of §3 (pp. 4 and 10): the action space `U ⊂ ℝ^ℓ` is compact with `Leb(U) > 0`,
and every action `u ∈ U` carries a rate matrix `q^u`. -/
structure StandingCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) : Prop where
  compact : IsCompact U
  vol_pos : 0 < volume U
  rate : ∀ u ∈ U, IsRateMatrix (q u)

/-- The rates are bounded on `U`: `|q^u_{ij}| ≤ C` for all `u ∈ U`. For measurable `q` this is
exactly what is needed for the relaxed rate matrix `Q^μ_{ij} = ∫_U q^u_{ij} μ(du)` (p. 10) to be
defined for every `μ ∈ 𝒫(U)`. -/
def RatesBdd {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ C : ℝ, ∀ u ∈ U, ∀ i j, |q u i j| ≤ C

/-- Measurability implicit in `f^μ(t,i) = ∫_U f(t,i,u) μ(du)`, `Q^μ_{ij} = ∫_U q^u_{ij} μ(du)` and
in the time integrals (3.1)–(3.5): `(s,u) ↦ f(s,i,u)` is jointly measurable and `u ↦ q^u_{ij}` is
measurable on their source domains `[0,∞) × U` and `U`. -/
structure MeasMapsCT {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℝ → Fin d → A ℓ → ℝ) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) :
    Prop where
  f_meas : ∀ i, Measurable (fun z : Set.Ici (0 : ℝ) × U => f z.1.1 i z.2.1)
  q_meas : ∀ i j, Measurable (fun u : U => q u.1 i j)

/-- The discount function (pp. 4–5) on `[0, ∞)`: `δ : [0,∞) → [0,1]`, nonincreasing, `δ(0) = 1`. -/
structure IsDiscountCT (δ : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ t → 0 ≤ δ t
  le_one : ∀ t, 0 ≤ t → δ t ≤ 1
  anti : AntitoneOn δ (Set.Ici 0)
  zero : δ 0 = 1

/-- Assumption 3.1 (p. 11): `M̃ := ∫_0^∞ (sup_{i∈S,u∈U} |f(s,i,u)| + δ(s)) ds < ∞`, written as
integrability of `δ` on `[0,∞)` and of a majorant `b(s) ≥ sup_{i,u∈U} |f(s,i,u)|` on `[0,∞)`.
It also records that `δ` is a discount function. -/
structure Assumption31 {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ) :
    Prop where
  discount : IsDiscountCT δ
  integrable_delta : IntegrableOn δ (Set.Ici 0)
  bound : ∃ b : ℝ → ℝ, IntegrableOn b (Set.Ici 0) ∧
    ∀ s, 0 ≤ s → ∀ i, ∀ u ∈ U, |f s i u| ≤ b s

/-- Assumption 2.2 (p. 8) with `p^u_i` replaced by `q^u_i` (p. 12), uniformly in `t ∈ [0,∞)`:
`|f(t,i,u₁) − f(t,i,u₂)| + |q^{u₁}_i − q^{u₂}_i| ≤ Θ |u₁ − u₂|` (Euclidean norms), `Θ > 0`. -/
structure Assumption22CT {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℝ → Fin d → A ℓ → ℝ)
    (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (Theta : ℝ) : Prop where
  pos : 0 < Theta
  lip : ∀ t, 0 ≤ t → ∀ i, ∀ u₁ ∈ U, ∀ u₂ ∈ U,
    |f t i u₁ - f t i u₂| + enorm2 (q u₁ i - q u₂ i) ≤ Theta * ‖u₁ - u₂‖

/-- Right continuity of the reward at time zero, uniformly over actions in `U`.
This is the local repair needed for (3.6)–(3.7): no uniformity at positive times is imposed. -/
def TimeContAtZeroUnif {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℝ → Fin d → A ℓ → ℝ) : Prop :=
  ∀ i, ∀ η > 0, ∃ ρ > 0, ∀ t, 0 ≤ t → t < ρ →
    ∀ u ∈ U, |f t i u - f 0 i u| < η

/-- `f^μ(s,i) := ∫_U f(s,i,u) μ(du)` (p. 4), continuous time. -/
noncomputable def fbarCT {d ℓ : ℕ} (f : ℝ → Fin d → A ℓ → ℝ) (μ : Measure (A ℓ)) (s : ℝ)
    (i : Fin d) : ℝ :=
  ∫ u, f s i u ∂μ

/-- The relaxed generator of a control (p. 10): row `i` is `Q^{π(i)}_i`, where
`Q^μ_{ij} := ∫_U q^u_{ij} μ(du)`. (This is the base averaged matrix `Pbar` with `q` for `p`.) -/
noncomputable abbrev Qbar {d ℓ : ℕ} (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (pol : Control d ℓ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Pbar q pol

/-- The transition matrix `P_i(X^π_s = j) = exp(s Q^π)_{ij}` of the chain driven by the relaxed
feedback control `π` (p. 10–11). -/
noncomputable def trans {d ℓ : ℕ} (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (pol : Control d ℓ)
    (s : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  NormedSpace.exp (s • Qbar q pol)

/-- Per-time reward vector `r^π(s)_j := f^{π(j)}(s, j)`. -/
noncomputable def rew {d ℓ : ℕ} (f : ℝ → Fin d → A ℓ → ℝ) (pol : Control d ℓ) (s : ℝ) :
    Fin d → ℝ :=
  fun j => fbarCT f (pol j) s j

/-- Regularized per-time reward vector `r^π_λ(s)_j := f^{π(j)}(s, j) + λ δ(s) ℋ(π(j))`. -/
noncomputable def rewLam {d ℓ : ℕ} (U : Set (A ℓ)) (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ)
    (lam : ℝ) (pol : Control d ℓ) (s : ℝ) : Fin d → ℝ :=
  fun j => fbarCT f (pol j) s j + lam * δ s * ent U (pol j)

/-- (3.1) (p. 11): `J̃^π(i) = E_i[∫_0^∞ f^{π(X_s)}(s, X_s) ds] = ∫_0^∞ (exp(sQ^π) r^π(s))_i ds`. -/
noncomputable def Jt {d ℓ : ℕ} (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℝ → Fin d → A ℓ → ℝ)
    (pol : Control d ℓ) : Fin d → ℝ :=
  fun i => ∫ s in Set.Ioi 0, (trans q pol s *ᵥ rew f pol s) i

/-- (3.2) (p. 11): `J̃^π_λ(i) = E_i[∫_0^∞ (f^{π(X_s)}(s, X_s) + λ δ(s) ℋ(π(X_s))) ds]`. -/
noncomputable def Jlamt {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ) (lam : ℝ) (pol : Control d ℓ) : Fin d → ℝ :=
  fun i => ∫ s in Set.Ioi 0, (trans q pol s *ᵥ rewLam U f δ lam pol s) i

/-- (3.4) (p. 11): `Ṽ^π(t,i) = E_i[∫_0^∞ f^{π(X_s)}(t + s, X_s) ds]`. -/
noncomputable def Vt {d ℓ : ℕ} (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℝ → Fin d → A ℓ → ℝ)
    (pol : Control d ℓ) (t : ℝ) : Fin d → ℝ :=
  fun i => ∫ s in Set.Ioi 0, (trans q pol s *ᵥ rew f pol (t + s)) i

/-- (3.5) (p. 11): `Ṽ^π_λ(t,i) = E_i[∫_0^∞ (f^{π(X_s)}(t + s, X_s) + λ δ(t + s) ℋ(π(X_s))) ds]`. -/
noncomputable def Vlamt {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ) (lam : ℝ) (pol : Control d ℓ) (t : ℝ) : Fin d → ℝ :=
  fun i => ∫ s in Set.Ioi 0, (trans q pol s *ᵥ rewLam U f δ lam pol (t + s)) i

/-- `J̃^{π′⊗_ε π}(i)` (p. 11): the value of the control that uses `π′` on `[0, ε)` and `π` on
`[ε, ∞)`. It is written through the Markov property at time `ε` (no process is constructed):
`∫_0^ε (exp(sQ^{π′}) r^{π′}(s))_i ds + (exp(εQ^{π′}) Ṽ^π(ε))_i`. -/
noncomputable def JconcatT {d ℓ : ℕ} (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (pol' pol : Control d ℓ) (ε : ℝ) : Fin d → ℝ :=
  fun i => (∫ s in (0 : ℝ)..ε, (trans q pol' s *ᵥ rew f pol' s) i) +
    (trans q pol' ε *ᵥ Vt q f pol ε) i

/-- `J̃^{π′⊗_ε π}_λ(i)` (p. 11), the regularized value of the concatenation, written through the
Markov property at time `ε`:
`∫_0^ε (exp(sQ^{π′}) r^{π′}_λ(s))_i ds + (exp(εQ^{π′}) Ṽ^π_λ(ε))_i`. -/
noncomputable def JlamConcatT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ) (lam : ℝ) (pol' pol : Control d ℓ) (ε : ℝ) :
    Fin d → ℝ :=
  fun i => (∫ s in (0 : ℝ)..ε, (trans q pol' s *ᵥ rewLam U f δ lam pol' s) i) +
    (trans q pol' ε *ᵥ Vlamt U q f δ lam pol ε) i

/-- Definition 3.1, (3.3) (p. 11): `π ∈ Π_r` is a regular relaxed equilibrium for (3.2) if
`limsup_{ε↓0} (J̃^{π′⊗_ε π}_λ(i) − J̃^π_λ(i))/ε ≤ 0` for all `π′ ∈ Π_r` and `i ∈ S`. The
`limsup ≤ 0` is written as: for every `η > 0`, the quotient is `≤ η` for all small `ε > 0`. -/
def IsRegularRelaxedEqCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ) (lam : ℝ) (pol : Control d ℓ) : Prop :=
  IsRegular U pol ∧ ∀ i, ∀ pol' : Control d ℓ, IsRegular U pol' → ∀ η > 0,
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (JlamConcatT U q f δ lam pol' pol ε i - Jlamt U q f δ lam pol i) / ε ≤ η

/-- Definition 3.1 (p. 11): `π ∈ Π` is a relaxed equilibrium for (3.1) if
`limsup_{ε↓0} (J̃^{π′⊗_ε π}(i) − J̃^π(i))/ε ≤ 0` for all `π′ ∈ Π` and `i ∈ S`. -/
def IsRelaxedEqCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (pol : Control d ℓ) : Prop :=
  IsRelaxed U pol ∧ ∀ i, ∀ pol' : Control d ℓ, IsRelaxed U pol' → ∀ η > 0,
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (JconcatT q f pol' pol ε i - Jt q f pol i) / ε ≤ η

/-- (3.8) (p. 12): `Γ̃_λ(y,i)(u) = e^{(f(0,i,u) + q^u_i·y)/λ} / ∫_U e^{(f(0,i,v) + q^v_i·y)/λ} dv`:
the base Gibbs density with `q` for `p` and the time-`0` reward `f(0,·,·)`. -/
noncomputable def gibbsDensityCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (lam : ℝ) (y : Fin d → ℝ) (i : Fin d) (u : A ℓ) : ℝ :=
  gibbsDensity U (fun _ : ℕ => f 0) q lam y i u

/-- The control `Γ̃_λ(y, ·)`: `π(i)` has density `Γ̃_λ(y,i)` on `U`. -/
noncomputable def gibbsCtrlCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (lam : ℝ) (y : Fin d → ℝ) : Control d ℓ :=
  gibbsCtrl U (fun _ : ℕ => f 0) q lam y

/-- p. 12: `Ψ̃_λ(y) := J̃_λ^{Γ̃_λ(y,·)}` (the time-`0` regularized value). -/
noncomputable def PsiLamCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ) (lam : ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  Jlamt U q f δ lam (gibbsCtrlCT U q f lam y)

/-- p. 12: `Φ̃_λ(π) := Γ̃_λ(J̃^π_λ, ·)`. -/
noncomputable def PhiLamCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ) (lam : ℝ) (pol : Control d ℓ) : Control d ℓ :=
  gibbsCtrlCT U q f lam (Jlamt U q f δ lam pol)

/-- (3.9) (p. 13): `Ẽ(y,i) := argmax_{u∈U} {f(0,i,u) + q^u_i · y} ⊆ U`. -/
def argmaxSetCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (y : Fin d → ℝ) (i : Fin d) : Set (A ℓ) :=
  argmaxSet U (fun _ : ℕ => f 0) q y i

/-- (3.10) (p. 13): `Γ̃(y) := {π ∈ Π : supp(π(i)) ⊆ Ẽ(y,i) ∀ i}` (the page prints `E(y,i)`, a
misprint for `Ẽ(y,i)`), with the support condition written as `π(i)(Ẽ(y,i)ᶜ) = 0`. -/
def GammaSetCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (y : Fin d → ℝ) : Set (Control d ℓ) :=
  {pol | IsRelaxed U pol ∧ ∀ i, pol i (argmaxSetCT U q f y i)ᶜ = 0}

/-- (3.11) (p. 13): `Ψ̃(y) := {J̃^π : π ∈ Γ̃(y)} ⊆ ℝ^d`. -/
def PsiSetCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (y : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {z | ∃ pol ∈ GammaSetCT U q f y, Jt q f pol = z}

/-- p. 13: `Φ̃(π) := Γ̃(J̃^π) ⊆ Π`. -/
def PhiSetCT {d ℓ : ℕ} (U : Set (A ℓ)) (q : A ℓ → Matrix (Fin d) (Fin d) ℝ)
    (f : ℝ → Fin d → A ℓ → ℝ) (pol : Control d ℓ) : Set (Control d ℓ) :=
  GammaSetCT U q f (Jt q f pol)

end RelaxedEqMDP.Discrete.Supplement


