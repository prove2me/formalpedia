-- Prove2me | Definitions.Def_DataDepProb_Discrete_Procedure
-- name    : DataDepProb_Discrete_Procedure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:11:44.824045+00:00
-- url     : https://prove2.me/theorems/bf9108ac-127f-4e5d-8c8d-11a73c29914e
-- title:
--   The penalized update $U_s$, its duality-gap relaxation, the procedure $q_t(s)$ of recursion (8), and $K_t$, $\ell_t$
-- statement:
--   Fix $\eta>0$, a weight $\lambda$ and a **penalty family** $s\mapsto P_s$ of functions $\mathbb R^d\to\mathbb R$ indexed by samples $s\in[d]^n$. For $q\in\tilde\Delta_d$, $f:[d]\to[0,1]$ and $b$, set $q^+=\mathrm{MW}_\eta(q,f,b)$ and (Eq. (14))
--   $$U_s(q,f,b)=\arg\min_{v\in\tilde\Delta_d}\{\mathrm{KL}(v\|q^+)+\lambda P_s(v)\}.$$
--   A point $v$ has **duality gap at most $\tau$** if $v\in\tilde\Delta_d$ and $\langle\log(v/q^+)+\lambda\nabla P_s(v),\,v-w\rangle\le\tau$ for every $w\in\tilde\Delta_d$ (Lemma 6.1).
--
--   An **update rule** maps $(s,q,f,b)$ to the next distribution. For a query mapping $\mathcal G:[d]^n\to[0,1]^{[d]}$ and an update rule $U$, the distribution $q_t(s)$ after a complete run with $t$ updates on input $s$ is given by recursion (8): $q_0(s)=e_s$ and
--   $$(s',y)=\mathrm{Amp}(s),\quad f'=\mathcal G(s'),\quad b'=\tfrac12\big(f'(y)+E_u[f']\big),\quad q_{t+1}(s)=U_{s'}\big(q_t(s'),f',b'\big),$$
--   where $q_t(s')$ is computed with fresh amplification coins, independent of those of $\mathrm{Amp}(s)$. Thus $q_t(s)$ is a function of $s$ and of $t$ independent uniform amplification coins. Finally (Eq. (5))
--   $$K_t=\mathbb E\,\mathrm{KL}(\tilde D\|q_t(S)),\qquad \ell_t=\mathbb E\big(E_{q_t(S)}[f_S]-E_{\tilde D}[f_S]\big)^2,\qquad f_S=\mathcal G(S),$$
--   with the expectations over $S\sim D^n$ and the coins of the run.
--
--   **Formalization Note.** $U_s$ is the minimizer selected by `Classical.epsilon`; under the hypotheses of Lemma 6.1 ($P_s$ continuous and convex near $\tilde\Delta_d$) the minimizer exists and is unique, so this is the paper's $U_s$. $\langle\nabla P_s(v),v-w\rangle$ is the Fréchet derivative of $P_s$ at $v$ applied to $v-w$. Coins are indexed so that the last coin is used by the outermost amplification; $K_t,\ell_t$ are finite averages, so no integrability question arises.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 12, Algorithm 1; p. 13, Eqs. (5) and (8); p. 15, Eq. (14) and Lemma 6.1

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_Divergence
import Definitions.Def_DataDepProb_Discrete_MW
import Definitions.Def_DataDepProb_Discrete_Amp

namespace DataDepProb.Discrete

/-!
# The penalized update `U_s`, the procedure `q_t(s)` of recursion (8), and `K_t`, `ℓ_t`

Feldman, Kale, Majid, Talwar, *Data-Dependent Probability Estimation via Sample Amplification*,
STOC 2027 submission (manuscript sha256 28400f1c…), §5 pp. 12–13 (Algorithm 1, Eq. (5),
recursion (8)) and §6 p. 15 (Eq. (14), Lemma 6.1).

* A **penalty family** `P : [d]^n → (ℝ^d → ℝ)` assigns to each sample `s` a function `P_s`.
* `exactUpdate η λ P s q f b = U_s(q, f, b) = argmin_{v ∈ ∆̃_d} {KL(v‖q⁺) + λ P_s(v)}` with
  `q⁺ = MW_η(q, f, b)` (Eq. (14)). It is the minimizer chosen by `Classical.epsilon`; under the
  hypotheses of Lemma 6.1 (`P_s` continuous and convex near `∆̃_d`, `λ > 0`) the minimizer exists
  (continuous objective on a compact nonempty set) and is unique (`KL(·‖q⁺)` is strictly convex),
  so this is the paper's `U_s`.
* `GapLE η λ τ P s q f b v`: `v ∈ ∆̃_d` and
  `max_{w ∈ ∆̃_d} ⟨log(v/q⁺) + λ∇P_s(v), v − w⟩ ≤ τ` (Lemma 6.1), where `⟨∇P_s(v), v − w⟩` is the
  Fréchet derivative `fderiv ℝ (P s) v (v − w)`.
* An **update rule** maps `(s, q, f, b)` to the next distribution; the estimator's rule is
  `exactUpdate` (or an approximation of it, Lemma 6.1's τ clause).
* `qRun G U t s ω` is `q_t(s)`, the final distribution of a complete run with exactly `t` updates on
  input `s`, as a function of the amplification coins `ω : Fin t → AmpCoin n`: `q_0(s) = e_s` and,
  by (8), `q_{t+1}(s) = U_{s′}(q_t(s′), f′, b′)` with `(s′, y) = Amp(s)` (coins `ω t`, the last
  one), `f′ = 𝒢(s′)`, `b′ = ½(f′(y) + E_u[f′])`, and `q_t(s′)` computed from the other, independent
  coins `ω 0, …, ω (t − 1)`. All coins are uniform and independent.
* `Kt` and `ellt` are `K_t = E KL(D̃‖q_t(S))` and `ℓ_t = E (E_{q_t(S)}[f_S] − E_{D̃}[f_S])²`
  (Eq. (5)), the expectations over `S ∼ D^n` and the coins, written as finite sums.
-/

/-- The penalized update `U_s(q, f, b) = argmin_{v ∈ ∆̃_d} {KL(v‖q⁺) + λP_s(v)}`,
`q⁺ = MW_η(q, f, b)` (Eq. (14)). -/
noncomputable def exactUpdate {n d : ℕ} (η lam : ℝ) (P : (Fin n → Fin d) → (Fin d → ℝ) → ℝ)
    (s : Fin n → Fin d) (q f : Fin d → ℝ) (b : ℝ) : Fin d → ℝ :=
  Classical.epsilon fun v => v ∈ truncSimplex d ∧
    IsMinOn (fun v => kl v (mw η q f b) + lam * P s v) (truncSimplex d) v

/-- The duality-gap condition of Lemma 6.1 for an approximate update `v`:
`v ∈ ∆̃_d` and `⟨log(v/q⁺) + λ∇P_s(v), v − w⟩ ≤ τ` for every `w ∈ ∆̃_d`, `q⁺ = MW_η(q, f, b)`. -/
def GapLE {n d : ℕ} (η lam τ : ℝ) (P : (Fin n → Fin d) → (Fin d → ℝ) → ℝ)
    (s : Fin n → Fin d) (q f : Fin d → ℝ) (b : ℝ) (v : Fin d → ℝ) : Prop :=
  v ∈ truncSimplex d ∧ ∀ w ∈ truncSimplex d,
    (∑ x, Real.log (v x / mw η q f b x) * (v x - w x)) + lam * fderiv ℝ (P s) v (v - w) ≤ τ

/-- An update rule: `(s, q, f, b) ↦` the next distribution. -/
abbrev UpdateRule (n d : ℕ) : Type :=
  (Fin n → Fin d) → (Fin d → ℝ) → (Fin d → ℝ) → ℝ → (Fin d → ℝ)

/-- `q_t(s)` (recursion (8)) for the query mapping `G` and the update rule `U`, as a function of
the amplification coins: `q_0(s) = e_s`; `q_{t+1}(s) = U_{s′}(q_t(s′), f′, b′)`. -/
noncomputable def qRun {n d : ℕ} (G : (Fin n → Fin d) → Fin d → ℝ) (U : UpdateRule n d) :
    (t : ℕ) → (Fin n → Fin d) → (Fin t → AmpCoin n) → Fin d → ℝ
  | 0, s, _ => eInit s
  | t + 1, s, ω =>
      let a := amp s (ω (Fin.last t))
      let f := G a.1
      U a.1 (qRun G U t a.1 (Fin.init (α := fun _ => AmpCoin n) ω)) f
        ((f a.2 + expect (unif d) f) / 2)

/-- `K_t = E_{S ∼ D^n} KL(D̃‖q_t(S))`, averaged also over the run's coins (Eq. (5)). -/
noncomputable def Kt {n d : ℕ} (D : Fin d → ℝ) (G : (Fin n → Fin d) → Fin d → ℝ)
    (U : UpdateRule n d) (t : ℕ) : ℝ :=
  ∑ s : Fin n → Fin d, sampleProb D s *
    ((∑ ω : Fin t → AmpCoin n, kl (shift D) (qRun G U t s ω)) /
      (Fintype.card (Fin t → AmpCoin n) : ℝ))

/-- `ℓ_t = E_{S ∼ D^n} (E_{q_t(S)}[f_S] − E_{D̃}[f_S])²`, `f_S = 𝒢(S)`, averaged also over the
run's coins (Eq. (5)). -/
noncomputable def ellt {n d : ℕ} (D : Fin d → ℝ) (G : (Fin n → Fin d) → Fin d → ℝ)
    (U : UpdateRule n d) (t : ℕ) : ℝ :=
  ∑ s : Fin n → Fin d, sampleProb D s *
    ((∑ ω : Fin t → AmpCoin n, (expect (qRun G U t s ω) (G s) - expect (shift D) (G s)) ^ 2) /
      (Fintype.card (Fin t → AmpCoin n) : ℝ))

end DataDepProb.Discrete


