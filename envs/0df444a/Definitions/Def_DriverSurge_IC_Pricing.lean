-- Prove2me | Definitions.Def_DriverSurge_IC_Pricing
-- name    : DriverSurge_IC_Pricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:26.376725+00:00
-- url     : https://prove2.me/theorems/bbd97cb1-a2e4-4e50-86ea-fd0015bdeca6
-- title:
--   Thm 3, Lemmas 5, 6, App. D.3.1, p. 63 — prices m_iτ + z_iq_{i→j}(τ), the constant C, r(u, i, w, σ), marginal gain ∂/∂u, strict quasi-convexity, surge state, policy forms
-- statement:
--   The vocabulary for the pricing and optimality results of Garg and Nazerzadeh.
--
--   1. **Prices** (Theorem 3, p. 13): $w_i(\tau)=m_i\tau+z_i\,q_{i\to j}(\tau)$.
--   2. **The constant** of Theorem 3 (pp. 13, 61), with $\bar T_i$, $\bar Q_i$ the values of $T_i$, $Q_i$ at accept-all:
--   $$C=1-\frac{1}{\bar T_1}\cdot\frac{\bar Q_2(\lambda_{1\to2}\bar T_1-\bar Q_1)+\bar Q_1(\bar T_2\lambda_{1\to2}+\bar Q_2)}{\bar Q_2(\lambda_{1\to2}\bar T_1-\bar Q_1)+\lambda_{1\to2}(\bar T_2\lambda_{1\to2}+\bar Q_2)}.$$
--   3. The policy $\{(0,t_1),(0,\infty)\}$ for $t_1\in[0,\infty]$.
--   4. **The function of Lemma 6** (p. 57), with $\Delta_{ji}=R_j-R_i$:
--   $$r(u,i,w,\sigma)=\frac{q_{i\to j}(u)}{u}\Delta_{ji}+\frac{w_i(u)}{u}\Big(\frac{Q_i}{T_i}+\frac{Q_j}{T_j}\Big)-\Big(\frac{Q_i}{T_i}R_j+\frac{Q_j}{T_j}R_i\Big).$$
--   5. **Marginal gain** (pp. 50, 56): $\partial/\partial u\,\hat R(\sigma)=D$ means $\big(\hat R(\sigma\cup(u,u+h))-\hat R(\sigma\setminus[u,u+h])\big)/h\to D$ as $h\downarrow0$, "the infinitesimal gain in the value of $\hat R(\sigma)$ by adding $u$ to the set $\sigma$". `rewardOn` is the closed-form reward as a function of one state's policy.
--   6. **Strict quasi-convexity** (p. 63): the derivative in $u$ is strictly negative up to a point $U\in[0,\infty]$ and strictly positive above it; strict quasi-concavity is the mirror image.
--   7. **Surge state** (p. 7): some policy $\sigma_2$ has $R_2(w_2,\sigma_2)>R_1(w_1,\sigma_1)$ for every policy $\sigma_1$.
--   8. **Policy forms** (Lemma 5, Theorem 4): $(0,t)$, $(\ell,\infty)$ with $\ell<\infty$, $(0,\ell)\cup(u,\infty)$, $(\ell,u)$, with endpoints in $[0,\infty]$; equality of policies up to null sets; upper endpoints of the intervals of an open set; and the two lists of bullets of Theorem 4 as properties of a set.
--   9. **Continuity in $\sigma$** with respect to the pseudometric $F(\sigma\triangle\sigma')$ (one state) or $F_1(\sigma_1\triangle\sigma_1')+F_2(\sigma_2\triangle\sigma_2')$ (policies).
--
--   **Formalization Note** In Lean indices $\bar T_1=$ `Tn P 0 (Ioi 0)`, $\bar Q_2=$ `Qn P 1 (Ioi 0)` and $\lambda_{1\to2}=$ `P.sw 0`; the printed `λ12` in $C$ is read as $\lambda_{1\to2}$. Under finite means the denominator of $C$ is positive. $r$ is used only at $u>0$ (Lean's $x/0=0$). Endpoints in $[0,\infty]$ are `EReal`s; `(0, t)` is `{τ | 0 < τ ∧ (τ : EReal) < t}`. In Theorem 4's bullets "$\partial/\partial u R(w,\sigma')>0$" is read as $r>0$, the meaning of $\propto$ fixed in D.3.1 ("same sign except where $f(u)=0$"); affine prices have $m_i\ge0$ (§2.4, p. 8).
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, pp. 7, 8, 13, 50–51, 56–58, 61, 63; Theorem 3, Lemmas 5, 6, Theorem 4, App. D.3.1

import Mathlib
import Definitions.Def_DriverSurge_IC_Model

namespace DriverSurge.IC

open MeasureTheory Set Filter Topology

/-! Garg–Nazerzadeh, *Driver Surge Pricing* (arXiv:1905.07544v4): the pricing form of Theorem 3
(p. 13), the constant `C` (pp. 13, 61), the function `r(u, i, w, σ)` of Lemma 6 (p. 57), the marginal
gain `∂/∂u` (pp. 50, 56), strict quasi-convexity (p. 63), the surge-state definition (p. 7), the
policy forms of Lemma 5 and Theorem 4 (pp. 51, 58) and continuity in `σ` (Remark 1, Lemma 5).
State labels: Lean `0` is the paper's non-surge state 1, Lean `1` is the surge state 2. -/

/-- Theorem 3 (p. 13): the prices `w_i(τ) = m_i τ + z_i q_{i→j}(τ)`. -/
noncomputable def price (P : Primitives) (m z : Fin 2 → ℝ) : Fin 2 → ℝ → ℝ :=
  fun i τ => m i * τ + z i * q P i τ

/-- The constant of Theorem 3 (p. 13; derived p. 61):
`C = 1 − (1/T̄_1) · [Q̄_2(λ_{1→2}T̄_1 − Q̄_1) + Q̄_1(T̄_2λ_{1→2} + Q̄_2)] / [Q̄_2(λ_{1→2}T̄_1 − Q̄_1) + λ_{1→2}(T̄_2λ_{1→2} + Q̄_2)]`,
where `T̄_i = λ_iF_i((0,∞))T_i((0,∞))` and `Q̄_i = Q_i((0,∞))` are taken at the accept-all policy and the
printed `λ12` is `λ_{1→2}`. In Lean indices: `T̄_1 = Tn P 0 (Ioi 0)`, `T̄_2 = Tn P 1 (Ioi 0)`,
`Q̄_1 = Qn P 0 (Ioi 0)`, `Q̄_2 = Qn P 1 (Ioi 0)`, `λ_{1→2} = P.sw 0`. Under finite mean the denominator
is positive (`Q̄_2 > 0`, `λ_{1→2}T̄_1 − Q̄_1 ≥ 0`, `λ_{1→2} > 0`) and `T̄_1 ≥ 1`. -/
noncomputable def Cconst (P : Primitives) : ℝ :=
  1 - (1 / Tn P 0 (Ioi 0)) *
    (Qn P 1 (Ioi 0) * (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) +
        Qn P 0 (Ioi 0) * (Tn P 1 (Ioi 0) * P.sw 0 + Qn P 1 (Ioi 0))) /
      (Qn P 1 (Ioi 0) * (P.sw 0 * Tn P 0 (Ioi 0) - Qn P 0 (Ioi 0)) +
        P.sw 0 * (Tn P 1 (Ioi 0) * P.sw 0 + Qn P 1 (Ioi 0)))

/-- The policy `{(0, t₁), (0, ∞)}` of Theorem 3: accept trips shorter than `t₁ ∈ [0, ∞]` in the
non-surge state and every trip in the surge state. -/
def lowerThenAll (t₁ : EReal) : Fin 2 → Set ℝ :=
  ![{τ : ℝ | 0 < τ ∧ (τ : EReal) < t₁}, Ioi 0]

/-- Lemma 6 (p. 57):
`r(u, i, w, σ) = (q_{i→j}(u)/u) Δ_{ji} + (w_i(u)/u)(Q_i/T_i + Q_j/T_j) − (Q_i/T_i · R_j + Q_j/T_j · R_i)`,
with `j` the other state, `R_k = R_k(w_k, σ_k)`, `Δ_{ji} = R_j − R_i`, and `Q_k`, `T_k` the normalized
quantities of D.3.1 at `σ_k`. Statements use it only at `u > 0`. -/
noncomputable def rFun (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i : Fin 2)
    (u : ℝ) : ℝ :=
  q P i u / u * (stateRate P (other i) (w (other i)) (σ (other i)) - stateRate P i (w i) (σ i)) +
    w i u / u * (Qn P i (σ i) / Tn P i (σ i) + Qn P (other i) (σ (other i)) / Tn P (other i) (σ (other i))) -
    (Qn P i (σ i) / Tn P i (σ i) * stateRate P (other i) (w (other i)) (σ (other i)) +
      Qn P (other i) (σ (other i)) / Tn P (other i) (σ (other i)) * stateRate P i (w i) (σ i))

/-- The closed-form reward as a function of state `i`'s policy, the other state's policy fixed:
`s ↦ R(w, σ)` with `σ_i` replaced by `s`. -/
noncomputable def rewardOn (P : Primitives) (w : Fin 2 → ℝ → ℝ) (σ : Fin 2 → Set ℝ) (i : Fin 2)
    (s : Set ℝ) : ℝ :=
  rewardCF P w (Function.update σ i s)

/-- `∂/∂u R̂(σ) = D` (pp. 50, 56): "the infinitesimal gain in the value of `R̂(σ)` by adding `u` to the
set `σ`", i.e. `(R̂(σ ∪ (u, u+h)) − R̂(σ ∖ [u, u+h]))/h → D` as `h ↓ 0`. -/
def HasMarginalGain (R : Set ℝ → ℝ) (s : Set ℝ) (u D : ℝ) : Prop :=
  Tendsto (fun h : ℝ => (R (s ∪ Ioo u (u + h)) - R (s \ Icc u (u + h))) / h) (𝓝[>] 0) (𝓝 D)

/-- Strict quasi-convexity in `u ∈ (0, ∞)` as defined on p. 63: the derivative is strictly negative up
to a point `U ∈ [0, ∞]` and strictly positive above it. -/
def StrictQuasiconvexIoi (g : ℝ → ℝ) : Prop :=
  ∃ U : EReal, 0 ≤ U ∧
    (∀ u : ℝ, 0 < u → (u : EReal) < U → ∃ d, HasDerivAt g d u ∧ d < 0) ∧
    (∀ u : ℝ, 0 < u → U < (u : EReal) → ∃ d, HasDerivAt g d u ∧ 0 < d)

/-- Strict quasi-concavity in `u ∈ (0, ∞)` (mirror of p. 63): the derivative is strictly positive up to
a point `U ∈ [0, ∞]` and strictly negative above it. -/
def StrictQuasiconcaveIoi (g : ℝ → ℝ) : Prop :=
  ∃ U : EReal, 0 ≤ U ∧
    (∀ u : ℝ, 0 < u → (u : EReal) < U → ∃ d, HasDerivAt g d u ∧ 0 < d) ∧
    (∀ u : ℝ, 0 < u → U < (u : EReal) → ∃ d, HasDerivAt g d u ∧ d < 0)

/-- Surge state (§2.2.2, p. 7): state 2 (Lean `1`) has a higher potential earning rate than state 1:
some policy `σ_2` satisfies `R_2(w_2, σ_2) > R_1(w_1, σ_1)` for every policy `σ_1` (open subsets of
`(0, ∞)`). -/
def IsSurgeState (P : Primitives) (w : Fin 2 → ℝ → ℝ) : Prop :=
  ∃ s₂ : Set ℝ, IsOpen s₂ ∧ s₂ ⊆ Ioi 0 ∧
    ∀ s₁ : Set ℝ, IsOpen s₁ → s₁ ⊆ Ioi 0 → stateRate P 0 (w 0) s₁ < stateRate P 1 (w 1) s₂

/-- `(0, t) = {τ | 0 < τ < t}` for `t ∈ [0, ∞]` (`t = ⊤` gives `(0, ∞)`). -/
def lowerSet (t : EReal) : Set ℝ := {τ : ℝ | 0 < τ ∧ (τ : EReal) < t}

/-- `(ℓ, ∞) ∩ (0, ∞) = {τ | 0 < τ, ℓ < τ}` for `ℓ ∈ [0, ∞]` (`ℓ = ⊤` gives `∅`). -/
def upperSet (ℓ : EReal) : Set ℝ := {τ : ℝ | 0 < τ ∧ ℓ < (τ : EReal)}

/-- An admissible single-state policy: an open subset of `(0, ∞)`. -/
def IsAdmissible (s : Set ℝ) : Prop := IsOpen s ∧ s ⊆ Ioi 0

/-- Continuity of a set function `G` on admissible sets with respect to the pseudometric
`F(s △ s')`. -/
def ContinuousInSet (F : Measure ℝ) (G : Set ℝ → ℝ) : Prop :=
  ∀ s, IsAdmissible s → ∀ ε > 0, ∃ δ > 0, ∀ s', IsAdmissible s' →
    F (symmDiff s s') < ENNReal.ofReal δ → |G s' - G s| < ε

/-- Continuity of a function of the policy pair with respect to the pseudometric
`F_1(σ_1 △ σ'_1) + F_2(σ_2 △ σ'_2)`, on policies. -/
def ContinuousInPolicy (P : Primitives) (G : (Fin 2 → Set ℝ) → ℝ) : Prop :=
  ∀ σ, IsPolicy σ → ∀ ε > 0, ∃ δ > 0, ∀ σ', IsPolicy σ' →
    ∑ i, P.F i (symmDiff (σ i) (σ' i)) < ENNReal.ofReal δ → |G σ' - G σ| < ε

/-- Lemma 5 / Theorem 4 form `(0, t)` with `t ∈ [0, ∞]`. -/
def IsLowerForm (s : Set ℝ) : Prop := ∃ t : EReal, 0 ≤ t ∧ s = lowerSet t

/-- Lemma 5 / Theorem 4 form `(ℓ, ∞)` with `ℓ ∈ [0, ∞)`. -/
def IsUpperForm (s : Set ℝ) : Prop := ∃ ℓ : ℝ, 0 ≤ ℓ ∧ s = Ioi ℓ

/-- Lemma 5 / Theorem 4 form `(0, ℓ) ∪ (u, ∞)` with `ℓ, u ∈ [0, ∞]`. -/
def IsTwoSidedForm (s : Set ℝ) : Prop :=
  ∃ ℓ u : EReal, 0 ≤ ℓ ∧ 0 ≤ u ∧ s = lowerSet ℓ ∪ upperSet u

/-- Lemma 5 / Theorem 4 form `(ℓ, u)` with `ℓ, u ∈ [0, ∞]`. -/
def IsBandForm (s : Set ℝ) : Prop :=
  ∃ ℓ u : EReal, 0 ≤ ℓ ∧ 0 ≤ u ∧ s = upperSet ℓ ∩ lowerSet u

/-- Policies are compared up to null sets (§2.2, p. 6: "equality up to changes of measure 0"). -/
def EqUpToNull (F : Measure ℝ) (s t : Set ℝ) : Prop := F (symmDiff s t) = 0

/-- `u` is the upper endpoint of one of the disjoint open intervals that make up the open set `s`:
`u ∉ s` and `(ℓ, u) ⊆ s` for some `ℓ < u`. -/
def IsUpperEndpoint (s : Set ℝ) (u : ℝ) : Prop := u ∉ s ∧ ∃ ℓ < u, Ioo ℓ u ⊆ s

/-- Theorem 4 (p. 58), the non-surge state's bullets as properties of a set `s` (state 1 = Lean `0`),
with affine pricing `w_1(τ) = m_1τ ± a_1`, `m_1 ≥ 0` (§2.4, p. 8):
* if `w_1(τ) = m_1τ + a_1` with `a_1 ≥ 0`, then `s = (0, t_1)` for some `t_1 ∈ [0, ∞]`;
* if `w_1(τ) = m_1τ − a_1` with `a_1 > 0`, then `s = (t_2, t_3)` for some `t_2, t_3 ∈ [0, ∞]`;
* if `∂/∂u R(w, σ') > 0` (read as `r(u, 1, w, σ') > 0`, the `∝` of D.3.1) for every policy `σ'` and
  every upper endpoint `u` of an interval of `σ'_1`, then `s = (0, ∞)`. -/
def NonSurgeForm (P : Primitives) (w : Fin 2 → ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∀ m a : ℝ, 0 ≤ m → 0 ≤ a → w 0 = (fun τ => m * τ + a) → IsLowerForm s) ∧
  (∀ m a : ℝ, 0 ≤ m → 0 < a → w 0 = (fun τ => m * τ - a) → IsBandForm s) ∧
  ((∀ σ', IsPolicy σ' → ∀ u : ℝ, 0 < u → IsUpperEndpoint (σ' 0) u → 0 < rFun P w σ' 0 u) →
    s = Ioi 0)

/-- Theorem 4 (p. 58), the surge state's bullets as properties of a set `s` (state 2 = Lean `1`), with
affine pricing `w_2(τ) = m_2τ ± a_2`, `m_2 ≥ 0` (§2.4, p. 8):
* if `w_2(τ) = m_2τ − a_2` with `a_2 ≥ 0`, then `s = (t_4, ∞)` for some `t_4 ∈ [0, ∞)`;
* if `w_2(τ) = m_2τ + a_2` with `a_2 > 0`, then `s = (0, t_5) ∪ (t_6, ∞)` for some `t_5, t_6 ∈ [0, ∞]`;
* if `r(u, 2, w, σ') > 0` for every policy `σ'` and every upper endpoint `u` of an interval of `σ'_2`,
  then `s = (0, ∞)`. -/
def SurgeForm (P : Primitives) (w : Fin 2 → ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∀ m a : ℝ, 0 ≤ m → 0 ≤ a → w 1 = (fun τ => m * τ - a) → IsUpperForm s) ∧
  (∀ m a : ℝ, 0 ≤ m → 0 < a → w 1 = (fun τ => m * τ + a) → IsTwoSidedForm s) ∧
  ((∀ σ', IsPolicy σ' → ∀ u : ℝ, 0 < u → IsUpperEndpoint (σ' 1) u → 0 < rFun P w σ' 1 u) →
    s = Ioi 0)

end DriverSurge.IC


