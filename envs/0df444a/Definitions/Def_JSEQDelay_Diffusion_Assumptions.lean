-- Prove2me | Definitions.Def_JSEQDelay_Diffusion_Assumptions
-- name    : JSEQDelay_Diffusion_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:52.410619+00:00
-- url     : https://prove2.me/theorems/8a6c1627-6d1b-4ebc-b243-4a94d6eff423
-- title:
--   §3.3–3.4, pp. 12–14 — the limiting estimator and Assumptions 3.5, 3.8, 3.9
-- statement:
--   Let $\tau$ be a delay function and let $\hat\Psi^n$ be the scaled estimators of the $n$-th network.
--
--   1. A **limiting estimator** $\hat\Psi$ maps $(q,a)\in\mathbb C_0(\mathbb R_+^K)\times\mathbb C_0(\mathbb R^K)$ to $\mathbb C_0(\mathbb R^K)$, measurably for each time, and $\hat\Psi(q,a)(t)$ depends only on $q_k$ on $[0,\tau_k(t)]$ and on $a$ on $[0,t]$. Its estimated queue length is (32)
--   $$\hat\Phi_k(q,a)(t)=q_k(\tau_k(t))+a_k(t)-a_k(\tau_k(t))+\hat\Psi_k(q,a)(t).$$
--   2. **Assumption 3.5.** If $(q^n,a^n)\in\mathbb D_0(\mathbb R_+^K)\times\mathbb D_0(\mathbb R^K)$, $(q,a)\in\mathbb C_0(\mathbb R_+^K)\times\mathbb C_0(\mathbb R^K)$ and $(q^n,a^n)\to(q,a)$ uniformly on compacts, then $\hat\Psi^n(q^n,a^n)\to\hat\Psi(q,a)$ uniformly on compacts.
--   3. **Assumption 3.8.** With $w(f,\delta,T)=\sup\{|f(t)-f(s)|:s,t\in[0,T],|t-s|\le\delta\}$, there are $\zeta_1\in[0,1)$ and a remainder $o(T,\delta,n)$ not depending on $(q,a)$ such that for all $n$, $(q,a)\in\mathbb D_0(\mathbb R_+^K)\times\mathbb D_0(\mathbb R^K)$, $T$, $\delta\in(0,T)$ and $k$,
--   $$w(\hat\Psi^n_k(q,a),\delta,T)\le w(q_k\circ\tau_k,\delta,T)+2w(a_k\circ\tau_k,\delta,T)+\zeta_1w(a_k,\delta,T)+o(T,\delta,n),$$
--   and $\lim_{\delta\to0}\limsup_{n\to\infty}o(T,\delta,n)\le 0$ for every $T$.
--   4. **Assumption 3.9.** There is $\zeta_2\in[0,1)$ such that for $q\in\mathbb C_0(\mathbb R_+^K)$, $a,a'\in\mathbb C_0(\mathbb R^K)$, $t>0$ and $k$,
--   $$|\hat\Psi_k(q,a)(t)-\hat\Psi_k(q,a')(t)|\le\zeta_2\sup_{\tau_k(t)\le s\le t}\big|a_k[\tau_k(t),s]-a'_k[\tau_k(t),s]\big|.$$
--
--   These are the hypotheses on the estimators under which Theorem 4.4 holds; Lemma 3.10 shows that a rich class of estimators satisfies them.
--
--   **Formalization Note** By Remark 3.6, $J_1$ convergence to a continuous limit is uniform convergence on compacts, so Assumption 3.5 is stated with the $\ell^1$ sup-distance `supDist`. Moduli are the published `modulus` (in $[0,\infty]$) of the one-coordinate path. The page's $o_{\delta,n}(1)$ with $\lim_{\delta\to0}\lim_{n\to\infty}o_{\delta,n}(1)=0$ is weakened to a remainder that may also depend on $T$ and whose iterated limit is read as a $\limsup$ upper bound; the proofs of Lemmas 5.2–5.3 fix $T$ first, and the weaker hypothesis gives the stronger theorem. Measurability is on the subtype of admissible pairs with the product σ-algebra. $\hat\Psi$ is unconstrained off $\mathbb C_0(\mathbb R_+^K)\times\mathbb C_0(\mathbb R^K)$.
-- source:
--   Atar & Lipshutz, Heavy traffic limits for join the shortest estimated queue policy using delayed information, authors' manuscript of January 12, 2020 (Math. Oper. Res. 46(3), 2021, doi:10.1287/moor.2020.1056), p. 12, (32) and the definition of Ψ̂; pp. 13–14, Assumption 3.5, Remark 3.6, Assumption 3.8 (37), Assumption 3.9 (38)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_CTight
import Definitions.Def_JSEQDelay_Diffusion_Model

namespace JSEQDelay.Diffusion

open MeasureTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

/-!
Atar & Lipshutz (authors' manuscript of January 12, 2020), §3.3 (32), p. 12 and §3.4,
pp. 13–14: the limiting estimator and Assumptions 3.5, 3.8 and 3.9 on the estimators.
-/

/-- `(q, a) ∈ ℂ₀(ℝ₊^K) × ℂ₀(ℝ^K)` (p. 12): both paths are continuous on `[0, ∞)` and start at
`0`, and `q` is non-negative on `[0, ∞)`. -/
def IsC0Pair {K : ℕ} (q a : Path K) : Prop :=
  ContinuousOn q (Set.Ici 0) ∧ ContinuousOn a (Set.Ici 0) ∧ q 0 = 0 ∧ a 0 = 0 ∧
  ∀ t, 0 ≤ t → ∀ k, 0 ≤ q t k

/-- **Limiting estimator** `Ψ̂` (p. 12): on `ℂ₀(ℝ₊^K) × ℂ₀(ℝ^K)` (`IsC0Pair`),
1. for each `t`, `(q, a) ↦ Ψ̂(q, a)(t)` is measurable for the product σ-algebra on paths;
2. `Ψ̂(q, a)` is continuous on `[0, ∞)` and starts at `0` (it maps into `ℂ₀(ℝ^K)`);
3. `Ψ̂(q, a)(t)` depends only on `(q|_{τ(t)}, a|_t)`.
Values of `Ψ̂` off `ℂ₀(ℝ₊^K) × ℂ₀(ℝ^K)` are unconstrained and never used. -/
def IsLimitEstimator {K : ℕ} (τ : ℝ → Fin K → ℝ) (Ψ : Path K → Path K → Path K) : Prop :=
  (∀ t, Measurable (fun p : {p : Path K × Path K // IsC0Pair p.1 p.2} => Ψ p.1.1 p.1.2 t)) ∧
  (∀ q a, IsC0Pair q a → ContinuousOn (Ψ q a) (Set.Ici 0) ∧ Ψ q a 0 = 0) ∧
  (∀ q a q' a', IsC0Pair q a → IsC0Pair q' a' → ∀ t, 0 ≤ t →
    (∀ k, ∀ s ∈ Set.Icc 0 (τ t k), q' s k = q s k) → (∀ s ∈ Set.Icc 0 t, a' s = a s) →
    Ψ q' a' t = Ψ q a t)

/-- The limiting estimated-queue-length function `Φ̂` of (32), p. 12:
`Φ̂_k(q, a)(t) = q_k(τ_k(t)) + a_k[τ_k(t), t] + Ψ̂_k(q, a)(t)`. -/
def PhiLim {K : ℕ} (τ : ℝ → Fin K → ℝ) (Ψ : Path K → Path K → Path K) (q a : Path K) :
    Path K :=
  fun t k => q (τ t k) k + (a t k - a (τ t k) k) + Ψ q a t k

/-- The modulus of continuity of a real path, `w(f, δ, T) = sup{|f(t) − f(s)| : s, t ∈ [0, T],
|t − s| ≤ δ}` (p. 14), in `[0, ∞]`: the published `modulus` of the one-coordinate path. -/
noncomputable def scalarModulus (f : ℝ → ℝ) (T δ : ℝ) : ℝ≥0∞ :=
  modulus (fun t (_ : Fin 1) => f t) T δ

/-- **Assumption 3.5** (p. 13), with the u.o.c. form of convergence licensed by Remark 3.6
(all limits are continuous): if `(qⁿ, aⁿ) ∈ 𝔻₀(ℝ₊^K) × 𝔻₀(ℝ^K)`, `(q, a) ∈ ℂ₀(ℝ₊^K) × ℂ₀(ℝ^K)`
and `(qⁿ, aⁿ) → (q, a)` uniformly on compact time intervals, then `Ψ̂ⁿ(qⁿ, aⁿ) → Ψ̂(q, a)`
uniformly on compact time intervals. `PsiHatSeq n` is the scaled estimator `Ψ̂ⁿ`. -/
def Assumption35 {K : ℕ} (PsiHatSeq : ℕ → Path K → Path K → Path K)
    (PsiLim : Path K → Path K → Path K) : Prop :=
  ∀ (qn an : ℕ → Path K) (q a : Path K),
    (∀ n, IsD0Pair (qn n) (an n)) → IsC0Pair q a →
    (∀ T, 0 ≤ T → Tendsto (fun n => supDist (qn n) q T) atTop (𝓝 0)) →
    (∀ T, 0 ≤ T → Tendsto (fun n => supDist (an n) a T) atTop (𝓝 0)) →
    ∀ T, 0 ≤ T → Tendsto (fun n => supDist (PsiHatSeq n (qn n) (an n)) (PsiLim q a) T)
      atTop (𝓝 0)

/-- **Assumption 3.8** (p. 14): there are `ζ₁ ∈ [0, 1)` and a function `o(T, δ, n)` not
depending on `(q, a)` such that for all `n`, `(q, a) ∈ 𝔻₀(ℝ₊^K) × 𝔻₀(ℝ^K)`, `T`,
`δ ∈ (0, T)` and `k`, (37) holds:
`w(Ψ̂ⁿ_k(q, a), δ, T) ≤ w(q_k ∘ τ_k, δ, T) + 2 w(a_k ∘ τ_k, δ, T) + ζ₁ w(a_k, δ, T) + o(T, δ, n)`,
and `lim_{δ → 0} limsup_{n → ∞} o(T, δ, n) ≤ 0` for every `T`: for every `ε > 0` there is
`δ₀ > 0` with `o(T, δ, n) ≤ ε` for all `δ ∈ (0, δ₀)` and all large `n`. (The page writes
`o_{δ,n}(1)` with `lim_{δ→0} lim_{n→∞} o_{δ,n}(1) = 0`; here the remainder may also depend on
`T`.) `PsiHatSeq n` is the scaled estimator `Ψ̂ⁿ`. -/
def Assumption38 {K : ℕ} (τ : ℝ → Fin K → ℝ) (PsiHatSeq : ℕ → Path K → Path K → Path K) :
    Prop :=
  ∃ ζ₁ : ℝ, 0 ≤ ζ₁ ∧ ζ₁ < 1 ∧ ∃ o : ℝ → ℝ → ℕ → ℝ,
    (∀ (n : ℕ) (q a : Path K), IsD0Pair q a → ∀ T δ : ℝ, 0 < δ → δ < T → ∀ k,
      scalarModulus (fun t => PsiHatSeq n q a t k) T δ ≤
        scalarModulus (fun t => q (τ t k) k) T δ +
        2 * scalarModulus (fun t => a (τ t k) k) T δ +
        ENNReal.ofReal ζ₁ * scalarModulus (fun t => a t k) T δ + ENNReal.ofReal (o T δ n)) ∧
    ∀ T ε : ℝ, 0 < T → 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      ∀ᶠ n in atTop, o T δ n ≤ ε

/-- **Assumption 3.9** (contraction property of the limiting estimator, p. 14): there is
`ζ₂ ∈ [0, 1)` such that for all `q ∈ ℂ₀(ℝ₊^K)`, `a, a' ∈ ℂ₀(ℝ^K)`, `t > 0` and `k`, (38):
`|Ψ̂_k(q, a)(t) − Ψ̂_k(q, a')(t)| ≤ ζ₂ sup_{τ_k(t) ≤ s ≤ t} |a_k[τ_k(t), s] − a'_k[τ_k(t), s]|`. -/
def Assumption39 {K : ℕ} (τ : ℝ → Fin K → ℝ) (PsiLim : Path K → Path K → Path K) : Prop :=
  ∃ ζ₂ : ℝ, 0 ≤ ζ₂ ∧ ζ₂ < 1 ∧
    ∀ q a a' : Path K, IsC0Pair q a → IsC0Pair q a' → ∀ t, 0 < t → ∀ k,
      ENNReal.ofReal |PsiLim q a t k - PsiLim q a' t k| ≤
        ENNReal.ofReal ζ₂ * ⨆ (s : ℝ) (_ : s ∈ Set.Icc (τ t k) t),
          ENNReal.ofReal |(a s k - a (τ t k) k) - (a' s k - a' (τ t k) k)|

end JSEQDelay.Diffusion


