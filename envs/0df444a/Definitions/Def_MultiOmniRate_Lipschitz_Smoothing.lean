-- Prove2me | Definitions.Def_MultiOmniRate_Lipschitz_Smoothing
-- name    : MultiOmniRate_Lipschitz_Smoothing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:22:29.024345+00:00
-- url     : https://prove2.me/theorems/dee5206e-c661-4faa-9772-921776135f62
-- title:
--   Smoothed reporting (3.1), smoothed decision weights (3.2), uniform covers (Definition 3.9), the corner simplex and the rate functions of (3.3)–(3.5)
-- statement:
--   1. **Reporting rule (3.1).** From a base prediction $q(x)\in\Delta_K$ (possibly randomized) the learner reports
--   $$p(x)=(1-r)\,q(x)+r\,z,\qquad z\sim\mathrm{Unif}(\Delta_K),$$
--   with $z$ fresh and independent of the example and of $q(x)$.
--   2. **Smoothed decision weights (3.2).** For a loss $\ell$ with properized loss $\ell^{\mathrm{pr}}$,
--   $$w_{\ell,r}(q)=\mathbb E_{z\sim\mathrm{Unif}(\Delta_K)}\big[\Delta\ell^{\mathrm{pr}}((1-r)q+rz)\big]\in\mathbb R^K .$$
--   The class of all of them is $\{w_{\ell,r}:\ell\in\mathcal L_{\mathrm{All}}\}$.
--   3. **Uniform cover (Definition 3.9).** A finite set $\mathcal B$ is a uniform $u$-cover of a class $\mathcal F$ of maps $Z\to\mathbb R^K$ if every $f\in\mathcal F$ has $b\in\mathcal B$ with $\|f-b\|_\infty=\sup_{z,k}|f(z)_k-b(z)_k|\le u$; the elements of $\mathcal B$ need not belong to $\mathcal F$.
--   4. **Corner simplex.** $\Sigma_d=\{x\in[0,1]^d:\sum_ix_i\le1\}$, the standard $d$-dimensional simplex of Lemma 3.10 (Appendix A.2.1).
--   5. **Rate functions.** The right-hand side of Lemma 3.11 with constant $C$ is $C\min\{(ru)^{-1/2},\tfrac1u\log\tfrac{C}{ru}\}$ for $K=2$ and $C\min\{(ru)^{-(K-1)/2},\tfrac1u(ru)^{-(K-2)/2}\}$ for $K\ge3$;
--   $$f_K(r)=\begin{cases}\sqrt{\log(2/r)},&K=2,\\ r^{-1/4},&K=3,\\ r^{-1/2}\log(2/r),&K=4,\\ r^{-(K-3)/2},&K\ge5,\end{cases}\qquad \beta_K(r)=\begin{cases}1,&K=2,\\ \log(2/r),&K=3,\\ r^{-(K-3)/2},&K\ge4,\end{cases}$$
--   as in (3.4) and (3.5).
--
--   These are the smoothing and covering objects of §3.2 and §3.4 on which the decision and hypothesis learners are built.
--
--   **Formalization Note.** `smoothKernel r q` is the kernel `(q ×ₖ const Unif(Δ_K))` mapped by $(a,z)\mapsto(1-r)a+rz$. `smoothW r ℓpr q` is coordinatewise a Bochner integral against `unifSimplex K`. `hypBracket K r` is $\beta_K(r)$.
-- source:
--   Rivkin, Okoroafor, Kim, The Sample Complexity of Multi-Class Omniprediction, STOC 2027 submission (manuscript sha256 135d9904…), pp. 25–26, (3.1)–(3.2); p. 29, Definition 3.9 and Lemma 3.11 (3.3); p. 35, (3.4); p. 36, (3.5); p. 55, App. A.2.1 (Σ_d)

import Mathlib
import Definitions.Def_MultiOmniRate_Lipschitz_Setting

set_option autoImplicit false

namespace MultiOmniRate.Lipschitz

open MeasureTheory ProbabilityTheory

noncomputable section

/-!
# Smoothed reporting, smoothed decision weights, uniform covers and the rate functions
(Rivkin–Okoroafor–Kim, (3.1)–(3.2) pp. 25–26, Definition 3.9 p. 29, (3.3)–(3.5) pp. 29, 35–36)

* `smoothKernel r q`: the reporting rule (3.1): from a base prediction `q(x)` (itself possibly
  randomized), report `p(x) = (1 − r) q(x) + r z` with a fresh `z ∼ Unif(Δ_K)`.
* `smoothW r ℓpr q = E_z[Δℓ^pr((1 − r) q + r z)]`, the smoothed decision weights (3.2).
* `cornerSimplex d`: `Σ_d = {x ∈ [0, 1]^d : Σ x_i ≤ 1}` (Lemma 3.10, Appendix A.2.1).
* `IsUniformCover B F u`: Definition 3.9, a finite `B` with every `f ∈ F` within sup distance `u`
  (over the domain and the `K` coordinates) of some `b ∈ B`; `B` need not lie in `F`.
* `smoothWClass r = {w_{ℓ,r} : ℓ ∈ L_All}`.
* `bound311 K C r u`: the right-hand side of Lemma 3.11 (two cases, `K = 2` and `K ≥ 3`).
* `fK K r` (four cases, (3.4)) and `hypBracket K r` (three cases, (3.5)).
-/

variable {K : ℕ} {X : Type*} [MeasurableSpace X]

/-- The reporting rule (3.1): `p(x) = (1 − r) q(x) + r z`, `z ∼ Unif(Δ_K)` independent of
everything else. -/
def smoothKernel [NeZero K] (r : ℝ) (q : Kernel X (Simplex K)) : Kernel X (Simplex K) :=
  Kernel.map (q ×ₖ Kernel.const X (unifSimplex K)) (fun az => mix r az.1 az.2)

/-- The smoothed decision weights (3.2): `w_{ℓ,r}(q) = E_{z∼Unif(Δ_K)}[Δℓ^pr((1 − r) q + r z)]`,
for a properized loss `ℓpr = ℓ^pr`. -/
def smoothW [NeZero K] (r : ℝ) (lpr : Simplex K → Fin K → ℝ) (q : Simplex K) : Fin K → ℝ :=
  fun y => ∫ z, dLoss (lpr (mix r q z)) y ∂(unifSimplex K)

/-- Definition 3.9: `B` is a uniform `u`-cover of `F`: every `f ∈ F` has `b ∈ B` with
`‖f − b‖_∞ = sup_{z, k} |f(z)_k − b(z)_k| ≤ u`. -/
def IsUniformCover {Z : Type*} (B : Finset (Z → Fin K → ℝ)) (F : Set (Z → Fin K → ℝ)) (u : ℝ) :
    Prop :=
  ∀ f ∈ F, ∃ b ∈ B, ∀ z k, |f z k - b z k| ≤ u

/-- The standard `d`-dimensional simplex in corner coordinates,
`Σ_d = {x ∈ [0, 1]^d : Σ_i x_i ≤ 1}` (Appendix A.2.1). -/
def cornerSimplex (d : ℕ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ 1}

universe u

/-- The smoothed decision weights of all bounded losses, `{w_{ℓ,r} : ℓ ∈ L_All}`. -/
def smoothWClass (K : ℕ) [NeZero K] (r : ℝ) : Set (Simplex K → Fin K → ℝ) :=
  {w | ∃ ℓ : AllLoss.{u} K, w = smoothW r ℓ.ℓ.pr}

/-- The right-hand side of Lemma 3.11 with constant `C`:
for `K = 2`, `C · min{(ru)^{−1/2}, (1/u) log(C/(ru))}`;
for `K ≥ 3`, `C · min{(ru)^{−(K−1)/2}, (1/u)(ru)^{−(K−2)/2}}`. -/
def bound311 (K : ℕ) (C r u : ℝ) : ℝ :=
  if K = 2 then C * min ((r * u) ^ (-(1 / 2 : ℝ))) (1 / u * Real.log (C / (r * u)))
  else C * min ((r * u) ^ (-((K : ℝ) - 1) / 2)) (1 / u * (r * u) ^ (-((K : ℝ) - 2) / 2))

/-- `f_K(r)` of (3.4): `√log(2/r)` (K = 2), `r^{−1/4}` (K = 3), `r^{−1/2} log(2/r)` (K = 4),
`r^{−(K−3)/2}` (K ≥ 5). -/
def fK (K : ℕ) (r : ℝ) : ℝ :=
  if K = 2 then Real.sqrt (Real.log (2 / r))
  else if K = 3 then r ^ (-(1 / 4 : ℝ))
  else if K = 4 then r ^ (-(1 / 2 : ℝ)) * Real.log (2 / r)
  else r ^ (-((K : ℝ) - 3) / 2)

/-- The bracket of (3.5): `1` (K = 2), `log(2/r)` (K = 3), `r^{−(K−3)/2}` (K ≥ 4). -/
def hypBracket (K : ℕ) (r : ℝ) : ℝ :=
  if K = 2 then 1
  else if K = 3 then Real.log (2 / r)
  else r ^ (-((K : ℝ) - 3) / 2)

end

end MultiOmniRate.Lipschitz


