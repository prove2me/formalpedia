-- Prove2me | Definitions.Def_BootRobust_NWDual_Setting
-- name    : BootRobust_NWDual_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:13.307798+00:00
-- url     : https://prove2.me/theorems/0cd71e97-76ec-478b-9ace-5897334a4062
-- title:
--   pp. 8–18 — robust budget (24), Corollary 1 program, dual sets (32)–(33), partial budget (25), and neighbourhood chain
-- statement:
--   This file fixes the finite setting of Bertsimas and Van Parys, *Bootstrap robust prescriptive analytics*, for the dual representations of §4.3. It imports the bootstrap distance, Nadaraya–Watson estimate, and neighbourhood domain from the shared `BootRobust.Perf.Setting` module.
--
--   The training data have finitely many distinct points $\Omega_n$, indexed by a finite set $\iota$. A **distribution** on $\Omega_n$ is a vector $D=(D_i)_{i\in\iota}$ with $D_i\ge 0$ and $\sum_i D_i=1$; the set of all of them is $\mathcal D_n$. For a fixed context $x_0$ and decision $\bar z$, only two numbers per support point matter: the positive weight $w_i=w_n(\bar x_i,x_0)>0$ and the loss $\ell_i=L(\bar z,\bar y_i)$.
--
--   1. **Bootstrap distance** (27). For $D',D\in\mathcal D_n$,
--   $$B(D',D)=\sum_{i} D'_i\log\frac{D'_i}{D_i}\in[0,+\infty],$$
--   with $0\log 0=0$, and $B(D',D)=+\infty$ whenever $D'_i>0=D_i$ for some $i$.
--   2. **Nadaraya–Watson estimate** (19) at $D$:
--   $$E^n_D[\ell]=\frac{\sum_i w_i\,\ell_i\,D_i}{\sum_i w_i\,D_i}.$$
--   3. **Robust budget** (24) with $k(n)=n$, for a distance function $R$, reference $D$ and radius $r\in\mathbb R$:
--   $$c_n(D)=\sup\{E^n_{D'}[\ell] : D'\in\mathcal D_n,\ R(D',D)\le r\},$$
--   an extended real number, equal to $-\infty$ when the ball is empty.
--   4. **Corollary 1's program**: the supremum of $\sum_i w_i\ell_iP_i$ over $s>0$ and $P\in\mathbb R^\iota$ with $P/s\in\mathcal D_n$, $s\,R(P/s,D)\le s\,r$, $\sum_iP_i=s$ and $\sum_iw_iP_i=1$.
--   5. **The dual set of (33)**: the $\alpha\in\mathbb R$ for which some $\nu>0$ satisfies
--   $$\nu\log\Big(\sum_i \exp\big((\ell_i-\alpha)w_i/\nu\big)D_i\Big)+r\nu\le 0.$$
--   6. **Nested neighbourhoods** $N^0\subseteq N^1\subseteq\cdots\subseteq N^n$ of $\Omega_n$ with $N^0=\emptyset$ and $N^n=\Omega_n$, and the set (23)
--   $$\mathcal D^j_n=\Big\{D'\in\mathcal D_n:\ \sum_{N^{j-1}}D'\le\tfrac{k-1}{n},\ \tfrac kn\le\sum_{N^j}D'\Big\}.$$
--   7. **Partial robust budget** (25) with $R=B$: the supremum of $\sum_{N^j}w_i\ell_iP_i$ over $s>0$, $P$ with $P/s\in\mathcal D_n$, $s\,B(P/s,D)\le s\,r$, $\sum_{\Omega_n}P=s$, $\sum_{N^j}wP=1$, $\sum_{N^j}P\ge sk/n$ and $\sum_{N^{j-1}}P\le s(k-1)/n$.
--   8. **The dual set of (32)**: the $\alpha$ for which some $\eta_1,\eta_2\ge0$ and $\nu>0$ satisfy
--   $$\nu\log\Big(\sum_{N^{j-1}}e^{((\ell_i-\alpha)w_i+\eta_1-\eta_2)/\nu}D_i+\sum_{N^j\setminus N^{j-1}}e^{((\ell_i-\alpha)w_i+\eta_1)/\nu}D_i+\sum_{\Omega_n\setminus N^j}D_i\Big)+r\nu-\tfrac kn(\eta_1-\eta_2)-\tfrac{\eta_2}{n}\le0.$$
--
--   These objects are the two sides of Lemmas 1 and 2 and of the intermediate steps of their proofs.
--
--   **Formalization Note** $\Omega_n$ is a `Fintype` and $\mathcal D_n$ is `stdSimplex ℝ ι`; covariates, responses and the distance function of Definition 2 do not appear. $B$ is `EReal`-valued with the absolute-continuity convention, so it is never a finite junk value when the reference has zeros. All suprema and infima are taken in `EReal` (empty supremum $=-\infty$, empty infimum $=+\infty$). The dual sets require $\nu>0$: at $\nu=0$ Lean's $x/0=0$ would make every $\alpha$ feasible; the page's $\nu\in\mathbb R_+$ includes $\nu=0$ only as a perspective limit, which does not change the infimum. "$P/s\in\mathcal D_n$" is implicit on the page (the distance $R$ is only defined on $\mathcal D_n$). The neighbourhood chain is abstracted to a monotone family of finite sets with $N^0=\emptyset$, $N^n=\Omega_n$.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, (19) p. 10, (23) p. 11, Definitions 4–5 and (24)–(25) pp. 11–12, Corollary 1 and Definition 6 (27) p. 13, (32)–(33) pp. 17–18

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.NWDual

/-!
Setting of Bertsimas and Van Parys, *Bootstrap robust prescriptive analytics*, arXiv:1711.09974v2,
§2–§4 and §4.3. The empirical support `Ωₙ` is a finite type `ι`; a distribution on it is a vector
`D : ι → ℝ` in `stdSimplex ℝ ι` (the set `Dₙ`). Only the weights `w i = wₙ(x̄ᵢ, x₀)` and the losses
`ℓ i = L(z̄, ȳᵢ)` of the support points enter the statements.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The robust Nadaraya–Watson budget (24), p. 12, with `k(n) = n`, around a reference
distribution `D`, for a distance function `R` and a radius `r`:
`sup { BootRobust.Perf.nwEst w ℓ D' : D' ∈ Dₙ, R(D', D) ≤ r }`, in `EReal` (the supremum of the empty set is `⊥`). -/
noncomputable def robustNW (R : (ι → ℝ) → (ι → ℝ) → EReal) (D : ι → ℝ) (r : ℝ) (w ℓ : ι → ℝ) :
    EReal :=
  ⨆ D' ∈ {D' : ι → ℝ | D' ∈ stdSimplex ℝ ι ∧ R D' D ≤ (r : EReal)}, ((BootRobust.Perf.nwEst w ℓ D' : ℝ) : EReal)

/-- The perspective program of Corollary 1, p. 13: the supremum over `s > 0` and `P : ι → ℝ` with
`P / s ∈ Dₙ`, `s · R(P/s, D) ≤ s · r`, `∑ᵢ Pᵢ = s` and `∑ᵢ wᵢ Pᵢ = 1` of `∑ᵢ wᵢ ℓᵢ Pᵢ`, in `EReal`. -/
noncomputable def perspValue (R : (ι → ℝ) → (ι → ℝ) → EReal) (D : ι → ℝ) (r : ℝ) (w ℓ : ι → ℝ) :
    EReal :=
  ⨆ sP ∈ {sP : ℝ × (ι → ℝ) | 0 < sP.1 ∧ (fun i => sP.2 i / sP.1) ∈ stdSimplex ℝ ι ∧
      (sP.1 : EReal) * R (fun i => sP.2 i / sP.1) D ≤ (sP.1 : EReal) * (r : EReal) ∧
      ∑ i, sP.2 i = sP.1 ∧ ∑ i, w i * sP.2 i = 1},
    ((∑ i, w i * ℓ i * sP.2 i : ℝ) : EReal)

/-- The feasible values of `α` in the dual program (33), p. 18: those `α` for which some `ν > 0`
satisfies `ν log (∑ᵢ exp((ℓᵢ − α) wᵢ / ν) Dᵢ) + r ν ≤ 0`. -/
noncomputable def dualSet (D : ι → ℝ) (r : ℝ) (w ℓ : ι → ℝ) : Set ℝ :=
  {α | ∃ ν : ℝ, 0 < ν ∧
    ν * Real.log (∑ i, Real.exp ((ℓ i - α) * w i / ν) * D i) + r * ν ≤ 0}

/-- A nested neighbourhood chain `N⁰ ⊆ N¹ ⊆ ⋯ ⊆ Nⁿ` of subsets of the support (Definition 2, p. 8),
abstracted to its order structure: monotone, `N 0 = ∅` and `N n = Ωₙ`. -/
def IsNeighborhoodChain (n : ℕ) (N : ℕ → Finset ι) : Prop :=
  Monotone N ∧ N 0 = ∅ ∧ N n = Finset.univ

/-- The partial bootstrap robust budget `cⁿʲ(z̄, D, x₀)` of (25), p. 12, with `R = B`: the supremum
over `s > 0` and `P` with `P / s ∈ Dₙ`, `s · B(P/s, D) ≤ s · r`, `∑_{Ωₙ} P = s`,
`∑_{N^j} w P = 1`, `∑_{N^j} P ≥ s k / n` and `∑_{N^{j−1}} P ≤ s (k − 1)/n` of `∑_{N^j} w ℓ P`. -/
noncomputable def partialRobust (n k : ℕ) (N : ℕ → Finset ι) (w ℓ D : ι → ℝ) (r : ℝ) (j : ℕ) :
    EReal :=
  ⨆ sP ∈ {sP : ℝ × (ι → ℝ) | 0 < sP.1 ∧ (fun i => sP.2 i / sP.1) ∈ stdSimplex ℝ ι ∧
      (sP.1 : EReal) * BootRobust.Perf.bootDist (fun i => sP.2 i / sP.1) D ≤ (sP.1 : EReal) * (r : EReal) ∧
      ∑ i, sP.2 i = sP.1 ∧ ∑ i ∈ N j, w i * sP.2 i = 1 ∧
      sP.1 * (k : ℝ) / n ≤ ∑ i ∈ N j, sP.2 i ∧
      ∑ i ∈ N (j - 1), sP.2 i ≤ sP.1 * ((k : ℝ) - 1) / n},
    ((∑ i ∈ N j, w i * ℓ i * sP.2 i : ℝ) : EReal)

/-- The feasible values of `α` in the dual program (32), p. 17: those `α` for which some
`η₁, η₂ ≥ 0` and `ν > 0` satisfy
`ν log( ∑_{N^{j−1}} exp(((ℓᵢ − α) wᵢ + η₁ − η₂)/ν) Dᵢ + ∑_{N^j \ N^{j−1}} exp(((ℓᵢ − α) wᵢ + η₁)/ν) Dᵢ
  + ∑_{Ωₙ \ N^j} Dᵢ ) + r ν − (k/n)(η₁ − η₂) − η₂/n ≤ 0`. -/
noncomputable def dualSet1 (n k : ℕ) (N : ℕ → Finset ι) (w ℓ D : ι → ℝ) (r : ℝ) (j : ℕ) :
    Set ℝ :=
  {α | ∃ η₁ η₂ ν : ℝ, 0 ≤ η₁ ∧ 0 ≤ η₂ ∧ 0 < ν ∧
    ν * Real.log (∑ i ∈ N (j - 1), Real.exp (((ℓ i - α) * w i + η₁ - η₂) / ν) * D i +
        ∑ i ∈ N j \ N (j - 1), Real.exp (((ℓ i - α) * w i + η₁) / ν) * D i +
        ∑ i ∈ Finset.univ \ N j, D i) +
      r * ν - (k : ℝ) / n * (η₁ - η₂) - η₂ / n ≤ 0}

end BootRobust.NWDual


