-- Prove2me | Definitions.Def_WFMFG_Conv_Setting
-- name    : WFMFG_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:37.588989+00:00
-- url     : https://prove2.me/theorems/34286185-f7a5-47ac-9832-f58c610e3c62
-- title:
--   Notation and §2–4, pp. 5–24 — weights $\mathbb Y$, $\mu^N_{x,y}$ (1.1), cutoff (2.2), $H$, $a^*$ (2.11), Nash system (3.2)–(3.3), master equation (2.3), regularity of $U$, $z^{N,l}$, $\mathcal T_N$
-- statement:
--   Fix $d \ge 1$ states $[\![d]\!]$ and $N \ge 1$ players $[\![N]\!]$. A configuration is $x \in [\![d]\!]^N$; for $m \in [\![N]\!]$ and $j \in [\![d]\!]$, $(j, x^{-m})$ is $x$ with the $m$-th entry replaced by $j$.
--
--   1. **Weights.** $\mathbb Y$ is the set of $y \in \mathbb Q^N$ with $y^l \ge 0$ and $\sum_l y^l = N$. The **weighted empirical measure** is $\mu^N_{x,y}[i] = \frac1N \sum_l y^l \mathbb 1_{\{x^l = i\}}$ (1.1); for $y \in \mathbb Y$ it lies in $\mathcal S_{d-1}$.
--   2. **Cutoff (2.2).** $\varphi$ is nonnegative, non-increasing and Lipschitz on $[0,\infty)$, with $\varphi(r) = \kappa$ for $0 \le r \le \delta$ and $\varphi(r) = 0$ for $r > 2\delta$.
--   3. **Hamiltonian (2.11).** $H(i, u) = -\frac12 \sum_{j \ne i} (u^i - u^j)_+^2$ and $a^*(i,u)[j] = (u^i - u^j)_+$, with $r_+ = \max(r,0)$.
--   4. **Reweighting (p. 9).** For a multi-index $k$, the ratio $k_{x^l}/(N \mu^N_{x,y}[x^l])$ is taken to be $1$ when $\mu^N_{x,y}[x^l] = 0$, and $y'$ is the tuple $\big(y^l\, k_{x^l}/(N\mu^N_{x,y}[x^l])\big)_{l}$.
--   5. **Normalized Nash system (3.2)–(3.3).** An $N$-tuple $w = (w^{N,l})_l$ of functions of $(t,x,y)$ is a bounded classical solution if, for all $l$, $x$, $y \in \mathbb Y$ and $t \in [0,T]$,
--   $$
--   \begin{aligned}
--   &\tfrac{d}{dt} w^{N,l} + \sum_{m} \sum_j \varphi(\mu^N_{x,y}[j])\, \Delta^m w^{N,l}[j] + \sum_{m \ne l} \sum_j a^*(x^m, w^{N,m}_\bullet)[j]\, \Delta^m w^{N,l}[j] + H(x^l, w^{N,l}_\bullet) + f(x^l, \mu^N_{x,y}) \\
--   &\quad + \varepsilon N\, \mathbf E\Big[\frac{S[x^l]}{N\mu^N_{x,y}[x^l]}\big(w^{N,l}(t, x, y') - w^{N,l}(t,x,y)\big)\Big] = 0,
--   \end{aligned}
--   $$
--   with $S \sim \mathcal M_{N, \mu^N_{x,y}}$, $y'$ the reweighting by $S$, $\Delta^m w(x,y)[j] = w((j,x^{-m}),y) - w(x,y)$ and $w^{N,l}_\bullet = (w^{N,l}(t,(j,x^{-l}),y))_j$; the terminal condition $w^{N,l}(T,x,y) = g(x^l, \mu^N_{x,y})$ holds; and $w$ is bounded on $[0,T] \times [\![d]\!]^N \times \mathbb Y$. The time derivative is one-sided at $0$ and $T$.
--   6. **Master equation (2.3).** $U = (U^1, \dots, U^d)$ is a classical solution if it is continuous on $[0,T] \times \mathcal S_{d-1}$, $U^i(T,p) = g^i(p)$ on $\mathcal S_{d-1}$, and on $[0,T] \times \operatorname{Int}\mathcal S_{d-1}$
--   $$
--   \begin{aligned}
--   &\partial_t U^i - \tfrac12 \sum_{j \ne i} (U^i - U^j)_+^2 + f^i(p) + \sum_j \varphi(p_j)(U^j - U^i) + \sum_{j,k} p_k\big[\varphi(p_j) + (U^k - U^j)_+\big](\mathfrak d_j U^i - \mathfrak d_k U^i) \\
--   &\quad + \varepsilon \sum_{j \ne i} p_j (\mathfrak d_i U^i - \mathfrak d_j U^i) + \frac{\varepsilon}{2} \sum_{j,k} (p_j \delta_{j,k} - p_j p_k)\, \mathfrak d^2_{j,k} U^i = 0.
--   \end{aligned}
--   $$
--   7. **Regularity of $U$.** For $\gamma' \in (0,1)$: $U$ is continuous on $[0,T]\times\mathcal S_{d-1}$; at interior points $U^i(t,\cdot)$ and each $\mathfrak d_k U^i(t,\cdot)$ are differentiable along the simplex; and there is $K$ with $|U^i| \le K$, $|\mathfrak d_j U^i| \le K$, $|\mathfrak d_j U^i(t,p) - \mathfrak d_j U^i(t,q)| \le K\|p - q\|^{\gamma'/2}$, $|\sqrt{p_j p_k}\, \mathfrak d^2_{j,k} U^i(t,p)| \le K$ and $|\sqrt{p_jp_k}\,\mathfrak d^2_{j,k}U^i(t,p) - \sqrt{q_jq_k}\,\mathfrak d^2_{j,k}U^i(t,q)| \le K \|p - q\|^{\gamma'/2}$ for $t \in [0,T]$ and interior $p, q$.
--   8. **Along the empirical measure.** $z^{N,l}(t,x,y) = U^{x^l}(t, \mu^N_{x,y})$ (2.18) and $u^{N,l} = y^l z^{N,l}$ (4.21). The set $\mathcal T_N$ (4.22) consists of the $(x, y) \in [\![d]\!]^N \times \mathbb Y$ with $\min_i \mu^N_{x,y}[i] \ge N^{-\epsilon}$ and $\max_l y^l \le \frac12 N^{1-\epsilon}$.
--
--   These are the objects of Theorem 2.4: the normalized equilibrium values $w^{N,l}$ of the $N$-player weighted game are compared with $z^{N,l}$.
--
--   **Formalization Note.** (i) The master equation carries $\varepsilon$ and $\varepsilon/2$ where (2.3) prints $\varepsilon^2$ and $\varepsilon^2/2$: the $N$-player common noise rings at rate $\varepsilon N$ (2.6), Lemma 4.8 expands its effect without any $\varepsilon$, and the limit SDE (2.4) has noise $\sqrt\varepsilon$; with $\varepsilon^2$ the identification of §4.2.3 fails. (ii) The Wright–Fisher Hölder space $[\mathcal C^{1+\gamma'/2,2+\gamma'}_{\mathrm{WF}}]^d$, which the paper only describes, is replaced by the regularity class of item 7, the properties §7 (p. 50) says the proofs use; Euclidean distance is the sup norm. (iii) Differentiability "on the simplex" is Fréchet differentiability within the hyperplane $\sum_i q_i = 1$. (iv) Weights are rational; functions are defined on all of $\mathbb Q^N$, and every condition is imposed only for $y \in \mathbb Y$ and $t \in [0,T]$. (v) Membership $y \in \mathbb Y$ is stated separately from the two conditions defining $\mathcal T_N$.
-- source:
--   Bayraktar, Cecchin, Cohen & Delarue, Finite State Mean Field Games with Wright–Fisher Common Noise as Limits of N-Player Weighted Games, arXiv:2012.04845v2, pp. 5–24, (1.1), (2.2), (2.3), (2.11), (2.18), (3.2), (3.3), (4.21), (4.22); p. 8 items (1)–(3); p. 50 (§7)

import Mathlib
import Definitions.Def_WFMFG_Conv_Simplex
import Definitions.Def_WFMFG_Conv_Multinomial

open Finset

namespace WFMFG.Conv

/-! ### Weights and the weighted empirical measure (p. 5) -/

/-- The weight set `𝕐`: tuples of nonnegative rationals summing to `N`. -/
def Yset (N : ℕ) : Set (Fin N → ℚ) :=
  {y | (∀ l, 0 ≤ y l) ∧ ∑ l, y l = N}

/-- `μ^N_{x,y}[i] = (1/N) ∑_l y^l 𝟙_{x^l = i}` (1.1), computed in `ℚ`. -/
def empQ {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (i : Fin d) : ℚ :=
  (N : ℚ)⁻¹ * ∑ l, if x l = i then y l else 0

/-- The weighted empirical measure `μ^N_{x,y}` (1.1), as a real `d`-tuple. -/
def empMeas {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) : Fin d → ℝ :=
  fun i => (empQ x y i : ℝ)

/-! ### Cutoff (2.2), Hamiltonian and optimal feedback (2.11) -/

/-- `φ` is a cutoff of (2.2) with parameters `κ, δ`: a nonnegative, non-increasing, Lipschitz
function on `[0, ∞)`, equal to `κ` on `[0, δ]` and to `0` on `(2δ, ∞)`. -/
def IsCutoff (κ δ : ℝ) (φ : ℝ → ℝ) : Prop :=
  (∀ r, 0 ≤ r → 0 ≤ φ r) ∧ AntitoneOn φ (Set.Ici 0) ∧
    (∃ L, LipschitzOnWith L φ (Set.Ici 0)) ∧
    (∀ r ∈ Set.Icc 0 δ, φ r = κ) ∧ (∀ r, 2 * δ < r → φ r = 0)

/-- Positive part `a_+ = max(a, 0)`. -/
def pos (a : ℝ) : ℝ := max a 0

/-- The Hamiltonian `H(i, u) = -(1/2) ∑_{j ≠ i} (u^i - u^j)_+^2` (2.11); the term `j = i` is 0. -/
noncomputable def ham {d : ℕ} (i : Fin d) (u : Fin d → ℝ) : ℝ :=
  -(1 / 2) * ∑ j, (pos (u i - u j)) ^ 2

/-- The minimizer `a*(i, u)[j] = (u^i - u^j)_+` of (2.11). -/
def astar {d : ℕ} (i : Fin d) (u : Fin d → ℝ) (j : Fin d) : ℝ :=
  pos (u i - u j)

/-! ### The common-noise reweighting (pp. 9, 16) -/

/-- The ratio `k_{x^l} / (N μ^N_{x,y}[x^l])`, treated as `1` when `μ^N_{x,y}[x^l] = 0` (p. 9). -/
def ratioQ {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (k : Fin d → ℕ) (l : Fin N) : ℚ :=
  if empQ x y (x l) = 0 then 1 else (k (x l) : ℚ) / (N * empQ x y (x l))

/-- The reweighted tuple `(y^1 k_{x^1}/(Nμ[x^1]), …, y^N k_{x^N}/(Nμ[x^N]))`. -/
def reweight {d N : ℕ} (x : Fin N → Fin d) (y : Fin N → ℚ) (k : Fin d → ℕ) : Fin N → ℚ :=
  fun l => y l * ratioQ x y k l

/-! ### The normalized Nash system (3.2)–(3.3) -/

/-- The two drift sums of (3.2) applied to an `N`-tuple `w` of functions of `(t, x, y)`:
`∑_m φ(μ[•]) · Δ^m w^l[•] + ∑_{m ≠ l} a*(x^m, w^m_•) · Δ^m w^l[•]`. -/
noncomputable def driftOp {d N : ℕ} (φ : ℝ → ℝ)
    (w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (l : Fin N) (t : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) : ℝ :=
  (∑ m, ∑ j, φ (empMeas x y j) * (w l t (Function.update x m j) y - w l t x y))
    + ∑ m ∈ univ.erase l, ∑ j,
        astar (x m) (fun j' => w m t (Function.update x m j') y) j *
          (w l t (Function.update x m j) y - w l t x y)

/-- Everything in (3.2) except `d/dt w^{N,l}`:
drift sums `+ H(x^l, w^l_•) + f(x^l, μ) + εN E[(S[x^l]/(Nμ[x^l])) (w^l(t, x, y') - w^l(t, x, y))]`,
with `y'` the reweighted tuple and `S ∼ 𝓜_{N, μ^N_{x,y}}`. -/
noncomputable def nashOp {d N : ℕ} (ε : ℝ) (φ : ℝ → ℝ) (f : Fin d → (Fin d → ℝ) → ℝ)
    (w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) (l : Fin N) (t : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) : ℝ :=
  driftOp φ w l t x y
    + ham (x l) (fun j => w l t (Function.update x l j) y) + f (x l) (empMeas x y)
    + ε * N * multE N (empMeas x y)
        (fun k => (ratioQ x y k l : ℝ) * (w l t x (reweight x y k) - w l t x y))

/-- `w` is a bounded classical solution of the normalized Nash system (3.2)–(3.3) on
`[0, T] × ⟦d⟧^N × 𝕐`. -/
def IsNashSol {d : ℕ} (N : ℕ) (ε T : ℝ) (φ : ℝ → ℝ) (f g : Fin d → (Fin d → ℝ) → ℝ)
    (w : Fin N → ℝ → (Fin N → Fin d) → (Fin N → ℚ) → ℝ) : Prop :=
  (∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt (fun s => w l s x y) (-(nashOp ε φ f w l t x y)) (Set.Icc 0 T) t) ∧
    (∀ l x, ∀ y ∈ Yset N, w l T x y = g (x l) (empMeas x y)) ∧
    (∃ B : ℝ, ∀ l x, ∀ y ∈ Yset N, ∀ t ∈ Set.Icc 0 T, |w l t x y| ≤ B)

/-! ### The master equation (2.3), with `ε` in place of `ε²` -/

/-- Everything in (2.3) except `∂_t U^i(t, p)`, with the common-noise coefficients `ε` and `ε/2`
(the printed `ε²`, `ε²/2` correspond to the noise intensity of (2.1); the `N`-player noise of
(2.6) at rate `εN` produces `ε`). -/
noncomputable def masterOp {d : ℕ} (ε : ℝ) (φ : ℝ → ℝ) (f : Fin d → (Fin d → ℝ) → ℝ)
    (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) (i : Fin d) (t : ℝ) (p : Fin d → ℝ) : ℝ :=
  -(1 / 2) * ∑ j, (pos (U i t p - U j t p)) ^ 2 + f i p
    + ∑ j, φ (p j) * (U j t p - U i t p)
    + ∑ j, ∑ k, p k * (φ (p j) + pos (U k t p - U j t p)) * (sD (U i t) p j - sD (U i t) p k)
    + ε * ∑ j ∈ univ.erase i, p j * (sD (U i t) p i - sD (U i t) p j)
    + (ε / 2) * ∑ j, ∑ k, (p j * (if j = k then 1 else 0) - p j * p k) * sD2 (U i t) p j k

/-- `U = (U^1, …, U^d)` is a classical solution of the master equation (2.3) (with `ε` for `ε²`):
continuous on `[0,T] × S_{d-1}`, the equation holds on `[0,T] × Int S_{d-1}`, and
`U^i(T, p) = g^i(p)` on `S_{d-1}`. -/
def IsMasterSol {d : ℕ} (ε T : ℝ) (φ : ℝ → ℝ) (f g : Fin d → (Fin d → ℝ) → ℝ)
    (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) : Prop :=
  (∀ i, ContinuousOn (fun z : ℝ × (Fin d → ℝ) => U i z.1 z.2)
      (Set.Icc 0 T ×ˢ stdSimplex ℝ (Fin d))) ∧
    (∀ i, ∀ t ∈ Set.Icc 0 T, ∀ p ∈ simplexInt d,
      HasDerivWithinAt (fun s => U i s p) (-(masterOp ε φ f U i t p)) (Set.Icc 0 T) t) ∧
    (∀ i, ∀ p ∈ stdSimplex ℝ (Fin d), U i T p = g i p)

/-- The regularity class standing for `U ∈ [C^{1+γ'/2, 2+γ'}_WF([0,T] × S_{d-1})]^d`, in the form
§7 (p. 50) uses it: `U` continuous on `[0,T] × S_{d-1}`; in the interior, `U^i(t, ·)` and
`𝔡_k U^i(t, ·)` are differentiable within the hyperplane of the simplex; `U`, `𝔡U` are bounded,
`𝔡U` is `γ'/2`-Hölder, and `√(p_j p_k) 𝔡²_{j,k} U` is bounded and `γ'/2`-Hölder on the interior. -/
def WFReg {d : ℕ} (γ' T : ℝ) (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) : Prop :=
  (∀ i, ContinuousOn (fun z : ℝ × (Fin d → ℝ) => U i z.1 z.2)
      (Set.Icc 0 T ×ˢ stdSimplex ℝ (Fin d))) ∧
    (∀ i, ∀ t ∈ Set.Icc 0 T, ∀ p ∈ simplexInt d,
      DifferentiableWithinAt ℝ (U i t) (affPlane d) p ∧
        ∀ k, DifferentiableWithinAt ℝ (fun q => sD (U i t) q k) (affPlane d) p) ∧
    ∃ K : ℝ, ∀ i j k, ∀ t ∈ Set.Icc 0 T, ∀ p ∈ simplexInt d, ∀ q ∈ simplexInt d,
      |U i t p| ≤ K ∧ |sD (U i t) p j| ≤ K ∧
      |sD (U i t) p j - sD (U i t) q j| ≤ K * ‖p - q‖ ^ (γ' / 2) ∧
      |Real.sqrt (p j * p k) * sD2 (U i t) p j k| ≤ K ∧
      |Real.sqrt (p j * p k) * sD2 (U i t) p j k
          - Real.sqrt (q j * q k) * sD2 (U i t) q j k| ≤ K * ‖p - q‖ ^ (γ' / 2)

/-! ### Mean-field values along the empirical measure, and the set `𝒯_N` -/

/-- `z^{N,l}(t, x, y) = U^{x^l}(t, μ^N_{x,y})` (2.18). -/
def zN {d N : ℕ} (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) (l : Fin N) (t : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) : ℝ :=
  U (x l) t (empMeas x y)

/-- `u^{N,l}(t, x, y) = y^l z^{N,l}(t, x, y)` (4.21). -/
def uN {d N : ℕ} (U : Fin d → ℝ → (Fin d → ℝ) → ℝ) (l : Fin N) (t : ℝ)
    (x : Fin N → Fin d) (y : Fin N → ℚ) : ℝ :=
  (y l : ℝ) * zN U l t x y

/-- The conditions of `𝒯_N` (4.22) on `(x, y)`: `min_i μ^N_{x,y}[i] ≥ N^{-ϵ}` and
`max_l y^l ≤ (1/2) N^{1-ϵ}` (membership `y ∈ 𝕐` is required separately). -/
def TN {d N : ℕ} (ϵ : ℝ) (x : Fin N → Fin d) (y : Fin N → ℚ) : Prop :=
  (∀ i, (N : ℝ) ^ (-ϵ) ≤ empMeas x y i) ∧ ∀ l, (y l : ℝ) ≤ (1 / 2) * (N : ℝ) ^ (1 - ϵ)

end WFMFG.Conv


