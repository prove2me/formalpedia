-- Prove2me | Definitions.Def_LearnDoFrontier_TwoAction_Model
-- name    : LearnDoFrontier_TwoAction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:41.562665+00:00
-- url     : https://prove2.me/theorems/bb86d87d-1bd9-471b-b46d-8b815b312c67
-- title:
--   §2, §4.1, Definitions 2–3, (13)–(15), (28)–(31) — two-state two-action learning model, anchor points û^a, the frontier boundary-value problems, f^A_θ, f^B_θ, Z_unit
-- statement:
--   This file fixes the learning-and-doing model of §2 and §4–§5 and the boundary-value problems whose solutions describe its efficient frontier.
--
--   **Model.** The unobserved state is $\theta \in \{1, 2\}$, the actions are $A$ and $B$, and the signals are $\gamma$ and $\bar\gamma$. The data are a discount factor $\delta$, the probabilities $p^A_\theta = p_\theta(A,\gamma)$ and $p^B_\theta = p_\theta(B,\gamma)$ (so that $p_\theta(a,\bar\gamma) = 1 - p_\theta(a,\gamma)$), the one-period rewards $r_\theta(a, s)$, and four positive integers $n^A, \bar n^A, n^B, \bar n^B$, the signal quality indices written as $(n(A,\gamma), n(A,\bar\gamma), n(B,\gamma), n(B,\bar\gamma)) = (n^A, -\bar n^A, n^B, -\bar n^B)$.
--
--   **Derived quantities.** The expected reward $r_\theta(a) = p_\theta(a,\gamma) r_\theta(a,\gamma) + p_\theta(a,\bar\gamma) r_\theta(a,\bar\gamma)$, the anchor points $\hat u^a_\theta = (1-\delta)^{-1} r_\theta(a)$, and the boundary constant $\hat u^B_\theta - \hat u^A_\theta$.
--
--   **Standing assumptions of §5.** $0 < \delta < 1$; General Position $r_1(A) > r_1(B)$, $r_2(A) < r_2(B)$; Informative Action A $1 > p_1(A,\gamma) > p_2(A,\gamma) > 0$; Informative Action B $1 > p_1(B,\gamma) > p_2(B,\gamma) > 0$; and Definition 3: the four indices are positive, their absolute values are relatively prime, and for some $\mu > 1$
--   $$\frac{\ln\frac{p_1(A,\gamma)}{p_2(A,\gamma)}}{n(A,\gamma)} = \frac{\ln\frac{p_1(A,\bar\gamma)}{p_2(A,\bar\gamma)}}{n(A,\bar\gamma)} = \frac{\ln\frac{p_1(B,\gamma)}{p_2(B,\gamma)}}{n(B,\gamma)} = \frac{\ln\frac{p_1(B,\bar\gamma)}{p_2(B,\bar\gamma)}}{n(B,\bar\gamma)} = \ln\mu.$$
--   The standing assumptions of §4 (the setting of Theorem 3) replace Informative Action B by Uninformative Action B, $p_1(B,\gamma) = p_2(B,\gamma)$, and Definition 3 by Definition 2, which concerns only $n(A,\gamma)$ and $n(A,\bar\gamma)$.
--
--   **Problem (13)–(15), $\theta$-th component.** A real sequence $v = v^A_\theta$ on $k = 0, 1, \dots$ with
--   $$v(k + n^A) - \delta^{-1}(p^A_\theta)^{-1} v(k) + (p^A_\theta)^{-1}(1 - p^A_\theta) v(k - \bar n^A) = 0 \quad (k \ge \bar n^A),$$
--   $v(0) = \cdots = v(\bar n^A - 1) = \hat u^B_\theta - \hat u^A_\theta$, and $v(k) \to 0$.
--
--   **Problem (28)–(31), $\theta$-th component.** Real sequences $v^A, v^B$ on $k = 0, 1, \dots$ with
--   $$v^A(k + n^A) - \delta^{-1}(p^A_\theta)^{-1} v^A(k) + (p^A_\theta)^{-1}(1 - p^A_\theta) v^A(k - \bar n^A) = 0 \quad (k \ge \bar n^A),$$
--   $$v^B(k + \bar n^B) - \delta^{-1}(1 - p^B_\theta)^{-1} v^B(k) + (1 - p^B_\theta)^{-1} p^B_\theta\, v^B(k - n^B) = 0 \quad (k \ge n^B),$$
--   $v^A(k) + \hat u^A_\theta = v^B(\bar n^A + n^B - 1 - k) + \hat u^B_\theta$ for $k = 0, \dots, \bar n^A + n^B - 1$, and $v^A(k) \to 0$, $v^B(k) \to 0$.
--
--   **Characteristic polynomials.** Over $\mathbb C$,
--   $$f^A_\theta(z) = z^{n^A + \bar n^A} - \delta^{-1}(p^A_\theta)^{-1} z^{\bar n^A} + (p^A_\theta)^{-1}(1 - p^A_\theta),\qquad f^B_\theta(z) = z^{n^B + \bar n^B} - \delta^{-1}(1 - p^B_\theta)^{-1} z^{n^B} + (1 - p^B_\theta)^{-1} p^B_\theta,$$
--   $Z_{unit}(f) = \{z : f(z) = 0,\ |z| < 1\}$, and $m_z$ is the multiplicity of the root $z$.
--
--   These are the objects of Theorem 3 and Theorem 6 (Complete). The link from the efficient frontier of the underlying partially observed decision problem to these equations (Theorems 2 and 4) is not part of this file.
--
--   **Formalization Note** States, actions and signals are each `Fin 2`: index $0$ is $\theta = 1$, action $A$, signal $\gamma$; index $1$ is $\theta = 2$, action $B$, signal $\bar\gamma$. The negative indices $n(A,\bar\gamma)$, $n(B,\bar\gamma)$ are stored as the positive naturals $\bar n^A$, $\bar n^B$ (the E-Companion's own notation), so sequences are indexed by $\mathbb N$ and the shift $k + n(A,\bar\gamma)$ becomes $k - \bar n^A$ with $k \ge \bar n^A$. "Relatively prime absolute values" is read jointly, $\gcd(n^A, \bar n^A, n^B, \bar n^B) = 1$; Example 5's indices $(4, -2, 1, -3)$ are not pairwise coprime, so the joint reading is the paper's.
-- source:
--   Zhang, SSRN 3847049 (accepted version with E-Companion), pp. 3–4 (§2), p. 14 (§4.1, r(a), û^a, Assumptions), p. 15 (Uninformative Action B), p. 17 (Definition 2), p. 20 (Eqs. (13)–(15)), p. 23 (Informative Action B, Definition 3, Eq. (22)), pp. 27–28 (Eqs. (28)–(31)); EC p. 11 (Theorem 6 (Complete): f^A_θ, f^B_θ, Z^a_unit, m^a_z)

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra

open Polynomial Filter Topology

namespace LearnDoFrontier.TwoAction

/-- The two-state, two-action, two-signal learning model of §2 (pp. 3–4) and §4.1 (p. 14), with
its signal quality indices (Appendix B notation, EC p. 11). The state `θ ∈ {1, 2}` is `Fin 2`
(index `0` is the paper's `θ = 1`, index `1` is `θ = 2`); the action `a ∈ {A, B}` is `Fin 2`
(`0 = A`, `1 = B`); the signal `s ∈ {γ, γ̄}` is `Fin 2` (`0 = γ`, `1 = γ̄`).
* `δ`: the discount factor;
* `pA θ = p_θ(A, γ)`, `pB θ = p_θ(B, γ)`; then `p_θ(a, γ̄) = 1 - p_θ(a, γ)` (p. 14);
* `r θ a s = r_θ(a, s)`: the one-period reward;
* `nA = n(A, γ)`, `nbarA = -n(A, γ̄)`, `nB = n(B, γ)`, `nbarB = -n(B, γ̄)`: the signal quality
  indices, with the negative ones stored as their absolute values. -/
structure Model where
  δ : ℝ
  pA : Fin 2 → ℝ
  pB : Fin 2 → ℝ
  r : Fin 2 → Fin 2 → Fin 2 → ℝ
  nA : ℕ
  nbarA : ℕ
  nB : ℕ
  nbarB : ℕ

namespace Model

variable (M : Model)

/-- `p_θ(a, γ)`: the probability of signal `γ` after action `a` in state `θ`. -/
def prob (a θ : Fin 2) : ℝ := if a = 0 then M.pA θ else M.pB θ

/-- The expected one-period reward `r_θ(a) = p_θ(a, γ) r_θ(a, γ) + p_θ(a, γ̄) r_θ(a, γ̄)`,
the `θ`-th component of `r(a)` (p. 14). -/
def rbar (θ a : Fin 2) : ℝ := M.prob a θ * M.r θ a 0 + (1 - M.prob a θ) * M.r θ a 1

/-- The anchor point `û^a = (1 - δ)⁻¹ r(a)` (p. 14), `θ`-th component. -/
noncomputable def uhat (a θ : Fin 2) : ℝ := (1 - M.δ)⁻¹ * M.rbar θ a

/-- The boundary constant `û^B_θ - û^A_θ` of (14) and of Theorem 6 (Complete). -/
noncomputable def bdryConst (θ : Fin 2) : ℝ := M.uhat 1 θ - M.uhat 0 θ

/-- The standing assumptions of §5 (p. 14, p. 23): `δ ∈ (0, 1)` (p. 4); General Position of
Reward Vectors `r₁(A) > r₁(B)`, `r₂(A) < r₂(B)`; Informative Action A `1 > p₁(A,γ) > p₂(A,γ) > 0`;
Informative Action B `1 > p₁(B,γ) > p₂(B,γ) > 0`; and Definition 3: the integers
`n(A,γ) = nA > 0`, `n(A,γ̄) = -nbarA < 0`, `n(B,γ) = nB > 0`, `n(B,γ̄) = -nbarB < 0` have
relatively prime absolute values (jointly: their gcd is `1`) and satisfy (22) for some `μ > 1`. -/
def Standing : Prop :=
  0 < M.δ ∧ M.δ < 1 ∧
  (M.rbar 0 0 > M.rbar 0 1 ∧ M.rbar 1 0 < M.rbar 1 1) ∧
  (1 > M.pA 0 ∧ M.pA 0 > M.pA 1 ∧ M.pA 1 > 0) ∧
  (1 > M.pB 0 ∧ M.pB 0 > M.pB 1 ∧ M.pB 1 > 0) ∧
  0 < M.nA ∧ 0 < M.nbarA ∧ 0 < M.nB ∧ 0 < M.nbarB ∧
  Nat.gcd (Nat.gcd M.nA M.nbarA) (Nat.gcd M.nB M.nbarB) = 1 ∧
  ∃ μ : ℝ, 1 < μ ∧
    Real.log (M.pA 0 / M.pA 1) / (M.nA : ℝ) = Real.log μ ∧
    Real.log ((1 - M.pA 0) / (1 - M.pA 1)) / (-(M.nbarA : ℝ)) = Real.log μ ∧
    Real.log (M.pB 0 / M.pB 1) / (M.nB : ℝ) = Real.log μ ∧
    Real.log ((1 - M.pB 0) / (1 - M.pB 1)) / (-(M.nbarB : ℝ)) = Real.log μ

/-- The standing assumptions of §4 (pp. 14–15, p. 17), the setting of Theorem 3: `δ ∈ (0, 1)`;
General Position; Informative Action A; Uninformative Action B `p₁(B,γ) = p₂(B,γ)`; and
Definition 2: `n(A,γ) = nA > 0`, `n(A,γ̄) = -nbarA < 0` with relatively prime absolute values and
`n(A,γ)⁻¹ ln(p₁(A,γ)/p₂(A,γ)) = n(A,γ̄)⁻¹ ln(p₁(A,γ̄)/p₂(A,γ̄)) = ln μ` for some `μ > 1`.
The fields `nB`, `nbarB` are not used. -/
def Standing4 : Prop :=
  0 < M.δ ∧ M.δ < 1 ∧
  (M.rbar 0 0 > M.rbar 0 1 ∧ M.rbar 1 0 < M.rbar 1 1) ∧
  (1 > M.pA 0 ∧ M.pA 0 > M.pA 1 ∧ M.pA 1 > 0) ∧
  M.pB 0 = M.pB 1 ∧
  0 < M.nA ∧ 0 < M.nbarA ∧ Nat.gcd M.nA M.nbarA = 1 ∧
  ∃ μ : ℝ, 1 < μ ∧
    Real.log (M.pA 0 / M.pA 1) / (M.nA : ℝ) = Real.log μ ∧
    Real.log ((1 - M.pA 0) / (1 - M.pA 1)) / (-(M.nbarA : ℝ)) = Real.log μ

/-- The `θ`-th component of the boundary-value problem (13)–(15) (p. 20), for a real sequence
`v = v^A_θ` indexed by `k = 0, 1, …`:
* (13) `v(k + nA) - δ⁻¹ p_θ(A,γ)⁻¹ v(k) + p_θ(A,γ)⁻¹ p_θ(A,γ̄) v(k - nbarA) = 0` for `k ≥ nbarA`;
* (14) `v(0) = ⋯ = v(nbarA - 1) = û^B_θ - û^A_θ`;
* (15) `v(k) → 0` as `k → ∞`. -/
def IsBVP3 (θ : Fin 2) (v : ℕ → ℝ) : Prop :=
  (∀ k, M.nbarA ≤ k →
    v (k + M.nA) - M.δ⁻¹ * (M.pA θ)⁻¹ * v k + (M.pA θ)⁻¹ * (1 - M.pA θ) * v (k - M.nbarA) = 0) ∧
  (∀ k, k < M.nbarA → v k = M.bdryConst θ) ∧
  Tendsto v atTop (𝓝 0)

/-- The `θ`-th component of the boundary-value problem (28)–(31) (pp. 27–28), for real sequences
`vA = v^A_θ`, `vB = v^B_θ` indexed by `k = 0, 1, …`:
* (28) `vA(k + nA) - δ⁻¹ p_θ(A,γ)⁻¹ vA(k) + p_θ(A,γ)⁻¹ p_θ(A,γ̄) vA(k - nbarA) = 0`, `k ≥ nbarA`;
* (29) `vB(k + nbarB) - δ⁻¹ p_θ(B,γ̄)⁻¹ vB(k) + p_θ(B,γ̄)⁻¹ p_θ(B,γ) vB(k - nB) = 0`, `k ≥ nB`;
* (30) `vA(k) + û^A_θ = vB(nbarA + nB - 1 - k) + û^B_θ` for `k = 0, …, nbarA + nB - 1`;
* (31) `vA(k) → 0` and `vB(k) → 0` as `k → ∞`. -/
def IsBVP (θ : Fin 2) (vA vB : ℕ → ℝ) : Prop :=
  (∀ k, M.nbarA ≤ k →
    vA (k + M.nA) - M.δ⁻¹ * (M.pA θ)⁻¹ * vA k
      + (M.pA θ)⁻¹ * (1 - M.pA θ) * vA (k - M.nbarA) = 0) ∧
  (∀ k, M.nB ≤ k →
    vB (k + M.nbarB) - M.δ⁻¹ * (1 - M.pB θ)⁻¹ * vB k
      + (1 - M.pB θ)⁻¹ * M.pB θ * vB (k - M.nB) = 0) ∧
  (∀ k, k < M.nbarA + M.nB →
    vA k + M.uhat 0 θ = vB (M.nbarA + M.nB - 1 - k) + M.uhat 1 θ) ∧
  Tendsto vA atTop (𝓝 0) ∧ Tendsto vB atTop (𝓝 0)

/-- The characteristic polynomial `f^A_θ(z) = z^{nA+nbarA} - δ⁻¹ (p^A_θ)⁻¹ z^{nbarA}
+ (p^A_θ)⁻¹ (1 - p^A_θ)` of Theorem 6 (Complete), EC p. 11 (and `f_θ` of Theorem 3, p. 22),
over `ℂ`. -/
noncomputable def fA (θ : Fin 2) : ℂ[X] :=
  X ^ (M.nA + M.nbarA) - C ((M.δ⁻¹ * (M.pA θ)⁻¹ : ℝ) : ℂ) * X ^ M.nbarA
    + C (((M.pA θ)⁻¹ * (1 - M.pA θ) : ℝ) : ℂ)

/-- The characteristic polynomial `f^B_θ(z) = z^{nB+nbarB} - δ⁻¹ (1 - p^B_θ)⁻¹ z^{nB}
+ (1 - p^B_θ)⁻¹ p^B_θ` of Theorem 6 (Complete), EC p. 11, over `ℂ`. -/
noncomputable def fB (θ : Fin 2) : ℂ[X] :=
  X ^ (M.nB + M.nbarB) - C ((M.δ⁻¹ * (1 - M.pB θ)⁻¹ : ℝ) : ℂ) * X ^ M.nB
    + C (((1 - M.pB θ)⁻¹ * M.pB θ : ℝ) : ℂ)

end Model

/-- `Z_unit = {z | f(z) = 0 and |z| < 1}`: the distinct roots of `f` in the open unit disk. -/
noncomputable def Zunit (f : ℂ[X]) : Finset ℂ :=
  f.roots.toFinset.filter (fun z => ‖z‖ < 1)

/-- `m_z`: the multiplicity of `z` as a root of `f`. -/
noncomputable def mult (f : ℂ[X]) (z : ℂ) : ℕ := f.rootMultiplicity z

end LearnDoFrontier.TwoAction


