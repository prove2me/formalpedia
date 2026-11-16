-- Prove2me | Definitions.Def_JointNonManip_Supplement_Codebook
-- name    : JointNonManip_Supplement_Codebook
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:28:43.877583+00:00
-- url     : https://prove2.me/theorems/2a15f5fa-4987-407f-9d65-37ca39c8fc33
-- title:
--   Parameters, admissible public codebook and error quantities of the unified profile $A^\star_{L,T}$
-- statement:
--   The parameters and the public codebook of the unified profile $A^\star_{L,T}$ (Appendix A.11). Fix a finite game with learners $L$, $\ell=|L|$, $k_i=|A_i|$, $d_0=|A_0|$ and $\Phi_i=\{\varphi:A_i\to A_i\}$. For a known horizon $T$ (natural logarithms throughout):
--
--   $$\varepsilon_T=\frac1{\lceil\log(T+2)\rceil},\quad m_T=\lceil T^{2/3}\rceil,\quad \gamma_T=T^{-1/4},\quad \alpha_T=(T+1)^{-2},$$
--   $$K_\Phi=\sum_{j\in L}|\Phi_j|,\quad \Lambda_T=\log\frac{6TK_\Phi}{\alpha_T},\quad h_i(s)=\Big(\frac{k_i}{\gamma_T}+2\Big)\sqrt{2s\Lambda_T},\quad \beta_i=\min\Big\{1,\sqrt{\tfrac{k_i\log k_i}{T}}\Big\}.$$
--
--   **Admissible codebook at horizon $T$.** A finite rational $\varepsilon_T$-net $N$ of the strategy-profile space $\Delta(A_0)\times\prod_i\Delta(A_i)$ under the sum of the players' $\ell_1$ distances; the retained profiles $(y_j,(x_{j,i})_i)$, $j\in[J_T]$, which are exactly the net points with
--   $$u_i(y_j,b,x_{j,-i})-u_i(y_j,x_j)\le2\varepsilon_T\qquad(i\in L,\ b\in A_i),$$
--   and $q_j=\bigotimes_i x_{j,i}$; a reference action $c_\star\in A_0$ and $M_T=\lceil4J_T/\varepsilon_T\rceil$; distinct labels $\theta_j\in\{0,1/M_T,\dots,1\}$ with $|\theta_j-y_j(c_\star)|\le\varepsilon_T/2$; encodings $z_j\in\Delta(A_0)$ with $z_j(c_\star)=\theta_j$ and $\|z_j-y_j\|_1\le\varepsilon_T$; and the fixed pure learner profile prescribed in the reading phase.
--
--   **Error quantities.** With $g_{i,\varphi}(a)=u_i(a_0,\varphi(a_i),a_{-i})-u_i(a)$, $C=\sqrt{2|A|}$, $C_i=\sqrt2\max_{\varphi\in\Phi_i}\|g_{i,\varphi}\|_2$ and $d_T=\max_{j\in[J_T]}\operatorname{dist}_1(y_j\otimes q_j,E_{\mathrm{NE}})$:
--   $$\xi_T=\min\Big\{1,\,2e^{-2m_T/(9M_T^2)}+2d_0Te^{-2m_T^2/(d_0^2T)}\Big\},\qquad a_T=d_T+\varepsilon_T+\frac{3m_T+2+C\sqrt T}{T},$$
--   $$b_T=\frac{3m_T}{T}+2\varepsilon_T+2\xi_T,\quad B_i(T)=4T\varepsilon_T+4m_T+2+C_i\sqrt T,\quad e_T=2\ell\gamma_T+\frac{2\alpha_T}3,$$
--   $$F_i(T)=2\Big[\frac{k_i^2\log k_i}{\beta_i}+2\beta_iT+\sqrt{k_iT\Big(k_i+\frac{k_i^2}{\beta_i}\Big)}\Big]\ (k_i\ge2),\qquad F_i(T)=0\ (k_i=1).$$
--
--   The right-hand side of the swap-regret bound (7) is $B_i(T)+4\ell\gamma_TT+2h_i(T)+4\sqrt{2T\Lambda_T}+2+F_i(T)+4\alpha_TT/3$.
--
--   **Formalization Note** The paper leaves the net, $c_\star$, the $\theta_j$, the $z_j$ and the reading profile free ("All common choices … fixed in advance"); the structure `Codebook u T` bundles one admissible choice with exactly these constraints, and Theorem A.5 quantifies over all of them. $d_T$ is a real supremum over the finite index set.
-- source:
--   Collina, Fullerton, Liu & Weinberg, Non-manipulability and Approachability Beyond Two-Player Games (manuscript, STOC 2027 submission), Appendix A.11, "Model and parameters" and "Target and public codebook", p.33; "Specification of the bandit fallback" and "Error quantities", p.35

import Mathlib
import Definitions.Def_JointNonManip_RepeatedPlay

namespace JointNonManip.Supplement

/-!
# Parameters, public codebook and error quantities of the unified profile `A⋆_{L,T}`

Collina, Fullerton, Liu & Weinberg, *Non-manipulability and Approachability Beyond Two-Player
Games* (manuscript, STOC 2027 submission), Appendix A.11: "Model and parameters" and "Target and
public codebook" (p.33), "Specification of the bandit fallback" and "Error quantities" (p.35).

**Formalization Note**
* `log` is the natural logarithm (`Real.log`) throughout; `⌈·⌉` is `Nat.ceil`.
* `ℓ = |L|`, `kᵢ = |Aᵢ|`, `d₀ = |A₀|`, `|A| = |A₀ × A_L|` and `|Φⱼ| = kⱼ^{kⱼ}` are `Fintype.card`s.
* A strategy profile is a pair `(y, (xᵢ)ᵢ)` of weight functions; the "sum of the players' ℓ₁
  distances" is `profileL1`.
* The paper leaves the rational `ε_T`-net, the reference action `c⋆`, the labels `θⱼ`, the
  encodings `zⱼ` and the reading-phase pure profile free ("All common choices … are
  deterministic and fixed in advance", p.33). `Codebook u T` bundles one admissible choice at
  horizon `T`, with exactly the constraints of p.33: the retained list `(yⱼ, xⱼ)_{j < J_T}` is an
  injective enumeration of the net points satisfying the `2ε_T` deviation inequalities.
* `d_T = max_{j} dist₁(yⱼ ⊗ qⱼ, E_NE)` is a real `⨆` over the finite index set `Fin J_T` of
  values bounded below by `0` (`0` only if the list is empty, which the cover property rules out).
* `F_i(T)` is `0` when `kᵢ = 1` (and also when `kᵢ = 0`, which never occurs: action sets are
  nonempty).
-/

open Finset

variable {A0 : Type} [Fintype A0] [DecidableEq A0]
variable {L : Type} [Fintype L] [DecidableEq L]
variable {Act : L → Type} [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]

/-! ### Parameters (p.33) -/

/-- `ε_T = 1/⌈log(T + 2)⌉` (p.33). -/
noncomputable def epsT (T : ℕ) : ℝ := 1 / (⌈Real.log ((T : ℝ) + 2)⌉₊ : ℝ)

/-- `m_T = ⌈T^{2/3}⌉` (p.33). -/
noncomputable def mT (T : ℕ) : ℕ := ⌈(T : ℝ) ^ ((2 : ℝ) / 3)⌉₊

/-- `γ_T = T^{−1/4}` (p.33). -/
noncomputable def gammaT (T : ℕ) : ℝ := (T : ℝ) ^ (-(1 : ℝ) / 4)

/-- `α_T = (T + 1)^{−2}` (p.33). -/
noncomputable def alphaT (T : ℕ) : ℝ := 1 / ((T : ℝ) + 1) ^ 2

/-- `K_Φ = ∑_{j ∈ L} |Φⱼ|`, `Φⱼ = {φ : Aⱼ → Aⱼ}` (p.33). -/
def KPhi {L : Type} [Fintype L] (Act : L → Type) [∀ i, Fintype (Act i)]
    [∀ i, DecidableEq (Act i)] : ℕ :=
  ∑ j : L, Fintype.card (Act j → Act j)

/-- `Λ_T = log(6 T K_Φ / α_T)` (p.33). -/
noncomputable def LambdaT {L : Type} [Fintype L] (Act : L → Type) [∀ i, Fintype (Act i)]
    [∀ i, DecidableEq (Act i)] (T : ℕ) : ℝ :=
  Real.log (6 * (T : ℝ) * (KPhi Act : ℝ) / alphaT T)

/-- The monitoring threshold `hᵢ(s) = (kᵢ/γ_T + 2) √(2 s Λ_T)` (p.33). -/
noncomputable def hThr {L : Type} [Fintype L] (Act : L → Type) [∀ i, Fintype (Act i)]
    [∀ i, DecidableEq (Act i)] (i : L) (T : ℕ) (s : ℝ) : ℝ :=
  ((Fintype.card (Act i) : ℝ) / gammaT T + 2) * Real.sqrt (2 * s * LambdaT Act T)

/-- The exploration rate of the Exp3-based fallback, `βᵢ = min{1, √(kᵢ log kᵢ / T)}` (p.35). -/
noncomputable def betaI {L : Type} (Act : L → Type) [∀ i, Fintype (Act i)] (i : L) (T : ℕ) : ℝ :=
  min 1 (Real.sqrt ((Fintype.card (Act i) : ℝ) * Real.log (Fintype.card (Act i)) / T))

/-! ### Public codebook (p.33) -/

/-- A strategy profile `(y, (xᵢ)_{i ∈ L})` of the optimizer and the learners. -/
abbrev StratProfile (A0 : Type) {L : Type} (Act : L → Type) :=
  (A0 → ℝ) × ((i : L) → Act i → ℝ)

/-- `(y, x)` is a mixed strategy profile: `y ∈ ∆(A₀)` and `xᵢ ∈ ∆(Aᵢ)` for every `i`. -/
def IsStratProfile (p : StratProfile A0 Act) : Prop :=
  AGT.IsLottery p.1 ∧ ∀ i, AGT.IsLottery (p.2 i)

/-- All weights of the profile are rational numbers. -/
def IsRationalProfile (p : StratProfile A0 Act) : Prop :=
  (∀ c, ∃ r : ℚ, p.1 c = r) ∧ ∀ i a, ∃ r : ℚ, p.2 i a = r

/-- The sum of the players' ℓ₁ distances, `‖y − y'‖₁ + ∑ᵢ ‖xᵢ − x'ᵢ‖₁` (p.33). -/
def profileL1 (p p' : StratProfile A0 Act) : ℝ :=
  l1dist p.1 p'.1 + ∑ i, l1dist (p.2 i) (p'.2 i)

/-- The retention test of p.33: `uᵢ(y, b, x₋ᵢ) − uᵢ(y, x) ≤ 2ε` for all `i ∈ L`, `b ∈ Aᵢ`, where
`uᵢ(y, ·)` is the expected utility in the induced game `G_L(y)`. -/
def IsRetained (u : L → A0 × ((i : L) → Act i) → ℝ) (ε : ℝ) (p : StratProfile A0 Act) : Prop :=
  ∀ (i : L) (b : Act i),
    AGT.expectedPayoff (inducedUtility u p.1) (Function.update p.2 i (pointMass b)) i -
      AGT.expectedPayoff (inducedUtility u p.1) p.2 i ≤ 2 * ε

/-- `M_T = ⌈4 J_T / ε_T⌉` (p.33). -/
noncomputable def MT (J T : ℕ) : ℕ := ⌈4 * (J : ℝ) / epsT T⌉₊

/-- An **admissible public codebook at horizon `T`** (p.33): a finite rational `ε_T`-net of the
strategy-profile space (sum of the players' ℓ₁ distances); the retained profiles
`(yⱼ, (x_{j,i})ᵢ)`, `j < J_T`, enumerated injectively, which are exactly the net points passing
the `2ε_T` test; a reference action `c⋆`; distinct labels `θⱼ ∈ {0, 1/M_T, …, 1}` with
`|θⱼ − yⱼ(c⋆)| ≤ ε_T/2`; encodings `zⱼ ∈ ∆(A₀)` with `zⱼ(c⋆) = θⱼ` and `‖zⱼ − yⱼ‖₁ ≤ ε_T`; and the
fixed pure learner profile of the reading phase. -/
structure Codebook (u : L → A0 × ((i : L) → Act i) → ℝ) (T : ℕ) where
  /-- The finite net. -/
  net : Finset (StratProfile A0 Act)
  /-- Net points are mixed strategy profiles. -/
  net_profile : ∀ p ∈ net, IsStratProfile p
  /-- Net points are rational. -/
  net_rational : ∀ p ∈ net, IsRationalProfile p
  /-- The net is an `ε_T`-net of the strategy-profile space. -/
  net_cover : ∀ p : StratProfile A0 Act, IsStratProfile p → ∃ p' ∈ net, profileL1 p p' ≤ epsT T
  /-- The number `J_T` of retained profiles. -/
  J : ℕ
  /-- The retained profiles `(yⱼ, xⱼ)`. -/
  prof : Fin J → StratProfile A0 Act
  /-- The enumeration is injective. -/
  prof_injective : Function.Injective prof
  /-- The retained profiles are exactly the net points passing the `2ε_T` test. -/
  prof_retained : ∀ p, p ∈ Set.range prof ↔ (p ∈ net ∧ IsRetained u (epsT T) p)
  /-- The reference optimizer action `c⋆`. -/
  cstar : A0
  /-- The labels `θⱼ`. -/
  theta : Fin J → ℝ
  /-- `θⱼ ∈ {0, 1/M_T, …, 1}`. -/
  theta_grid : ∀ j, ∃ k : ℕ, k ≤ MT J T ∧ theta j = (k : ℝ) / (MT J T : ℝ)
  /-- The labels are distinct. -/
  theta_injective : Function.Injective theta
  /-- `|θⱼ − yⱼ(c⋆)| ≤ ε_T/2`. -/
  theta_close : ∀ j, |theta j - (prof j).1 cstar| ≤ epsT T / 2
  /-- The encodings `zⱼ`. -/
  z : Fin J → A0 → ℝ
  /-- `zⱼ ∈ ∆(A₀)`. -/
  z_lottery : ∀ j, AGT.IsLottery (z j)
  /-- `zⱼ(c⋆) = θⱼ`. -/
  z_cstar : ∀ j, z j cstar = theta j
  /-- `‖zⱼ − yⱼ‖₁ ≤ ε_T`. -/
  z_close : ∀ j, l1dist (z j) (prof j).1 ≤ epsT T
  /-- The fixed pure learner profile prescribed in the reading phase. -/
  aRead : (i : L) → Act i

/-! ### Error quantities (p.35) -/

/-- `C = √(2|A|)` (p.35). -/
noncomputable def constC (A0 : Type) [Fintype A0] {L : Type} [Fintype L] [DecidableEq L]
    (Act : L → Type) [∀ i, Fintype (Act i)] : ℝ :=
  Real.sqrt (2 * (Fintype.card (A0 × ((i : L) → Act i)) : ℝ))

/-- The coefficient vector `g_{i,φ}(a) = uᵢ(a₀, φ(aᵢ), a₋ᵢ) − uᵢ(a)` of `G_{i,φ}` (p.35). -/
def swapCoef (u : L → A0 × ((i : L) → Act i) → ℝ) (i : L) (φ : Act i → Act i)
    (a : A0 × ((i : L) → Act i)) : ℝ :=
  u i (a.1, Function.update a.2 i (φ (a.2 i))) - u i a

/-- `Cᵢ = √2 · max_{φ ∈ Φᵢ} ‖g_{i,φ}‖₂` (p.35). -/
noncomputable def constCi (u : L → A0 × ((i : L) → Act i) → ℝ) (i : L) : ℝ :=
  Real.sqrt 2 * Finset.univ.sup' ⟨id, Finset.mem_univ _⟩
    (fun φ : Act i → Act i => Real.sqrt (∑ a, swapCoef u i φ a ^ 2))

/-- `d_T = max_{j ∈ [J_T]} dist₁(yⱼ ⊗ qⱼ, E_NE)`, `qⱼ = ⊗ᵢ x_{j,i}` (p.35). -/
noncomputable def dT {u : L → A0 × ((i : L) → Act i) → ℝ} {T : ℕ} (C : Codebook u T) : ℝ :=
  ⨆ j : Fin C.J, l1InfDist (otimes (C.prof j).1 (AGT.profileProb (C.prof j).2)) (ENE u)

/-- `ξ_T = min{1, 2 exp(−2m_T/(9M_T²)) + 2 d₀ T exp(−2m_T²/(d₀² T))}` (p.35). -/
noncomputable def xiT {u : L → A0 × ((i : L) → Act i) → ℝ} {T : ℕ} (C : Codebook u T) : ℝ :=
  min 1 (2 * Real.exp (-(2 * (mT T : ℝ)) / (9 * (MT C.J T : ℝ) ^ 2)) +
    2 * (Fintype.card A0 : ℝ) * T *
      Real.exp (-(2 * (mT T : ℝ) ^ 2) / ((Fintype.card A0 : ℝ) ^ 2 * T)))

/-- `a_T = d_T + ε_T + (3m_T + 2 + C√T)/T` (p.35). -/
noncomputable def aT {u : L → A0 × ((i : L) → Act i) → ℝ} {T : ℕ} (C : Codebook u T) : ℝ :=
  dT C + epsT T + (3 * (mT T : ℝ) + 2 + constC A0 Act * Real.sqrt T) / T

/-- `b_T = 3m_T/T + 2ε_T + 2ξ_T` (p.35). -/
noncomputable def bT {u : L → A0 × ((i : L) → Act i) → ℝ} {T : ℕ} (C : Codebook u T) : ℝ :=
  3 * (mT T : ℝ) / T + 2 * epsT T + 2 * xiT C

/-- `Bᵢ(T) = 4Tε_T + 4m_T + 2 + Cᵢ√T` (p.35). -/
noncomputable def BiT (u : L → A0 × ((i : L) → Act i) → ℝ) (i : L) (T : ℕ) : ℝ :=
  4 * T * epsT T + 4 * (mT T : ℝ) + 2 + constCi u i * Real.sqrt T

/-- `e_T = 2ℓγ_T + 2α_T/3`, `ℓ = |L|` (p.35). -/
noncomputable def eT (L : Type) [Fintype L] (T : ℕ) : ℝ :=
  2 * (Fintype.card L : ℝ) * gammaT T + 2 * alphaT T / 3

/-- `Fᵢ(T) = 2[kᵢ² log kᵢ / βᵢ + 2βᵢT + √(kᵢT(kᵢ + kᵢ²/βᵢ))]` for `kᵢ ≥ 2`, and `Fᵢ(T) = 0`
otherwise (p.35). -/
noncomputable def FiT {L : Type} (Act : L → Type) [∀ i, Fintype (Act i)] (i : L) (T : ℕ) : ℝ :=
  if 2 ≤ Fintype.card (Act i) then
    2 * ((Fintype.card (Act i) : ℝ) ^ 2 * Real.log (Fintype.card (Act i)) / betaI Act i T +
      2 * betaI Act i T * T +
      Real.sqrt ((Fintype.card (Act i) : ℝ) * T *
        ((Fintype.card (Act i) : ℝ) + (Fintype.card (Act i) : ℝ) ^ 2 / betaI Act i T)))
  else 0

/-- The right-hand side of (7):
`Bᵢ(T) + 4ℓγ_T T + 2hᵢ(T) + 4√(2TΛ_T) + 2 + Fᵢ(T) + 4α_T T/3` (p.35). -/
noncomputable def regretBound7 (u : L → A0 × ((i : L) → Act i) → ℝ) (i : L) (T : ℕ) : ℝ :=
  BiT u i T + 4 * (Fintype.card L : ℝ) * gammaT T * T + 2 * hThr Act i T T +
    4 * Real.sqrt (2 * T * LambdaT Act T) + 2 + FiT Act i T + 4 * alphaT T * T / 3

end JointNonManip.Supplement


