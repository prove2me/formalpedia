-- Prove2me | Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions
-- name    : InvestCommonGood_MixedTSSPE_Conditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:03.877736+00:00
-- url     : https://prove2.me/theorems/b315d7c4-84a2-4bf9-9503-9b9ae897248c
-- title:
--   §4.2, Lemma B.8 — the conditions on F₁ = (U₁ | V₁), F₂ = V₂, the reward g_i (28), the rates λ_i (29), and the closed forms of Lemma B.8
-- statement:
--   The analytic certificates of Kim and Kwon's mixed equilibrium (§4.2, pp. 20–22) and the explicit functions of the proof of Lemma B.8. Costs are $c=(c_1,c_2)$, targets $z=(z_1,z_2)$, the threshold is $\theta^*$ and the atom probability $q$; the first-stage functions are $F_{1,0}=U_1$, $F_{2,0}=V_2$.
--
--   **Reward and rates.** For a first-stage function $F_{i,0}$, (28) is
--   $$g_i(x)=\begin{cases}F_{i,0}(z_i)-k(z_i-x)-c_i,&x<z_i,\\F_{i,0}(x)-c_i,&x\ge z_i,\end{cases}\qquad \lambda_i(x)=\mathbf 1_{\{x\in(a,\theta^*)\}}\frac{-\mathcal Ag_j(x)-\pi(x)}{F_{j,0}(z_i)-g_j(x)}\ \ (29).$$
--
--   **The conditions of §4.2.** On $V_2$: $\theta^*,z_2\in\mathcal I$; $V_2\in C^2(\mathcal I\setminus\{\theta^*\})\cap C^1(\mathcal I)$; $V_2>R_r\pi$; (24) $\mathcal AV_2+\pi=0$ on $(\theta^*,b)$; (25) $\mathcal AV_2+\pi<0$ on $(a,\theta^*)$; (27) $V_2(x)\ge V_2(x+\zeta)-k\zeta-c_2$ for all $\zeta\ge0$; $z_2$ is the unique maximizer of $V_2(z)-kz$; $V_2=g_2$ on $(a,\theta^*)$; (30) $V_2=R_r\pi+w_2\varphi$ on $[\theta^*,b)$ with $w_2>0$. On $F_1$, in addition: $z_1\in\mathcal I$; $U_1\in C^2(\mathcal I\setminus\{\theta^*\})$, $V_1\in C^2(\mathcal I\setminus\{\theta^*\})\cap C^1(\mathcal I)$, $V_1>R_r\pi$; $U_1>V_1$ on $[\theta^*,b)$ and $U_1=V_1$ on $(a,\theta^*)$; (24)–(25) for $V_1$ and (26) $\mathcal AU_1+\pi=0$ on $(\theta^*,b)$; (27) $V_1(x)\ge U_1(x+\zeta)-k\zeta-c_1$ and $U_1(x)\ge U_1(x+\zeta)-k\zeta-c_1$; $z_1$ is the unique maximizer of $U_1(z)-kz$; $V_1=g_1$ on $(a,\theta^*)$; (30) $V_1=R_r\pi+w_1\varphi$, $U_1=R_r\pi+u_1\varphi$ on $[\theta^*,b)$ with $0<w_1<u_1$; the boundary condition $U_1(\theta^*)=qU_1(z_2)+(1-q)V_1(\theta^*)$; and $U_1(z_2)\ge V_1(\theta^*)=g_1(\theta^*)$.
--
--   **Induced payoffs.** $\nu^*$ induces $F$ if from every $x\in\mathcal I$ and stage, every play of $\nu^*$ has well-defined payoffs, player 2 receives $V_2(x)$, and player 1 receives $U_1(x)$ from stage 1 and $V_1(x)$ from stage 2 ((23)).
--
--   **Closed forms of Lemma B.8** (EC pp. 22, 24), with $\alpha=-I(\theta^*)$ and $\beta=-I(z_1)$:
--   $$\hat V_2(x)=\begin{cases}\alpha\varphi(z_2)+(R_r\pi)(z_2)-k(z_2-x)-c_2,&x\le\theta^*\\ \alpha\varphi(x)+(R_r\pi)(x),&x>\theta^*\end{cases},\quad \hat V_1(x)=\begin{cases}\hat U_1(z_1)-k(z_1-x)-c_1,&x<\theta^*\\ \alpha\varphi(x)+(R_r\pi)(x),&x\ge\theta^*\end{cases},$$
--   $\hat U_1=\hat V_1$ on $(a,\theta^*)$ and $\hat U_1=\beta\varphi+R_r\pi$ on $[\theta^*,b)$. Finally, the left side of (B.22) is $\varphi(\theta^*)[I(\theta^*)-I(z_1)]\big/\big(-I(z_1)\varphi(z_2)+(R_r\pi)(z_2)+I(\theta^*)\varphi(\theta^*)-(R_r\pi)(\theta^*)\big)$ and (B.23) is $-I(z_1)\varphi(\theta^*)+(R_r\pi)(\theta^*)-k\theta^*<J(z_1)$.
--
--   These conditions are the hypotheses of the verification theorem (Theorem 2) and the conclusion of the existence argument (Lemma B.8).
--
--   **Formalization Note.** Each supremum in (27) is stated pointwise over $\zeta\ge0$ with $x+\zeta\in\mathcal I$. The paper's $|U_1''|,|V_i''|<\infty$ off $\theta^*$ is automatic. The conditions also require the denominators $F_{j,0}(z_i)-g_j(x)$ of (29) to be positive on $(a,\theta^*)$: the paper calls $\lambda_i$ an investment rate and uses its positivity there; it holds for the closed forms of Lemma B.8. The closed forms of (30) are listed among the conditions, as the paper uses them.
-- source:
--   Kim & Kwon, Investment in the common good: free rider effect and the stability of mixed strategy equilibria, arXiv:2208.11217v1, pp. 20–22, §4.2, (23)–(30); EC pp. 21–24 (PDF 52–55), Lemma B.8 and its proof, (B.21)–(B.23)

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace InvestCommonGood.MixedTSSPE

open VarContrib.RegularMPE

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The reward from investment (28): `g(x) = F₀(z) − k(z − x) − c` for `x < z` and
`F₀(x) − c` for `x ≥ z`. -/
noncomputable def gFun (k : ℝ) (F0 : ℝ → ℝ) (c z : ℝ) (x : ℝ) : ℝ :=
  if x < z then F0 z - k * (z - x) - c else F0 x - c

open Classical in
/-- The investment rate (29):
`λ_i(x) = 1{x ∈ (a, θ*)} (−𝒜g_j(x) − π(x)) / (F_{j,0}(z_i) − g_j(x))`, `j` the opponent, where
`F0 0 = U₁` and `F0 1 = V₂` are the first-stage functions and `g_j` is (28) for `F_{j,0}`,
`c_j`, `z_j`. -/
noncomputable def rate29 (m : Model) (F0 : Fin 2 → ℝ → ℝ) (c z : Fin 2 → ℝ) (θ : ℝ) (i : Fin 2)
    (x : ℝ) : ℝ :=
  if x ∈ m.I ∧ x < θ then
    (-(gen m (gFun m.k (F0 (other i)) (c (other i)) (z (other i))) x) - m.π x) /
      (F0 (other i) (z i) - gFun m.k (F0 (other i)) (c (other i)) (z (other i)) x)
  else 0

/-- The conditions of §4.2 (pp. 20–22) on player 2's function `V₂` (`F_{2,t} = V₂`), threshold
`θ*`, cost `c₂` and target `z₂`:
1. `θ*, z₂ ∈ I`; `V₂ ∈ C²(I∖{θ*}) ∩ C¹(I)`; `V₂ > R_rπ` on `I`;
2. (24) `𝒜V₂ + π = 0` on `(θ*, b)`, (25) `𝒜V₂ + π < 0` on `(a, θ*)`;
3. (27) `V₂(x) ≥ V₂(x + ζ) − kζ − c₂` for `ζ ≥ 0` (`x, x + ζ ∈ I`);
4. `z₂` is the unique maximizer of `V₂(z) − kz` on `I`;
5. `V₂ = g₂` on `(a, θ*)`, `g₂` of (28);
6. (30) `V₂ = R_rπ + w₂φ` on `[θ*, b)` for some `w₂ > 0`. -/
def Sec42V2 (m : Model) (S : Setting Ω) (c2 θ z2 : ℝ) (V2 : ℝ → ℝ) : Prop :=
  θ ∈ m.I ∧ z2 ∈ m.I ∧
  ContDiffOn ℝ 2 V2 (m.I \ {θ}) ∧ ContDiffOn ℝ 1 V2 m.I ∧
  (∀ x ∈ m.I, R m S m.π x < V2 x) ∧
  (∀ x ∈ m.I, θ < x → gen m V2 x + m.π x = 0) ∧
  (∀ x ∈ m.I, x < θ → gen m V2 x + m.π x < 0) ∧
  (∀ x ∈ m.I, ∀ ζ : ℝ, 0 ≤ ζ → x + ζ ∈ m.I → V2 (x + ζ) - m.k * ζ - c2 ≤ V2 x) ∧
  (∀ y ∈ m.I, y ≠ z2 → V2 y - m.k * y < V2 z2 - m.k * z2) ∧
  (∀ x ∈ m.I, x < θ → V2 x = gFun m.k V2 c2 z2 x) ∧
  ∃ w2 : ℝ, 0 < w2 ∧ ∀ x ∈ m.I, θ ≤ x → V2 x = R m S m.π x + w2 * S.φ x

/-- All conditions of §4.2 (pp. 20–22) on `F₁ = (U₁ | V₁)` and `F₂ = V₂`, with costs
`c = (c₁, c₂)`, targets `z = (z₁, z₂)`, threshold `θ*` and atom probability `q`:
1. `Sec42V2` for `V₂`; `z₁ ∈ I`;
2. `U₁ ∈ C²(I∖{θ*})`, `V₁ ∈ C²(I∖{θ*}) ∩ C¹(I)`, `V₁ > R_rπ`; `U₁ > V₁` on `[θ*, b)`,
   `U₁ = V₁` on `(a, θ*)`;
3. (24), (25) for `V₁` and (26) `𝒜U₁ + π = 0` on `(θ*, b)`;
4. (27) `V₁(x) ≥ U₁(x + ζ) − kζ − c₁`, `U₁(x) ≥ U₁(x + ζ) − kζ − c₁`;
5. `z₁` is the unique maximizer of `U₁(z) − kz` on `I`; `V₁ = g₁` on `(a, θ*)`;
6. (30) `V₁ = R_rπ + w₁φ`, `U₁ = R_rπ + u₁φ` on `[θ*, b)`, `0 < w₁ < u₁`;
7. `U₁(θ*) = qU₁(z₂) + (1 − q)V₁(θ*)` and `U₁(z₂) ≥ V₁(θ*) = g₁(θ*)`;
8. (pinned reading) the rates (29) are well defined and positive on `(a, θ*)`: their
   denominators `F_{j,0}(z_i) − g_j(x)` are positive there. -/
def Sec42 (m : Model) (S : Setting Ω) (c : Fin 2 → ℝ) (θ : ℝ) (z : Fin 2 → ℝ) (q : ℝ)
    (U1 V1 V2 : ℝ → ℝ) : Prop :=
  Sec42V2 m S (c 1) θ (z 1) V2 ∧ z 0 ∈ m.I ∧
  ContDiffOn ℝ 2 U1 (m.I \ {θ}) ∧ ContDiffOn ℝ 2 V1 (m.I \ {θ}) ∧ ContDiffOn ℝ 1 V1 m.I ∧
  (∀ x ∈ m.I, R m S m.π x < V1 x) ∧
  (∀ x ∈ m.I, θ ≤ x → V1 x < U1 x) ∧ (∀ x ∈ m.I, x < θ → U1 x = V1 x) ∧
  (∀ x ∈ m.I, θ < x → gen m V1 x + m.π x = 0) ∧
  (∀ x ∈ m.I, x < θ → gen m V1 x + m.π x < 0) ∧
  (∀ x ∈ m.I, θ < x → gen m U1 x + m.π x = 0) ∧
  (∀ x ∈ m.I, ∀ ζ : ℝ, 0 ≤ ζ → x + ζ ∈ m.I → U1 (x + ζ) - m.k * ζ - c 0 ≤ V1 x) ∧
  (∀ x ∈ m.I, ∀ ζ : ℝ, 0 ≤ ζ → x + ζ ∈ m.I → U1 (x + ζ) - m.k * ζ - c 0 ≤ U1 x) ∧
  (∀ y ∈ m.I, y ≠ z 0 → U1 y - m.k * y < U1 (z 0) - m.k * z 0) ∧
  (∀ x ∈ m.I, x < θ → V1 x = gFun m.k U1 (c 0) (z 0) x) ∧
  (∃ w1 u1 : ℝ, 0 < w1 ∧ w1 < u1 ∧ ∀ x ∈ m.I, θ ≤ x →
    V1 x = R m S m.π x + w1 * S.φ x ∧ U1 x = R m S m.π x + u1 * S.φ x) ∧
  U1 θ = q * U1 (z 1) + (1 - q) * V1 θ ∧
  V1 θ ≤ U1 (z 1) ∧ V1 θ = gFun m.k U1 (c 0) (z 0) θ ∧
  (∀ x ∈ m.I, x < θ →
    0 < V2 (z 0) - gFun m.k V2 (c 1) (z 1) x ∧ 0 < U1 (z 1) - gFun m.k U1 (c 0) (z 0) x)

/-- `ν*` induces the payoffs `F` (Lemmas B.6, B.7): from every `x ∈ I` and stage `s0`, every play
of `ν*` has well-defined payoffs, player 2's payoff is `V₂(x)`, and player 1's is `U₁(x)` if the
game starts in stage 1 and `V₁(x)` if it starts in stage 2 (`F_{1,t}` of (23)). -/
def Induces (m : Model) (S : Setting Ω) (Rd : Rand Ω) (c : Fin 2 → ℝ) (θ q : ℝ) (z : Fin 2 → ℝ)
    (lam : Fin 2 → ℝ → ℝ) (U1 V1 V2 : ℝ → ℝ) : Prop :=
  ∀ x ∈ m.I, ∀ s0 : Fin 2, ∀ O : Play Ω, IsPlay m S Rd x O →
    (∀ j, FollowsStar Rd q θ z lam s0 O j) →
    (∀ i, PayInt m S c O i) ∧ pay m S c O 1 = V2 x ∧
    pay m S c O 0 = (if s0 = 0 then U1 x else V1 x)

/-- `V̂₂` of the proof of Lemma B.8 (i) (EC p. 22), with `α = −I(θ*)`:
`V̂₂(x) = αφ(z₂) + (R_rπ)(z₂) − k(z₂ − x) − c₂` on `(a, θ*]`, `αφ(x) + (R_rπ)(x)` on `(θ*, b)`. -/
noncomputable def Vhat2 (m : Model) (S : Setting Ω) (c2 θ z2 : ℝ) (x : ℝ) : ℝ :=
  if x ≤ θ then -Ifun m S θ * S.φ z2 + R m S m.π z2 - m.k * (z2 - x) - c2
  else -Ifun m S θ * S.φ x + R m S m.π x

/-- `Û₁` of the proof of Lemma B.8 (ii) (EC p. 24), with `β = −I(z₁)`:
`Û₁(x) = βφ(x) + (R_rπ)(x)` on `[θ*, b)` and `Û₁ = V̂₁ = Û₁(z₁) − k(z₁ − x) − c₁` on `(a, θ*)`. -/
noncomputable def Uhat1 (m : Model) (S : Setting Ω) (c1 θ z1 : ℝ) (x : ℝ) : ℝ :=
  if x < θ then (-Ifun m S z1 * S.φ z1 + R m S m.π z1) - m.k * (z1 - x) - c1
  else -Ifun m S z1 * S.φ x + R m S m.π x

/-- `V̂₁` of the proof of Lemma B.8 (ii) (EC p. 24), with `α = −I(θ*)`, `β = −I(z₁)`:
`V̂₁(x) = αφ(x) + (R_rπ)(x)` on `[θ*, b)` and `Û₁(z₁) − k(z₁ − x) − c₁` on `(a, θ*)`. -/
noncomputable def Vhat1 (m : Model) (S : Setting Ω) (c1 θ z1 : ℝ) (x : ℝ) : ℝ :=
  if x < θ then (-Ifun m S z1 * S.φ z1 + R m S m.π z1) - m.k * (z1 - x) - c1
  else -Ifun m S θ * S.φ x + R m S m.π x

/-- The left-hand side of (B.22):
`φ(θ*)[I(θ*) − I(z₁)] / (−I(z₁)φ(z₂) + (R_rπ)(z₂) + I(θ*)φ(θ*) − (R_rπ)(θ*))`. -/
noncomputable def qB22 (m : Model) (S : Setting Ω) (θ z1 z2 : ℝ) : ℝ :=
  S.φ θ * (Ifun m S θ - Ifun m S z1) /
    (-Ifun m S z1 * S.φ z2 + R m S m.π z2 + Ifun m S θ * S.φ θ - R m S m.π θ)

/-- Condition (B.23): `−I(z₁)φ(θ*) + (R_rπ)(θ*) − kθ* < J(z₁)`. -/
def B23 (m : Model) (S : Setting Ω) (θ z1 : ℝ) : Prop :=
  -Ifun m S z1 * S.φ θ + R m S m.π θ - m.k * θ < Jfun m S z1

end InvestCommonGood.MixedTSSPE


