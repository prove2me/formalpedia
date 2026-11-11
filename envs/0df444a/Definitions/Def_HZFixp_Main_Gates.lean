-- Prove2me | Definitions.Def_HZFixp_Main_Gates
-- name    : HZFixp_Main_Gates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:52:37.14925+00:00
-- url     : https://prove2.me/theorems/cae379ec-d8ef-4acd-9904-e7314a68adfc
-- title:
--   §3.3.2 — the basic gate (Table 2, (9)) and the harmonic, reciprocal and feedback gates ((10), (11), Table 3)
-- statement:
--   A **basic gate** with center $T > 0$, sign $\sigma \in \{1,-1\}$ and terms $w_q/(d_q y + e_q A_q)$ ($d_q, e_q > 0$) has an output node $x$, a private node $y$ and input nodes $A_q$. With $Q(y,A) = \sum_q w_q/(d_q y + e_q A_q)$, its intended output is $x^\star(A) = 1/Q(T,A) - T$, and its edges (Table 2) produce, with $K_x = 1/(x+y)$ and $B_x = 1/(x+T)$, the contributions (9)
--   $$h = \sigma(B_x - K_x),\qquad G_y = \sigma(K_x - Q),\qquad P_q = \sigma w_q\Big(\frac{1}{d_q y + e_q A_q} - \frac{1}{d_q T + e_q A_q}\Big)$$
--   at the output node, the private node and input $A_q$. Write $f(y,A) = 1/Q(y,A) - y$.
--
--   - **Harmonic gate** ($T=1$, $\sigma=-1$): $Q(y,A,B) = \rho/(y+A) + (1-\rho)/(y+B)$, intended output $H_\rho(A,B) = \big(\rho/(1+A) + (1-\rho)/(1+B)\big)^{-1} - 1$; the derivative bounds $m_0 = \rho(1-\rho)(a_2-b_1)^2/(1.001+\rho b_2+(1-\rho)b_1)^2$ and $M_f = \rho(1-\rho)(b_2-a_1)^2/(0.999+\rho a_2+(1-\rho)a_1)^2$ for $A \in [a_1,b_1]$, $B \in [a_2,b_2]$.
--   - **Reciprocal gate** ($\sigma = 1$, integer $T$): intended output $J(A) = \kappa/(A+c) + \beta$; with $R_T = T+\beta$, $D_T = \kappa + R_T c$, (10) $Q(y,A) = \dfrac{101T/R_T}{y+100T} - \dfrac{\kappa/R_T}{(D_T/T)\,y + R_T A}$; its input contribution $P_A$ is (9) with $w = -\kappa/R_T$, $d = D_T/T$, $e = R_T$; the center (11) is $T = \big\lceil \max\{1,\ 20(u+|\beta|),\ 128\kappa(\kappa+c)/((a+c)^2\varepsilon)\}\big\rceil$.
--   - **Feedback gate** ($\sigma=1$, $T = 2\beta$, $\beta \ge 2$): $d = (\beta+1)/(2\beta)$ and $Q(y,Y) = 1/(Y + d y)$, so $x^\star = Y + 1 - \beta$.
--
--   These formulas are the local building blocks of the reduction from Quadratic Fixed Point to Reciprocal VI; Lemmas 3.7, 3.8, B.1 and B.2 are statements about them.
--
--   **Formalization Note.** The gates are represented by their formulas, with real parameters; a gate's edge multiplicities enter only as a common positive factor of its contributions (Lemma 3.7 states this factor explicitly).
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), pp. 15–18 (PDF 17–20), Table 2, (9), (10), (11), Figures 5–6, Table 3; p. 48 (PDF 50), definition of f; p. 50 (PDF 52), m_0 and M_f

import Mathlib
import Definitions.Def_HZFixp_Main_ReciprocalVI

namespace HZFixp.Main

/-! # The basic gate and its three instances (§3.3.2)

Liu, Tao, Yan, *Settling the Complexity of Hylland–Zeckhauser Equilibria*, arXiv:2606.06317 (held
version later than v2, sha256 36e91522…af1c), pp. 15–18 (PDF 17–20): the basic gate (Table 2,
(9)), the harmonic gate (Figure 5), the reciprocal gate ((10), (11), Figure 6) and the feedback
gate (Table 3); p. 48 (PDF 50): `f(y, A) = 1/Q(y, A) − y`.

A basic gate with center `T > 0`, sign `σ ∈ {1, −1}` and terms `w_q / (d_q y + e_q A_q)` has output
node `x`, private node `y` and inputs `A_q`; its edges (Table 2) make the contributions of (9). -/

/-- `K_x = 1/(x + y)` (§3.3.2, before (9)). -/
noncomputable def gateK (x y : ℝ) : ℝ := 1 / (x + y)

/-- `B_x = 1/(x + T)` (§3.3.2, before (9)). -/
noncomputable def gateB (x T : ℝ) : ℝ := 1 / (x + T)

/-- **The output contribution (9)** `h = σ(B_x − K_x)` of a basic gate at its output node `x`. -/
noncomputable def gateH (σ x y T : ℝ) : ℝ := σ * (gateB x T - gateK x y)

/-- **The private-node field (9)** `G_y = σ(K_x − Q)`, with `Q = Q(y, A)` the gate's sum of terms. -/
noncomputable def gateGy (σ x y Q : ℝ) : ℝ := σ * (gateK x y - Q)

/-- **The input contribution (9)** `P_q = σ w_q (1/(d_q y + e_q A_q) − 1/(d_q T + e_q A_q))` of the
term `w_q/(d_q y + e_q A_q)` at its input node `A_q` (the second fraction is the
input-compensation edge). -/
noncomputable def gateP (σ w d e y T A : ℝ) : ℝ := σ * w * (1 / (d * y + e * A) - 1 / (d * T + e * A))

/-- **The intended output** `x⋆(A) = 1/Q(T, A) − T`, from the value `Q(T, A)` at the center. -/
noncomputable def gateXStar (QT T : ℝ) : ℝ := 1 / QT - T

/-! ## The harmonic gate (T = 1, σ = −1) -/

/-- The harmonic function `H_ρ(A, B) = (ρ/(1 + A) + (1 − ρ)/(1 + B))^{−1} − 1`. -/
noncomputable def harmH (ρ A B : ℝ) : ℝ := (ρ / (1 + A) + (1 - ρ) / (1 + B))⁻¹ - 1

/-- `Q(y, A, B) = ρ/(y + A) + (1 − ρ)/(y + B)` of the harmonic gate. -/
noncomputable def harmQ (ρ y A B : ℝ) : ℝ := ρ / (y + A) + (1 - ρ) / (y + B)

/-- `f(y, A, B) = 1/Q(y, A, B) − y` of the harmonic gate. -/
noncomputable def harmF (ρ y A B : ℝ) : ℝ := 1 / harmQ ρ y A B - y

/-- The lower derivative bound `m_0` of the harmonic gate (p. 50) for inputs `A ∈ [a_1, b_1]`,
`B ∈ [a_2, b_2]`. -/
noncomputable def harmM0 (ρ a₁ b₁ a₂ b₂ : ℝ) : ℝ :=
  ρ * (1 - ρ) * (a₂ - b₁) ^ 2 / (1.001 + ρ * b₂ + (1 - ρ) * b₁) ^ 2

/-- The upper derivative bound `M_f` of the harmonic gate (p. 50). -/
noncomputable def harmMf (ρ a₁ b₁ a₂ b₂ : ℝ) : ℝ :=
  ρ * (1 - ρ) * (b₂ - a₁) ^ 2 / (0.999 + ρ * a₂ + (1 - ρ) * a₁) ^ 2

/-! ## The reciprocal gate (σ = 1) -/

/-- The reciprocal function `J(A) = κ/(A + c) + β`. -/
noncomputable def recJ (κ c β A : ℝ) : ℝ := κ / (A + c) + β

/-- `D_T = κ + R_T c` with `R_T = T + β`. -/
noncomputable def recD (κ c β T : ℝ) : ℝ := κ + (T + β) * c

/-- **(10)** `Q(y, A) = (101T/R_T)/(y + 100T) − (κ/R_T)/((D_T/T) y + R_T A)`, `R_T = T + β`. -/
noncomputable def recQ (κ c β T y A : ℝ) : ℝ :=
  (101 * T / (T + β)) / (y + 100 * T) - (κ / (T + β)) / ((recD κ c β T / T) * y + (T + β) * A)

/-- `f(y, A) = 1/Q(y, A) − y` of the reciprocal gate. -/
noncomputable def recF (κ c β T y A : ℝ) : ℝ := 1 / recQ κ c β T y A - y

/-- The input contribution `P_A` of the reciprocal gate: (9) for its input term, with
`w = −κ/R_T`, `d = D_T/T`, `e = R_T`, `σ = 1`. -/
noncomputable def recP (κ c β T y A : ℝ) : ℝ :=
  gateP 1 (-(κ / (T + β))) (recD κ c β T / T) (T + β) y T A

/-- **The center (11)** of a reciprocal gate with input interval `[a, b]`, output interval
`[ℓ, u]` and input tolerance `ε`:
`T = ⌈max{1, 20(u + |β|), 128κ(κ + c)/((a + c)² ε)}⌉`. -/
noncomputable def recCenter (κ c β a u ε : ℝ) : ℤ :=
  ⌈max (max 1 (20 * (u + |β|))) (128 * κ * (κ + c) / ((a + c) ^ 2 * ε))⌉

/-! ## The feedback gate (σ = 1, `x = z_j`, input `Y_j`, (w, d, e) = (1, d_j, 1)) -/

/-- `d_j = (β_j + 1)/(2β_j)`. -/
noncomputable def fbD (β : ℝ) : ℝ := (β + 1) / (2 * β)

/-- `Q(y, Y) = 1/(Y + d_j y)` of the feedback gate. -/
noncomputable def fbQ (β y Y : ℝ) : ℝ := 1 / (Y + fbD β * y)

end HZFixp.Main


