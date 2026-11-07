-- Prove2me | Definitions.Def_ArbSlowFP_tblD
-- name    : ArbSlowFP_tblD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:49.133353+00:00
-- url     : https://prove2.me/theorems/358b511c-151f-4bf7-bf02-90f9ba741a20
-- title:
--   Bare parent tables and the old-action tables (27), (28), (35), (39)
-- statement:
--   For **bare parent data** $(A,R,C,b,v)$ of order $k$, write $w=k+1$, $\chi=R_{b,:}$. For a baseline $H$, a scale $\tau$ and a gain $c$, the **height row** $\zeta$ is determined by
--   $$\zeta(I-B)=\chi(E_{2\tau}-E_\tau)+ce_{0,w}^\top,\qquad \zeta p_k(0)=H .$$
--   With $h=\zeta B-\chi E_\tau$ and $\psi=\zeta B-\zeta$, the **old-action tables** on the parent actions and the endpoint action $g$ are
--   $$G_O=\begin{pmatrix}A&-(A_{b,:}+v)^\top\\A_{b,:}+v&0\end{pmatrix},\quad X=\begin{pmatrix}CF_\tau\\e_{0,w}^\top\end{pmatrix},\quad S=\begin{pmatrix}RE_\tau+\mathbf 1_mh\\\zeta B-vCF_\tau+\delta e_{0,w}^\top\end{pmatrix},$$
--   $S_{\mathrm{mid}}=S+G_OX$ and $D=ST-S_{\mathrm{mid}}$. For a reset count table $M$, an interaction matrix $J$ and a coupling $P$, the module defines $V=\mathbf 1\zeta B-J^\top MB$, $Q=\mathbf 1(\zeta B-\zeta)+JM-J^\top MB$, $G=\begin{pmatrix}G_O&P\\-P^\top&J-J^\top\end{pmatrix}$, and the solution formula $P=P_0+D_RR_M+L_X(Q_R^\top-X^\top D_RR_M)$ with $D_R=D-P_0M$, $Q_R=Q-P_0^\top X$.
--
--   These are the tables of the one-step lift, with no trajectory in them, since Lemma 7.2 and Definition 6.2 apply to them before the next clock exists.
--
--   **Formalization Note** The endpoint action is `Sum.inr ()` on the type `ι ⊕ Unit`. The row $\zeta$ is given by $\zeta_0=H$ and $\zeta_{j+1}=(wT)_j$ with $w$ the right side above, equivalent to the printed equations because $I-B=NB$. The residual of (31) evaluates $D$ at $\delta=0$, which is harmless since $D$ does not depend on $\delta$ (Lemma 6.3). `IsAlgebraic` collects $AC=RN_k$, $vC=e_{0,k}^\top$, $\chi_{k-1}>0$.
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), pp.35–36, 40, 42; eqs. (27), (28), (35), (39)

import Mathlib
import Definitions.Def_ArbSlowFP_binomBasis

open Matrix

namespace ArbSlowFP

/-- The algebraic parent data `(A, R, C, b, v)` of §6.1, p.35, without any trajectory.

**Formalization Note.** Lemma 7.2 and Definition 6.2 are stated on these bare tables since
Proposition 7.6 applies them before the next clock exists ("It does not use trajectory validity",
p.56). -/
structure Parent (k : ℕ) (ι : Type*) where
  /-- The payoff matrix. -/
  A : Matrix ι ι ℚ
  /-- The score table. -/
  R : Matrix ι (Fin k) ℚ
  /-- The count table. -/
  C : Matrix ι (Fin k) ℚ
  /-- The entry action. -/
  b : ι
  /-- The counter row. -/
  v : ι → ℚ

namespace Parent

variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Parent k ι)

/-- The identities `AC = RN_k`, `vC = e⊤_{0,k}` and `χ_{k-1} > 0` of Definition 4.1 that Lemma 7.2
uses ("the reset identity, the counter identity, and the positive leading entry coefficient", p.56). -/
structure IsAlgebraic : Prop where
  AC_eq : P.A * P.C = P.R * shiftN k
  vC_eq : P.v ᵥ* P.C = e0Row k
  chi_last : 0 < lastCoef (P.R P.b)

/-- The right side `χ(E_{2τ} - E_τ) + c e⊤_{0,w}` of the height equation (27). -/
def zetaRhs (τ : ℕ) (c : ℚ) : Fin (k + 1) → ℚ :=
  P.R P.b ᵥ* (transE k (2 * τ) - transE k τ) + c • e0Row (k + 1)

/-- The height row `ζ` of (27), p.36, determined by `ζ(I - B) = χ(E_{2τ} - E_τ) + c e⊤_{0,w}` and
`ζ p_k(0) = H`. Since `I - B = NB`, the first equation reads `ζN = (…)T`, so `ζ₀ = H` and
`ζ_{j+1} = ((…)T)_j`. The mission's sanity file checks (27) for this row at orders 2 and 3. -/
def zeta (H : ℚ) (τ : ℕ) (c : ℚ) : Fin (k + 1) → ℚ :=
  Fin.cons H fun j => (P.zetaRhs τ c ᵥ* shiftT (k + 1)) j.castSucc

/-- The row `ψ = ζB - ζ`, p.42, computed from the height row at gain `c`. -/
def psi (H : ℚ) (τ : ℕ) (c : ℚ) : Fin (k + 1) → ℚ :=
  P.zeta H τ c ᵥ* shiftB (k + 1) - P.zeta H τ c

/-- The translation row `h = ζB - χE_τ` of (27), p.36. -/
def hRow (H : ℚ) (τ : ℕ) (c : ℚ) : Fin (k + 1) → ℚ :=
  P.zeta H τ c ᵥ* shiftB (k + 1) - P.R P.b ᵥ* transE k τ

/-- The old-action payoff matrix `G_O` of (28), p.36. The endpoint action `g` is `Sum.inr ()`. -/
def GO : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℚ :=
  Matrix.fromBlocks P.A (Matrix.of fun i _ => -(P.A P.b i + P.v i))
    (Matrix.of fun _ j => P.A P.b j + P.v j) 0

/-- The old-action count table `X = col(CF_τ, e⊤_{0,w})` of (28), p.36. -/
def X (τ : ℕ) : Matrix (ι ⊕ Unit) (Fin (k + 1)) ℚ :=
  Matrix.fromRows (P.C * transF k τ) (Matrix.of fun _ j => e0Row (k + 1) j)

/-- The old-action score table `S = col(RE_τ + 1_m h, ζB - vCF_τ + δe⊤_{0,w})` of (28), p.36. -/
def S (H : ℚ) (τ : ℕ) (c δ : ℚ) : Matrix (ι ⊕ Unit) (Fin (k + 1)) ℚ :=
  Matrix.fromRows (P.R * transE k τ + Matrix.of fun _ j => P.hRow H τ c j)
    (Matrix.of fun _ j =>
      (P.zeta H τ c ᵥ* shiftB (k + 1) - P.v ᵥ* (P.C * transF k τ) + δ • e0Row (k + 1)) j)

/-- `S_mid = S + G_O X` of (28), p.36. -/
def Smid (H : ℚ) (τ : ℕ) (c δ : ℚ) : Matrix (ι ⊕ Unit) (Fin (k + 1)) ℚ :=
  P.S H τ c δ + P.GO * P.X τ

/-- `D = ST - S_mid` of (28), p.36. Lemma 6.3 states that it does not depend on `δ`. -/
def D (H : ℚ) (τ : ℕ) (c δ : ℚ) : Matrix (ι ⊕ Unit) (Fin (k + 1)) ℚ :=
  P.S H τ c δ * shiftT (k + 1) - P.Smid H τ c δ

/-- The residual `(D°)⊤X - ℓ⊤_∗ψ°` of (31), p.38, at reference gain `cref`.

**Formalization Note.** `D°` is `D` evaluated at `δ = 0`, since `D` does not depend on `δ`. -/
def testResidual (H : ℚ) (τ : ℕ) (cref : ℚ) (ℓ : Fin (k + 1) → ℚ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
  (P.D H τ cref 0)ᵀ * P.X τ - Matrix.vecMulVec ℓ (P.psi H τ cref)

end Parent

/-- The reset-entry score table `V = 1_n ζB - J⊤MB` of (35), p.40. -/
def resetV {w : ℕ} {ρ : Type*} [Fintype ρ] (ζ : Fin w → ℚ) (J : Matrix ρ ρ ℚ)
    (M : Matrix ρ (Fin w) ℚ) : Matrix ρ (Fin w) ℚ :=
  (Matrix.of fun _ j => (ζ ᵥ* shiftB w) j) - Jᵀ * M * shiftB w

/-- The score-change table `Q = 1_n(ζB - ζ) + JM - J⊤MB` of (35), p.40. -/
def resetQ {w : ℕ} {ρ : Type*} [Fintype ρ] (ζ : Fin w → ℚ) (J : Matrix ρ ρ ℚ)
    (M : Matrix ρ (Fin w) ℚ) : Matrix ρ (Fin w) ℚ :=
  (Matrix.of fun _ j => (ζ ᵥ* shiftB w - ζ) j) + J * M - Jᵀ * M * shiftB w

/-- The lifted payoff matrix `G = [[G_O, P], [-P⊤, K]]`, `K = J - J⊤`, of (35), p.40. -/
def liftG {α ρ : Type*} (GO : Matrix α α ℚ) (P : Matrix α ρ ℚ) (J : Matrix ρ ρ ℚ) :
    Matrix (α ⊕ ρ) (α ⊕ ρ) ℚ :=
  Matrix.fromBlocks GO P (-Pᵀ) (J - Jᵀ)

/-- The solution formula (39), p.42:
`P = P₀ + D_R R_M + L_X(Q_R⊤ - X⊤D_R R_M)`, `D_R = D - P₀M`, `Q_R = Q - P₀⊤X`. -/
def couplingP {w : ℕ} {α ρ : Type*} [Fintype α] [Fintype ρ]
    (P₀ : Matrix α ρ ℚ) (D : Matrix α (Fin w) ℚ) (Q : Matrix ρ (Fin w) ℚ)
    (X : Matrix α (Fin w) ℚ) (M : Matrix ρ (Fin w) ℚ)
    (LX : Matrix α (Fin w) ℚ) (RM : Matrix (Fin w) ρ ℚ) : Matrix α ρ ℚ :=
  P₀ + (D - P₀ * M) * RM + LX * ((Q - P₀ᵀ * X)ᵀ - Xᵀ * (D - P₀ * M) * RM)

end ArbSlowFP


