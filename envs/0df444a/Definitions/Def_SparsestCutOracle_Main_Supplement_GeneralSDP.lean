-- Prove2me | Definitions.Def_SparsestCutOracle_Main_Supplement_GeneralSDP
-- name    : SparsestCutOracle_Main_Supplement_GeneralSDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:47:48.914503+00:00
-- url     : https://prove2.me/theorems/c1dc1e96-9cfd-4bc6-bfd4-443d24455a43
-- title:
--   General normalized SDPs and changing-objective oracles
-- statement:
--   Let $A_1,\ldots,A_M,D,C$ be arbitrary real symmetric $n\times n$ matrices, with $D$ positive definite and $\tau>0$. The last constraint is $A_M=-D$, $b_M=-\tau$. A primal feasible matrix and a dual feasible vector satisfy, respectively,
--   $$
--   X\succeq0,\quad A_j\mathbin\bullet X\ge b_j\ (1\le j\le M),\qquad y\ge0,\quad C-\sum_j y_j A_j\succeq0.
--   $$
--   The trace pairing is $A\mathbin\bullet X=\operatorname{Tr}(AX)$, and the dual value is $b^\top y$. The canonical inverse positive square root $\Gamma=D^{-1/2}$ is defined by continuous functional calculus. In Lean the total constraint count is $M=m+1$, with the distinguished last coordinate indexed by $\operatorname{Fin.last}(m)$.
--
--   An oracle receives $X\succeq0$ with $D\mathbin\bullet X=\tau$, a current symmetric objective $C_{\rm in}$, and a positive target $\alpha$. On failure it returns a feasible integral certificate with cost at most $\gamma\alpha$, for the application's fixed factor $\gamma\ge1$. The underlying certificate type, feasibility and objective are supplied by the integral problem. On success it returns $y\ge0,F,C_{\rm out}$, all matrix quantities symmetric, with
--   $$
--   b^\top y\ge\alpha,\quad C_{\rm in}\preceq C_{\rm out},\quad F\preceq C_{\rm out},\quad Z\mathbin\bullet X\ge0,\quad-\rho D\preceq Z\preceq\rho D,\qquad Z=F-\sum_jy_jA_j.
--   $$
--   Responses are indexed by their call number, allowing arbitrary legal choices even at repeated matrix inputs. This general object has no graph-specific constraints, diagonal restriction, Slater assumption or feasibility assumption on the oracle's candidates beyond normalization.
-- source:
--   Robin Münk, Monika Henzinger, Harald Räcke, STOC 2027 submission #1170 (October 2026), pp. 10–14, (Primal), (Dual), §3.2–3.3, equation (4)

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_SDP

namespace SparsestCutOracle.Main.Supplement

/-- A general normalized minimization SDP. m counts constraints BEFORE the last one,
so the total number of constraints is m+1, including when m=0. -/
structure NormalizedSDP (n m : ℕ) where
  A : Fin (m + 1) → Mat n
  b : Fin (m + 1) → ℝ
  D : Mat n
  τ : ℝ
  symmetric : ∀ j, (A j).IsSymm
  positive : D.PosDef
  τ_pos : 0 < τ
  last_matrix : A (Fin.last m) = -D
  last_rhs : b (Fin.last m) = -τ

def primalFeasible {n m : ℕ} (S : NormalizedSDP n m) (X : Mat n) : Prop :=
  X.PosSemidef ∧ ∀ j, S.b j ≤ dot (S.A j) X

def constraintCombination {n m : ℕ} (S : NormalizedSDP n m)
    (y : Fin (m + 1) → ℝ) : Mat n := ∑ j, y j • S.A j

def objectiveValue {n m : ℕ} (S : NormalizedSDP n m) (y : Fin (m + 1) → ℝ) : ℝ :=
  ∑ j, S.b j * y j

def dualFeasible {n m : ℕ} (S : NormalizedSDP n m) (C : Mat n)
    (y : Fin (m + 1) → ℝ) : Prop :=
  (∀ j, 0 ≤ y j) ∧ (C - constraintCombination S y).PosSemidef

/-- Canonical inverse positive square root, via the real continuous functional calculus.
On the positive-definite domain this is D^(-1/2), for arbitrary symmetric D. -/
noncomputable def inverseSqrt {n m : ℕ} (S : NormalizedSDP n m) : Mat n :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) S.D

/-- The underlying integral optimization problem is application-dependent. The oracle's
failure branch must give a feasible integral object of cost at most ratio*α. -/
structure IntegralCertificates (n : ℕ) (Certificate : Type) where
  feasible : Certificate → Prop
  cost : Mat n → Certificate → ℝ
  ratio : ℝ
  ratio_ge_one : 1 ≤ ratio

structure OracleSuccess (n m : ℕ) where
  y : Fin (m + 1) → ℝ
  F : Mat n
  C_out : Mat n

def oracleFeedback {n m : ℕ} (S : NormalizedSDP n m) (r : OracleSuccess n m) : Mat n :=
  r.F - constraintCombination S r.y

/-- A call index allows arbitrary legal response sequences, including random or stateful
oracles after fixing their choices. No stationarity at repeated inputs is required. -/
abbrev GeneralOracle (n m : ℕ) (Certificate : Type) :=
  ℕ → Mat n → Mat n → ℝ → Certificate ⊕ OracleSuccess n m

/-- No primal feasibility or individual dual feasibility is assumed for an iterate/answer.
The oracle is specified on normalized PSD inputs and may increase the objective. -/
def GeneralOracleContract {n m : ℕ} {Certificate : Type}
    (S : NormalizedSDP n m) (I : IntegralCertificates n Certificate) (ρ : ℝ)
    (O : GeneralOracle n m Certificate) : Prop :=
  ∀ (t : ℕ) (X C : Mat n) (α : ℝ), X.PosSemidef → dot S.D X = S.τ → C.IsSymm → 0 < α →
    match O t X C α with
    | Sum.inl r => I.feasible r ∧ I.cost C r ≤ I.ratio * α
    | Sum.inr r =>
      (∀ j, 0 ≤ r.y j) ∧ r.F.IsSymm ∧ r.C_out.IsSymm ∧
      α ≤ objectiveValue S r.y ∧ LePSD C r.C_out ∧ LePSD r.F r.C_out ∧
      0 ≤ dot (oracleFeedback S r) X ∧
      LePSD ((-ρ) • S.D) (oracleFeedback S r) ∧
      LePSD (oracleFeedback S r) (ρ • S.D)

end SparsestCutOracle.Main.Supplement


