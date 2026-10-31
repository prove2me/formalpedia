-- Prove2me | Definitions.Def_ScalableMARL_ProjectedBellman
-- name    : ScalableMARL_ProjectedBellman
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:25.658488+00:00
-- url     : https://prove2.me/theorems/e4a4a339-37b4-4959-a226-87af2ec25521
-- title:
--   The matrices $\Phi$, $P$, $\bar A_d$, $\bar b_d$, $D$, $\Pi_d$ and the projected Bellman operator $g_d$
-- statement:
--   The objects of Lemma 17 (p. 29), for a policy $\theta$, an agent $i$, the hop count $\kappa$ and a weight vector $d$ on the state-action pairs $\mathcal Z$.
--
--   1. $\Phi\in\mathbb R^{\mathcal Z\times\mathcal Z_{N_i^\kappa}}$ with $\Phi(z,x)=1$ if $z_{N_i^\kappa}=x$ and $0$ otherwise.
--   2. $P\in\mathbb R^{\mathcal Z\times\mathcal Z}$, the transition matrix of the state-action chain under $\theta$, and $r_i$ read as the vector $z\mapsto r_i(s_i,a_i)$ on $\mathcal Z$.
--   3. $\bar A_d=\Phi^\top\operatorname{diag}(d)(\gamma P\Phi-\Phi)$ (40) and $\bar b_d=\Phi^\top\operatorname{diag}(d)r_i$ (41).
--   4. $D=\Phi^\top\operatorname{diag}(d)\Phi$ and $\Pi_d=(\Phi^\top\operatorname{diag}(d)\Phi)^{-1}\Phi^\top\operatorname{diag}(d)$.
--   5. The Bellman operator $T_D(Q)=r_i+\gamma PQ$ of (15) and the projected operator $g_d(\hat Q_i)=\Pi_d T_D\Phi\hat Q_i$ on $\mathbb R^{\mathcal Z_{N_i^\kappa}}$.
--
--   $g_d$ is the operator whose fixed point the TD critic tracks; Lemma 17 states its properties.
--
--   **Formalization Note** Matrices are Mathlib `Matrix` over the finite types $\mathcal Z$ and $\mathcal Z_{N_i^\kappa}$; the inverse is Mathlib's `Matrix.inv` (equal to the true inverse when $D$ is invertible, as it is under the hypotheses of Lemma 17).
-- source:
--   Qu, Wierman & Li, Scalable Reinforcement Learning for Multi-Agent Networked Systems, arXiv:1912.02906v3, p. 15 (eq. (15)), p. 29 (eqs. (39)–(41), Lemma 17)

import Mathlib
import Definitions.Def_ScalableMARL_NetworkedMDP

namespace ScalableMARL

open Matrix

variable {n : ℕ} {S A : Fin n → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- `Φ ∈ ℝ^{Z × Z_{N_i^κ}}`, `Φ(z, x) = 1` if `z_{N_i^κ} = x` and `0` otherwise (p. 29). -/
noncomputable def Phi (M : NetMDP n S A) (κ : ℕ) (i : Fin n) :
    Matrix ((∀ i, S i) × (∀ i, A i)) (LocSA M.G κ i S A) ℝ :=
  Matrix.of fun z x => if restrictSA M.G κ i z = x then 1 else 0

/-- `P ∈ ℝ^{Z × Z}`, the transition matrix of the state-action chain under `θ` (p. 29). -/
noncomputable def Pmat (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param) :
    Matrix ((∀ i, S i) × (∀ i, A i)) ((∀ i, S i) × (∀ i, A i)) ℝ :=
  Matrix.of (chainKernel M pol θ)

/-- `r_i` read as a vector on the whole state-action space `Z`, `z ↦ r_i(s_i, a_i)` (p. 29). -/
def rVec (M : NetMDP n S A) (i : Fin n) : ((∀ i, S i) × (∀ i, A i)) → ℝ :=
  fun z => M.r i (z.1 i) (z.2 i)

/-- `Ā_d = Φᵀ diag(d)(γ P Φ − Φ)`, (40), p. 29. -/
noncomputable def Abar (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    (κ : ℕ) (i : Fin n) (d : ((∀ i, S i) × (∀ i, A i)) → ℝ) :
    Matrix (LocSA M.G κ i S A) (LocSA M.G κ i S A) ℝ :=
  (Phi M κ i)ᵀ * diagonal d * (M.γ • (Pmat M pol θ * Phi M κ i) - Phi M κ i)

/-- `b̄_d = Φᵀ diag(d) r_i`, (41), p. 29. -/
noncomputable def bbar (M : NetMDP n S A) (κ : ℕ) (i : Fin n)
    (d : ((∀ i, S i) × (∀ i, A i)) → ℝ) : LocSA M.G κ i S A → ℝ :=
  ((Phi M κ i)ᵀ * diagonal d) *ᵥ rVec M i

/-- `D = Φᵀ diag(d) Φ` (Lemma 17, p. 29). -/
noncomputable def Dmat (M : NetMDP n S A) (κ : ℕ) (i : Fin n)
    (d : ((∀ i, S i) × (∀ i, A i)) → ℝ) : Matrix (LocSA M.G κ i S A) (LocSA M.G κ i S A) ℝ :=
  (Phi M κ i)ᵀ * diagonal d * Phi M κ i

/-- `Π_d = (Φᵀ diag(d) Φ)⁻¹ Φᵀ diag(d)` (Lemma 17, p. 29). -/
noncomputable def projD (M : NetMDP n S A) (κ : ℕ) (i : Fin n)
    (d : ((∀ i, S i) × (∀ i, A i)) → ℝ) :
    Matrix (LocSA M.G κ i S A) ((∀ i, S i) × (∀ i, A i)) ℝ :=
  (Dmat M κ i d)⁻¹ * (Phi M κ i)ᵀ * diagonal d

/-- The Bellman operator `T_D(Q_i) = r_i + γ P Q_i` of (15), p. 15. -/
noncomputable def bellmanT (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param)
    (i : Fin n) (Q : ((∀ i, S i) × (∀ i, A i)) → ℝ) : ((∀ i, S i) × (∀ i, A i)) → ℝ :=
  rVec M i + M.γ • (Pmat M pol θ *ᵥ Q)

/-- `g_d(Q̂_i) = Π_d T_D Φ Q̂_i` (Lemma 17, p. 29). -/
noncomputable def gD (M : NetMDP n S A) (pol : LocalPolicyClass n S A) (θ : pol.Param) (κ : ℕ)
    (i : Fin n) (d : ((∀ i, S i) × (∀ i, A i)) → ℝ) (Qh : LocSA M.G κ i S A → ℝ) :
    LocSA M.G κ i S A → ℝ :=
  projD M κ i d *ᵥ bellmanT M pol θ i (Phi M κ i *ᵥ Qh)

end ScalableMARL


