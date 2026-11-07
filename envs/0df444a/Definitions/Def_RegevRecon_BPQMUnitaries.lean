-- Prove2me | Definitions.Def_RegevRecon_BPQMUnitaries
-- name    : RegevRecon_BPQMUnitaries
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:04:01.653084+00:00
-- url     : https://prove2.me/theorems/8edbb43a-1059-4845-b1eb-c7f30e53e18f
-- title:
--   The BPQM message states $|\phi_d(\mu)\rangle$, the vectors $|g_a\rangle$ and $V_{\mathrm{par}}$
-- statement:
--   A BPQM message about $d\in\mathbb F_p$ with classical part $\mu$ is the state $|\phi_d(\mu)\rangle=\sum_a\sqrt{\mu_a}\,\omega^{-ad}|a\rangle$ (26). The equality rule groups the product of two messages by $a=b+c$ with the vectors $|g_a\rangle=\sum_b\sqrt{\mu_b\nu_{a-b}}\,|b,a-b\rangle$. The parity rule applies the modular subtraction $V_{\mathrm{par}}|a,b\rangle=|a,b-a\rangle$.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), (26), p.9; pp.10–11

import Mathlib
import Definitions.Def_RegevRecon_Messages

namespace RegevRecon

open Finset

variable {p : ℕ} [Fact p.Prime]

/-- **The quantum message** `|ϕ_d(μ)⟩ = Σ_a √μ_a ω^{−ad} |a⟩`, Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), (26), p.9. -/
noncomputable def messageState (μ : Vec p) (d : ZMod p) : EuclideanSpace ℂ (ZMod p) :=
  WithLp.toLp 2 fun a => ((Real.sqrt (μ a) : ℝ) : ℂ) * zeta (-(a * d))

/-- `|ψ⟩ ⊗ |φ⟩` on two qudits. -/
noncomputable def qditTensor (ψ φ : EuclideanSpace ℂ (ZMod p)) :
    EuclideanSpace ℂ (ZMod p × ZMod p) :=
  WithLp.toLp 2 fun x => ψ x.1 * φ x.2

/-- `|a⟩ ⊗ |0⟩`-type vectors: `|ψ⟩ ⊗ |0⟩`. -/
noncomputable def withZero (ψ : EuclideanSpace ℂ (ZMod p)) : EuclideanSpace ℂ (ZMod p × ZMod p) :=
  WithLp.toLp 2 fun x => if x.2 = 0 then ψ x.1 else 0

/-- `|g_a⟩ = Σ_b √(μ_b ν_{a−b}) |b, a − b⟩`, p.10. -/
noncomputable def gVector (μ ν : Vec p) (a : ZMod p) : EuclideanSpace ℂ (ZMod p × ZMod p) :=
  WithLp.toLp 2 fun x => if x.1 + x.2 = a then ((Real.sqrt (μ x.1 * ν x.2) : ℝ) : ℂ) else 0

/-- **The modular subtraction** `V_par |a, b⟩ = |a, b − a⟩`, p.11. -/
noncomputable def Vpar : Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℂ :=
  Matrix.of fun y x => if y.1 = x.1 ∧ y.2 = x.2 - x.1 then 1 else 0

/-- The vector `A ψ` on two qudits. -/
noncomputable def qditAct (A : Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℂ)
    (ψ : EuclideanSpace ℂ (ZMod p × ZMod p)) : EuclideanSpace ℂ (ZMod p × ZMod p) :=
  WithLp.toLp 2 (Matrix.mulVec A (WithLp.ofLp ψ))

end RegevRecon


