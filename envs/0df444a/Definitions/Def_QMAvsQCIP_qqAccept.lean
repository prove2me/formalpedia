-- Prove2me | Definitions.Def_QMAvsQCIP_qqAccept
-- name    : QMAvsQCIP_qqAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:45.927248+00:00
-- url     : https://prove2.me/theorems/7b109147-6cc4-41ef-bb70-12f95025d955
-- title:
--   Acceptance probability of a QCIP$^{\mathrm{bb}}$ verifier
-- statement:
--   For a quantum query verifier $V$, an oracle $O:Z\to\{0,1\}$ and a deterministic prover $P$, the acceptance probability $\Pr[\langle P^O,V^O\rangle(1^\lambda)=\mathrm{ACCEPT}]$: for verifier messages $a=(a_0,\dots,a_{R-1})$ the replies are $b_j=P([a_0,\dots,a_j])$; starting from the initial basis vector, round $j$ applies the reply unitary for $b_{j-1}$ (if $j\ge1$) and its operations, and projects onto outgoing message $a_j$ (if $j<R$). With $\phi_a$ the final unnormalized vector,
--   $$
--   \Pr[\langle P^O,V^O\rangle=\mathrm{ACCEPT}]=\sum_{a}\ \sum_{r:\ \mathrm{dec}(r)=1}|\phi_a(r)|^2 .
--   $$
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definition 5, p.17; Section 3.2, p.14

import Definitions.Def_QMAvsQCIP_QQVerifier
import Definitions.Def_QMAvsQCIP_BBProver

set_option autoImplicit false

namespace QMAvsQCIP

open Matrix

/-- The **acceptance probability** `Pr[⟨P^O, V^O⟩(1^λ) = ACCEPT]` of the query-model verifier
`V` against the deterministic prover `P` with oracle `O : Z → {0,1}`. For a sequence of verifier
messages `a = (a₀, …, a_{R−1})`, the replies are `b_j = P([a₀, …, a_j])`; starting from the basis
vector `|init⟩`, round `j < R` applies `recv (j−1) b_{j−1}` (if `j ≥ 1`), then `ops j`, then the
projection onto `sendOf = a_j`; round `R` applies `recv (R−1) b_{R−1}` (if `R ≥ 1`) and `ops R`.
The acceptance probability is `∑_a ∑_{r : decOf r = 1} |φ_a(r)|²`, `φ_a` the final unnormalized
vector.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 5, p.17 (PDF p.20): "Pr[⟨P_λ^O, V_λ^O⟩(1^λ) = ACCEPT] … the
probabilities are over their randomness and measurements with O fixed"; Section 3.2, p.14:
"U_O |z⟩_X |o⟩_A = |z⟩_X |o ⊕ O(z)⟩_A … The gate acts linearly on superpositions".

**Formalization Note.** Measurements of outgoing messages are projective; the probability of a
message sequence and a decision is the squared norm of the projected branch. -/
noncomputable def qqAccept {Z : Type} [Fintype Z] [DecidableEq Z] (V : QQVerifier Z)
    (O : Z → Bool) (P : BBProver V.ℓ) : ℝ :=
  let step : Option (Matrix.unitaryGroup (Z × Bool × Fin V.d) ℂ) →
      (Z × Bool × Fin V.d → ℂ) → (Z × Bool × Fin V.d → ℂ) := fun op ψ =>
    match op with
    | some U => (U : Matrix (Z × Bool × Fin V.d) (Z × Bool × Fin V.d) ℂ) *ᵥ ψ
    | none => fun r => ψ (r.1, xor r.2.1 (O r.1), r.2.2)
  let runOps : Fin (V.R + 1) → (Z × Bool × Fin V.d → ℂ) → (Z × Bool × Fin V.d → ℂ) :=
    fun j ψ => (V.ops j).foldl (fun χ op => step op χ) ψ
  let reply : (Fin V.R → Fin V.ℓ → Bool) → ℕ → Fin V.ℓ → Bool := fun a j =>
    P (((List.finRange V.R).filter (fun k => k.val ≤ j)).map a)
  let recvStep : (Fin V.R → Fin V.ℓ → Bool) → ℕ →
      (Z × Bool × Fin V.d → ℂ) → (Z × Bool × Fin V.d → ℂ) := fun a j ψ =>
    if h : 0 < j ∧ j ≤ V.R then
      (V.recv ⟨j - 1, by omega⟩ (reply a (j - 1)) :
        Matrix (Z × Bool × Fin V.d) (Z × Bool × Fin V.d) ℂ) *ᵥ ψ
    else ψ
  let start : Z × Bool × Fin V.d → ℂ := fun r => if r = V.init then 1 else 0
  let final : (Fin V.R → Fin V.ℓ → Bool) → (Z × Bool × Fin V.d → ℂ) := fun a =>
    runOps (Fin.last V.R) (recvStep a V.R
      ((List.finRange V.R).foldl
        (fun ψ j => fun r =>
          if V.sendOf r = a j then runOps j.castSucc (recvStep a j.val ψ) r else 0)
        start))
  ∑ a : Fin V.R → Fin V.ℓ → Bool, ∑ r, if V.decOf r then Complex.normSq (final a r) else 0

end QMAvsQCIP


