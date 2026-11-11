-- Prove2me | Definitions.Def_GapAgnosticGS_vgtt
-- name    : GapAgnosticGS_vgtt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:51.849808+00:00
-- url     : https://prove2.me/theorems/7dacbb86-3ae1-426e-b27a-de0c1651313e
-- title:
--   Variable-time threshold test VGTT (Algorithm 2)
-- statement:
--   Fix an environment unitary $E$, a family of threshold tests $\mathrm{GTT}(\eta,a;\tau)$, a number of stages $m$ and an upper threshold $\ell_1$. **Algorithm 2** acts on $I$, $A$, stage registers $(C_r,P_r)_{r=1}^m$, a register $C_{m+1}$ and a flag $F$:
--
--   1. apply $E$ to $(I,A)$;
--   2. for $r=1,\dots,m$, with $\epsilon_r=2^{-r}$: if $\ell_1-3\epsilon_r/2\ge0$, apply $\mathrm{GTT}(\epsilon_r/2,a;\ell_1-3\epsilon_r/2)$ to $(I,A,C_r,P_r)$ controlled on $C_1=\dots=C_{r-1}=0$; then apply $\mathrm{CNOT}_{C_r\to F}$;
--   3. if $C_1=\dots=C_m=0$, flip $C_{m+1}$.
--
--   A branch is rejected (and stops) at the first stage whose flag is set, so different hidden branches stop at different times.
--
--   **Formalization Note** Stages are indexed from $0$ (Lean stage $r$ is the paper's stage $r+1$). All stages use one workspace type $P$. The initial state is `vgttInit`.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Algorithm 2, App. A.2, p.27 (PDF p.28)

import Definitions.Def_QAlgorithms_Defs_Basic

namespace GapAgnosticGS

open Classical in
/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Algorithm 2, Appendix A.2, p.27 (PDF p.28): "VGTT(E, |Ψ⟩_I, ℓ2, ℓ1, a) … 4: Change
registers I, A to E_{IA}|Ψ⟩_I|0⟩_A; 5: for r = 1, …, m do 6: ϵ_r ← 2^{−r}; 7: If ℓ1 − 3ϵ_r/2 ≥ 0,
controlled on C_1 = ⋯ = C_{r−1} = 0, apply GTT(ϵ_r/2, a; ℓ1 − 3ϵ_r/2) to (I, A, C_r, P_r).
8: Apply CNOT_{C_r→F}; 9: If C_1 = ⋯ = C_m = 0, flip C_{m+1}".

The unitary of Algorithm 2 with `m` stages and upper threshold `ℓ₁`, built from the environment
unitary `E` and a family `gtt η τ` of threshold tests on `(I, A, C, P)`, on the register
`(Fin n × A) × (Fin m → Bool × P) × Bool × Bool` = (`I`, `A`; stage registers `(C_r, P_r)`;
`C_{m+1}`; `F`). In order: `E` on `(I, A)`; for each stage `r` the controlled test and
`CNOT_{C_r → F}`; finally the flip of `C_{m+1}`.

**Formalization Note.** Stages are 0-based: Lean stage `r` is the paper's stage `r + 1`, with
`ϵ = 2^{−(r+1)}`, controlled on the flags of the earlier stages. A skipped stage (line 7's
condition false) is the identity. The initial state (line 3) is `vgttInit`; `m` and `a` are fixed
by the caller (`m = ⌈log₂(1/∆)⌉ + 2`, `a` inside `gtt`). -/
noncomputable def vgtt {n : ℕ} {A P : Type} [Fintype A] [DecidableEq A] [Fintype P]
    [DecidableEq P] (E : Matrix (Fin n × A) (Fin n × A) ℂ)
    (gtt : ℝ → ℝ → Matrix ((Fin n × A) × Bool × P) ((Fin n × A) × Bool × P) ℂ) (m : ℕ)
    (ℓ₁ : ℝ) :
    Matrix ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool)
      ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool) ℂ :=
  let applyE : Matrix ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool)
      ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool) ℂ :=
    Matrix.of fun x x' => if x.2 = x'.2 then E x.1 x'.1 else 0
  let stage : Fin m → Matrix ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool)
      ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool) ℂ := fun r =>
    let ε : ℝ := (2 : ℝ)⁻¹ ^ ((r : ℕ) + 1)
    if 0 ≤ ℓ₁ - 3 * ε / 2 then
      Matrix.of fun x x' =>
        if (∀ i, i ≠ r → x.2.1 i = x'.2.1 i) ∧ x.2.2 = x'.2.2 then
          if ∀ i : Fin m, i < r → (x'.2.1 i).1 = false then
            gtt (ε / 2) (ℓ₁ - 3 * ε / 2) (x.1, x.2.1 r) (x'.1, x'.2.1 r)
          else if x = x' then 1 else 0
        else 0
    else 1
  let cnotF : Fin m → Matrix ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool)
      ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool) ℂ := fun r =>
    Matrix.of fun x x' =>
      if x.1 = x'.1 ∧ x.2.1 = x'.2.1 ∧ x.2.2.1 = x'.2.2.1 ∧
          x.2.2.2 = xor x'.2.2.2 (x'.2.1 r).1 then 1 else 0
  let flipLast : Matrix ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool)
      ((Fin n × A) × (Fin m → Bool × P) × Bool × Bool) ℂ :=
    Matrix.of fun x x' =>
      if x.1 = x'.1 ∧ x.2.1 = x'.2.1 ∧ x.2.2.2 = x'.2.2.2 ∧
          x.2.2.1 = xor x'.2.2.1 (decide (∀ i, (x'.2.1 i).1 = false)) then 1 else 0
  flipLast * QAlgorithms.orderedProd (fun r => cnotF r * stage r) * applyE

end GapAgnosticGS


