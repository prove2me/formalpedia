-- Prove2me | Definitions.Def_QuantumWalkSearch_ApproxRAA_Circuit
-- name    : QuantumWalkSearch_ApproxRAA_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:06.125141+00:00
-- url     : https://prove2.me/theorems/fc3ad4a8-9d25-4e29-81f7-8ac404aacace
-- title:
--   Approximate RAA(i, γ): Aᵢ = A_{i−1}·Oᵢ·A_{i−1}†·ref(M̃⊥)·A_{i−1}, the states |φᵢ⟩, the error operators Eᵢ, the angles ϕᵢ, |µ⊥ᵢ⟩ and ẽᵢ (pp. 12–14)
-- statement:
--   This module defines the circuit **Approximate RAA**$(i,\gamma)$ of Magniez, Nayak, Roland and Santha and the quantities of the proof of their Lemma 1.
--
--   Fix $T$ extra registers $K_1,\dots,K_T$, $K_j=\mathbb C^{\kappa_j}$ with all-zeros state $|0\rangle$, and work on $\mathcal H\otimes[\bigotimes_{j=1}^T K_j]$. The **marked subspace** $\tilde{\mathcal M}=\mathcal M\otimes[\bigotimes_j K_j]$ consists of the states whose first register is marked, and $\mathrm{ref}(\tilde{\mathcal M}^\perp)=\mathrm{Id}-2\Pi_{\tilde M}$. The initial state is $|\varphi_0\rangle=|\pi\rangle|0^S\rangle$ (all registers zero).
--
--   1. **Step 4** of the $i$-th level ($1\le i\le T$) is the operator $O_i$: on a basis state in which some register $K_j$ with $j<i$ is not in $|0\rangle$ it multiplies by $-1$; on the other basis states it applies $R_i$ to $\mathcal H\otimes K_i$ and the identity to the remaining registers.
--   2. **Approximate RAA.** $A_0=\mathrm{Id}$ and, for $1\le i\le T$,
--   $$
--   A_i=A_{i-1}\cdot O_i\cdot A_{i-1}^\dagger\cdot \mathrm{ref}(\tilde{\mathcal M}^\perp)\cdot A_{i-1},
--   $$
--   i.e. apply $A_{i-1}$, flip the phase of marked states, undo $A_{i-1}$, apply step 4, apply $A_{i-1}$.
--   3. $|\varphi_i\rangle=A_i|\varphi_0\rangle$.
--   4. $R_i=A_{i-1}\,O_i\,A_{i-1}^\dagger$ (steps 3–5) and the **error operator** $E_i=R_i-\mathrm{ref}(\varphi_{i-1})$.
--   5. The **angle** of a state $v$ is $\phi=\sin^{-1}\|\Pi_{\tilde M}v\|\in[0,\pi/2]$, so that $\sin^2\phi_i=\|\Pi_{\tilde M}|\varphi_i\rangle\|^2$.
--   6. $|\mu_i^\perp\rangle=(\mathrm{Id}-\Pi_{\tilde M})|\varphi_i\rangle/\|(\mathrm{Id}-\Pi_{\tilde M})|\varphi_i\rangle\|$.
--   7. The **surrogate error** $\tilde e_0=0$, $\tilde e_{i+1}=4\beta_{i+1}\bar\phi_i+3\tilde e_i$ with the ideal angle $\bar\phi_i=3^i\phi_0$.
--
--   If every $R_i$ were the exact reflection $\mathrm{ref}(\pi)\otimes$(projection on $|0\rangle$ of $K_i$), $A_i$ would be the recursive amplitude amplification of Høyer, Mosca and de Wolf; the module encodes the paper's variant in which $\mathrm{ref}(\pi)$ is replaced at level $i$ by the given approximation $R_i$.
--
--   **Formalization Note** Registers are indexed $0$-based in Lean: index $j$ is $K_{j+1}$, and the step operator, $R_i$ and $E_i$ are indexed by $ii=i-1$. "Undo" is the conjugate transpose $A_{i-1}^\dagger$, which is the inverse because $A_{i-1}$ is unitary under the hypotheses on $R$. For $i>T$ there is no register $K_i$; the definition sets $A_i=A_{i-1}$ there and no statement uses it. The normalization $v/\|v\|$ is $0$ when $v=0$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 12 (Approximate RAA(i, γ); φᵢ, Rᵢ, Eᵢ in the proof of Lemma 1), p. 13 (M̃, µ⊥ᵢ, Eq. (1)), p. 14 (ẽᵢ)

import Mathlib
import Definitions.Def_QuantumWalkSearch_ApproxRAA_Setting

namespace QuantumWalkSearch.ApproxRAA

open Matrix

/-! # Approximate RAA(i, γ) (p. 12) and the quantities of the proof of Lemma 1 (pp. 12–14)

The circuit with `T` induction steps acts on `H ⊗ [⊗_{i=1}^{T} K_i]`. Register `K_i` has basis
`κ i` and all-zeros state `z i`. The registers are indexed 0-based by `j : Fin T`, so `j`
is the register `K_{j+1}`, used at step `j + 1` with the circuit `R (j + 1)`. -/

variable {X : Type*} [Fintype X] [DecidableEq X] {κ : ℕ → Type*} [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)]

/-- The content of the extra registers `K_1, …, K_T`: `j : Fin T` holds a basis state of
`K_{j+1} = ℂ^{κ (j+1)}`. -/
abbrev Regs (κ : ℕ → Type*) (T : ℕ) : Type _ := (j : Fin T) → κ (j.val + 1)

/-- All registers in their all-zeros state `|0^S⟩`. -/
def zeroRegs (z : ∀ i, κ i) (T : ℕ) : Regs κ T := fun j => z (j.val + 1)

/-- The initial state `|φ₀⟩ = |π⟩|0^S⟩` of `H ⊗ [⊗_{i=1}^{T} K_i]`. -/
noncomputable def initState (z : ∀ i, κ i) (T : ℕ) (piState : EuclideanSpace ℂ (X × X)) :
    EuclideanSpace ℂ (X × X × Regs κ T) :=
  tensorZero (zeroRegs z T) piState

/-- Step 4 of Approximate RAA(i, γ) at step `i = ii + 1` (p. 12): "If any of the registers
`K_j`, with `j < i`, are not in state `|0^{s_j}⟩`, respectively, then flip the phase of the
state. Otherwise, apply `R(β_i)` on `H ⊗ K_i`." As a matrix: on a basis column `q` in which
some register `K_{j+1}` with `j < ii` is not `0`, it is `−Id`; on the other basis columns it is
`R i` acting on the `H`-part and the register `K_i` (index `ii`), and the identity on the
remaining registers. -/
noncomputable def controlledR (z : ∀ i, κ i) (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ)
    (T : ℕ) (ii : Fin T) : Matrix (X × X × Regs κ T) (X × X × Regs κ T) ℂ :=
  fun p q =>
    if ∃ j : Fin T, j < ii ∧ q.2.2 j ≠ z (j.val + 1) then
      (if p = q then -1 else 0)
    else if ∀ j : Fin T, j ≠ ii → p.2.2 j = q.2.2 j then
      R (ii.val + 1) (p.1, p.2.1, p.2.2 ii) (q.1, q.2.1, q.2.2 ii)
    else 0

/-- The unitary `A_i` of Approximate RAA(i, γ) (p. 12), on `H ⊗ [⊗_{j=1}^{T} K_j]`.
`A_0 = Id` and, for `1 ≤ i ≤ T`, the five steps give, as an operator (rightmost first),
`A_i = A_{i−1} · O_i · A_{i−1}† · ref(M̃⊥) · A_{i−1}`, where `ref(M̃⊥)` is step 2
(`flipMarked`), `A_{i−1}†` (conjugate transpose) is "Undo Approximate RAA(i − 1, γ)", and
`O_i` is step 4 (`controlledR`). There is no register `K_i` for `i > T`; the definition sets
`A_i = A_{i−1}` there, and no statement uses it. The precisions `β_i` enter only through the
hypotheses on `R` (`ApproxReflections`). -/
noncomputable def approxRAA (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (T : ℕ) :
    ℕ → Matrix (X × X × Regs κ T) (X × X × Regs κ T) ℂ
  | 0 => 1
  | n + 1 =>
    if h : n < T then
      approxRAA M z R T n * controlledR z R T ⟨n, h⟩ * (approxRAA M z R T n)ᴴ *
        flipMarked M * approxRAA M z R T n
    else approxRAA M z R T n

/-- `|φ_i⟩ = A_i |φ₀⟩`, the output of Approximate RAA(i, γ) on `|φ₀⟩ = |π⟩|0^S⟩` (p. 12). -/
noncomputable def phi (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (piState : EuclideanSpace ℂ (X × X))
    (T i : ℕ) : EuclideanSpace ℂ (X × X × Regs κ T) :=
  act (approxRAA M z R T i) (initState z T piState)

/-- `R_i`, the product of steps 3–5 of Approximate RAA(i, γ), at `i = ii + 1`:
`R_i = A_{i−1} · O_i · A_{i−1}†` (p. 12). -/
noncomputable def reflStep (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (T : ℕ) (ii : Fin T) :
    Matrix (X × X × Regs κ T) (X × X × Regs κ T) ℂ :=
  approxRAA M z R T ii.val * controlledR z R T ii * (approxRAA M z R T ii.val)ᴴ

/-- The error operator `E_i = R_i − ref(φ_{i−1})` at `i = ii + 1` (p. 12). -/
noncomputable def errOp (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (piState : EuclideanSpace ℂ (X × X))
    (T : ℕ) (ii : Fin T) : Matrix (X × X × Regs κ T) (X × X × Regs κ T) ℂ :=
  reflStep M z R T ii - refState (phi M z R piState T ii.val)

/-- The angle `ϕ ∈ [0, π/2]` of a state `v` with the unmarked subspace:
`sin ϕ = ‖Π_M̃ v‖`, i.e. `ϕ = sin⁻¹ ‖Π_M̃ v‖` (p. 13, Eq. (1): `sin² ϕ_i = ‖Π_M̃ |φ_i⟩‖²`). -/
noncomputable def markedAngle {ρ : Type*} [Fintype ρ] [DecidableEq ρ] (M : Finset X)
    (v : EuclideanSpace ℂ (X × ρ)) : ℝ :=
  Real.arcsin ‖act (markedProj M) v‖

/-- The normalization `v / ‖v‖` of a vector; it is `0` for `v = 0` (as `‖0‖⁻¹ = 0`). -/
noncomputable def normalize {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ ι :=
  (‖v‖⁻¹ : ℝ) • v

/-- `|µ⊥_i⟩ = (Id − Π_M̃)|φ_i⟩ / ‖(Id − Π_M̃)|φ_i⟩‖` (p. 13). -/
noncomputable def muPerp (M : Finset X) (z : ∀ i, κ i)
    (R : ∀ i, Matrix (X × X × κ i) (X × X × κ i) ℂ) (piState : EuclideanSpace ℂ (X × X))
    (T i : ℕ) : EuclideanSpace ℂ (X × X × Regs κ T) :=
  normalize (act (unmarkedProj M) (phi M z R piState T i))

/-- The surrogate error `ẽ_i` (p. 14): `ẽ_0 = 0`, `ẽ_{i+1} = 4 β_{i+1} ϕ̄_i + 3 ẽ_i`, with the
ideal angle `ϕ̄_i = 3^i ϕ₀`. -/
noncomputable def etilde (γ φ₀ : ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => 4 * beta γ (i + 1) * ((3 : ℝ) ^ i * φ₀) + 3 * etilde γ φ₀ i

end QuantumWalkSearch.ApproxRAA


