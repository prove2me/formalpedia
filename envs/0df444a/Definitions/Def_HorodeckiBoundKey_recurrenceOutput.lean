-- Prove2me | Definitions.Def_HorodeckiBoundKey_recurrenceOutput
-- name    : HorodeckiBoundKey_recurrenceOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:15:35.955167+00:00
-- url     : https://prove2.me/theorems/a3873abe-d6f3-46f4-b9b7-116d11f1f764
-- title:
--   The state $\rho'$ of (12) after the recurrence step on $n$ copies
-- statement:
--   Fix $d\ge 2$, $l\ge 1$, $n\ge 1$ and $p$. Let $\varrho_s = \frac{2}{d^2+d}P_{sym}$ and $\varrho_a = \frac{2}{d^2-d}P_{as}$ be the extreme Werner states (9) on $\mathbb C^d\otimes\mathbb C^d$, and let $\tau_0 = \varrho_s^{\otimes l}$ and $\tau_1 = [(\varrho_a+\varrho_s)/2]^{\otimes l}$ be the hiding states (10), with Alice holding the first qudit of each copy and Bob the second. In the basis $|00\rangle, |01\rangle, |10\rangle, |11\rangle$ of the key qubits $AB$,
--   $$
--   \rho' = \frac1N\begin{bmatrix}
--   [\frac p2(\tau_0+\tau_1)]^{\otimes n} & 0 & 0 & [\frac p2(\tau_1-\tau_0)]^{\otimes n}\\
--   0 & [(\frac12-p)\tau_0]^{\otimes n} & 0 & 0\\
--   0 & 0 & [(\frac12-p)\tau_0]^{\otimes n} & 0\\
--   [\frac p2(\tau_1-\tau_0)]^{\otimes n} & 0 & 0 & [\frac p2(\tau_0+\tau_1)]^{\otimes n}
--   \end{bmatrix},
--   \qquad N = 2p^n + 2\left(\tfrac12-p\right)^n .
--   $$
--
--   Its upper-right block $X$ is the one whose trace norm (13) measures how close $\rho'$ is to a private bit.
--
--   **Formalization Note** $\tau_0$ and $\tau_1$ are the published `hidingTwo d l` and `hidingOne d l`. The shields of $\rho'$ are Alice's $n$ copies of her $l$ qudits and Bob's $n$ copies of his; $[X]^{\otimes n}$ is `bipartiteCopies X n`, which groups the copies by party.
-- source:
--   Horodecki, Horodecki, Horodecki, Oppenheim, Secure key from bound entanglement, arXiv:quant-ph/0309110v2, eq. (12), p.3 (with (9), p.2, and (10), p.3)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_HorodeckiBoundKey_recurrenceNorm

open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Dependency50.P24 (Key hidingOne hidingTwo bipartiteCopies)

namespace HorodeckiBoundKey

/-- Horodecki, Horodecki, Horodecki, Oppenheim, arXiv:quant-ph/0309110v2, eq. (12), p.3: the
state `ρ′` obtained from `n` copies of the state (11) by the recurrence step. In the basis
`|00⟩, |01⟩, |10⟩, |11⟩` of the key qubits `A B` it is `1/N` times the block matrix with
* diagonal blocks `[p/2 (τ₀+τ₁)]^{⊗n}`, `[(½−p) τ₀]^{⊗n}`, `[(½−p) τ₀]^{⊗n}`,
  `[p/2 (τ₀+τ₁)]^{⊗n}`;
* blocks `[p/2 (τ₁−τ₀)]^{⊗n}` at positions `(00, 11)` and `(11, 00)`;
* zero elsewhere,

where `N = 2pⁿ + 2(½ − p)ⁿ` (`recurrenceNorm`), and `τ₀ = ϱ_s^{⊗l}`, `τ₁ = [(ϱ_a+ϱ_s)/2]^{⊗l}`
are the hiding states (10) on `d ⊗ d` Werner systems.

**Formalization Note.** `τ₀ = hidingTwo d l` and `τ₁ = hidingOne d l` (published layer
`Dependency50.P24`), on Alice's `l` qudits × Bob's `l` qudits. The shield of `ρ′` is Alice's
`n` copies of her `l` qudits × Bob's `n` copies, and `[X]^{⊗n}` is `bipartiteCopies X n`, which
groups the copies by party. Registers are ordered `Key 2 × (A′ × B′)` as in `hidingFamily`. -/
noncomputable def recurrenceOutput (p : ℝ) (d l n : ℕ) :
    Op (Key 2 × ((Fin n → Fin l → Fin d) × (Fin n → Fin l → Fin d))) :=
  fun a b => ((recurrenceNorm p n : ℝ) : ℂ)⁻¹ *
    if (a.1 = (0,0) ∧ b.1 = (0,0)) ∨ (a.1 = (1,1) ∧ b.1 = (1,1)) then
      bipartiteCopies (((p/2 : ℝ) : ℂ) • (hidingTwo d l + hidingOne d l)) n a.2 b.2
    else if (a.1 = (0,0) ∧ b.1 = (1,1)) ∨ (a.1 = (1,1) ∧ b.1 = (0,0)) then
      bipartiteCopies (((p/2 : ℝ) : ℂ) • (hidingOne d l - hidingTwo d l)) n a.2 b.2
    else if (a.1 = (0,1) ∧ b.1 = (0,1)) ∨ (a.1 = (1,0) ∧ b.1 = (1,0)) then
      bipartiteCopies (((1/2 - p : ℝ) : ℂ) • hidingTwo d l) n a.2 b.2
    else 0

end HorodeckiBoundKey


