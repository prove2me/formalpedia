-- Prove2me | Definitions.Def_KMSHolder_realChain
-- name    : KMSHolder_realChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:16.772449+00:00
-- url     : https://prove2.me/theorems/c46b2bf7-37fb-46c5-b88b-49788ea6da00
-- title:
--   Real-time correlation $\langle\Omega, A_n\Delta^{is_n}\cdots A_1\Delta^{is_1}A_0\Omega\rangle$
-- statement:
--   Let $M$ be a von Neumann algebra on a Hilbert space $H$ with a cyclic and separating unit vector $\Omega$, vector state $\omega = \langle \Omega, \cdot\, \Omega\rangle$ and modular operator $\Delta$, so that $s \mapsto \Delta^{is}$ is a strongly continuous unitary group. For bounded operators $A_0, \dots, A_n$ and real $s_1, \dots, s_n$ put
--
--   $$
--   F_A(s_1, \dots, s_n) = \langle \Omega,\ A_n \Delta^{is_n} A_{n-1} \cdots A_1 \Delta^{is_1} A_0\, \Omega \rangle .
--   $$
--
--   Its analytic continuation in $z_j = i s_j$ to the tube $I^{(n)}$ is Araki's multiple-time correlation $\omega(A_n \Delta^{z_n} \cdots A_1 \Delta^{z_1} A_0)$, the object bounded by the Hölder inequality for KMS states. For a $(\tau,\beta)$-KMS state, $\Delta = e^{-\beta L}$ with $L$ the Liouvillean.
--
--   **Formalization Note** The modular data are the published `OAI.BoundedRecovery.StandardModularData` (cyclic separating unit vector `S.xi` and the functional calculus `S.D` of $\log\Delta$); $\Delta^{is}$ is `S.D.unitary s`. The Lean variable `s j` is the paper's $s_{j+1}$, the unitary between $A_j$ and $A_{j+1}$.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §2, eqs. (2)–(3), p.3; Δ^{1/2} = e^{−βL/2}, p.2 and p.4

import Mathlib
import Definitions.Def_BoundedRecovery

open OAI.BoundedRecovery
open scoped InnerProductSpace

namespace KMSHolder

/-- Jäkel–Robl, arXiv:1103.3608v2, §2, eqs. (2)–(3), p.3: the real-time correlation whose
analytic continuation is Araki's multiple-time expression `ω(Aₙ Δ^{zₙ} ⋯ A₁ Δ^{z₁} A₀)`:
for real `s₁, …, sₙ`,
`⟪Ω, Aₙ Δ^{isₙ} Aₙ₋₁ ⋯ A₁ Δ^{is₁} A₀ Ω⟫`.

**Formalization Note.**
* The KMS state is replaced by standard modular data `S` (`OAI.BoundedRecovery.StandardModularData`):
  `Ω = S.xi`, `ω = ⟪Ω, · Ω⟫`, and `Δ = e^{D}` with `D = S.D` (the Tomita graph pins
  `D = log Δ`). The paper's `e^{−zβL}` is `Δ^z` (p.2: "Δ^{1/2} = e^{−βL/2}"; p.4).
* `Δ^{is} = S.D.unitary s`, the calculus applied to `u ↦ e^{isu}`.
* Indices: `A ⟨j⟩` is the paper's `Aⱼ` (`j = 0, …, n`), and the Lean variable `s ⟨j⟩` is the
  paper's `s_{j+1}`: the unitary `Δ^{i s_{j+1}}` sits between `Aⱼ` and `A_{j+1}`.
  The operator is the product `(A₁Δ^{is₁})`, …, `(AₙΔ^{isₙ})` listed and reversed, so the
  leftmost factor is `Aₙ Δ^{isₙ}` and the rightmost is `A₀`. -/
noncomputable def realChain {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StandardModularData H) {n : ℕ} (A : Fin (n + 1) → H →L[ℂ] H)
    (s : Fin n → ℝ) : ℂ :=
  ⟪S.xi, ((List.ofFn (fun j : Fin n => A j.succ * S.D.unitary (s j))).reverse.prod * A 0)
    S.xi⟫_ℂ

end KMSHolder


