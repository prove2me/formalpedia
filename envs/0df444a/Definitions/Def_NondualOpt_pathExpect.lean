-- Prove2me | Definitions.Def_NondualOpt_pathExpect
-- name    : NondualOpt_pathExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:41.399507+00:00
-- url     : https://prove2.me/theorems/a16cbc9a-3de6-4440-8739-a65662366240
-- title:
--   Path expectation $\mathbb E_\pi$ under an adaptive adversary
-- statement:
--   An **adaptive adversary** $\pi$ assigns to every round $t$ and loss history $z_{1:t}$ a finitely supported law $\pi_t(\cdot\mid z_{1:t})$ for the next loss index. For a functional $\Psi$ of the path, $\mathbb E_\pi[\Psi(z_{1:T})]$ is the nested expectation
--   $$
--   \mathbb E_{z_1\sim\pi_0}\,\mathbb E_{z_2\sim\pi_1(\cdot\mid z_1)}\cdots\mathbb E_{z_T\sim\pi_{T-1}(\cdot\mid z_{1:T-1})}\,\Psi(z_{1:T}).
--   $$
--   This is the nested expectation $\langle\!\langle\sup_{r_t}\mathbb E_{\ell_t\sim r_t}\rangle\!\rangle$ of Proposition 4 for a fixed strategy.
--
--   **Formalization Note** Computed by recursion on the number of remaining rounds; a finite nested sum, extended-real valued.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Proposition 4, (9), p.10; footnote 6, p.9

import Mathlib
import Definitions.Def_NondualOpt_FinLaw_expect

namespace NondualOpt

/-- The expectation `E_π[Ψ(z_{1:T})]` of a functional of the path under an adaptive adversary
with finitely supported laws: `π t h` is the law of `z_{t+1}` given the history `h = z_{1:t}`.
`pathExpect π Ψ k n h` integrates the remaining `k` rounds after the history `h`; the
expectation over a full horizon `T` is `pathExpect π Ψ T 0 Fin.elim0`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Proposition 4, (9), p.10 (the nested
expectation `⟪sup_{r_t} E_{ℓ_t ∼ r_t}⟫`), and footnote 6, p.9.

**Formalization Note.** Laws are finitely supported, so the expectation is a finite nested sum,
computed by recursion on the number of remaining rounds; `EReal`-valued. -/
noncomputable def pathExpect {Q : Type*} {S : Set Q} (π : (t : ℕ) → (Fin t → Q) → FinLaw S)
    (Ψ : (n : ℕ) → (Fin n → Q) → EReal) : (k n : ℕ) → (Fin n → Q) → EReal
  | 0, n, h => Ψ n h
  | k + 1, n, h => (π n h).expect (fun z => pathExpect π Ψ k (n + 1)
      (Fin.snoc (α := fun _ => Q) h z))

end NondualOpt


