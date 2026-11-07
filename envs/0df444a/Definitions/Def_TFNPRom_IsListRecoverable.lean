-- Prove2me | Definitions.Def_TFNPRom_IsListRecoverable
-- name    : TFNPRom_IsListRecoverable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:11.194256+00:00
-- url     : https://prove2.me/theorems/462cb4af-e29a-4ca3-8c8f-6918d3fe325a
-- title:
--   List recoverable codes
-- statement:
--   A code $C\subseteq\Gamma^L$ is **$(\delta,a,b)$-list recoverable** if for all $S_1,\dots,S_L\subseteq\Gamma$ with $|S_i|\le a$,
--   $$
--   \big|\{c\in C:\ |\{i: c_i\in S_i\}|\ge(1-\delta)L\}\big|\le b .
--   $$
--   By Claim 11 this gives well-spreadness of the hypergraph of the code.
--
--   **Formalization Note** The paper's $S_i\subset\Gamma$ is read as $S_i\subseteq\Gamma$, the larger class of lists.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…), §3.3, p.17

import Mathlib

namespace TFNPRom

open Classical in
/-- `C ⊆ Γ^L` is `(δ, a, b)`-list recoverable (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §3.3, p.17: "for every `S_1, …, S_ℓ ⊂ Γ` with
`|S_i| ≤ a`, the number of codewords `(c_1, …, c_ℓ) ∈ C` with `|{i ∈ [ℓ] | c_i ∈ S_i}| ≥ (1 - δ)ℓ` is at
most `b`").

**Formalization Note** The paper's `S_i ⊂ Γ` is read as `S_i ⊆ Γ`, the larger class of lists, so that
the whole alphabet is allowed when `|Γ| ≤ a`. -/
def IsListRecoverable {L : ℕ} {Γ : Type} (C : Finset (Fin L → Γ)) (δ : ℝ) (a b : ℕ) : Prop :=
  ∀ S : Fin L → Finset Γ, (∀ i, (S i).card ≤ a) →
    (C.filter fun c =>
      (1 - δ) * (L : ℝ) ≤ ((Finset.univ.filter fun i => c i ∈ S i).card : ℝ)).card ≤ b

end TFNPRom


