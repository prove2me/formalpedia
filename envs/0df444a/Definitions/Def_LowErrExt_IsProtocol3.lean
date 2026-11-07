-- Prove2me | Definitions.Def_LowErrExt_IsProtocol3
-- name    : LowErrExt_IsProtocol3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:35.866957+00:00
-- url     : https://prove2.me/theorems/b8b760f7-5d6d-4f3d-a5e5-96174c37f504
-- title:
--   Three-round communication protocol
-- statement:
--   A function $\Gamma=(\Gamma_1,\Gamma_2,\Gamma_3):X_1\times X_2\to\Sigma_1\times\Sigma_2\times\Sigma_3$ is a **three-round communication protocol** if for each round $i$ there are a side $p_i\in\{1,2\}$ and a function $g_i$ with
--   $$\Gamma_i(x_1,x_2)=g_i\big(\Gamma_1(x_1,x_2),\dots,\Gamma_{i-1}(x_1,x_2),x_{p_i}\big)$$
--   for all $x_1,x_2$: each message depends on the earlier messages and on one input only. Every fiber of a protocol is a Cartesian product.
--
--   **Formalization Note** The first round sees no earlier message (the unit type).
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Definition 2.22, p.19

import Mathlib

namespace LowErrExt

/-- **One round of a protocol.** `IsRound h prev`: the message `h(x₁, x₂)` is a function of the
previous messages `prev(x₁, x₂)` and of one of the two inputs. -/
def IsRound {A B P M : Type*} (h : A × B → M) (prev : A × B → P) : Prop :=
  (∃ g : P → A → M, ∀ x y, h (x, y) = g (prev (x, y)) x) ∨
    (∃ g : P → B → M, ∀ x y, h (x, y) = g (prev (x, y)) y)

/-- **Three-round communication protocol.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 2.22, p.19: "We say that a function Γ : X1 × X2 → Σ1 × · · · × Σr is an r-round
communication protocol if for every i ∈ [r], the following holds. There is some pi ∈ [2] and function
gi : Σ1 × · · · × Σi−1 × Xpi → Σi such that Γi(x1, x2) = gi(Γ1(x1, x2), . . . , Γi−1(x1, x2), xpi)".

Here `r = 3`: `Γ = (Γ₁, Γ₂, Γ₃)` with `Γ₁` a function of one input, `Γ₂` of `Γ₁` and one input,
`Γ₃` of `(Γ₁, Γ₂)` and one input; the side `pᵢ` is chosen per round.

**Formalization Note.** The first round sees the empty tuple of previous messages, `Unit`. -/
def IsProtocol3 {A B S₁ S₂ S₃ : Type*} (Γ : A × B → S₁ × S₂ × S₃) : Prop :=
  IsRound (fun z => (Γ z).1) (fun _ => ()) ∧
    IsRound (fun z => (Γ z).2.1) (fun z => (Γ z).1) ∧
      IsRound (fun z => (Γ z).2.2) (fun z => ((Γ z).1, (Γ z).2.1))

end LowErrExt


