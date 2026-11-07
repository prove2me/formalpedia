-- Prove2me | Definitions.Def_ImplicitParityWL_ParitySystem
-- name    : ImplicitParityWL_ParitySystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:05.149531+00:00
-- url     : https://prove2.me/theorems/4dc84fc4-dc64-4ffd-b773-d0f9f5d9ae88
-- title:
--   Parity system, unit propagation $K_r$ and first conflict round $\tau$
-- statement:
--   A **parity system** $P=(V,H,K_0)$ consists of variables taking values in $\mathbb F_2$, a family $H$ of homogeneous linear equations, each viewed as the set of its two or three distinct variables, and a set $K_0\subseteq V\times\mathbb F_2$ of initial facts. **Unit propagation** computes the facts known after round $r$ by
--   $$
--   K_{r+1}=K_r\cup\bigl\{(X,b_1+\dots+b_m)\ \big|\ \{X,Y_1,\dots,Y_m\}\in H,\ (Y_1,b_1),\dots,(Y_m,b_m)\in K_r\bigr\}.
--   $$
--   A **conflict** occurs when both $X=0$ and $X=1$ have been inferred for some variable $X$. The value $\tau(P)$ is the first round with a conflict, or $\infty$ if no conflict occurs.
--
--   This is the proof system whose round count the graph compiler transfers to $k$-WL.
--
--   **Formalization Note** $\tau$ takes values in `ℕ∞`, as an infimum over the rounds with a conflict, whose empty case is $\top$.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §4.1, p.16, eq. (5)

import Mathlib

namespace ImplicitParityWL

/-- A **parity system** `P = (V, H, K₀)` over a variable type `V` (Curticapean, Liu, Neuen, Seppelt,
*Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of
November 3, 2026, §4.1, p.16): a family `H` of homogeneous linear equations over `𝔽₂`, each viewed as
the set of its two or three distinct variables, and a set `K₀ ⊆ V × 𝔽₂` of initial facts.

**Formalization Note** Finiteness of the variable set is a property of the instance used; nothing in
the round structure below depends on it. -/
structure ParitySystem (V : Type*) where
  /-- The equations, each the set of its variables. -/
  eqs : Set (Finset V)
  /-- Every equation involves two or three distinct variables. -/
  eqs_card : ∀ h ∈ eqs, h.card = 2 ∨ h.card = 3
  /-- The initial facts `K₀`. -/
  init : Set (V × ZMod 2)

namespace ParitySystem

variable {V : Type*}

open scoped Classical in
/-- The set `K_r` of facts known after round `r` of unit propagation (§4.1, p.16, eq. (5)):
`K_{r+1} = K_r ∪ {(X, b₁ + ⋯ + b_m) | {X, Y₁, …, Y_m} ∈ H, (Y₁, b₁), …, (Y_m, b_m) ∈ K_r}`. -/
def K (P : ParitySystem V) : ℕ → Set (V × ZMod 2)
  | 0 => P.init
  | r + 1 => P.K r ∪ {f | ∃ h ∈ P.eqs, f.1 ∈ h ∧ ∃ b : V → ZMod 2,
      (∀ Y ∈ h.erase f.1, (Y, b Y) ∈ P.K r) ∧ f.2 = ∑ Y ∈ h.erase f.1, b Y}

/-- `K_r` contains a conflict: both `X = 0` and `X = 1` have been inferred for some variable `X`. -/
def HasConflict (P : ParitySystem V) (r : ℕ) : Prop :=
  ∃ X : V, (X, 0) ∈ P.K r ∧ (X, 1) ∈ P.K r

/-- `K_r` is conflict-free (§4.1, p.16). -/
def ConflictFree (P : ParitySystem V) (r : ℕ) : Prop := ¬ P.HasConflict r

/-- `τ(P)`, the first round with a conflict, or `∞` if no conflict occurs (§4.1, p.16).

**Formalization Note** The value lies in `ℕ∞`, and the infimum over the empty set of rounds is `⊤`. -/
noncomputable def τ (P : ParitySystem V) : ℕ∞ :=
  ⨅ (r : ℕ) (_ : P.HasConflict r), (r : ℕ∞)

end ParitySystem

end ImplicitParityWL


