-- Prove2me | Definitions.Def_SteinitzExchange_Duality_SetFunction
-- name    : SteinitzExchange_Duality_SetFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:54:46.188988+00:00
-- url     : https://prove2.me/theorems/5fb5eb29-4116-467c-b4c0-4c95da2f6fba
-- title:
--   Submodular and supermodular set functions; the set functions and support functions of a base set
-- statement:
--   A set function $f:2^V\to\mathbb R$ (or $\to\mathbb Z$) is **submodular** if
--
--   $$f(X)+f(Y)\ge f(X\cup Y)+f(X\cap Y)\qquad(X,Y\subseteq V),$$
--
--   and $g:2^V\to\mathbb R$ is **supermodular** if $g(X)+g(Y)\le g(X\cup Y)+g(X\cap Y)$ for all $X,Y\subseteq V$.
--
--   For a finite nonempty $B\subseteq\mathbb Z^V$ define, for $X\subseteq V$ and $p\in\mathbb R^V$,
--
--   $$g_B(X)=\min\{x(X)\mid x\in B\},\quad f_B(X)=\max\{x(X)\mid x\in B\},\quad \psi^\circ_B(p)=\min\{\langle p,x\rangle\mid x\in B\},\quad \psi^\bullet_B(p)=\max\{\langle p,x\rangle\mid x\in B\}.$$
--
--   When $B$ is a finite integral base set, $f_B$ is the submodular and $g_B$ the supermodular function describing $B$ (Theorem 2.1); in Lemma 6.7 they appear as $g_1=g_{B_1}$, $f_2=f_{B_2}$, $\psi_1^\circ=\psi^\circ_{B_1}$ and $\psi_2^\bullet=\psi^\bullet_{B_2}$.
--
--   **Formalization Note.** `IsSubmodular`/`IsSupermodular` are stated for set functions `Finset V → β` with any ordered additive codomain (used with `ℤ` and `ℝ`). `setMin`, `setMax`, `supportMin`, `supportMax` are real `⨅`/`⨆` over the finite index set $B$; they are the paper's min/max for nonempty $B$ and take the junk value $0$ for empty $B$, which no statement uses.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 277, Eqs. (2.1), (2.2) and Theorem 2.1; p. 289, Eq. (5.1); p. 297 (before Lemma 6.7)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet

namespace SteinitzExchange.Duality

/-- A set function `f : 2^V → β` is submodular if `f(X) + f(Y) ≥ f(X ∪ Y) + f(X ∩ Y)` for all
`X, Y ⊆ V` (Murota 1996, p. 277, Eq. (2.1)). Used with `β = ℤ` (Theorem 2.1) and `β = ℝ`
(Theorem 6.5). -/
def IsSubmodular {V : Type*} [DecidableEq V] {β : Type*} [Add β] [LE β]
    (f : Finset V → β) : Prop :=
  ∀ X Y : Finset V, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y

/-- A set function `g : 2^V → β` is supermodular if `g(X) + g(Y) ≤ g(X ∪ Y) + g(X ∩ Y)` for all
`X, Y ⊆ V` (Murota 1996, p. 277, Eq. (2.2)). -/
def IsSupermodular {V : Type*} [DecidableEq V] {β : Type*} [Add β] [LE β]
    (g : Finset V → β) : Prop :=
  ∀ X Y : Finset V, g X + g Y ≤ g (X ∪ Y) + g (X ∩ Y)

/-- `g(X) = min{x(X) | x ∈ B}` (Murota 1996, p. 277, Theorem 2.1: the supermodular function
describing `B`; `g₁` on p. 297). For nonempty `B` the infimum over the finite index set is the
minimum; for empty `B` the value is the junk value `0`, and every statement assumes `B`
nonempty. -/
noncomputable def setMin {V : Type*} (B : Finset (V → ℤ)) (X : Finset V) : ℝ :=
  ⨅ x : (B : Set (V → ℤ)), ((sumOn (x : V → ℤ) X : ℤ) : ℝ)

/-- `f(X) = max{x(X) | x ∈ B}` (Murota 1996, p. 277, Theorem 2.1: the submodular function
describing `B`; `f₂` on p. 297). For nonempty `B` the supremum over the finite index set is the
maximum; for empty `B` the value is the junk value `0`, and every statement assumes `B`
nonempty. -/
noncomputable def setMax {V : Type*} (B : Finset (V → ℤ)) (X : Finset V) : ℝ :=
  ⨆ x : (B : Set (V → ℤ)), ((sumOn (x : V → ℤ) X : ℤ) : ℝ)

/-- `ψ°(p) = min{⟨p, x⟩ | x ∈ B}` (Murota 1996, p. 289, Eq. (5.1); `ψ₁°` on p. 297).
For empty `B` the value is the junk value `0`; every statement assumes `B` nonempty. -/
noncomputable def supportMin {V : Type*} [Fintype V] (B : Finset (V → ℤ)) (p : V → ℝ) : ℝ :=
  ⨅ x : (B : Set (V → ℤ)), pairing p (toReal (x : V → ℤ))

/-- `ψ•(p) = max{⟨p, x⟩ | x ∈ B}` (Murota 1996, p. 297, `ψ₂•`). For empty `B` the value is the
junk value `0`; every statement assumes `B` nonempty. -/
noncomputable def supportMax {V : Type*} [Fintype V] (B : Finset (V → ℤ)) (p : V → ℝ) : ℝ :=
  ⨆ x : (B : Set (V → ℤ)), pairing p (toReal (x : V → ℤ))

end SteinitzExchange.Duality


