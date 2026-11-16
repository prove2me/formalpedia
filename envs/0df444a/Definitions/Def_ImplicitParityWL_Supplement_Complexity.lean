-- Prove2me | Definitions.Def_ImplicitParityWL_Supplement_Complexity
-- name    : ImplicitParityWL_Supplement_Complexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:25:39.0871+00:00
-- url     : https://prove2.me/theorems/a9a0be17-e159-4e0d-8077-5076a8ede344
-- title:
--   WL Distinguishing, XP and fpt-reductions
-- statement:
--   Machines are the deterministic multitape Turing machines of the published `VariableWL` definition, which read their input and write their output as bit words on tape $0$.
--
--   1. **WL Distinguishing** with the dimension in the input is the language of the words $\mathrm{code}(G,H,k)$, for uncolored graphs $G,H$ and an integer $k\ge2$ (adjacency matrices and $k$ in the published `pairCode` format), such that $k$-WL distinguishes $G$ and $H$: in some round the histograms of $k$-tuple colors differ.
--   2. Its parameterization $\kappa$ maps $\mathrm{code}(G,H,k)$ to $k$ and every other word to $0$.
--   3. A **parameterization** $\kappa$ is a map from words to $\mathbb N$ computable in polynomial time.
--   4. $(Q,\kappa)\in\mathrm{XP}$ if one machine decides $Q$ and halts on every word $w$ within $f(\kappa(w))\cdot(|w|+1)^{f(\kappa(w))}$ steps, for a computable $f$.
--   5. An **fpt-reduction** from $(Q,\kappa)$ to $(Q',\kappa')$ is a machine mapping $w$ to a word $w'$ within $f(\kappa(w))\cdot(|w|+1)^c$ steps with $w\in Q\iff w'\in Q'$ and $\kappa'(w')\le g(\kappa(w))$, for computable $f,g$ and a constant $c$.
--   6. $(Q,\kappa)$ is **XP-complete** if $\kappa$ is a parameterization, $(Q,\kappa)\in\mathrm{XP}$, and every parameterized problem in XP fpt-reduces to it.
--
--   These are the classes of Theorem 1.2; the definitions are the standard ones of Flum and Grohe, *Parameterized Complexity Theory* (2006), Definitions 2.1 and 2.22.
--
--   **Formalization Note** WL Distinguishing is the complement, among well-formed codes, of the published language `OAI.VariableWL.WL`. $\kappa$ is written as the least $k$ with $w=\mathrm{code}(G,H,k)$, which is $0$ on words that are not codes.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §1.1, p.2 (WL Distinguishing, Theorem 1.2); Flum–Grohe 2006, Definitions 1.1, 2.1, 2.22

import Mathlib
import Definitions.Def_VariableWL

namespace ImplicitParityWL

namespace Supplement

open OAI.VariableWL

/-- The language **WL Distinguishing** with the dimension `k` part of the input (Curticapean, Liu,
Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, STOC
2027 submission, manuscript of November 3, 2026, §1.1, p.2): the codes `pairCode G H k` of two
uncolored graphs and a dimension `k ≥ 2` such that `k`-WL distinguishes `G` and `H`, i.e. some round's
histograms of `k`-tuple colors differ.

**Formalization Note** Graphs, colors, histograms and the code are the published `OAI.VariableWL`
ones (adjacency matrices, `k` as `integerCode`). This is the complement of `OAI.VariableWL.WL` among
well-formed codes. -/
def WLDist : Language :=
  {w | ∃ (G H : Graph) (k : ℕ), w = pairCode G H k ∧ 2 ≤ k ∧ ¬ Equivalent G H k}

/-- The parameterization `κ` of WL Distinguishing by the dimension (§1.1, p.2): `κ(pairCode G H k) = k`,
and `κ(w) = 0` for a word that is not a pair code.

**Formalization Note** Written as the least `k` with `w = pairCode G H k` for some `G`, `H`, which is
`0` (the infimum of the empty set) on other words. -/
noncomputable def wlParam (w : Word) : ℕ := sInf {k | ∃ G H : Graph, w = pairCode G H k}

/-- `κ` is a **parameterization** (Flum–Grohe, *Parameterized Complexity Theory*, Def. 1.1): a map
from words to `ℕ` computable in polynomial time, the output being `integerCode (κ w)`. -/
def IsParameterization (κ : Word → ℕ) : Prop :=
  ∃ (M : Machine) (c d : ℕ), ∀ w : Word,
    OutputsWithin M w (integerCode (κ w)) (c * (w.length + 1) ^ d)

/-- The parameterized problem `(Q, κ)` is in **XP** (Flum–Grohe, Def. 2.22): one deterministic
multitape machine decides `Q` and halts on every word `w` within `f(κ(w)) · |w|^{f(κ(w))}` steps, for a
computable `f`.

**Formalization Note** `|w|` is `|w| + 1`, which changes nothing up to `f`. -/
def InXP (Q : Language) (κ : Word → ℕ) : Prop :=
  ∃ (M : Machine) (f : ℕ → ℕ), Computable f ∧ ∀ w : Word, ∃ b : Bool, (b = true ↔ w ∈ Q) ∧
    OutputsWithin M w [b] (f (κ w) * (w.length + 1) ^ f (κ w))

/-- An **fpt-reduction** from `(Q, κ)` to `(Q', κ')` (Flum–Grohe, Def. 2.1): a machine computing
`w ↦ out` within `f(κ(w)) · |w|^c` steps, with `w ∈ Q ↔ out ∈ Q'` and `κ'(out) ≤ g(κ(w))`, for
computable `f`, `g` and a constant `c`. -/
def FptReduces (Q : Language) (κ : Word → ℕ) (Q' : Language) (κ' : Word → ℕ) : Prop :=
  ∃ (M : Machine) (f g : ℕ → ℕ) (c : ℕ), Computable f ∧ Computable g ∧ ∀ w : Word, ∃ out : Word,
    OutputsWithin M w out (f (κ w) * (w.length + 1) ^ c) ∧ (w ∈ Q ↔ out ∈ Q') ∧ κ' out ≤ g (κ w)

/-- `(Q, κ)` is **XP-complete under fpt-reductions**: `κ` is a parameterization, `(Q, κ) ∈ XP`, and
every parameterized problem in XP fpt-reduces to it. -/
def XPComplete (Q : Language) (κ : Word → ℕ) : Prop :=
  IsParameterization κ ∧ InXP Q κ ∧
    ∀ (Q' : Language) (κ' : Word → ℕ), IsParameterization κ' → InXP Q' κ' → FptReduces Q' κ' Q κ

end Supplement

end ImplicitParityWL


