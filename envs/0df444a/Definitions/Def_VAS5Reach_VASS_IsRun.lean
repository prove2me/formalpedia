-- Prove2me | Definitions.Def_VAS5Reach_VASS_IsRun
-- name    : VAS5Reach_VASS_IsRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:34.669885+00:00
-- url     : https://prove2.me/theorems/16568bbe-2c0b-4c25-9366-21f1f5bdce05
-- title:
--   Paths, runs and $\mathbb Z$-runs of a VASS
-- statement:
--   Let $V = (Q, T)$ be a $d$-VASS. A **path** $\pi = (p_1, a_1, q_1) \cdots (p_k, a_k, q_k)$ is a sequence of transitions with $q_i = p_{i+1}$ for $i < k$; empty paths are allowed at every state. Its effect is $\mathrm{EFF}(\pi) := \sum_{i=1}^k a_i$ (`eff`). A configuration is a pair $p(x)$ with $x \in \mathbb N^d$.
--
--   1. The path $\pi$ from $p$ to $q$ induces a **run** $p(x) \xrightarrow{\pi} q(y)$ if all intermediate counter vectors $x + \mathrm{EFF}(\pi_1 \cdots \pi_j)$, $0 \le j \le k$, are nonnegative and $y = x + \mathrm{EFF}(\pi)$ (`IsRun`).
--   2. For $z, w \in \mathbb Z^d$ it induces a **$\mathbb Z$-run** $p(z) \xrightarrow{\pi}_{\mathbb Z} q(w)$ if $w = z + \mathrm{EFF}(\pi)$, with no sign constraint (`IsZRun`).
--   3. $p(x) \xrightarrow{*} q(y)$ (`Reach`) and $p(z) \xrightarrow{*}_{\mathbb Z} q(w)$ (`ZReach`) mean that such a path exists.
--
--   Reachability distances in the mission are stated as "some run of length at most $N$".
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3, pp.13–14 (PDF pp.15–16)

import Mathlib
import Definitions.Def_VAS5Reach_VASS

namespace VAS5Reach

namespace VASS

variable {S ι : Type}

/-- The effect `EFF(π) := a₁ + ⋯ + a_k` of a transition sequence `π = (p₁,a₁,q₁)⋯(p_k,a_k,q_k)`
(`0` for the empty sequence). -/
def eff (π : List (S × (ι → ℤ) × S)) : ι → ℤ :=
  (π.map fun τ => τ.2.1).sum

/-- `IsPath V p π q`: `π` is a path of `V` from state `p` to state `q`: a sequence of transitions
of `V` whose states chain together, starting at `p` and ending at `q`. The empty path is allowed
at every state of `V` (from `p` to `p`).

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3, printed p. 13
(PDF p. 15): "A path is a transition sequence π = (p1, a1, q1) · · · (pk, ak, qk) with qi = pi+1 for
i < k. […] Empty paths are allowed at every state and have length zero and effect 0." -/
def IsPath (V : VASS S ι) : S → List (S × (ι → ℤ) × S) → S → Prop
  | p, [], q => p ∈ V.states ∧ p = q
  | p, τ :: π, q => τ ∈ V.trans ∧ τ.1 = p ∧ IsPath V τ.2.2 π q

/-- `IsRun V p x π q y`: the path `π` induces an `ℕ`-run (a run) `p(x) −π→ q(y)`: `π` is a path
from `p` to `q`, all intermediate counter vectors `x + EFF(π₁⋯πⱼ)` (`0 ≤ j ≤ |π|`) are
nonnegative, and `y = x + EFF(π)`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3, printed pp. 13–14
(PDF pp. 15–16): "A configuration is a pair p(x) with p ∈ Q and x ∈ N^d. A transition
u = (p, a, q) induces a one-step run p(x) −u→ q(y) if x + a = y and both vectors are nonnegative.
[…] A path induces an N-run (or simply a run) when all intermediate counter values remain
nonnegative. […] We write p(x) −π→ q(y) if π induces a run from p(x) to q(y)".

**Formalization Note** Configurations `p(x)` are pairs of a state and a vector `x : ι → ℕ`;
intermediate counter values are computed in `ℤ`. -/
def IsRun (V : VASS S ι) (p : S) (x : ι → ℕ) (π : List (S × (ι → ℤ) × S)) (q : S)
    (y : ι → ℕ) : Prop :=
  IsPath V p π q ∧
  (∀ j ≤ π.length, ∀ i, 0 ≤ (x i : ℤ) + eff (π.take j) i) ∧
  (∀ i, (y i : ℤ) = (x i : ℤ) + eff π i)

/-- `IsZRun V p z π q w`: the path `π` induces a `ℤ`-run (integer run) `p(z) −π→_Z q(w)` between
`ℤ`-configurations: `π` is a path from `p` to `q` and `w = z + EFF(π)`; counters may be negative.

Source: arXiv:2610.40012, §3, printed p. 14 (PDF p. 16): "A looser semantics is defined on
Z-configurations of the form p(z), where z ∈ Z^d. A Z-run or integer run p(z) −π→Z q(w) is defined
analogously to a run, with configurations replaced by Z-configurations. […] a path π = t1 · · · tk
from p to q induces a Z-run p(z) −π→Z q(w), where w = z + EFF(π)."

**Formalization Note** In a `B`-encoding the *states* still record the encoded coordinates, so a
Z-run of an encoding keeps those coordinates in `[0, B]`; only the remaining counters are
unconstrained. -/
def IsZRun (V : VASS S ι) (p : S) (z : ι → ℤ) (π : List (S × (ι → ℤ) × S)) (q : S)
    (w : ι → ℤ) : Prop :=
  IsPath V p π q ∧ w = z + eff π

/-- Reachability `p(x) −∗→ q(y)`: some path induces a run from `p(x)` to `q(y)` (p. 14). -/
def Reach (V : VASS S ι) (p : S) (x : ι → ℕ) (q : S) (y : ι → ℕ) : Prop :=
  ∃ π, IsRun V p x π q y

/-- `ℤ`-reachability `p(z) −∗→_Z q(w)`: some path induces a `ℤ`-run from `p(z)` to `q(w)`
(p. 14). -/
def ZReach (V : VASS S ι) (p : S) (z : ι → ℤ) (q : S) (w : ι → ℤ) : Prop :=
  ∃ π, IsZRun V p z π q w

end VASS

end VAS5Reach


