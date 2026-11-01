-- Prove2me | Definitions.Def_MultiIssueMediation_Model
-- name    : MultiIssueMediation_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:01.280987+00:00
-- url     : https://prove2.me/theorems/dd378557-2584-4cab-bff3-5924acdbe36d
-- title:
--   Issues, bundles, one-issue preferences, acceptability and logrolling bundles
-- statement:
--   Two negotiators settle two issues with outcome sets $X=\{x_1,\dots,x_m,o_X\}$ and $Y=\{y_1,\dots,y_m,o_Y\}$, $m\ge 2$.
--
--   On either issue negotiator 1 prefers the smaller index and negotiator 2 the larger index. The outside option $o_Y$ is worst for both. The position of $o_X$ is private: row $\ell$ is the type of negotiator 1 that accepts $\{x_k: k\le\ell\}$ and column $j$ is the type of negotiator 2 that accepts $\{x_k: k\ge j\}$, each ranking the accepted alternatives above $o_X$ and the others below it. The set of acceptable alternatives is
--
--   $$A(\theta_i)=\{x\in X \mid x\ \theta_i^X\ o_X\}.$$
--
--   A bundle is a pair $(x,y)\in X\times Y$. The logrolling map is $t(x_k)=y_{m+1-k}$, and the logrolling bundles are
--
--   $$\mathbf B=\{b_k=(x_k,y_{m+1-k}) \mid k=1,\dots,m\}.$$
--
--   This is the common data of every statement of the mission.
--
--   **Formalization Note** An issue is `Option (Fin m)`: `some k` has paper index `k.val + 1`, and `none` is the outside option. The type that accepts nothing is left out, as on p.15. The relation of $\theta_i^X$ is computed from the type. `Fin.rev` is $k\mapsto m+1-k$ in paper indexing.
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, pp.11–15, Example 1, pp.13–14, and the definition of B, p.14

import Mathlib

namespace MultiIssueMediation

/-- The two negotiators `I = {1, 2}` (Kesten, Özyurt, *Efficient and Incentive Compatible
Mediation: An Ordinal Market Design Approach*, working paper, 4 October 2018, p.11). -/
inductive Negotiator
  | one
  | two
  deriving DecidableEq

/-- A bundle `(x, y) ∈ X × Y` (working paper of 4 October 2018, p.12), where
`X = {x₁, …, x_m, o_X}` and `Y = {y₁, …, y_m, o_Y}` (p.11).

**Formalization Note.** Each issue is `Option (Fin m)`: `some k` is the alternative of paper index
`k.val + 1`, and `none` is the outside option. -/
abbrev Bundle (m : ℕ) : Type := Option (Fin m) × Option (Fin m)

/-- The public ranking of the `m` alternatives of an issue (working paper of 4 October 2018, p.12):
"`z_k θ₁^Z z_{k+1}` and `z_{k+1} θ₂^Z z_k` for all `k = 1, …, m−1`". Negotiator 1 prefers the
smaller index and negotiator 2 the larger one. -/
def publicPrefers {m : ℕ} : Negotiator → Fin m → Fin m → Prop
  | .one, a, b => a < b
  | .two, a, b => b < a

/-- Whether the alternative `a` of issue `X` is acceptable to the type `t` of negotiator `i`
(working paper of 4 October 2018, p.15): "row (column) `ℓ` represents the preference of negotiator
1 (2) that finds all alternatives `{x_k | k ≤ ℓ}` (`{x_k | k ≥ ℓ}`) acceptable".

**Formalization Note.** A type is an index in `Fin m`, as in the paper's matrix `M × M`; the type
that accepts nothing is left out, as on p.15. -/
def acceptsIndex {m : ℕ} : Negotiator → Fin m → Fin m → Prop
  | .one, t, a => a ≤ t
  | .two, t, a => t ≤ a

/-- The strict preference `x θ_i^X x'` of the type `t` of negotiator `i` on issue `X` (working
paper of 4 October 2018, pp.11–12, 15): the public ranking on the alternatives, with `o_X` placed
below the acceptable alternatives and above the unacceptable ones. `o_X` is not strictly preferred
to itself. -/
def issueXPrefers {m : ℕ} (i : Negotiator) (t : Fin m) :
    Option (Fin m) → Option (Fin m) → Prop
  | some a, some b => publicPrefers i a b
  | some a, none => acceptsIndex i t a
  | none, some a => ¬ acceptsIndex i t a
  | none, none => False

/-- The strict preference `y θ_i^Y y'` of negotiator `i` on issue `Y` (working paper of 4 October
2018, p.12): the public ranking on the alternatives, and "`y θ_i^Y o_Y` for all `i` and
`y ∈ Y ∖ {o_Y}`". It does not depend on the type. -/
def issueYPrefers {m : ℕ} (i : Negotiator) : Option (Fin m) → Option (Fin m) → Prop
  | some a, some b => publicPrefers i a b
  | some _, none => True
  | none, _ => False

/-- The acceptable alternatives `A(θ_i) = {x ∈ X | x θ_i^X o_X}` (working paper of 4 October 2018,
p.12). In particular `o_X ∉ A(θ_i)`. -/
def acceptable {m : ℕ} (i : Negotiator) (t : Fin m) : Set (Option (Fin m)) :=
  {x | issueXPrefers i t x none}

/-- The logrolling map `t : X → Y`, with `t(x_k) = y_{m+1−k}` for both negotiators (working paper
of 4 October 2018, Example 1, pp.13–14, and the definition of `B` on p.14).

**Formalization Note.** `Fin.rev` is `k ↦ m+1−k` in the paper's indexing. The value at `o_X` is
never used, because Definition 1(iii) concerns acceptable alternatives only; `t(o_X) = o_Y` makes
the map one-to-one. -/
def logroll {m : ℕ} : Option (Fin m) → Option (Fin m) :=
  Option.map Fin.rev

/-- The logrolling bundle `b_k = (x_k, y_{m+1−k})` (working paper of 4 October 2018, p.14 and the
notation of Definition 5, p.19). -/
def logrollBundle {m : ℕ} (k : Fin m) : Bundle m :=
  (some k, some k.rev)

/-- The set of logrolling bundles `B = {(x_k, y_{m+1−k}) ∈ X × Y | k = 1, …, m}` (working paper of
4 October 2018, p.14). -/
def logrollBundles (m : ℕ) : Set (Bundle m) :=
  Set.range logrollBundle

end MultiIssueMediation


