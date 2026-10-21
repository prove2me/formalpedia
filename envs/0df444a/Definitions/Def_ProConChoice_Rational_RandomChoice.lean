-- Prove2me | Definitions.Def_ProConChoice_Rational_RandomChoice
-- name    : ProConChoice_Rational_RandomChoice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:38.221927+00:00
-- url     : https://prove2.me/theorems/bf106450-1368-4063-b496-07c806dc137b
-- title:
--   §3.1, p. 8 and §6, pp. 17–19 — random choice functions, the Möbius transform q (9), prefix classes Pₖ, representation and refinement (14)
-- statement:
--   The objects used in the proof of Theorems 1 and 2 (Section 6 of the paper).
--
--   Let $X$ be a finite set with $n = |X|$ alternatives. A **random choice function** (RCF) $p$ assigns to every choice set (nonempty $S \subseteq X$) a probability distribution on $S$; $p(x, S)$ is the probability that $x$ is chosen from $S$, so $p(x, S) \ge 0$ for $x \in S$ and $\sum_{x \in S} p(x, S) = 1$. A deterministic choice function $C$ gives the RCF $p_C(x, S) = 1$ if $C(S) = x$ and $0$ otherwise.
--
--   **Möbius transform.** For an alternative $a$ and a set $S$ the paper's (9) defines
--   $$q(a, S) = \sum_{S \subseteq T \subseteq X} (-1)^{|T| - |S|}\, p(a, T) \qquad (a \in S),$$
--   and extends it by $q(a, S) = q(a, S \cup \{a\})$ for $a \notin S$.
--
--   **Prefix classes.** Two orderings are $k$-identical if they rank the same $k$ alternatives, in the same order, in the first $k$ positions. An equivalence class $[\succ^k] \in P_k$ is determined by its list of first $k$ alternatives $(\pi_0, \dots, \pi_{k-1})$ (distinct elements of $X$), called a $k$-prefix. If $S$ meets the prefix, the top of $S$ along it is the $\pi_i \in S$ with the least $i$; this is $\max(S, \succ)$ for every ordering $\succ$ of the class.
--
--   **Representation.** Let $\Omega_k = \{S : |S| > n - k\}$; every $k$-prefix meets every $S \in \Omega_k$. A signed weight function $\lambda_k$ on $P_k$ **represents** $p_k$, the restriction of $p$ to $\Omega_k$, if for every $S \in \Omega_k$ and every $x \in S$
--   $$p(x, S) = \sum_{[\succ^k] \,:\, x = \max(S, \succ^k)} \lambda_k([\succ^k]).$$
--
--   **Refinement (14).** $\lambda_{k+1}$ on $P_{k+1}$ refines $\lambda_k$ if for every $k$-prefix $[\succ^k]$, $\lambda_k([\succ^k])$ is the sum of $\lambda_{k+1}$ over the $(k+1)$-prefixes that extend it.
--
--   **Formalization Note** An RCF is a function `p : X → Finset X → ℝ` with the two conditions on every nonempty `S`; values `p x S` with $x \notin S$ are unconstrained and never enter a statement. `mobiusQ p a S` sums over $T \supseteq S \cup \{a\}$, which is (9) for $a \in S$ and builds the extension in for $a \notin S$. A $k$-prefix is an injection `Fin k ↪ X` (index base $0$). `TopAlong π S x` says that $x = \pi_i \in S$ and $\pi_j \notin S$ for $j < i$. `Represents k λ p` quantifies over `S` with `n < |S| + k`, i.e. $|S| > n - k$ without natural-number subtraction. `Refines k λ λ'` sums $\lambda'$ over the injections `Fin (k+1) ↪ X` whose first $k$ values are those of the given prefix.
-- source:
--   Dogan & Yildiz, Every choice function is pro-con rationalizable, SSRN 3085542 (January 10, 2021), p. 8 (Section 3.1, random choice function), p. 17 (q and eq. (9)), p. 18 (k-identical orderings, Pₖ, Ωₖ, pₖ, representation), p. 19 (eq. (14)); p. 22 (Cₖ for a choice function, Section 7)

import Mathlib

namespace ProConChoice.Rational

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A random choice function `p`: `p x S` is the probability that `x` is chosen from the choice
set `S`; for every nonempty `S` the values on `S` are nonnegative and sum to one. Values `p x S`
with `x ∉ S` or `S = ∅` are irrelevant. -/
def IsRCF (p : X → Finset X → ℝ) : Prop :=
  ∀ S : Finset X, S.Nonempty → (∀ x ∈ S, 0 ≤ p x S) ∧ ∑ x ∈ S, p x S = 1

/-- The random choice function of a deterministic choice function `C`: `p(x, S) = 1` if
`C(S) = x` and `0` otherwise. -/
def choiceRCF (C : Finset X → X) : X → Finset X → ℝ :=
  fun x S => if C S = x then 1 else 0

/-- The Möbius transform (9): `q(a, S) = ∑_{S ⊆ T ⊆ X} (-1)^{|T|-|S|} p(a, T)` for `a ∈ S`,
extended to `a ∉ S` by `q(a, S) = q(a, S ∪ {a})` (both cases are the sum over `T ⊇ S ∪ {a}`). -/
def mobiusQ (p : X → Finset X → ℝ) (a : X) (S : Finset X) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset X).powerset.filter (fun T => insert a S ⊆ T),
    (-1 : ℝ) ^ (T.card - (insert a S).card) * p a T

/-- A `k`-prefix `π : Fin k ↪ X` (the first `k` alternatives of an ordering, in order) stands for
the class `[≻ᵏ] ∈ Pₖ` of orderings that rank `π 0, π 1, …, π (k-1)` first. `TopAlong π S x`: `x` is
the first alternative of the prefix that lies in `S` (so `x = max(S, ≻)` for every ordering of the
class, when the prefix meets `S`). -/
def TopAlong {k : ℕ} (π : Fin k ↪ X) (S : Finset X) (x : X) : Prop :=
  ∃ i : Fin k, π i = x ∧ x ∈ S ∧ ∀ j : Fin k, j < i → π j ∉ S

instance {k : ℕ} (π : Fin k ↪ X) (S : Finset X) (x : X) : Decidable (TopAlong π S x) := by
  unfold TopAlong; infer_instance

/-- `λ` (a signed weight function on `Pₖ`) represents `pₖ`, the restriction of `p` to
`Ωₖ = {S : |S| > n - k}`: for every `S` with `|S| > n - k` and every `x ∈ S`,
`p(x, S) = ∑_{[≻ᵏ] : x = max(S, ≻ᵏ)} λ([≻ᵏ])`. (`n - k < |S|` is written `n < |S| + k`.) -/
def Represents (k : ℕ) (lam : (Fin k ↪ X) → ℝ) (p : X → Finset X → ℝ) : Prop :=
  ∀ S : Finset X, Fintype.card X < S.card + k → ∀ x ∈ S,
    p x S = ∑ π ∈ (Finset.univ : Finset (Fin k ↪ X)).filter (fun π => TopAlong π S x), lam π

/-- Refinement (14): `λₖ([≻ᵏ]) = ∑ λₖ₊₁([≻ᵏ⁺¹])` over the `(k+1)`-prefixes extending the
`k`-prefix. -/
def Refines (k : ℕ) (lam : (Fin k ↪ X) → ℝ) (lam' : (Fin (k + 1) ↪ X) → ℝ) : Prop :=
  ∀ π : Fin k ↪ X, lam π =
    ∑ π' ∈ (Finset.univ : Finset (Fin (k + 1) ↪ X)).filter
      (fun π' => ∀ i : Fin k, π' (Fin.castSucc i) = π i), lam' π'

end ProConChoice.Rational


