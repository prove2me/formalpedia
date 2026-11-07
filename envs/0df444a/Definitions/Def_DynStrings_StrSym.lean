-- Prove2me | Definitions.Def_DynStrings_StrSym
-- name    : DynStrings_StrSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:04.452648+00:00
-- url     : https://prove2.me/theorems/161abc12-7d0f-40f0-8634-321e2bf4f092
-- title:
--   Structural symbols, expansion, RLSLP weights, thresholds $\ell_k$, $\kappa(m)$ and creation rounds $\lambda(A)$
-- statement:
--   The grammar symbols of restricted block compression.
--
--   Structural symbols are built from characters: every character $a$ is a terminal; for a symbol $A$ and an integer $r\ge2$, $(A,r)$ is a run; for $s\ge2$ symbols $A_1,\dots,A_s$, the sequence $(A_1,\dots,A_s)$ is a tuple of arity $s$. Two symbols are equal exactly when they are syntactically identical. The expansion is $\mathrm{val}(a)=a$, $\mathrm{val}((A,r))=\mathrm{val}(A)^r$ and $\mathrm{val}((A_1,\dots,A_s))=\mathrm{val}(A_1)\cdots\mathrm{val}(A_s)$, and the length of $A$ is $|\mathrm{val}(A)|$. In the size of a run-length straight-line program a terminal and a run count one unit each and a tuple of arity $s$ counts $s$ units.
--
--   The length thresholds and the round bound are
--
--   $$\ell_k=\Big(\frac43\Big)^{\lceil k/2\rceil-1},\qquad \kappa(m)=2\Big\lceil\log_{4/3}\big(4\max\{2,m\}\big)\Big\rceil .$$
--
--   A symbol is active in round $k$ if its length is at most $\ell_k$, and paused otherwise. The creation round is $\lambda(a)=0$; for a run $(B,r)$, $\lambda$ is the smallest odd $k>\lambda(B)$ with $B$ active in round $k$; for a tuple, the smallest even $k>\max_i\lambda(A_i)$ with all $A_i$ active in round $k$.
--
--   These are the objects the parse manipulates, and the creation round is the round in which a nonterminal can be formed.
--
--   **Formalization Note** The inductive type also contains syntactic objects with $r<2$ or fewer than two children; the predicate `WF` singles out the source's symbols, and the parse creates only well-formed ones. Equality is syntactic and decidable. The minimum in $\lambda$ is `sInf` of a set of naturals that is never empty, since $\ell_k\to\infty$. `syms A` is the set of symbols labelling the nodes of the tree obtained by unfolding $A$.
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Definition 4.1, pp.14–15; §4.2, p.15 (ℓ_k, active/paused); §4.3, p.16 (κ); Definition 4.6, p.17 (λ); p.13 (RLSLP size)

import Mathlib

namespace DynStrings

/-!
# Structural symbols, thresholds and creation rounds

Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript,
sha256 cfcb3de9…), Definition 4.1, pp.14–15 (structural symbols, expansion, length, arity,
RLSLP size), §4.2, p.15 (length thresholds `ℓ_k`, active and paused symbols), §4.3, p.16 (`κ`),
and Definition 4.6, p.17 (creation round `λ`).

**Formalization Note.**
* `StrSym α` is the free syntax of terminals `term a`, runs `run A r` and tuples `tuple [A₁, …, A_s]`;
  equality is syntactic, as on p.15. The paper's set `𝒜` requires `r ≥ 2` and `s ≥ 2`; this is the
  predicate `WF`. The parse only ever creates well-formed symbols, and the random-order hypothesis
  (`IsRandomOrders`) constrains orders only on well-formed symbols.
* `ℓ_k = (4/3)^{⌈k/2⌉ − 1}` is the real power `(4/3) ^ (((k + 1) / 2 : ℕ) - 1 : ℤ)`, so `ℓ_0 = 3/4`
  and `ℓ_1 = ℓ_2 = 1`.
* `κ(m) = 2⌈log_{4/3}(4 max{2, m})⌉` uses `Nat.ceil` of a positive real.
* `λ(A)` ("the smallest odd/even `k` with …") is `sInf` of a set of naturals; the set is never empty
  because `ℓ_k → ∞`.
* `syms A` is the set of symbols labelling the nodes of the tree obtained by unfolding `A`
  (Definition 4.5): `A` together with the symbols of its children, recursively.
-/

/-- Structural symbols (Definition 4.1): terminals, runs `(A, r)`, and tuples `(A₁, …, A_s)`. -/
inductive StrSym (α : Type) where
  /-- A terminal `a ∈ Σ`. -/
  | term : α → StrSym α
  /-- A run `(A, r)`. -/
  | run : StrSym α → ℕ → StrSym α
  /-- A tuple `(A₁, …, A_s)`. -/
  | tuple : List (StrSym α) → StrSym α

namespace StrSym

variable {α : Type}

section DecEq

variable [DecidableEq α]

mutual
/-- Syntactic equality of structural symbols is decidable. -/
def decEqSym : (A B : StrSym α) → Decidable (A = B)
  | .term a, .term b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .run A r, .run B s =>
    match decEqSym A B, decEq r s with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .tuple As, .tuple Bs =>
    match decEqList As Bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .term _, .run _ _ => isFalse (by intro e; cases e)
  | .term _, .tuple _ => isFalse (by intro e; cases e)
  | .run _ _, .term _ => isFalse (by intro e; cases e)
  | .run _ _, .tuple _ => isFalse (by intro e; cases e)
  | .tuple _, .term _ => isFalse (by intro e; cases e)
  | .tuple _, .run _ _ => isFalse (by intro e; cases e)
/-- Decidable equality of lists of structural symbols. -/
def decEqList : (As Bs : List (StrSym α)) → Decidable (As = Bs)
  | [], [] => isTrue rfl
  | A :: As, B :: Bs =>
    match decEqSym A B, decEqList As Bs with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
end

instance : DecidableEq (StrSym α) := decEqSym

end DecEq

mutual
/-- Well-formedness: runs have `r ≥ 2` and tuples have arity `s ≥ 2`, recursively
(the set `𝒜` of Definition 4.1). -/
def WF : StrSym α → Prop
  | .term _ => True
  | .run A r => 2 ≤ r ∧ WF A
  | .tuple As => 2 ≤ As.length ∧ WFList As
/-- Every symbol of the list is well formed. -/
def WFList : List (StrSym α) → Prop
  | [] => True
  | A :: As => WF A ∧ WFList As
end

mutual
/-- The expansion `val(A)`: `val(a) = a`, `val((A, r)) = val(A)^r`,
`val((A₁, …, A_s)) = val(A₁) ⋯ val(A_s)` (Definition 4.1). -/
def val : StrSym α → List α
  | .term a => [a]
  | .run A r => (List.replicate r (val A)).flatten
  | .tuple As => valL As
/-- `val(A₁ ⋯ A_m) = val(A₁) ⋯ val(A_m)` for a string of structural symbols. -/
def valL : List (StrSym α) → List α
  | [] => []
  | A :: As => val A ++ valL As
end

/-- The length `|val(A)|` of a structural symbol. -/
def len (A : StrSym α) : ℕ := (val A).length

/-- The arity `deg(A₁, …, A_s) = s` of a tuple; `0` for terminals and runs. -/
def deg : StrSym α → ℕ
  | .tuple As => As.length
  | _ => 0

/-- The contribution of a symbol to the RLSLP size (p.13): one unit per terminal, one per run,
and `s` per tuple of arity `s`. -/
def weight : StrSym α → ℕ
  | .term _ => 1
  | .run _ _ => 1
  | .tuple As => As.length

/-- A nonterminal is a run or a tuple. -/
def IsNonterminal : StrSym α → Prop
  | .term _ => False
  | _ => True

/-- The symbol is a tuple. -/
def IsTuple : StrSym α → Prop
  | .tuple _ => True
  | _ => False

section Syms

variable [DecidableEq α]

mutual
/-- The symbols labelling the nodes of the unfolding of `A` (Definition 4.5): `A` and,
recursively, the symbols of its children. -/
def syms : StrSym α → Finset (StrSym α)
  | .term a => {.term a}
  | .run A r => insert (.run A r) (syms A)
  | .tuple As => insert (.tuple As) (symsL As)
/-- The union of `syms` over a list of symbols. -/
def symsL : List (StrSym α) → Finset (StrSym α)
  | [] => ∅
  | A :: As => syms A ∪ symsL As
end

end Syms

end StrSym

/-- The length threshold `ℓ_k = (4/3)^{⌈k/2⌉ − 1}` (§4.2, p.15). -/
noncomputable def ell (k : ℕ) : ℝ := (4 / 3 : ℝ) ^ ((((k + 1) / 2 : ℕ) : ℤ) - 1)

/-- `A ∈ 𝒜_k`: the symbol is active in round `k`, i.e. `|val(A)| ≤ ℓ_k` (§4.2, p.15).
Otherwise it is paused. -/
def Active {α : Type} (k : ℕ) (A : StrSym α) : Prop := (StrSym.len A : ℝ) ≤ ell k

/-- `κ(m) = 2⌈log_{4/3}(4 max{2, m})⌉` (§4.3, p.16). -/
noncomputable def kappa (m : ℕ) : ℕ := 2 * ⌈Real.logb (4 / 3) (4 * max 2 (m : ℝ))⌉₊

namespace StrSym

variable {α : Type}

mutual
/-- The creation round `λ(A)` (Definition 4.6, p.17): `λ(a) = 0`; for a run `(B, r)` the smallest
odd `k > λ(B)` with `B ∈ 𝒜_k`; for a tuple the smallest even `k > maxᵢ λ(Aᵢ)` with all
`Aᵢ ∈ 𝒜_k`. -/
noncomputable def cr : StrSym α → ℕ
  | .term _ => 0
  | .run B _ => sInf {k : ℕ | Odd k ∧ cr B < k ∧ Active k B}
  | .tuple As => sInf {k : ℕ | Even k ∧ crMax As < k ∧ ∀ A ∈ As, Active k A}
/-- `maxᵢ λ(Aᵢ)` over a list (`0` for the empty list). -/
noncomputable def crMax : List (StrSym α) → ℕ
  | [] => 0
  | A :: As => max (cr A) (crMax As)
end

end StrSym

end DynStrings


