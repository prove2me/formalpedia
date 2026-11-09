-- Prove2me | Definitions.Def_NCFactorClosure607_Circuits_CofactorNFA
-- name    : NCFactorClosure607_Circuits_CofactorNFA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:17.865389+00:00
-- url     : https://prove2.me/theorems/4cd091e9-db37-479a-b8db-e277eb5673bd
-- title:
--   Cofactor data and the weighted automaton map $T$ removing a right cofactor
-- statement:
--   **Cofactor data.** For a nonzero polynomial $h\in F\langle X\rangle$ of degree $b$, cofactor data consist of a word $v=v_1\cdots v_b$ of maximum length $b$ with coefficient $c=[v]h\neq0$, and the coefficients
--   $$d_\ell=[t_\ell]h,\qquad t_\ell=v_{\ell+1}\cdots v_b\qquad(1\le\ell\le b)$$
--   of all proper suffixes of $v$, including $t_b=\varepsilon$. Put $\alpha_\ell=d_\ell/c$. For $b=0$ the data reduce to the nonzero scalar $c=h$.
--
--   **The automaton.** Given a word $v$ of length $b$, a scalar $c$ and $d_1,\dots,d_b$, the weighted automaton has states $*,0,1,\dots,b$, initial state $*$ and sole accepting state $b$. Its transitions, each with the input it reads and the replacement label it outputs, are exactly:
--
--   1. $*\to*$, reading any letter $x$, replacement $x$;
--   2. $*\to0$, reading nothing, replacement $1$;
--   3. $i\to i+1$, reading $v_{i+1}$, replacement $1$ $(0\le i<b)$;
--   4. $i\to0$, reading $v_{i+1}$, replacement $-\alpha_{i+1}$ $(0\le i<b)$.
--
--   An accepting run on a word $w$ is a path from $*$ to $b$ whose consumed letters spell exactly $w$. With the product of the replacement labels along a run taken in order,
--   $$T(w)=c^{-1}\sum_{\text{accepting runs on }w}\bigl(\text{ordered product of labels}\bigr),\qquad T(P)=\sum_{w\in X^*}[w]P\;T(w).$$
--   $T$ is an $F$-linear map $F\langle X\rangle\to F\langle X\rangle$; transitions with replacement $0$ are kept as formal runs contributing zero.
--
--   This map is the object of the cofactor-removal identity $T(gh)=g$ and is implemented by circuits through matrix substitution.
--
--   **Formalization Note** States are `Option (Fin (b+1))` with `none` the state $*$. The list of suffix coefficients is 0-indexed: entry $i$ is $d_{i+1}$. `ValidFor h` states that $h\neq0$, $|v|=\deg h$, $c=[v]h\neq0$ and that the list consists of exactly the $b$ suffix coefficients. The sum over runs is a `finsum` over the set of accepting runs, which is finite (each run uses the $\varepsilon$-transition at most once and every other transition reads a letter); this finiteness is proved without `sorry` in the mission's verification file.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.6, §3, eq. (2); p.6–7, §3.1, transition table and eq. (3); p.2–3, Theorem 1.1 (cofactor data); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Polynomials

/-!
# Cofactor data and the right-cofactor removal automaton

Arvind–Joglekar, *Factor Closure in Noncommutative Algebraic Complexity*,
STOC 2027 submission #607, §3, eq. (2), p.6; §3.1, p.6–7, eq. (3).

Cofactor data for a right cofactor `h` are a word `v = v₁ ⋯ v_b` of maximum length in `h`,
its coefficient `c = [v]h ≠ 0`, and the coefficients `d_ℓ = [t_ℓ]h` of its proper suffixes
`t_ℓ = v_{ℓ+1} ⋯ v_b` (`1 ≤ ℓ ≤ b`, `t_b = ε`). In Lean the list `suffixCoeffs` is
0-indexed: `suffixCoeffs[i] = d_{i+1}`.

The weighted automaton has states `∗, 0, 1, …, b` (Lean: `none` is `∗`, `some i` is `i`),
initial state `∗`, sole accepting state `b`, and exactly the transitions
* `∗ → ∗` reading any letter `x`, replacement `x`;
* `∗ → 0` reading nothing (ε), replacement `1`;
* `i → i+1` reading `v_{i+1}`, replacement `1` (`0 ≤ i < b`);
* `i → 0` reading `v_{i+1}`, replacement `-α_{i+1} = -d_{i+1}/c` (`0 ≤ i < b`).
`T(w)` is `c⁻¹` times the sum, over all accepting runs on `w`, of the ordered product of the
replacement labels, and `T(P) = Σ_w [w]P · T(w)` (eq. (3)).
-/

namespace NCFactorClosure607.Circuits

/-- Cofactor data (eq. (2), p.6; Theorem 1.1, p.2–3): a word `v`, a field element `c`, and the
list `(d₁, …, d_b)` of suffix coefficients. -/
structure CofactorData (F : Type*) (X : Type*) where
  /-- the word `v = v₁ ⋯ v_b` -/
  word : FreeMonoid X
  /-- the coefficient `c = [v]h` -/
  c : F
  /-- `suffixCoeffs[i] = d_{i+1} = [v_{i+2} ⋯ v_b]h`, for `0 ≤ i < b` -/
  suffixCoeffs : List F

namespace CofactorData

variable {F : Type*} [Field F] {X : Type*}

/-- `b = |v|`, the length of the cofactor word. -/
abbrev b (data : CofactorData F X) : ℕ := data.word.toList.length

/-- The letter `v_{i+1}` (0-indexed position `i`, `0 ≤ i < b`). -/
def letter (data : CofactorData F X) (i : Fin data.b) : X :=
  data.word.toList[i.val]'i.isLt

/-- The reset replacement `-α_{i+1} = -d_{i+1} · c⁻¹` (eq. (2) and the table of §3.1). -/
noncomputable def resetCoeff (data : CofactorData F X) (i : Fin data.b) : F :=
  -(data.suffixCoeffs.getD i.val 0 * data.c⁻¹)

/-- `data` are valid cofactor data for `h` (eq. (2), p.6; Theorem 1.1): `h ≠ 0`, the word `v`
has maximum length `|v| = deg h`, `c = [v]h ≠ 0`, and the list holds exactly the coefficients
in `h` of the proper suffixes `t_ℓ = v_{ℓ+1} ⋯ v_b`, `1 ≤ ℓ ≤ b` (including `t_b = ε`).
For `b = 0` this says that `h` is the nonzero scalar `c` and the list is empty. -/
def ValidFor (data : CofactorData F X) (h : FreeAlgebra F X) : Prop :=
  h ≠ 0 ∧ data.b = ncDeg h ∧ data.c = coeff data.word h ∧ data.c ≠ 0 ∧
    data.suffixCoeffs.length = data.b ∧
    ∀ (i : ℕ) (hi : i < data.suffixCoeffs.length),
      data.suffixCoeffs[i] = coeff (FreeMonoid.ofList (data.word.toList.drop (i + 1))) h

end CofactorData

/-- States `∗, 0, …, b` of the automaton: `none` is `∗`, `some i` is state `i`. -/
abbrev State (b : ℕ) := Option (Fin (b + 1))

/-- The transitions of the automaton (all of them, §3.1, p.6). -/
inductive Transition (b : ℕ) (X : Type*) where
  /-- `∗ → ∗`, reads `x`, replacement `x` -/
  | copy (x : X)
  /-- `∗ → 0`, reads nothing, replacement `1` -/
  | enter
  /-- `i → i+1`, reads `v_{i+1}`, replacement `1` -/
  | advance (i : Fin b)
  /-- `i → 0`, reads `v_{i+1}`, replacement `-α_{i+1}` -/
  | reset (i : Fin b)

namespace Transition

variable {b : ℕ} {X : Type*}

/-- Source state of a transition. -/
def src : Transition b X → State b
  | copy _ => none
  | enter => none
  | advance i => some i.castSucc
  | reset i => some i.castSucc

/-- Target state of a transition. -/
def tgt : Transition b X → State b
  | copy _ => none
  | enter => some 0
  | advance i => some i.succ
  | reset _ => some 0

end Transition

namespace CofactorData

variable {F : Type*} [Field F] {X : Type*}

/-- The input consumed by a transition (the empty list for the ε-transition). -/
def consumed (data : CofactorData F X) : Transition data.b X → List X
  | .copy x => [x]
  | .enter => []
  | .advance i => [data.letter i]
  | .reset i => [data.letter i]

/-- The replacement label of a transition, an element of `F⟨X⟩`. -/
noncomputable def label (data : CofactorData F X) : Transition data.b X → FreeAlgebra F X
  | .copy x => FreeAlgebra.ι F x
  | .enter => 1
  | .advance _ => 1
  | .reset i => algebraMap F (FreeAlgebra F X) (data.resetCoeff i)

/-- An accepting run on the word `w`: a path of transitions starting at the initial state
`∗`, consecutive transitions sharing their intermediate state, ending at the accepting state
`b`, whose consumed letters concatenate to the whole input `w`. (The empty path stays at `∗`,
which is not accepting.) -/
def IsAcceptingRun (data : CofactorData F X) (w : FreeMonoid X)
    (ρ : List (Transition data.b X)) : Prop :=
  (∀ t ∈ ρ.head?, t.src = none) ∧
    ρ.IsChain (fun t t' => t.tgt = t'.src) ∧
    ρ.getLast?.map Transition.tgt = some (some (Fin.last data.b)) ∧
    ρ.flatMap data.consumed = w.toList

/-- The ordered product of the replacement labels along a run. -/
noncomputable def runProduct (data : CofactorData F X) (ρ : List (Transition data.b X)) :
    FreeAlgebra F X :=
  (ρ.map data.label).prod

/-- `T(w) = c⁻¹ · Σ_{accepting runs ρ on w} (ordered product of the labels of ρ)` (§3.1, p.7).
The set of accepting runs on `w` is finite (every run uses the ε-transition at most once and
every other transition consumes a letter), so the `finsum` is a finite sum. -/
noncomputable def mapWord (data : CofactorData F X) (w : FreeMonoid X) : FreeAlgebra F X :=
  algebraMap F (FreeAlgebra F X) data.c⁻¹ *
    ∑ᶠ ρ : {ρ : List (Transition data.b X) // data.IsAcceptingRun w ρ}, data.runProduct ρ.1

/-- The cofactor-removal map `T(P) = Σ_{w ∈ X*} [w]P · T(w)` (eq. (3), p.7), an `F`-linear map
on `F⟨X⟩`. -/
noncomputable def cofactorMap (data : CofactorData F X) (P : FreeAlgebra F X) :
    FreeAlgebra F X :=
  (coeffs P).sum (fun w a => a • data.mapWord w)

end CofactorData

end NCFactorClosure607.Circuits


