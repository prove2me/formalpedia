-- Prove2me | Definitions.Def_MultiphaseDisj_Supplement_RegexFamily
-- name    : MultiphaseDisj_Supplement_RegexFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:34:34.976204+00:00
-- url     : https://prove2.me/theorems/79ccbe59-c6c1-4a75-a34f-f24b8930ecb0
-- title:
--   The expression family $R_{\vec S}$ of Appendix A.7 and its maximal length $M_n$
-- statement:
--   Fix $n, m \ge 0$ and sets $S_1,\dots,S_m \subseteq [n]$. The **alphabet** consists of the symbol $\#$, the **data symbols** $a_1,\dots,a_n$ and the **selectors** $c_1,\dots,c_m$; for $m=n$ it has $2n+1$ symbols.
--
--   For each $i\in[m]$ with $S_i\neq[n]$ let
--   $$
--   \Gamma_i := \bigcup_{j\in[n]\setminus S_i} a_j
--   $$
--   be the alternation of the data symbols of the elements outside $S_i$, and let the $i$-th **branch** be $\#\,\Gamma_i^*\,c_i$; if $S_i=[n]$ the $i$-th branch is $\#\,c_i$. The expression $R_{\vec S}$ is the union of the $m$ branches, an ordinary regular expression using only union, concatenation and Kleene star. Its language consists exactly of the words $\#\,a_{j_1}\cdots a_{j_k}\,c_q$ with $S_q\cap\{j_1,\dots,j_k\}=\emptyset$.
--
--   The **length** $|R|$ of a regular expression is the number of nodes of its syntax tree, and
--   $$
--   M_n := \max_{S_1,\dots,S_n\subseteq[n]} |R_{\vec S}|
--   $$
--   is the maximal length over the family $\mathcal R_n=\{R_{\vec S}: S_1,\dots,S_n\subseteq[n]\}$ (the case $m=n$).
--
--   This is the expression family through which Disjointness is encoded into streaming regular-expression membership.
--
--   **Formalization Note** Expressions are Mathlib `RegularExpression` terms with language `matches'`. Indices are 0-based (`data j` is $a_{j+1}$, `sel i` is $c_{i+1}$). Alternations are right-nested in increasing order of the index, so $\vec S\mapsto R_{\vec S}$ is a function; this does not change the language. The paper fixes no length convention: every standard one is within a constant factor of the node count, which affects only the constants of $\Theta$ and $\Omega$.
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), §A.7 "The expression family", p.47; Theorem A.6 (R_n, M_n), p.48

import Mathlib

set_option autoImplicit false

namespace MultiphaseDisj.Supplement

/-- The alphabet of the expression family of Appendix A.7 (Ko, *Unconditional Boolean Dynamic
Lower Bounds from Disjointness*, arXiv:2610.10904, held version sha256 ba26649b…, §A.7, p.47):
the symbol `#`, the data symbols `a_1, …, a_n` and the selectors `c_1, …, c_m`.

**Formalization Note** `data j` is `a_{j+1}` and `sel i` is `c_{i+1}`: indices are 0-based
(`Fin n`, `Fin m`). For `m = n` the alphabet has `2n + 1` symbols. -/
inductive Sym (n m : ℕ) : Type where
  | hash : Sym n m
  | data : Fin n → Sym n m
  | sel : Fin m → Sym n m
  deriving DecidableEq

/-- The alternation (union) of a nonempty list of regular expressions, right-nested:
`altList [r₁, r₂, …, r_k] = r₁ ∪ (r₂ ∪ (⋯ ∪ r_k))`. The empty list gives `∅` (the expression
`zero`); it is never used for `Γ_i` (see `branch`).

**Formalization Note** The nesting and the order of the alternatives are fixed so that the
expression of the family is a function of the sets; neither changes the language. -/
def altList {α : Type} : List (RegularExpression α) → RegularExpression α
  | [] => 0
  | [r] => r
  | r :: s :: rs => r + altList (s :: rs)

/-- `Γ_i := ⋃_{j ∈ [n] ∖ S_i} a_j`, the alternation of the data symbols of the elements outside
`S_i`, in increasing order of `j` (arXiv:2610.10904, §A.7, p.47). -/
def gamma {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) : RegularExpression (Sym n m) :=
  altList (((List.finRange n).filter (fun j => j ∉ S i)).map
    (fun j => RegularExpression.char (Sym.data j)))

/-- The `i`-th branch of `R_S` (arXiv:2610.10904, §A.7, p.47): `# Γ_i* c_i` if `S_i ≠ [n]`,
and `# c_i` if `S_i = [n]`. -/
def branch {n m : ℕ} (S : Fin m → Finset (Fin n)) (i : Fin m) : RegularExpression (Sym n m) :=
  if S i = Finset.univ then
    RegularExpression.char Sym.hash * RegularExpression.char (Sym.sel i)
  else
    RegularExpression.char Sym.hash * (gamma S i).star * RegularExpression.char (Sym.sel i)

/-- The expression `R_S` of Appendix A.7 (arXiv:2610.10904, §A.7, p.47): the union of the `m`
branches, an ordinary regular expression that uses only union, concatenation and Kleene star.

**Formalization Note** A Mathlib `RegularExpression`; its language is `(RS S).matches'`. The
branches are taken in increasing order of `i` and nested by `altList`. -/
def RS {n m : ℕ} (S : Fin m → Finset (Fin n)) : RegularExpression (Sym n m) :=
  altList ((List.finRange m).map (branch S))

/-- The length `|R|` of a regular expression: the number of nodes of its syntax tree (every
symbol, `∅`, `ε`, union, concatenation and star counts one).

**Formalization Note** The paper (§A.7, pp.47–48) fixes no length convention; every standard one
(characters of the written expression, with or without parentheses) is within a constant factor
of the node count, which changes only the constants of the `Θ` and `Ω` bounds. -/
def size {α : Type} : RegularExpression α → ℕ
  | RegularExpression.zero => 1
  | RegularExpression.epsilon => 1
  | RegularExpression.char _ => 1
  | RegularExpression.plus r s => size r + size s + 1
  | RegularExpression.comp r s => size r + size s + 1
  | RegularExpression.star r => size r + 1

/-- `M_n := max_{R ∈ R_n} |R|`, where `R_n := {R_S : S_1, …, S_n ⊆ [n]}` is the family with
`m = n` (arXiv:2610.10904, Theorem A.6, p.48). The maximum is over the finitely many
`S : Fin n → Finset (Fin n)`. -/
def Mn (n : ℕ) : ℕ :=
  Finset.univ.sup (fun S : Fin n → Finset (Fin n) => size (RS S))

end MultiphaseDisj.Supplement


