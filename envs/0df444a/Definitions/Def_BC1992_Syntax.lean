-- Prove2me | Definitions.Def_BC1992_Syntax
-- name    : BC1992_Syntax
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T19:44:41.88697+00:00
-- url     : https://prove2.me/theorems/cbef260f-b16d-49f7-b2df-d37dcf6ed213
-- title:
--   Section 2: Syntactic Polynomials, Two-Sorted Safe Recursion Syntax (Fn n m), Semantics, and Size Polynomials
-- statement:
--   Formalizes the syntactic univariate polynomial semiring `Poly` (`const`, `var`, `add`, `mul`, `comp`) with evaluation `Poly.eval` and formal degree `Poly.degree`, together with Section 2 (Definition 2.1) of Bellantoni and Cook (1992) over binary words `Word := List Bool`: the two-sorted inductive family `Fn n m` of Bellantoni-Cook programs with `n` normal and `m` safe arguments (`zero`, `projN`, `projS`, `s0`, `s1`, `pred`, `cond`, safe composition `comp`, and predicative recursion on notation `srec`), denotational semantics `Fn.eval`, syntactic polynomial output-length bounds `Fn.sizePoly` and `Fn.fullSizePoly`, and the definability predicate `BCDefinable`.
-- source:
--   Stephen Bellantoni and Stephen Cook, 'A new recursion-theoretic characterization of the polytime functions', Computational Complexity 2 (1992), pp. 97-110 (doi:10.1007/BF01201998). Section 2, Definition 2.1 & Lemma 2.1, pp. 99-101.

/-
  Source: Stephen Bellantoni and Stephen Cook,
  "A new recursion-theoretic characterization of the polytime functions",
  Computational Complexity 2 (1992), 97–110, DOI: 10.1007/BF01201998.

  Part I (`BC1992_Syntax`):
  Syntactic univariate polynomials (`Poly`), the two-sorted Bellantoni–Cook safe recursion
  function algebra (`Fn n m` with `n` normal and `m` safe arguments), denotational semantics
  (`Fn.eval`), and syntactic polynomial output-size certificates (`Fn.sizePoly`, `Fn.fullSizePoly`).
-/
import Init

namespace BC1992

/-- Binary words `{0,1}*`, represented as `List Bool`. In Bellantoni–Cook notation the head of
    the list is the least significant (last-appended) bit, so `s₀(;a) = false :: a`,
    `s₁(;a) = true :: a`, and the predecessor `p(;a)` is `a.tail`. -/
abbrev Word := List Bool

/-- Syntax of univariate polynomials with natural-number coefficients (`ℕ[X]`),
    equipped with explicit formal composition (`comp`). -/
inductive Poly : Type where
  | const (c : Nat)
  | var
  | add (p q : Poly)
  | mul (p q : Poly)
  | comp (p q : Poly)
  deriving DecidableEq, Repr

namespace Poly

/-- Evaluate a polynomial `p : Poly` at `n : Nat`. -/
def eval : Poly → Nat → Nat
  | .const c, _ => c
  | .var, n => n
  | .add p q, n => p.eval n + q.eval n
  | .mul p q, n => p.eval n * q.eval n
  | .comp p q, n => p.eval (q.eval n)

/-- Pointwise dominance of polynomials on all natural numbers. -/
def le (p q : Poly) : Prop :=
  ∀ n : Nat, p.eval n ≤ q.eval n

/-- Formal degree upper bound of a polynomial. -/
def degree : Poly → Nat
  | .const _ => 0
  | .var => 1
  | .add p q => max p.degree q.degree
  | .mul p q => p.degree + q.degree
  | .comp p q => p.degree * q.degree

/-- Linear polynomial `a * X + b`. -/
def linear (a b : Nat) : Poly :=
  .add (.mul (.const a) .var) (.const b)

/-- Sum of a finite family of polynomials. -/
def sumFin : {k : Nat} → (Fin k → Poly) → Poly
  | 0, _ => .const 0
  | _ + 1, ps => .add (ps ⟨0, Nat.zero_lt_succ _⟩) (sumFin fun i => ps i.succ)

end Poly

/-- Bellantoni–Cook programs with `n` normal and `m` safe arguments (§2, Definition 2.1).
    No constructor takes an arbitrary semantic function on words: `comp` takes finite tuples
    of syntactic subprograms `Fin k → Fn n 0` and `Fin l → Fn n m`. -/
inductive Fn : Nat → Nat → Type where
  /-- Constant `0` (empty word `ε`), arity `(0; 0)`. -/
  | zero : Fn 0 0
  /-- Projection onto the `i`-th normal argument, arity `(n; m)`. -/
  | projN {n m : Nat} (i : Fin n) : Fn n m
  /-- Projection onto the `j`-th safe argument, arity `(n; m)`. -/
  | projS {n m : Nat} (j : Fin m) : Fn n m
  /-- Binary zero-successor `s₀(;a) = false :: a`, arity `(0; 1)`. -/
  | s0 : Fn 0 1
  /-- Binary one-successor `s₁(;a) = true :: a`, arity `(0; 1)`. -/
  | s1 : Fn 0 1
  /-- Predecessor `p(;a) = a.tail`, arity `(0; 1)`. -/
  | pred : Fn 0 1
  /-- Three-way word conditional `C(;a, b, c, d)`, arity `(0; 4)`. -/
  | cond : Fn 0 4
  /-- Safe composition `f(x̄; ȳ) = h(r̄(x̄;); t̄(x̄; ȳ))`, where normal-position subprograms `rs i`
      cannot depend on safe inputs (`Fn n 0`). -/
  | comp {n m k l : Nat} (h : Fn k l) (rs : Fin k → Fn n 0) (ts : Fin l → Fn n m) : Fn n m
  /-- Predicative (safe) recursion on notation on the first normal argument:
      `f(ε, x̄; ȳ) = g(x̄; ȳ)`,
      `f(s_b(w), x̄; ȳ) = h_b(w, x̄; f(w, x̄; ȳ), ȳ)`,
      where the recursive call result is placed in the first *safe* position of `h₀, h₁`. -/
  | srec {n m : Nat} (g : Fn n m) (h0 h1 : Fn (n + 1) (m + 1)) : Fn (n + 1) m

/-- Iteration underlying recursion on notation:
    `recIter g h [] = g`, `recIter g h (b :: w) = h b w (recIter g h w)`. -/
def recIter (g : Word) (h : Bool → Word → Word → Word) : Word → Word
  | [] => g
  | b :: w => h b w (recIter g h w)

/-- Three-way conditional on words: `b` on `[]`, `c` on `false :: _`, `d` on `true :: _`. -/
def condW (a b c d : Word) : Word :=
  match a with
  | [] => b
  | false :: _ => c
  | true :: _ => d

namespace Fn

/-- Maximum bit-length among a list of words: $\max_{y \in ys} |y|$. -/
def maxLen : List Word → Nat
  | [] => 0
  | y :: ys => max y.length (maxLen ys)

/-- Denotational semantics: `f.eval xs ys = f(xs; ys)`. -/
def eval : {n m : Nat} → Fn n m → List Word → List Word → Word
  | _, _, .zero, _, _ => []
  | _, _, .projN i, xs, _ => xs.getD i.val []
  | _, _, .projS j, _, ys => ys.getD j.val []
  | _, _, .s0, _, ys => false :: ys.getD 0 []
  | _, _, .s1, _, ys => true :: ys.getD 0 []
  | _, _, .pred, _, ys => (ys.getD 0 []).tail
  | _, _, .cond, _, ys => condW (ys.getD 0 []) (ys.getD 1 []) (ys.getD 2 []) (ys.getD 3 [])
  | _, _, .comp h rs ts, xs, ys =>
      h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)
  | _, _, .srec g h0 h1, xs, ys =>
      recIter (g.eval xs.tail ys)
        (fun b w r => if b then h1.eval (w :: xs.tail) (r :: ys) else h0.eval (w :: xs.tail) (r :: ys))
        (xs.headD [])

/-- Syntactic polynomial `q_f : Poly` bounding the contribution of the normal inputs to the
    output length of `f : Fn n m` (Lemma 2.1):
    $$|f(\vec{x}; \vec{y})| \le q_f(\max_i |x_i|) + \max_j |y_j|.$$
    Computed purely by structural recursion on `f`. -/
def sizePoly : {n m : Nat} → Fn n m → Poly
  | _, _, .zero => .const 0
  | _, _, .projN _ => .var
  | _, _, .projS _ => .const 0
  | _, _, .s0 => .const 1
  | _, _, .s1 => .const 1
  | _, _, .pred => .const 0
  | _, _, .cond => .const 0
  | _, _, .comp h rs ts =>
      .add (h.sizePoly.comp (Poly.sumFin fun i => (rs i).sizePoly))
           (Poly.sumFin fun j => (ts j).sizePoly)
  | _, _, .srec g h0 h1 =>
      .add (.mul .var (.add h0.sizePoly h1.sizePoly)) g.sizePoly

/-- Combined size polynomial when all normal and safe arguments have length at most `K`. -/
def fullSizePoly {n m : Nat} (f : Fn n m) : Poly :=
  .add f.sizePoly .var

end Fn

/-- A unary word function `f : Word → Word` is **BC-definable** if it is the denotation of a
    closed Bellantoni–Cook program `prog : Fn 1 0` with one normal and zero safe arguments. -/
def BCDefinable (f : Word → Word) : Prop :=
  ∃ prog : Fn 1 0, ∀ x : Word, prog.eval [x] [] = f x

end BC1992


