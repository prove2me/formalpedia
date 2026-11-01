-- Prove2me | Definitions.Def_XOSMax_OracleProg
-- name    : XOSMax_OracleProg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:43.585991+00:00
-- url     : https://prove2.me/theorems/4d608953-70fa-4c92-a62d-d48e2bbbc248
-- title:
--   Value-oracle programs and their cost
-- statement:
--   A **value-oracle program** over a ground type $E$ with results in $\alpha$ is a finite-depth tree built from three constructors:
--
--   1. return a value of $\alpha$;
--   2. query a set $X$, and continue with a function of the real answer;
--   3. perform one elementary step, and continue.
--
--   No constructor mentions a set function. Executing a program $p$ against $f$ answers each query $X$ with $f(X)$, and yields the result together with the **cost**
--   $$
--   \mathrm{cost}=\#\{\text{oracle calls}\}+\#\{\text{elementary steps}\}.
--   $$
--   Each oracle call costs $1$ whatever the size of the queried set, as in the value oracle model, in which "we can access a set function only by querying the oracle for the function value of each set".
--
--   This type is what makes the mission's statements about an algorithm given by a value oracle: a program cannot read $f$, and its running time is computed by execution and not written down separately.
--
--   **Formalization Note** The module also defines sequential composition, the `Monad` instance, `ask`, `tick`, `ticks n`, and the structural lemma `run_bind`. What happens between two constructors is free, so a cost bound is a statement about a concrete program. The charges of the programs of this mission are stated in their docstrings.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, §1, pp.1–2 (value oracle model; "the running time of each presented algorithm is shown by the number of value oracle calls")

import Mathlib

namespace XOSMax

/-- **Value-oracle programs** over the ground type `E` with result type `α`: the model in which "we
can access a set function only by querying the oracle for the function value of each set"
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, §1, p.1).

* `ret a` ends the computation with result `a`;
* `query X k` asks the oracle for the value on the set `X`, and continues with `k` on the answer;
* `step p` performs one elementary step, then continues with `p`.

**Formalization Note** No constructor mentions the set function: a program sees `f` only through the
real numbers its queries return. This is what makes the algorithms of the mission value-oracle
algorithms, and what makes their cost meaningful. Everything between two constructors is free, so a
cost bound is about a concrete program, and the charges are audited against the paper in the
docstrings of the algorithms. -/
inductive OracleProg (E α : Type) : Type
  | ret : α → OracleProg E α
  | query : Finset E → (ℝ → OracleProg E α) → OracleProg E α
  | step : OracleProg E α → OracleProg E α

namespace OracleProg

variable {E α β : Type}

/-- Sequential composition of programs. -/
def bind : OracleProg E α → (α → OracleProg E β) → OracleProg E β
  | ret a, g => g a
  | query X k, g => query X fun r => bind (k r) g
  | step p, g => step (bind p g)

instance : Monad (OracleProg E) where
  pure := ret
  bind := bind

/-- The program that queries the value oracle on `X` and returns the answer. -/
def ask (X : Finset E) : OracleProg E ℝ := query X ret

/-- The program that performs one elementary step. -/
def tick : OracleProg E Unit := step (ret ())

/-- The program that performs `n` elementary steps. -/
def ticks : ℕ → OracleProg E Unit
  | 0 => ret ()
  | n + 1 => step (ticks n)

/-- `run f p` executes `p` against the value oracle of `f`, and returns the result and the **cost**
of the execution: every value oracle call costs `1`, whatever the size of the queried set, every
elementary step costs `1`, and `ret` costs `0`. -/
def run (f : Finset E → ℝ) : OracleProg E α → α × ℕ
  | ret a => (a, 0)
  | query X k => ((run f (k (f X))).1, (run f (k (f X))).2 + 1)
  | step p => ((run f p).1, (run f p).2 + 1)

@[simp] theorem pure_eq_ret (a : α) : (pure a : OracleProg E α) = ret a := rfl

@[simp] theorem bind_eq_bind (p : OracleProg E α) (g : α → OracleProg E β) :
    p >>= g = bind p g := rfl

@[simp] theorem run_ret (f : Finset E → ℝ) (a : α) : run f (ret a) = (a, 0) := rfl

/-- The result and cost of a composition: the second program receives the result of the first one,
and the costs add up. -/
@[simp] theorem run_bind (f : Finset E → ℝ) (p : OracleProg E α) (g : α → OracleProg E β) :
    run f (bind p g) = ((run f (g (run f p).1)).1, (run f p).2 + (run f (g (run f p).1)).2) := by
  induction p with
  | ret a => simp [bind, run]
  | query X k ih => simp only [bind, run, ih]; ext <;> simp; omega
  | step p ih => simp only [bind, run, ih]; ext <;> simp; omega

end OracleProg

end XOSMax


