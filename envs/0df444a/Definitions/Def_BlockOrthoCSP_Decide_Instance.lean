-- Prove2me | Definitions.Def_BlockOrthoCSP_Decide_Instance
-- name    : BlockOrthoCSP_Decide_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:11:48.100565+00:00
-- url     : https://prove2.me/theorems/2603f5e7-663d-41bf-8bf3-12e0b00c7b62
-- title:
--   Complex-weighted #CSP instances, the instance function $F_I$, $F_I^{[t]}$ and the generated family $W_{\mathcal F}$
-- statement:
--   Fix $q \ge 1$ and the domain $D = \{0,\dots,q-1\}$ (in Lean `Fin q`). A **constraint function** is a pair $(r, f)$ with $f : D^r \to \mathbb C$ (`CFn q`); two are equal when they have the same arity and the same values. A **constraint language** is a finite set $\mathcal F$ of constraint functions, every arity $r_f \ge 1$ and every value an algebraic number (`IsAlgLanguage`).
--
--   An **instance** with $t$ retained variables has variables $x_1,\dots,x_{t+h}$ ($h \ge 0$ hidden ones) and a finite multiset (a list) of constraints $(f; i_1,\dots,i_{r_f})$ whose ordered scope may repeat variables. Its **instance function** is
--   $$F_I(a_1,\dots,a_{t+h}) = \prod_{(f;i_1,\dots,i_{r_f}) \in C_I} f(a_{i_1},\dots,a_{i_{r_f}})$$
--   (empty product $1$), and summing out the hidden variables gives
--   $$F_I^{[t]}(a_1,\dots,a_t) = \sum_{(a_{t+1},\dots,a_{t+h}) \in D^h} F_I(a_1,\dots,a_{t+h}).$$
--   The **generated family** $W_{\mathcal F}$ is the set of all $F_I^{[t]}$, $t \ge 1$, over instances using only functions of $\mathcal F$. With the first $t$ variables as labels, $F_I^{[t]}$ is also the pinned partition vector $z_I$ of a $t$-labelled instance (Eq. (F.27)).
--
--   **Formalization Note.** $n = t + h \ge 1$ and $1 \le t \le n$ become $t \ge 1$, $h \ge 0$; the retained variables are the first $t$ (the paper's variable ordering is arbitrary).
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), pp. F-6–F-7, §F.2.2, Eqs. (F.4)–(F.5); p. F-18, Eq. (F.27)

import Mathlib

set_option autoImplicit false

namespace BlockOrthoCSP.Decide

/-- A complex-valued constraint function on the domain `D = Fin q` (the paper's
`D = {0, …, q − 1}`): its arity `r` together with its table `D^r → ℂ`.
Liu–Meng, p. F-6, §F.2.2. Two constraint functions are equal exactly when they have the same
arity and the same values. -/
abbrev CFn (q : ℕ) : Type := Σ r : ℕ, (Fin r → Fin q) → ℂ

/-- The standing assumptions on a constraint language (p. F-6): a finite set `F` of functions
`f : D^{r_f} → ℂ` with `r_f ≥ 1`, every value an algebraic complex number (the paper's field
"C" is the field of algebraic complex numbers). Finiteness is the `Finset`. -/
def IsAlgLanguage {q : ℕ} (F : Finset (CFn q)) : Prop :=
  (∀ f ∈ F, 1 ≤ f.1) ∧ ∀ f ∈ F, ∀ a : Fin f.1 → Fin q, IsAlgebraic ℚ (f.2 a)

/-- A constraint `(f; i_1, …, i_{r_f})` on the variable set `Fin n`: a constraint function and an
ordered scope, whose indices need not be distinct. -/
abbrev Constraint (q n : ℕ) : Type := Σ f : CFn q, (Fin f.1 → Fin n)

/-- A finite #CSP instance with `t` retained variables (the first `t` variables, `Fin t` inside
`Fin (t + h)`) and `h ≥ 0` further variables that are summed out. The constraints form a list
(a multiset: the order is irrelevant to the product (F.4), multiplicities are retained).
Variables may be isolated and the list may be empty. -/
structure Inst (q t : ℕ) where
  /-- number of summed-out (hidden) variables -/
  h : ℕ
  /-- the constraints, with multiplicity -/
  cons : List (Constraint q (t + h))

/-- The instance uses only constraint functions from `F` (an instance of #CSP(F)). -/
def Inst.Over {q t : ℕ} (I : Inst q t) (F : Finset (CFn q)) : Prop :=
  ∀ c ∈ I.cons, c.1 ∈ F

/-- The instance function `F_I(a_1, …, a_n) = ∏_{(f; i_1..i_r) ∈ C_I} f(a_{i_1}, …, a_{i_r})`,
Eq. (F.4), p. F-6; the empty product is `1`. -/
def Inst.fn {q t : ℕ} (I : Inst q t) (a : Fin (t + I.h) → Fin q) : ℂ :=
  (I.cons.map fun c => c.1.2 (a ∘ c.2)).prod

/-- `F_I^{[t]}(a_1, …, a_t) = ∑_{(a_{t+1}, …, a_n) ∈ D^{n−t}} F_I(a_1, …, a_n)`, Eq. (F.5),
p. F-7: the first `t` variables are retained and the last `h = n − t` are summed out.
For a `t`-labelled instance this is also the pinned partition vector `z_I` of (F.27). -/
def Inst.genFn {q t : ℕ} (I : Inst q t) (x : Fin t → Fin q) : ℂ :=
  ∑ y : Fin I.h → Fin q, I.fn (Fin.append x y)

/-- The generated family `W_F = {F_I^{[t]} : I a finite #CSP(F) instance, 1 ≤ t ≤ n(I)}`,
p. F-7 (also (F.1), p. F-1). An instance with `t ≥ 1` retained and `h ≥ 0` hidden variables has
`n = t + h ≥ 1` variables, so `1 ≤ t ≤ n` is exactly `1 ≤ t`. -/
def W {q : ℕ} (F : Finset (CFn q)) : Set (CFn q) :=
  {G | ∃ t : ℕ, 1 ≤ t ∧ ∃ I : Inst q t, I.Over F ∧ G = ⟨t, I.genFn⟩}

end BlockOrthoCSP.Decide


