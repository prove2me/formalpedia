-- Prove2me | Definitions.Def_SmolenskyAC_Easy
-- name    : SmolenskyAC_Easy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:32.384219+00:00
-- url     : https://prove2.me/theorems/02ed8662-485f-4823-b0c9-ba5d2c5e97cd
-- title:
--   $F$-easy and nearly $F$-easy operations
-- statement:
--   Let $F$ be a field and $\lambda\ge 0$ an integer.
--
--   1. An operation $f$ is **$F$-easy with constant $\lambda$** if for every arity $m$ there is a polynomial $P$ in $m$ variables of total degree at most $\lambda$ with $P(z_1,\dots,z_m)=f(z_1,\dots,z_m)$ for all $z\in\{0,1\}^m$ (read in $F$).
--   2. An operation $f$ is **nearly $F$-easy with constant $\lambda$** if for every $n$, every $m$ Boolean functions $g_1,\dots,g_m$ on $D^n$ and every $l\ge 0$ there are a set $E\subseteq D^n$ with
--   $$|E|\cdot 2^{l}\le 2^{n}$$
--   and a polynomial $P$ in $m$ variables of total degree at most $\lambda l$ such that $P(g_1(x),\dots,g_m(x))=f(g_1(x),\dots,g_m(x))$ for every $x\notin E$.
--
--   The second notion says that $f(g_1,\dots,g_m)$ is a polynomial of degree $\lambda l$ in the $g$'s in an algebra $A\in\Omega^n_F$ of dimension at least $2^n-2^{n-l}$.
--
--   **Formalization Note** "Dimension at least $2^n-2^{n-l}$" is written $|E|\cdot 2^l\le 2^n$, which stays correct for $l>n$. The constant $\lambda$ does not depend on $n$, $m$, the $g_i$ or $l$.
-- source:
--   Smolensky, Algebraic methods in the theory of lower bounds for Boolean circuit complexity, Proc. 19th ACM STOC (1987), pp. 77–82, doi:10.1145/28395.28404, F-easy and Nearly F-easy Operations, Definitions, p.79 (pdf 3)

import Mathlib
import Definitions.Def_SmolenskyAC_CubeAlgebra

namespace SmolenskyAC

/-- An operation is **F-easy with constant `λ`** (Smolensky, STOC 1987, Definition, p.79): at every
arity `m`, its value on inputs `g_1, …, g_m` is a fixed polynomial in the `g_i` of total degree at
most `λ`.

**Formalization Note.** The page writes the identity in `U^n_F` for Boolean functions
`g_1, …, g_m`; pointwise this is the identity at every Boolean point `z ∈ {0,1}^m`, which is what
is stated. `λ` is independent of `m` (and of `n`). -/
def IsFEasy (F : Type*) [Field F] (lam : ℕ) (op : Operation) : Prop :=
  ∀ m : ℕ, ∃ P : MvPolynomial (Fin m) F, P.totalDegree ≤ lam ∧
    ∀ z : Fin m → Bool, MvPolynomial.eval (fun i => toF (z i)) P = toF (op m z)

/-- An operation is **nearly F-easy with constant `λ`** (Smolensky, STOC 1987, Definition, p.79):
for every `n`, every `m` Boolean functions `g_1, …, g_m` on `D^n` and every `l`, there is an
algebra `A ∈ Ω^n_F` of dimension at least `2^n − 2^{n−l}` in which `op(g_1, …, g_m)` is a
polynomial in the `g`'s of degree at most `λ l`.

**Formalization Note.** The algebra is encoded by its erased set `E` (see `degOff`); "dimension at
least `2^n − 2^{n−l}`" is `|E| · 2^l ≤ 2^n`, which avoids truncated subtraction when `l > n`. The
polynomial `P` has `m` variables and is evaluated at `(g_1(x), …, g_m(x))`. -/
def IsNearlyFEasy (F : Type*) [Field F] (lam : ℕ) (op : Operation) : Prop :=
  ∀ (n m : ℕ) (g : Fin m → Cube n → Bool) (l : ℕ),
    ∃ (E : Finset (Cube n)) (P : MvPolynomial (Fin m) F),
      E.card * 2 ^ l ≤ 2 ^ n ∧ P.totalDegree ≤ lam * l ∧
      ∀ x, x ∉ E → MvPolynomial.eval (fun i => toF (g i x)) P = toF (op m (fun i => g i x))

end SmolenskyAC


