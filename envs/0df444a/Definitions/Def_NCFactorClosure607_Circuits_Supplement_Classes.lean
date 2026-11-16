-- Prove2me | Definitions.Def_NCFactorClosure607_Circuits_Supplement_Classes
-- name    : NCFactorClosure607_Circuits_Supplement_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:06:53.540196+00:00
-- url     : https://prove2.me/theorems/4404711a-68ce-4738-bdbc-7ac88a7b5253
-- title:
--   Boolean-sum representations (16) and the classes $\mathrm{VF}_{nc}$, $\mathrm{VP}_{nc}$, $\mathrm{VNP}_{nc}$, closure under factors
-- statement:
--   **Boolean sums.** Let $X$ and $Z=\{z_1,\dots,z_t\}$ be disjoint sets of free noncommuting variables. For $e\in\{0,1\}^t$, $G(X,e)$ is the image of $G\in F\langle X\cup Z\rangle$ under the algebra map fixing every $x\in X$ and sending $z_j$ to the field scalar $e_j$. The verifier $G$ represents
--   $$f(X)=\sum_{e\in\{0,1\}^t}G(X,e). \tag{16}$$
--
--   **Families.** A family over a fixed field $F$ assigns to every $n\in\mathbb N$ a number $m_n$ of variables and a polynomial $f_n\in F\langle x_1,\dots,x_{m_n}\rangle$. A function $u:\mathbb N\to\mathbb N$ is **polynomially bounded** when $u(n)\le c\,n^c+c$ for some $c$ and all $n$.
--
--   1. $(f_n)\in\mathrm{VF}_{nc}$ (polynomial-size formulas) when some formula for $f_n$ has polynomially bounded size.
--   2. $(f_n)\in\mathrm{VP}_{nc}$ when $m_n$ and $\deg f_n$ are polynomially bounded and some circuit for $f_n$ has polynomially bounded size.
--   3. $(f_n)\in\mathrm{VNP}_{nc}$ when $m_n$ and a number $t_n$ of Boolean variables are polynomially bounded, and $f_n=\sum_{e\in\{0,1\}^{t_n}}G_n(X,e)$ for verifiers $G_n$ computed by circuits of polynomially bounded size and of polynomially bounded degree (the degree of the polynomial $G_n$).
--
--   A class is **closed under taking factors** when for all families $(a_n),(g_n),(b_n)$ in the same variables with $f_n=a_ng_nb_n\neq0$ for every $n$, $(f_n)$ in the class implies $(g_n)$ in the class.
--
--   These are the objects of Theorem 1.2 and Theorem 6.1.
--
--   **Formalization Note** $X\cup Z$ is `X ⊕ Fin t`; $z_j\mapsto e_j$ sends `true` to $1$ and `false` to $0$.
--
--   The formula-family class allows any ambient variable count, generalizing the polynomial-variable family convention of §6. Formula size already bounds polynomial degree. Restricting to polynomially bounded variable counts recovers the source class.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.3, Theorem 1.2; p.14, §6 opening and §6.1; p.15, §6.2, eq. (16) and the definition of VNP_nc; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Polynomials
import Definitions.Def_NCFactorClosure607_Circuits_Supplement_Formula

/-!
# Boolean-sum representations and the classes VF_nc, VP_nc, VNP_nc

Arvind–Joglekar, *Factor Closure in Noncommutative Algebraic Complexity*,
STOC 2027 submission #607, Theorem 1.2, p.3; §6 opening and §6.1, p.14; §6.2, eq. (16), p.15.

* Boolean-sum representation (16): for disjoint sets `X` and `Z = {z_1, …, z_t}` of free
  noncommuting variables, a verifier `G ∈ F⟨X ∪ Z⟩` (Lean: `FreeAlgebra F (X ⊕ Fin t)`)
  represents `f(X) = Σ_{e ∈ {0,1}^t} G(X, e)`, where `G(X, e)` replaces every `z_j` by the field
  scalar `e_j ∈ {0, 1}` and keeps every `x ∈ X`.
* Families over a fixed field `F`: for every `n : ℕ` a number of variables `m n` and a
  polynomial `f n ∈ F⟨x_1, …, x_{m n}⟩` (Lean: `FreeAlgebra F (Fin (m n))`).
* A function `u : ℕ → ℕ` is polynomially bounded when `u n ≤ c nᶜ + c` for one `c` and all `n`.
* `VF_nc`: polynomial-size formulas, allowing any ambient variable count (a generalization
  of the polynomial-variable family convention of §6); `VP_nc`: polynomially many variables, polynomial degree and
  polynomial-size circuits; `VNP_nc`: polynomially many variables and Boolean inputs, and a
  verifier of polynomial circuit size and polynomial degree.
* Closure under factors (Theorem 1.2, p.3): for every specified `g_n` in `f_n = a_n g_n b_n ≠ 0`.
-/

namespace NCFactorClosure607.Circuits.Supplement

open NCFactorClosure607.Circuits

section BooleanSum

variable {F : Type*} [Field F] {X : Type*} {t : ℕ}

/-- `G ↦ G(X, e)`: the `F`-algebra map `F⟨X ∪ Z⟩ → F⟨X⟩` sending every `x ∈ X` to `x` and every
Boolean variable `z_j` to the field scalar `e_j` (`1` for `true`, `0` for `false`) (§6.2, p.15). -/
noncomputable def specialize (e : Fin t → Bool) :
    FreeAlgebra F (X ⊕ Fin t) →ₐ[F] FreeAlgebra F X :=
  FreeAlgebra.lift F (Sum.elim (FreeAlgebra.ι F) fun j => if e j then 1 else 0)

/-- The polynomial represented by the verifier `G` (eq. (16), p.15):
`Σ_{e ∈ {0,1}^t} G(X, e)`. -/
noncomputable def boolSum (G : FreeAlgebra F (X ⊕ Fin t)) : FreeAlgebra F X :=
  ∑ e : Fin t → Bool, specialize e G

end BooleanSum

/-- `u` is polynomially bounded: `u n ≤ c · nᶜ + c` for some `c` and every `n`. -/
def PolyBounded (u : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, u n ≤ c * n ^ c + c

variable (F : Type*) [Field F]

/-- A family `(f_n)` has **polynomial-size noncommutative formulas**: some `c` such that every
`f_n` is computed by a formula with at most `c nᶜ + c` nodes (Theorem 1.2, p.3). -/
def VFnc (m : ℕ → ℕ) (f : ∀ n, FreeAlgebra F (Fin (m n))) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, ∃ Φ : Formula F (Fin (m n)), Φ.eval = f n ∧ Φ.size ≤ c * n ^ c + c

/-- `(f_n) ∈ VP_nc` (§6, p.14): polynomially many variables, polynomial degree, and
polynomial-size noncommutative circuits. -/
def VPnc (m : ℕ → ℕ) (f : ∀ n, FreeAlgebra F (Fin (m n))) : Prop :=
  PolyBounded m ∧ PolyBounded (fun n => ncDeg (f n)) ∧
    ∃ c : ℕ, ∀ n : ℕ, ∃ C : Circuit F (Fin (m n)),
      C.WellFormed ∧ C.eval = f n ∧ C.size ≤ c * n ^ c + c

/-- `(f_n) ∈ VNP_nc` (§6.2, p.15): polynomially many variables `m n` and Boolean inputs `t n`,
and verifiers `G_n ∈ F⟨X_n ∪ Z_n⟩`, computed by circuits of polynomial size, of polynomial
degree (the degree of the polynomial `G_n`), with `f_n = Σ_{e ∈ {0,1}^{t n}} G_n(X, e)`. -/
def VNPnc (m : ℕ → ℕ) (f : ∀ n, FreeAlgebra F (Fin (m n))) : Prop :=
  PolyBounded m ∧ ∃ t : ℕ → ℕ, PolyBounded t ∧
    ∃ c : ℕ, ∀ n : ℕ, ∃ C : Circuit F (Fin (m n) ⊕ Fin (t n)),
      C.WellFormed ∧ C.size ≤ c * n ^ c + c ∧ ncDeg C.eval ≤ c * n ^ c + c ∧
        boolSum C.eval = f n

/-- A class of families is **closed under taking factors** (Theorem 1.2, p.3): for all
families `(a_n), (g_n), (b_n)` in the same variables with `f_n = a_n g_n b_n ≠ 0` for every `n`,
if `(f_n)` belongs to the class then so does `(g_n)`. -/
def ClosedUnderFactors
    (Cls : (m : ℕ → ℕ) → (∀ n, FreeAlgebra F (Fin (m n))) → Prop) : Prop :=
  ∀ (m : ℕ → ℕ) (a g b : ∀ n, FreeAlgebra F (Fin (m n))),
    (∀ n, a n * g n * b n ≠ 0) → Cls m (fun n => a n * g n * b n) → Cls m g

end NCFactorClosure607.Circuits.Supplement


