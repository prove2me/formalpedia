-- Prove2me | Definitions.Def_ScatPoly_Construction_Model
-- name    : ScatPoly_Construction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:04.911043+00:00
-- url     : https://prove2.me/theorems/441bbf36-3d26-4dff-880f-873944092e4b
-- title:
--   §§1, 3, pp. 2, 6–8 — q-polynomials, scattered polynomials, U_f, ψ_{h,t} and the maps L, M, R, T
-- statement:
--   This file fixes the objects of Longobardi, Marino, Trombetti and Zhou's construction of scattered polynomials. Throughout, $F$ is a field, to be read as the finite field $\mathbb F_{q^n}$, and $q$ a natural number (in the theorems, a power of the characteristic).
--
--   1. **$q$-polynomials** (p. 2). For coefficients $c_0, c_1, \dots$ in $F$, the $q$-polynomial
--   $$f(x) = \sum_{i=0}^{n-1} c_i\, x^{q^i}$$
--   is regarded as a map $F \to F$. These are the elements of $\mathcal L_{n,q}[x]$, also called *linearized polynomials*.
--
--   2. **Scattered polynomials** (p. 2). Given a subfield $\mathbb F_q \subseteq F$, a map $f : F \to F$ is *scattered* if for all $z, y \in F^*$
--   $$\frac{f(z)}{z} = \frac{f(y)}{y} \quad\Longrightarrow\quad z = c\,y \text{ for some } c \in \mathbb F_q,$$
--   that is, $z$ and $y$ are $\mathbb F_q$-linearly dependent (for nonzero $z, y$ this is the same thing).
--
--   3. **The graph** (p. 2). $U_f = \{(x, f(x)) : x \in F\} \subseteq F^2$, the $\mathbb F_q$-subspace defining the linear set $L_f$ of $\mathrm{PG}(1, q^n)$.
--
--   4. **The polynomial $\psi_{h,t}$** (display (2), p. 6). For $h \in F$,
--   $$\psi_{h,t}(x) = x^q + x^{q^{t-1}} - h^{1-q^{t+1}} x^{q^{t+1}} + h^{1-q^{2t-1}} x^{q^{2t-1}}.$$
--   For $t \ge 3$ (the range of Theorem 3.1) it is the $q$-polynomial $\sum_{i=0}^{2t-1} c_i x^{q^i}$ with $c_1 = c_{t-1} = 1$, $c_{t+1} = -h^{1-q^{t+1}}$, $c_{2t-1} = h^{1-q^{2t-1}}$ and all other $c_i = 0$; for $t = 2$ the indices coincide in pairs ($1 = t-1$, $t+1 = 2t-1$) and the coefficients add.
--
--   5. **Its two halves** (display (3), p. 7). $\psi_{h,t} = L + M$ with
--   $$L(x) = x^q - h^{1-q^{t+1}} x^{q^{t+1}}, \qquad M(x) = x^{q^{t-1}} + h^{1-q^{2t-1}} x^{q^{2t-1}}.$$
--
--   6. **The maps $R$ and $T$** (display (8), p. 8).
--   $$R(x) = x^{q^t} + h^{q^{t-1}-q} x, \qquad T(x) = x^{q^t} + h^{q-q^{t-1}} x.$$
--
--   These are the objects every statement of the mission refers to: Theorem 3.1 asserts that $\psi_{h,t}$ is scattered, and the lemmas of §3 describe the kernels and images of $L$, $M$, $R$, $T$.
--
--   **Formalization Note.** A negative power of $h$ is written as a field quotient, e.g. $h^{1-q^{t+1}}$ as `h / h ^ q ^ (t+1)` and $h^{q-q^{t-1}}$ as `h ^ q / h ^ q ^ (t-1)`; this is exact whenever $h \neq 0$, which the hypothesis $h^{q^t+1} = -1$ of every theorem guarantees. The exponents $t-1$ and $2t-1$ are natural-number subtractions, exact in the range $t \ge 1$ used by every theorem. $x^{q^i}$ is written `x ^ q ^ i`, which Lean parses as $x^{(q^i)}$. The plane $F^2$ is `Fin 2 → F`. The subfields $\mathbb F_q$, $\mathbb F_{q^t}$ are taken from the published definition `ScatCaps.LinearSets.subfieldOf` (fixed field of $x \mapsto x^{q^m}$) in the theorems.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 2 (q-polynomials, U_f, scattered polynomial), p. 6 display (2), p. 7 display (3), p. 8 display (8)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatPoly.Construction

/-- A `q`-polynomial `∑_{i=0}^{n-1} c_i x^{q^i}` over `F` (p. 2, the set `𝓛_{n,q}[x]`),
viewed as a map `F → F`. -/
def qpoly {F : Type*} [Field F] (q n : ℕ) (c : ℕ → F) (x : F) : F :=
  ∑ i ∈ Finset.range n, c i * x ^ q ^ i

/-- Scattered polynomial (p. 2): for all nonzero `z, y`, `f(z)/z = f(y)/y` forces `z` and `y`
to be `Fq`-linearly dependent, i.e. `z = c * y` for some `c ∈ Fq`. -/
def IsScatteredPoly {F : Type*} [Field F] (Fq : Subfield F) (f : F → F) : Prop :=
  ∀ z y : F, z ≠ 0 → y ≠ 0 → f z / z = f y / y → ∃ c ∈ Fq, z = c * y

/-- The graph `U_f = {(x, f(x)) : x ∈ F}` of `f`, a subset of `F²` (p. 2). -/
def graph {F : Type*} [Field F] (f : F → F) : Set (Fin 2 → F) :=
  {v | ∃ x : F, v = ![x, f x]}

/-- `ψ_{h,t}(x) = x^q + x^{q^{t-1}} - h^{1-q^{t+1}} x^{q^{t+1}} + h^{1-q^{2t-1}} x^{q^{2t-1}}`
(display (2), p. 6). The negative powers of `h` are written as field quotients. -/
def psi {F : Type*} [Field F] (q t : ℕ) (h x : F) : F :=
  x ^ q + x ^ q ^ (t - 1) - h / h ^ q ^ (t + 1) * x ^ q ^ (t + 1)
    + h / h ^ q ^ (2 * t - 1) * x ^ q ^ (2 * t - 1)

/-- `L(x) = x^q - h^{1-q^{t+1}} x^{q^{t+1}}` (display (3), p. 7). -/
def Lmap {F : Type*} [Field F] (q t : ℕ) (h x : F) : F :=
  x ^ q - h / h ^ q ^ (t + 1) * x ^ q ^ (t + 1)

/-- `M(x) = x^{q^{t-1}} + h^{1-q^{2t-1}} x^{q^{2t-1}}` (display (3), p. 7). -/
def Mmap {F : Type*} [Field F] (q t : ℕ) (h x : F) : F :=
  x ^ q ^ (t - 1) + h / h ^ q ^ (2 * t - 1) * x ^ q ^ (2 * t - 1)

/-- `R(x) = x^{q^t} + h^{q^{t-1}-q} x` (display (8), p. 8). -/
def Rmap {F : Type*} [Field F] (q t : ℕ) (h x : F) : F :=
  x ^ q ^ t + h ^ q ^ (t - 1) / h ^ q * x

/-- `T(x) = x^{q^t} + h^{q-q^{t-1}} x` (display (8), p. 8). -/
def Tmap {F : Type*} [Field F] (q t : ℕ) (h x : F) : F :=
  x ^ q ^ t + h ^ q / h ^ q ^ (t - 1) * x

end ScatPoly.Construction


