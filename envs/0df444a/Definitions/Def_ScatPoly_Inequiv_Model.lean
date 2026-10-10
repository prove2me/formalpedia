-- Prove2me | Definitions.Def_ScatPoly_Inequiv_Model
-- name    : ScatPoly_Inequiv_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:12.755718+00:00
-- url     : https://prove2.me/theorems/c05674c1-28ec-45b9-a099-538837deb3f9
-- title:
--   §§1–5, pp. 2–3, 5–6, 16, 20 — q-polynomials, scattered polynomials, ψ_{h,t}, H, U_f, L_f, and GL/ΓL/PGL/PΓL-equivalence
-- statement:
--   This file fixes the objects of Longobardi, Marino, Trombetti and Zhou's study of the equivalence classes of the linear sets $L_{h,t}$. Throughout, $F$ is a field, to be read as the finite field $\mathbb F_{q^n}$ with $n = 2t$, and $q$ a natural number (in the theorems, $q = p^r$ with $p$ the characteristic).
--
--   1. **$q$-polynomials** (p. 5, Lemma 2.2). For coefficients $\alpha_0, \alpha_1, \dots \in F$ and $n \ge 1$,
--   $$f(x) = \sum_{i=0}^{n-1} \alpha_i\, x^{q^i},$$
--   regarded as a map $F \to F$.
--
--   2. **Scattered polynomials** (p. 2). A map $f : F \to F$ is *scattered* if for all $z, y \in F^*$
--   $$\frac{f(z)}{z} = \frac{f(y)}{y} \quad\Longrightarrow\quad z = c\,y \text{ for some } c \in \mathbb F_q,$$
--   where $\mathbb F_q = \{c \in F : c^q = c\}$ is the fixed field of $x \mapsto x^q$ (for $|F| = q^n$ with $q$ a power of the characteristic, this is the unique subfield of order $q$).
--
--   3. **The polynomial $\psi_{h,t}$** (display (2), p. 6). For $h \in F$,
--   $$\psi_{h,t}(x) = x^q + x^{q^{t-1}} - h^{1-q^{t+1}} x^{q^{t+1}} + h^{1-q^{2t-1}} x^{q^{2t-1}}.$$
--
--   4. **The index set** $H = \{h \in F : h^{q^t+1} = -1\}$ (pp. 16, 20, 26). It does not exclude elements of $\mathbb F_{q^t}$.
--
--   5. **The graph** $U_f = \{(x, f(x)) : x \in F\} \subseteq F^2$ (p. 2).
--
--   6. **Points and linear sets of $\mathrm{PG}(1, q^n)$.** The point $\langle v \rangle_{\mathbb F_{q^n}}$ is the set of all $F$-multiples of $v \in F^2$, and
--   $$L_f = \{\langle (x, f(x)) \rangle_{\mathbb F_{q^n}} : x \in \mathbb F_{q^n}^*\}$$
--   is the linear set defined by $U_f$ (display (36), p. 20), a set of points.
--
--   7. **Semilinear maps.** For a field automorphism $\sigma$ of $F$ and a $2\times 2$ matrix $A$, the map $v \mapsto A\, v^\sigma$, where $\sigma$ acts on each coordinate. For invertible $A$ these maps form $\Gamma\mathrm L(2, q^n)$; for $\sigma = \mathrm{id}$, $\mathrm{GL}(2, q^n)$.
--
--   8. **Equivalences** (pp. 3, 16, 20). Two subsets $U, W \subseteq F^2$ are *$\mathrm{GL}(2,q^n)$-equivalent* if some invertible $A$ maps $U$ onto $W$, and *$\Gamma\mathrm L(2,q^n)$-equivalent* if some $v \mapsto A v^\sigma$ with $A$ invertible maps $U$ onto $W$. Two point sets $L, L'$ of $\mathrm{PG}(1,q^n)$ are *$\mathrm{PGL}(2,q^n)$-equivalent* (resp. *$\mathrm{P\Gamma L}(2,q^n)$-equivalent*) if the collineation induced by such a linear (resp. semilinear) map, sending each point $P$ to its image, maps $L$ onto $L'$. Since the image of $\langle v\rangle$ under $v \mapsto A v^\sigma$ is $\langle A v^\sigma \rangle$, these are the actions of $\mathrm{PGL}(2,q^n)$ and $\mathrm{P\Gamma L}(2,q^n)$ on points.
--
--   These are the objects every statement of the mission refers to: the goal, Theorem 5.1, counts the $\mathrm{P\Gamma L}(2,q^n)$-classes met by the linear sets $L_{h,t} = L_{\psi_{h,t}}$, $h \in H$.
--
--   **Formalization Note.** A negative power of $h$ is written as a field quotient, e.g. $h^{1-q^{t+1}}$ as `h / h ^ q ^ (t+1)`; this is exact whenever $h \neq 0$, which $h \in H$ guarantees. The exponents $t-1$ and $2t-1$ are natural-number subtractions, exact for $t \ge 1$. $x^{q^i}$ is `x ^ q ^ i`. The plane is `Fin 2 → F`; a point is a set of vectors; a linear set is a set of points. Equivalences are stated on sets (images of sets), not as group orbits of `Submodule`s; they are the same relations. These objects duplicate parts of the draft `ScatPoly.Construction.Model` of the companion mission, because draft definitions cannot import each other.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 2 (U_f, L_f, scattered polynomial), p. 3 (PΓL-equivalence), p. 5 (q-polynomials in Lemma 2.2), p. 6 display (2), p. 16 (GL/ΓL-equivalence of U_h), p. 20 display (36)

import Mathlib
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Inequiv

/-- Scattered polynomial (p. 2): for all nonzero `z, y`, `f(z)/z = f(y)/y` forces `z` and `y`
to be `𝔽_q`-linearly dependent, i.e. `z = c * y` with `c` in the fixed field
`{c | c ^ q = c}` of `x ↦ x^q`. -/
def IsScatteredPoly {F : Type*} [Field F] (q : ℕ) (f : F → F) : Prop :=
  ∀ z y : F, z ≠ 0 → y ≠ 0 → f z / z = f y / y → ∃ c : F, c ^ q = c ∧ z = c * y

/-- The index set `H = {h ∈ 𝔽_{q^n} : h^{q^t+1} = -1}` of the family (pp. 16, 20, 26). -/
def hSet (F : Type*) [Field F] (q t : ℕ) : Set F :=
  {h | h ^ (q ^ t + 1) = -1}

/-- The point `⟨v⟩_{𝔽_{q^n}}` of `PG(1, q^n)`: the set of all scalar multiples of `v`. -/
def point {F : Type*} [Field F] (v : Fin 2 → F) : Set (Fin 2 → F) :=
  {w | ∃ c : F, w = c • v}

/-- The linear set `L_f = {⟨(x, f(x))⟩_{𝔽_{q^n}} : x ∈ 𝔽*_{q^n}}` of `PG(1, q^n)`
(p. 2; display (36), p. 20), as a set of points. -/
def linSet {F : Type*} [Field F] (f : F → F) : Set (Set (Fin 2 → F)) :=
  {P | ∃ x : F, x ≠ 0 ∧ P = point ![x, f x]}

/-- The semilinear map `v ↦ A · v^σ` of `𝔽_{q^n}²`, with `σ` acting coordinatewise.
For invertible `A` these maps form `ΓL(2, q^n)`; `σ = id` gives `GL(2, q^n)`. -/
def act {F : Type*} [Field F] (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F)
    (v : Fin 2 → F) : Fin 2 → F :=
  A.mulVec (fun i => σ (v i))

/-- `U` and `W` are `GL(2, q^n)`-equivalent: some invertible matrix maps `U` onto `W`. -/
def GLEquiv {F : Type*} [Field F] (U W : Set (Fin 2 → F)) : Prop :=
  ∃ A : Matrix (Fin 2) (Fin 2) F, IsUnit A.det ∧ A.mulVec '' U = W

/-- `U` and `W` are `ΓL(2, q^n)`-equivalent: some `v ↦ A · v^σ` with `A` invertible maps `U`
onto `W`. -/
def GammaLEquiv {F : Type*} [Field F] (U W : Set (Fin 2 → F)) : Prop :=
  ∃ (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F), IsUnit A.det ∧ act σ A '' U = W

/-- Two point sets of `PG(1, q^n)` are `PGL(2, q^n)`-equivalent: some invertible matrix,
acting on points `P ↦ A(P)`, maps the first onto the second. -/
def PGLEquiv {F : Type*} [Field F] (L L' : Set (Set (Fin 2 → F))) : Prop :=
  ∃ A : Matrix (Fin 2) (Fin 2) F, IsUnit A.det ∧ (fun P => A.mulVec '' P) '' L = L'

/-- Two point sets of `PG(1, q^n)` are `PΓL(2, q^n)`-equivalent (p. 3): some collineation
induced by `v ↦ A · v^σ`, acting on points, maps the first onto the second. -/
def PGammaLEquiv {F : Type*} [Field F] (L L' : Set (Set (Fin 2 → F))) : Prop :=
  ∃ (σ : F ≃+* F) (A : Matrix (Fin 2) (Fin 2) F), IsUnit A.det ∧
    (fun P => act σ A '' P) '' L = L'

end ScatPoly.Inequiv


