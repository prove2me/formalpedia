-- Prove2me | Definitions.Def_LLLFactor_Factors_Setting
-- name    : LLLFactor_Factors_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:59:29.998064+00:00
-- url     : https://prove2.me/theorems/166bef5e-2e9c-4052-ab7a-6a45eb848f6d
-- title:
--   Sect. 2, pp. 515–527 — |g|, (g mod pᵏ), the setting (2.1)–(2.4), h₀ as in (2.5), the lattice L of (2.6), reduced bases (1.4)–(1.5)
-- statement:
--   This file fixes the objects of Sect. 2 of Lenstra–Lenstra–Lovász.
--
--   **Length of a polynomial** (p. 515). For $g=\sum_i a_iX^i\in\mathbb Z[X]$,
--   $$|g|=\Big(\sum_i a_i^2\Big)^{1/2}.$$
--
--   **Coefficient vectors** (2.6). A polynomial $\sum_{i=0}^m a_iX^i$ of degree at most $m$ is identified with $(a_0,a_1,\dots,a_m)\in\mathbb R^{m+1}$; for such a polynomial $|g|$ is the Euclidean length of this vector.
--
--   **Reduction modulo $q$.** For $g=\sum_i a_iX^i\in\mathbb Z[X]$ and a positive integer $q$, $(g \bmod q)=\sum_i (a_i \bmod q)X^i\in(\mathbb Z/q\mathbb Z)[X]$; it is used with $q=p^k$ and $q=p$.
--
--   **The setting of Sect. 2** (p. 526). $p$ is a prime number, $k$ a positive integer, $f\in\mathbb Z[X]$ has degree $n>0$, and $h\in\mathbb Z[X]$ satisfies
--
--   1. (2.1) $h$ has leading coefficient $1$;
--   2. (2.2) $(h \bmod p^k)$ divides $(f \bmod p^k)$ in $(\mathbb Z/p^k\mathbb Z)[X]$;
--   3. (2.3) $(h \bmod p)$ is irreducible in $\mathbb F_p[X]$;
--   4. (2.4) $(h \bmod p)^2$ does not divide $(f \bmod p)$ in $\mathbb F_p[X]$.
--
--   We write $l=\deg h$.
--
--   **The factor $h_0$** (2.5). A polynomial $h_0\in\mathbb Z[X]$ is *as in (2.5)* if it is an irreducible element of $\mathbb Z[X]$ dividing $f$ such that $(h \bmod p)$ divides $(h_0 \bmod p)$ in $\mathbb F_p[X]$. Proposition (2.5) shows that such an $h_0$ exists and is unique up to sign.
--
--   **The lattice $L$** (2.6). For an integer $m\ge l$, $L$ is the set of $g\in\mathbb Z[X]$ of degree $\le m$ such that $(h\bmod p^k)$ divides $(g\bmod p^k)$ in $(\mathbb Z/p^k\mathbb Z)[X]$.
--
--   **Reduced bases** (1.2)–(1.5). For linearly independent $v_1,\dots,v_N\in\mathbb R^N$, the Gram–Schmidt vectors are $v_i^*=v_i-\sum_{j<i}\mu_{ij}v_j^*$ with $\mu_{ij}=(v_i,v_j^*)/(v_j^*,v_j^*)$. The family is *reduced* if
--   $$|\mu_{ij}|\le\tfrac12\quad(1\le j<i\le N),\qquad |v_i^*+\mu_{i\,i-1}v_{i-1}^*|^2\ge\tfrac34|v_{i-1}^*|^2\quad(1<i\le N).$$
--   Polynomials $b_1,\dots,b_{m+1}$ form a *reduced basis for $L$* if each $b_j$ lies in $L$, their coefficient vectors are linearly independent over $\mathbb R$, every element of $L$ is an integer combination of them, and their coefficient vectors form a reduced family.
--
--   These are the objects every statement of Sect. 2 is about.
--
--   **Formalization Note** Indices are 0-based: the paper's $b_1,\dots,b_{m+1}$ are Lean's `b 0, …, b m`, and condition (1.5) for the paper's pair $(i-1,i)$ is stated for Lean's pair $(i,i+1)$. The Gram–Schmidt vectors are Mathlib's unnormalised `InnerProductSpace.gramSchmidt`. Irreducibility in $\mathbb Z[X]$ is Mathlib's `Irreducible`; no prime constant can satisfy the condition of (2.5) under (2.1)–(2.4), so no degree clause is added. The reduced-basis predicate duplicates the one of the companion missions I and II of this series (separate namespaces).
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 515 (definition of |f|), p. 516 (1.2)–(1.5), p. 526 (2.1)–(2.4), (2.5), pp. 526–527 (2.6)

import Mathlib

namespace LLLFactor.Factors
open Polynomial
noncomputable section

/-- The length `|g| = (Σᵢ aᵢ²)^{1/2}` of an integer polynomial `g = Σᵢ aᵢ Xⁱ` (p. 515). -/
def polyNorm (g : ℤ[X]) : ℝ :=
  Real.sqrt (∑ i ∈ g.support, ((g.coeff i : ℤ) : ℝ) ^ 2)

/-- The coefficient vector `(a₀, a₁, …, a_m) ∈ ℝ^{m+1}` of `Σᵢ aᵢ Xⁱ` (identification of (2.6)). -/
def coeffVec (m : ℕ) (g : ℤ[X]) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (fun i : Fin (m + 1) => ((g.coeff (i : ℕ) : ℤ) : ℝ))

/-- `(g mod q)`: reduce every coefficient of `g` modulo `q`, giving a polynomial over `ℤ/qℤ`. -/
def modPk (q : ℕ) (g : ℤ[X]) : (ZMod q)[X] :=
  g.map (Int.castRingHom (ZMod q))

/-- The standing assumptions of Sect. 2 (p. 526): `p` prime, `k ≥ 1`, `deg f = n > 0`, and (2.1)–(2.4). -/
structure IsSetting (p k : ℕ) (f h : ℤ[X]) : Prop where
  prime : p.Prime
  k_pos : 0 < k
  deg_f_pos : 0 < f.natDegree
  /-- (2.1) `h` has leading coefficient 1. -/
  monic : h.Monic
  /-- (2.2) `(h mod pᵏ)` divides `(f mod pᵏ)` in `(ℤ/pᵏℤ)[X]`. -/
  dvd_mod_pk : modPk (p ^ k) h ∣ modPk (p ^ k) f
  /-- (2.3) `(h mod p)` is irreducible in `𝔽_p[X]`. -/
  irreducible_mod_p : Irreducible (modPk p h)
  /-- (2.4) `(h mod p)²` does not divide `(f mod p)` in `𝔽_p[X]`. -/
  sq_not_dvd_mod_p : ¬ (modPk p h) ^ 2 ∣ modPk p f

/-- `h₀` is "as in (2.5)": an irreducible factor of `f` in `ℤ[X]` with `(h mod p) ∣ (h₀ mod p)`. -/
def IsH0 (p : ℕ) (f h h₀ : ℤ[X]) : Prop :=
  Irreducible h₀ ∧ h₀ ∣ f ∧ modPk p h ∣ modPk p h₀

/-- The set `L` of (2.6): polynomials of degree `≤ m` whose reduction mod `pᵏ` is divisible by
`(h mod pᵏ)`. -/
def latticeL (p k : ℕ) (h : ℤ[X]) (m : ℕ) : Set ℤ[X] :=
  {g | g.natDegree ≤ m ∧ modPk (p ^ k) h ∣ modPk (p ^ k) g}

/-- Gram–Schmidt vectors `bᵢ*` of (1.2) (unnormalised). -/
def gs {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin N)) (i : Fin N) : EuclideanSpace ℝ (Fin N) :=
  InnerProductSpace.gramSchmidt ℝ v i

/-- Gram–Schmidt coefficients `μᵢⱼ = (bᵢ, bⱼ*)/(bⱼ*, bⱼ*)` of (1.3). -/
def mu {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin N)) (i j : Fin N) : ℝ :=
  inner ℝ (v i) (gs v j) / inner ℝ (gs v j) (gs v j)

/-- Conditions (1.4) and (1.5) of a reduced basis, 0-based: Lean's pair `(i, i+1)` is the
paper's `(i−1, i)`. -/
def IsReduced {N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin N)) : Prop :=
  (∀ i j : Fin N, j < i → |mu v i j| ≤ (1 / 2 : ℝ)) ∧
  (∀ (i : ℕ) (hi : i + 1 < N),
    (3 / 4 : ℝ) * ‖gs v ⟨i, by omega⟩‖ ^ 2 ≤
      ‖gs v ⟨i + 1, hi⟩ + mu v ⟨i + 1, hi⟩ ⟨i, by omega⟩ • gs v ⟨i, by omega⟩‖ ^ 2)

/-- `b₁, …, b_{m+1}` (Lean `b 0, …, b m`) is a reduced basis for the lattice `L` of (2.6). -/
def IsReducedBasisOfL (p k : ℕ) (h : ℤ[X]) (m : ℕ) (b : Fin (m + 1) → ℤ[X]) : Prop :=
  (∀ j, b j ∈ latticeL p k h m) ∧
  LinearIndependent ℝ (coeffVec m ∘ b) ∧
  (∀ g ∈ latticeL p k h m, g ∈ Submodule.span ℤ (Set.range b)) ∧
  IsReduced (coeffVec m ∘ b)

end
end LLLFactor.Factors


