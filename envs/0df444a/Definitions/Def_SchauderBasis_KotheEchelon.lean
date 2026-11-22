-- Prove2me | Definitions.Def_SchauderBasis_KotheEchelon
-- name    : SchauderBasis_KotheEchelon
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T17:00:37.069822+00:00
-- url     : https://prove2.me/theorems/de5aa011-cb89-48bd-8b5a-f6bcca873b8b
-- title:
--   Köthe matrices and the Köthe echelon space $\lambda^1(A)$ with its Fréchet topology
-- statement:
--   **Köthe matrices and Köthe echelon spaces.** A *Köthe matrix* is a family $A=(a_{k,m})_{k,m\in\mathbb N}$ of real numbers such that
--
--   1. $a_{k,m}\ge0$ for all $k,m$;
--   2. $a_{k,m}\le a_{k+1,m}$ for all $k,m$ (non-decreasing in the row index $k$);
--   3. for every $m$ there is $k$ with $a_{k,m}>0$.
--
--   The *Köthe echelon space* (Köthe sequence space) of order one of $A$ is
--   $$\lambda^1(A)=\Big\{\xi=(\xi_m)_{m\in\mathbb N}\in\mathbb C^{\mathbb N}\;:\;p_k(\xi):=\sum_{m\ge0}a_{k,m}\,|\xi_m|<\infty\ \text{ for every }k\in\mathbb N\Big\},$$
--   a complex vector space under coordinatewise operations, equipped with the locally convex topology defined by the seminorms $p_k$, $k\in\mathbb N$; for a Köthe matrix this is a Fréchet space. For example $a_{k,m}=1$ gives $\ell^1$, and $a_{k,m}=(m+1)^k$ gives the nuclear Fréchet space $\mathfrak s$ of rapidly decreasing sequences.
--
--   Köthe echelon spaces are the coordinate models of Fréchet spaces with an absolute Schauder basis. The paper recalls (p. 161, after the Dynin–Mityagin theorem 4.1.2.6) that every nuclear Fréchet space with a Schauder basis is linearly and topologically isomorphic to a Köthe sequence space, and identifies the spaces carrying its own bases with $\mathfrak s$.
--
--   **Formalization Note.** `IsKotheMatrix a` encodes conditions 1–3, with `a k m` $=a_{k,m}$ (row index $k$ first). `kotheEchelonSubmodule a` is the submodule of `ℕ → ℂ` of the sequences $\xi$ with $(a_{k,m}\xi_m)_m\in\ell^1$ for every $k$. `KotheEchelon a` is a type synonym of this submodule carrying the initial topology of the weighted maps `weight a k : ξ ↦ (a k m * ξ m)_m` into `lp (fun _ => ℂ) 1`, i.e. the topology of the seminorms $\sum_m|a_{k,m}|\,|\xi_m|$ (which are the $p_k$ when $A\ge0$) — not the subspace topology of the product $\mathbb C^{\mathbb N}$, which is why a type synonym is used. `toSeq` (also available as a coercion to functions `ℕ → ℂ`) returns the underlying sequence. The construction makes sense for every real matrix; the Köthe conditions are imposed separately through `IsKotheMatrix`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 161, §4.1.2.1, paragraph following Theorem 4.1.2.6 (Köthe sequence spaces); classical reference: H. Jarchow, Locally Convex Spaces, Teubner, 1981, Part III, Ch. 21, §21.6, p. 496 (as cited by the paper)

import Mathlib

/-!
# Köthe matrices and the Köthe echelon spaces `λ¹(A)`

A *Köthe matrix* is a family `A = (a k m)_{k, m ∈ ℕ}` of non-negative real numbers which is
non-decreasing in the row index `k` and such that for every coordinate `m` some entry `a k m` is
positive.  The *Köthe echelon space* (Köthe sequence space) of order one is
$$\lambda^1(A) = \Big\{\xi \in \mathbb C^{\mathbb N} : p_k(\xi) := \sum_{m} a_{k,m}\,|\xi_m| < \infty
  \text{ for every } k\Big\},$$
with the locally convex topology defined by the seminorms `p_k`.  It is a Fréchet space whenever `A`
is a Köthe matrix.

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), §4.1.2.1, p. 161,
which recalls that every nuclear Fréchet space with a Schauder basis is isomorphic to a Köthe
sequence space (referring to H. Jarchow, *Locally convex spaces*, Part III, Ch. 21, §21.6, p. 496).

Encoding: the space is the type synonym `KotheEchelon a` of the submodule
`kotheEchelonSubmodule a` of `ℕ → ℂ`; its topology is the initial topology of the weighted maps
`ξ ↦ (a k m * ξ m)_m` into `ℓ¹` (`lp (fun _ : ℕ => ℂ) 1`), `k ∈ ℕ`.  The `ℓ¹` norm of the `k`-th
weighted map is the seminorm `p_k` (for non-negative `a`), so this is the topology of the
seminorms `p_k`, not the subspace topology of the product `ℂ^ℕ` (which is why a type synonym is
used).
-/

namespace SchauderBasis

noncomputable section

/-- A Köthe matrix `A = (a k m)`: non-negative entries, non-decreasing in the row index `k`, and
every column `m` has a positive entry. -/
structure IsKotheMatrix (a : ℕ → ℕ → ℝ) : Prop where
  nonneg : ∀ k m, 0 ≤ a k m
  mono : ∀ k m, a k m ≤ a (k + 1) m
  exists_pos : ∀ m, ∃ k, 0 < a k m

/-- The submodule of `ℂ^ℕ` underlying the Köthe echelon space `λ¹(A)`: the sequences `ξ` with
`∑_m |a k m| |ξ m| < ∞` for every `k`. -/
def kotheEchelonSubmodule (a : ℕ → ℕ → ℝ) : Submodule ℂ (ℕ → ℂ) where
  carrier := {ξ | ∀ k, Memℓp (fun m => (a k m : ℂ) * ξ m) 1}
  zero_mem' := by
    intro k
    convert (zero_memℓp : Memℓp (0 : ℕ → ℂ) 1) using 1
    funext m
    simp
  add_mem' := by
    intro ξ η hξ hη k
    have h := (hξ k).add (hη k)
    convert h using 1
    funext m
    simp [mul_add]
  smul_mem' := by
    intro c ξ hξ k
    have h := (hξ k).const_smul c
    convert h using 1
    funext m
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The Köthe echelon space `λ¹(A)` of a matrix `a` (a type synonym of
`kotheEchelonSubmodule a`, carrying the topology of the seminorms `ξ ↦ ∑_m a k m |ξ m|`). -/
def KotheEchelon (a : ℕ → ℕ → ℝ) : Type := kotheEchelonSubmodule a

namespace KotheEchelon

variable (a : ℕ → ℕ → ℝ)

instance : AddCommGroup (KotheEchelon a) :=
  inferInstanceAs (AddCommGroup (kotheEchelonSubmodule a))

instance : Module ℂ (KotheEchelon a) :=
  inferInstanceAs (Module ℂ (kotheEchelonSubmodule a))

/-- The underlying sequence of an element of `λ¹(A)`. -/
def toSeq (ξ : KotheEchelon a) : ℕ → ℂ := Subtype.val (p := (· ∈ kotheEchelonSubmodule a)) ξ

instance : CoeFun (KotheEchelon a) (fun _ => ℕ → ℂ) := ⟨toSeq a⟩

theorem mem (ξ : KotheEchelon a) (k : ℕ) : Memℓp (fun m => (a k m : ℂ) * ξ m) 1 :=
  (Subtype.prop (p := (· ∈ kotheEchelonSubmodule a)) ξ) k

/-- The `k`-th weighted coordinate map `λ¹(A) → ℓ¹`, `ξ ↦ (a k m * ξ m)_m`. -/
def weight (k : ℕ) : KotheEchelon a →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 1 where
  toFun ξ := ⟨fun m => (a k m : ℂ) * ξ m, mem a ξ k⟩
  map_add' ξ η := by
    ext m
    show (a k m : ℂ) * (ξ.1 m + η.1 m) = (a k m : ℂ) * ξ.1 m + (a k m : ℂ) * η.1 m
    ring
  map_smul' c ξ := by
    ext m
    show (a k m : ℂ) * (c * ξ.1 m) = c * ((a k m : ℂ) * ξ.1 m)
    ring

/-- The topology of `λ¹(A)`: the initial topology of the weighted maps into `ℓ¹`, i.e. the
locally convex topology of the seminorms `p_k(ξ) = ∑_m |a k m| |ξ m|`. -/
instance : TopologicalSpace (KotheEchelon a) :=
  ⨅ k : ℕ, TopologicalSpace.induced (weight a k) inferInstance

end KotheEchelon

end

end SchauderBasis


