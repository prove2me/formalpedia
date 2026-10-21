-- Prove2me | Definitions.Def_EJASpectral_RootDet_EJA
-- name    : EJASpectral_RootDet_EJA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:26.574283+00:00
-- url     : https://prove2.me/theorems/23f8393f-73b7-48cc-abcc-c58624070a1c
-- title:
--   §2–§2.1, pp. 5–6 — Euclidean Jordan algebra of rank d with its spectral decomposition, det, trace inner product, cone of squares, L, P
-- statement:
--   This file fixes the algebraic setting of Coey, Kapelevich and Vielma: a finite-dimensional **Euclidean Jordan algebra** of rank $d$ together with the spectral decomposition of its elements.
--
--   Let $V$ be a real inner product space with a bilinear product $\circ : V\times V\to V$ and a multiplicative identity $e$. Write $w^2 := w\circ w$. The structure $\mathrm{EJA}(V,d)$ records:
--
--   1. **Jordan axioms**: $w_a\circ w_b = w_b\circ w_a$ (1a) and $w_a\circ(w_a^2\circ w_b) = w_a^2\circ(w_a\circ w_b)$ (1b) for all $w_a,w_b\in V$, and $e\circ w = w$.
--   2. **Euclidean property**: $\langle w_a\circ w_b, w_c\rangle = \langle w_b, w_a\circ w_c\rangle$ for all $w_a,w_b,w_c$.
--   3. **Spectral data**: for every $w\in V$, real numbers $w_1,\dots,w_d$ (the eigenvalues) and a **Jordan frame** $c_1,\dots,c_d$ with
--   $$w = \sum_{i\in[\![d]\!]} w_i\, c_i. \tag{5}$$
--   A Jordan frame is a family of idempotents ($c_i^2=c_i$) that are pairwise orthogonal ($c_i\circ c_j = 0$ for $i\ne j$), sum to $e$, and are each **primitive**: non-zero and not the sum of two orthogonal non-zero idempotents.
--   4. **Trace inner product**: $\langle w_a, w_b\rangle = \operatorname{tr}(w_a\circ w_b)$.
--
--   From these data the file defines $\det(w) = \prod_i w_i$, $\operatorname{tr}(w)=\sum_i w_i$, the **cone of squares** $\mathcal Q = \{w\circ w : w\in V\}$, the multiplication operator $L(w_a)w_b = w_a\circ w_b$ (2), the quadratic representation
--   $$P(w) = 2L(w)^2 - L(w^2), \tag{3}$$
--   and the spectral function $f(w) = \sum_i f(w_i)\,c_i$ of a real function $f$, used for $w^{-1/2}$.
--
--   These are the objects every statement of the mission is written in. The examples $\mathbb R^d$ (entrywise product), $\mathbb S^d$ and $\mathbb H^d$ are instances; nothing restricts $V$ to them.
--
--   **Formalization Note** The spectral theorem (Faraut–Korányi, Theorem III.1.2, quoted on p. 6) guarantees that eigenvalues and a Jordan frame exist for every element of a Euclidean Jordan algebra of rank $d$, so carrying them as fields of the structure is an encoding of the paper's setting, not an extra hypothesis. Primitivity of the frame is required, so $d$ is the rank of $V$. Uniqueness of the eigenvalues (up to order) is a theorem and is not asserted; $\det$, $\operatorname{tr}$ and spectral functions of the eigenvalues do not depend on the choice. The inner product of $V$ is the trace form, as the paper fixes on p. 6. Finite-dimensionality is assumed in every theorem that uses the structure.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, pp. 5–6, (1a)–(1b), (2), (3), (5), definitions of idempotent, Jordan frame, rank, det, tr, cone of squares, trace inner product

import Mathlib

namespace EJASpectral.RootDet

open scoped RealInnerProductSpace

/-! # Euclidean Jordan algebras of rank `d` with their spectral data (§2–§2.1, pp. 5–6)

Coey, Kapelevich & Vielma, *Conic optimization with spectral functions on Euclidean Jordan
algebras*, arXiv:2103.04104v2, pp. 5–6, (1)–(3), (5). -/

/-- `c` is an idempotent of the product `jmul`: `c ∘ c = c` (p. 6). -/
def IsIdem {V : Type*} [AddCommGroup V] [Module ℝ V] (jmul : V →ₗ[ℝ] V →ₗ[ℝ] V) (c : V) : Prop :=
  jmul c c = c

/-- A primitive idempotent (p. 6): a non-zero idempotent that cannot be written as the sum of two
orthogonal (`a ∘ b = 0`) non-zero idempotents. -/
def IsPrimitiveIdem {V : Type*} [AddCommGroup V] [Module ℝ V] (jmul : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (c : V) : Prop :=
  IsIdem jmul c ∧ c ≠ 0 ∧
    ∀ a b : V, IsIdem jmul a → IsIdem jmul b → jmul a b = 0 → a + b = c → a = 0 ∨ b = 0

/-- A Jordan frame (p. 6): a complete system `c₁, …, c_d` of pairwise orthogonal idempotents with
`Σᵢ cᵢ = e`, each of which is primitive. -/
def IsJordanFrame {V : Type*} [AddCommGroup V] [Module ℝ V] (jmul : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : V)
    {d : ℕ} (c : Fin d → V) : Prop :=
  (∀ i, IsPrimitiveIdem jmul (c i)) ∧ (∀ i j, i ≠ j → jmul (c i) (c j) = 0) ∧ ∑ i, c i = e

/-- A Euclidean Jordan algebra of rank `d` (pp. 5–6), on a real inner product space `V`.

* `jmul` is the bilinear Jordan product `∘`, commutative (1a) and satisfying the Jordan
  identity (1b); `e` is its multiplicative identity;
* Euclidean: `⟨a ∘ b, c⟩ = ⟨b, a ∘ c⟩`;
* every `w` has a spectral decomposition (5) `w = Σᵢ wᵢ cᵢ` over a Jordan frame `c = frame w`
  with eigenvalues `wᵢ = eig w i` (Faraut–Korányi III.1.2, quoted on p. 6);
* the inner product is the trace form, `⟨a, b⟩ = tr(a ∘ b)` (p. 6). -/
structure EJA (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (d : ℕ) where
  /-- the Jordan product `a ∘ b` -/
  jmul : V →ₗ[ℝ] V →ₗ[ℝ] V
  /-- the multiplicative identity `e` -/
  e : V
  /-- (1a) -/
  comm : ∀ a b : V, jmul a b = jmul b a
  /-- (1b) -/
  jordan : ∀ a b : V, jmul a (jmul (jmul a a) b) = jmul (jmul a a) (jmul a b)
  /-- `e` is a multiplicative identity -/
  one_mul : ∀ a : V, jmul e a = a
  /-- the Euclidean property -/
  euclid : ∀ a b c : V, ⟪jmul a b, c⟫ = ⟪b, jmul a c⟫
  /-- the eigenvalues `w₁, …, w_d` of `w` -/
  eig : V → Fin d → ℝ
  /-- the Jordan frame `c₁, …, c_d` of the spectral decomposition of `w` -/
  frame : V → Fin d → V
  frame_jordan : ∀ w : V, IsJordanFrame jmul e (frame w)
  /-- (5): `w = Σᵢ wᵢ cᵢ` -/
  spectral : ∀ w : V, w = ∑ i, eig w i • frame w i
  /-- the inner product is the trace form `⟨a, b⟩ = tr(a ∘ b)` (p. 6) -/
  inner_eq_tr : ∀ a b : V, ⟪a, b⟫ = ∑ i, eig (jmul a b) i

namespace EJA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {d : ℕ}

/-- `det(w) = Πᵢ wᵢ` (p. 6). -/
def det (J : EJA V d) (w : V) : ℝ := ∏ i, J.eig w i

/-- `tr(w) = Σᵢ wᵢ` (p. 6). -/
def tr (J : EJA V d) (w : V) : ℝ := ∑ i, J.eig w i

/-- The cone of squares `Q = {w ∘ w : w ∈ V}` (p. 5). -/
def Q (J : EJA V d) : Set V := {w | ∃ a : V, w = J.jmul a a}

/-- `L(a) b = a ∘ b` (2). -/
def L (J : EJA V d) (a : V) : V →ₗ[ℝ] V := J.jmul a

/-- `P(a) = 2 L(a)² − L(a²)` (3). -/
def P (J : EJA V d) (a : V) : V →ₗ[ℝ] V := 2 • (J.L a ∘ₗ J.L a) - J.L (J.jmul a a)

/-- The spectral function `f(w) = Σᵢ f(wᵢ) cᵢ` of a real function `f` (§2.1), e.g. `w^{-1/2}`. -/
def spec (J : EJA V d) (f : ℝ → ℝ) (w : V) : V := ∑ i, f (J.eig w i) • J.frame w i

end EJA

end EJASpectral.RootDet


