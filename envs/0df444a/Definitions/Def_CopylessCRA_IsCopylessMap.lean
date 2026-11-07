-- Prove2me | Definitions.Def_CopylessCRA_IsCopylessMap
-- name    : CopylessCRA_IsCopylessMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:19.946965+00:00
-- url     : https://prove2.me/theorems/4fba36c0-a5de-4dad-b506-788ebbfdcbc8
-- title:
--   Multiaffine polynomials $V_r$, copyless maps, pullbacks $B_P$, $k(P)$, $L_P$, affine coordinate permutations, $\mathcal W_k$, linearization of a CCRA
-- statement:
--   1. $V_r$ is the space of multiaffine polynomials in $x_1,\dots,x_r$ (degree at most one in each variable), with basis the squarefree monomials $x_I=\prod_{i\in I}x_i$.
--   2. A *copyless map* $P:\mathbb Q^r\to\mathbb Q^r$ has multiaffine coordinates with pairwise disjoint variable supports; its *pullback* is $B_P(h)=h\circ P$.
--   3. $k(P)$ is the number of nonconstant coordinates of $P$, and $L_P$ the coordinate affine subspace obtained by fixing each constant coordinate to its value.
--   4. An *affine coordinate permutation* of $K^k$ is a map $R_i(x)=\alpha_ix_{\pi(i)}+\beta_i$ with $\alpha_i\ne0$ and $\pi$ a permutation (display (3)); over $\overline{\mathbb Q}$ these form $\mathfrak A_k=(\overline{\mathbb Q}^\times\ltimes\overline{\mathbb Q})^k\rtimes S_k$.
--   5. $\mathcal W_k=\{B_R:R\in\mathfrak A_k\}\subseteq GL(V_k\otimes\overline{\mathbb Q})$, as matrices in the squarefree monomial basis: the $(J,I)$ entry of $B_R$ is the coefficient of $x_J$ in $\prod_{i\in I}R_i$.
--   6. The linearization of a CCRA: on $\bigoplus_{s\in S}V_r$, $(B_ah)_s=h_{\delta(s,a)}\circ P_{s,a}$, $\lambda(h)=h_{s_0}(x^{(0)})$, $o=(\omega_s)_s$.
--
--   These are the objects of §2.1 and §3.
--
--   **Formalization Note** "Copyless map" is the semantic consequence of the syntactic definition (multiaffine, disjoint supports) that §3 uses; every syntactic copyless tuple gives one. $B_P$ is defined on all polynomials and preserves $V_r$ for copyless $P$; the linearization operators are defined on $S\to\mathbb Q[x]$.
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), §2.1, p.6 (PDF p.8); §3, display (3), p.8 (PDF p.10); p.9 (PDF p.11)

import Mathlib
import Definitions.Def_CopylessCRA_CCRA

namespace CopylessCRA

open MvPolynomial

/-- `V_r`, the space of **multiaffine polynomials** in `x₁, …, x_r` (degree at most one in each
variable), with basis the squarefree monomials `x_I = ∏_{i ∈ I} x_i`. Zeng–Cao–Dai–Wang–Ding,
*Copyless Cost Register Automata and Algebraic Groups*, STOC 2027 submission (manuscript sha256
434d3094…), §2.1, p.6 (PDF p.8). -/
noncomputable def multiaffine (r : ℕ) : Submodule ℚ (MvPolynomial (Fin r) ℚ) :=
  MvPolynomial.restrictDegree (Fin r) ℚ 1

/-- A **copyless map** `P : ℚ^r → ℚ^r` in the semantic sense of §2.1 (p.6): its coordinate
polynomials are multiaffine and distinct coordinates have disjoint variable supports.

**Formalization Note** §2.1 derives these two properties from the syntactic definition (each
variable written at most once across the tuple) and §3 uses only them. Every syntactic copyless
tuple gives such a map, and compositions of such maps are again such maps, so the §3 statements made
for this class contain the paper's (a generalization, recorded on each item). -/
def IsCopylessMap {r : ℕ} (P : Fin r → MvPolynomial (Fin r) ℚ) : Prop :=
  (∀ i, P i ∈ multiaffine r) ∧ Pairwise fun i j => Disjoint (P i).vars (P j).vars

/-- The **pullback** `B_P(h) = h ∘ P` (§2.1, p.6), as a linear endomorphism of `ℚ[x₁, …, x_r]`;
on copyless `P` it preserves `V_r`. -/
noncomputable def pullback {r : ℕ} (P : Fin r → MvPolynomial (Fin r) ℚ) :
    Module.End ℚ (MvPolynomial (Fin r) ℚ) :=
  (MvPolynomial.aeval P).toLinearMap

/-- The polynomial map `x ↦ P(x)` on `ℚ^r`. -/
noncomputable def evalMap {r : ℕ} (P : Fin r → MvPolynomial (Fin r) ℚ) (x : Fin r → ℚ) :
    Fin r → ℚ :=
  fun i => MvPolynomial.eval x (P i)

/-- Coordinate `i` of `P` is **free** (nonconstant). -/
def IsFreeCoord {r : ℕ} (P : Fin r → MvPolynomial (Fin r) ℚ) (i : Fin r) : Prop :=
  ¬ ∃ c : ℚ, P i = C c

/-- `k(P)`, the number of nonconstant coordinates of `P` (§3, p.8, PDF p.10). -/
noncomputable def numFree {r : ℕ} (P : Fin r → MvPolynomial (Fin r) ℚ) : ℕ :=
  Nat.card {i // IsFreeCoord P i}

/-- `L_P(ℚ)`, the coordinate affine subspace obtained by fixing each constant coordinate of `P` to its
value (§3, p.8). -/
def coordSubspace {r : ℕ} (P : Fin r → MvPolynomial (Fin r) ℚ) : Set (Fin r → ℚ) :=
  {x | ∀ i (c : ℚ), P i = C c → x i = c}

/-- An **affine coordinate permutation** of `K^k`, display (3), p.8: `R_i(x) = α_i x_{π(i)} + β_i`
with `α_i ≠ 0` and `π` a permutation. Over `K = ℚ̄` these maps form the group `𝔄_k` of p.9. -/
def IsAffineCoordPerm {K : Type*} [Field K] {k : ℕ} (R : Fin k → MvPolynomial (Fin k) K) : Prop :=
  ∃ (π : Equiv.Perm (Fin k)) (a b : Fin k → K), (∀ i, a i ≠ 0) ∧
    ∀ i, R i = C (a i) * X (π i) + C (b i)

/-- The exponent vector of the squarefree monomial `x_I`. -/
noncomputable def sqfreeMonomial {k : ℕ} (I : Finset (Fin k)) : Fin k →₀ ℕ :=
  ∑ i ∈ I, Finsupp.single i 1

/-- The matrix of the pullback `B_R` on `V_k ⊗ K` in the squarefree monomial basis: the entry
`(J, I)` is the coefficient of `x_J` in `B_R x_I = ∏_{i ∈ I} R_i`. -/
noncomputable def pullbackMatrix {K : Type*} [Field K] {k : ℕ}
    (R : Fin k → MvPolynomial (Fin k) K) : Matrix (Finset (Fin k)) (Finset (Fin k)) K :=
  fun J I => MvPolynomial.coeff (sqfreeMonomial J) (∏ i ∈ I, R i)

/-- `𝒲_k = {B_R : R ∈ 𝔄_k} ⊆ GL(V_k ⊗ K)` (p.9, PDF p.11; there `K = ℚ̄`), in the squarefree
monomial basis. -/
def affinePullbackGroup (K : Type*) [Field K] (k : ℕ) :
    Set (Matrix (Finset (Fin k)) (Finset (Fin k)) K)ˣ :=
  {g | ∃ R : Fin k → MvPolynomial (Fin k) K, IsAffineCoordPerm R ∧
    (g : Matrix (Finset (Fin k)) (Finset (Fin k)) K) = pullbackMatrix R}

namespace CCRA

variable {α : Type*} (C : CCRA α)

/-- The letter operator of the linearization of §2.1 (p.6): on `⊕_{s ∈ S} ℚ[x]`,
`(B_a h)_s = h_{δ(s,a)} ∘ P_{s,a}`. -/
noncomputable def linOp (a : α) : Module.End ℚ (C.S → MvPolynomial (Fin C.r) ℚ) :=
  LinearMap.pi fun s => pullback (C.updPoly s a) ∘ₗ LinearMap.proj (C.δ s a)

/-- The initial functional of the linearization, `λ(h) = h_{s0}(x0)` (§2.1, p.6). -/
noncomputable def linInit : (C.S → MvPolynomial (Fin C.r) ℚ) →ₗ[ℚ] ℚ :=
  (MvPolynomial.aeval C.x0).toLinearMap ∘ₗ LinearMap.proj C.s0

/-- The final vector of the linearization, `o = (ω_s)_s` (§2.1, p.6). -/
noncomputable def linOut : C.S → MvPolynomial (Fin C.r) ℚ := fun s => (C.out s).toPoly

end CCRA

end CopylessCRA


