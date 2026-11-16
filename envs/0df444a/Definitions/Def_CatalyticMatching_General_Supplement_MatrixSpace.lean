-- Prove2me | Definitions.Def_CatalyticMatching_General_Supplement_MatrixSpace
-- name    : CatalyticMatching_General_Supplement_MatrixSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:05:49.501987+00:00
-- url     : https://prove2.me/theorems/113f3224-de1e-4d34-8214-eb2804eb2724
-- title:
--   Matrix spaces, linear pencils, commutative rank and rank-preserving replacement tuples
-- statement:
--   Let $F$ be a field and $A_1,\dots,A_m\in F^{n\times n}$. For $a\in F^m$ put $B(a)=\sum_{i=1}^m a_iA_i$. The **matrix space** $\mathcal A=\langle A_1,\dots,A_m\rangle$ is the full $F$-linear span, and its **rank** is
--
--   $$\operatorname{rank}(\mathcal A)=\max_{a\in F^m}\operatorname{rank}B(a).$$
--
--   The set of ranks is nonempty and bounded by $n$; for $m=0$ or $n=0$ the value is $0$. The generic pencil $\sum_i A_ix_i$ over $F(x_1,\dots,x_m)$ is defined separately. No linear independence of the generators is assumed.
--
--   For $I\subseteq[m]$, a tuple $\lambda\in F^I$ and a finite $S\subseteq F$, let $B_{a,I}(\lambda)=\sum_{i\notin I}A_ia_i+\sum_{i\in I}A_i\lambda_i$ and
--
--   $$\mathcal I_{a,I}=\{\lambda\in S^{I}:\ \operatorname{rank}B_{a,I}(\lambda)=\operatorname{rank}B(a)\}.$$
--
--   These are the objects of Lemma 5.2, Remark 5.3 and Theorem 5.4.
--
--   **Formalization Note** The maximum is the natural-number supremum of the attained ranks, which equals the maximum because the set is bounded. Tuples indexed by $I=\{i_1<\dots<i_\ell\}$ are functions $I\to F$.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, §5, displayed definition of rank(𝒜), printed/PDF p.26; Lemma 5.2, p.27

import Mathlib

namespace CatalyticMatching.General.Supplement

/-- B(a) = Σᵢ aᵢ Aᵢ for generators A₁,…,A_m ∈ F^{n×n}; m = 0 gives the zero matrix. -/
def pencil {F : Type} [Field F] {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) F)
    (a : Fin m → F) : Matrix (Fin n) (Fin n) F :=
  ∑ i, a i • A i

/-- The matrix space 𝒜 = ⟨A₁,…,A_m⟩: the whole F-linear span; no independence assumed. -/
def matrixSpan {F : Type} [Field F] {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) F) :
    Submodule F (Matrix (Fin n) (Fin n) F) :=
  Submodule.span F (Set.range A)

/-- §5 p.26: rank(𝒜) = max_{a ∈ F^m} rank B(a). The set is nonempty and bounded by n,
so the natural-number supremum is this maximum. -/
noncomputable def commRank {F : Type} [Field F] {n m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) F) : ℕ :=
  sSup {k | ∃ a : Fin m → F, (pencil A a).rank = k}

/-- The generic pencil Σᵢ Aᵢ xᵢ over F(x₁,…,x_m) (used in the statement of Theorem 5.1). -/
noncomputable def genericPencil {F : Type} [Field F] {n m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) F) :
    Matrix (Fin n) (Fin n) (FractionRing (MvPolynomial (Fin m) F)) :=
  fun u v => algebraMap _ _ (∑ i, MvPolynomial.X i * MvPolynomial.C (A i u v))

/-- Replace the coordinates in I by λ, keep aᵢ for i ∉ I:
B_{a,I}(λ) = Σ_{i∉I} Aᵢaᵢ + Σ_{i∈I} Aᵢλᵢ is `pencil A (replaceCoords a I λ)`. -/
def replaceCoords {F : Type} {m : ℕ} (a : Fin m → F) (I : Finset (Fin m))
    (lam : I → F) : Fin m → F :=
  fun i => if h : i ∈ I then lam ⟨i, h⟩ else a i

/-- Lemma 5.2 p.27: 𝓘_{a,I} = {λ ∈ S^I : rank B_{a,I}(λ) = rank B(a)} (equality). -/
noncomputable def rankPreservingTuples {F : Type} [Field F] {n m : ℕ}
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) (I : Finset (Fin m))
    (S : Finset F) : Finset (I → F) :=
  (Fintype.piFinset fun _ : I => S).filter
    (fun lam => (pencil A (replaceCoords a I lam)).rank = (pencil A a).rank)

end CatalyticMatching.General.Supplement


