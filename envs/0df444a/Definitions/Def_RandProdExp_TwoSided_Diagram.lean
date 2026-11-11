-- Prove2me | Definitions.Def_RandProdExp_TwoSided_Diagram
-- name    : RandProdExp_TwoSided_Diagram
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:19:32.077361+00:00
-- url     : https://prove2.me/theorems/f48e3e73-0a5c-45d7-9f44-638f49926966
-- title:
--   The parametrized diagram $\alpha_M^X,\beta_M^X$, its specializations, $N_M$, and real sign witnesses (Definitions 4.6–4.11)
-- statement:
--   Fix $M\subseteq[n]^D$, dimensions $k_1,\dots,k_D$ and matrices $G_i\in R^{k_i\times n}$ over a commutative ring $R$, with columns $g_i(1),\dots,g_i(n)$. For a plane $P=P(I,a)$ put $U_P=\bigotimes_{i\in I}R^{k_i}$ ($U_\emptyset=R$). For planes $P=P(I,a)\subseteq Q=P(J,b)$ the insertion map of Equation (12) is
--   $$\tau_{P\to Q}:U_P\to U_Q,\qquad u\mapsto u\otimes\bigotimes_{j\in J\setminus I}g_j(a_j).$$
--   Let $U_M=\bigoplus_{P\in\mathcal P_\cap(M)}U_P$, $E_M=\bigoplus_{P\subsetneq Q\text{ in }\mathcal P_\cap(M)}U_P$ and $U_{[D]}=\bigotimes_{i\in[D]}R^{k_i}$, and define (Definition 4.10, Equation (13))
--   $$\alpha_M^G(e_{P,Q}(u))=e_P(u)-e_Q(\tau_{P\to Q}(u)),\qquad \beta_M^G((u_P)_P)=\sum_P\tau_{P\to[n]^D}(u_P).$$
--   Since $\beta\alpha=0$, $\beta$ descends to $\bar\beta_M^G:\operatorname{Coker}\alpha_M^G\to U_{[D]}$, which is injective exactly when $\ker\beta_M^G\subseteq\operatorname{Im}\alpha_M^G$.
--
--   With $R=\mathbb Z[X]$ and $G_i=X_i$, the $k_i\times n$ matrix of independent indeterminates $X^{(i)}_{r,j}$, this is the formal diagram of Definitions 4.9–4.10; a **specialization** substitutes matrices over a field for the $X_i$ and gives the same diagram with those matrices. $N_M=\dim U_M=\sum_{P=P(I,a)\in\mathcal P_\cap(M)}\prod_{i\in I}k_i$. A **real sign witness** (Definition 4.11) is a tuple of sign matrices $\sigma^{(i)}\in\{-1,1\}^{k_i\times n}$ at whose specialization over $\mathbb R$ the map $\bar\beta_M$ is injective; no rank condition is imposed. The row-space code of $x_i\in K^{k_i\times n}$ is $\operatorname{Im}(x_i^\top)\subseteq K^n$.
--
--   When every $G_i$ has full row rank, $\operatorname{Coker}\alpha_M^G$ is the cosheaf $\mathcal G(M)$ of the row-space codes and $\bar\beta_M^G$ is their corestriction map $\tau_M$ (Lemma 4.8); in general the diagram is still defined, which is what the transfer from $\mathbb R$ to finite fields uses.
--
--   **Formalization Note** Everything is written as matrices over basis indices. A basis index of $U_P$ is a tuple $v$ with $v_i\in[k_i]$ for $i\in I$ and $v_i=$ `none` otherwise (`TensorIdx`, `Compat`); `UIdx M k` and `EIdx M k` index the bases of $U_M$ and $E_M$, and `insCoeff G p q w v` is the $(w,v)$ entry of $\tau_{P\to Q}$. `BarInjective M G` is $\ker\beta\subseteq\operatorname{Im}\alpha$. `specialize x f` evaluates $f\in\mathbb Z[X]$ at $X_i:=x_i$. Signs are `ℤˣ`.
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), pp. 30–32, Definition 4.6, Fact 4.7 (Eq. (12)), Definitions 4.9–4.11; p. 41 (N_M)

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Grid
import Definitions.Def_RandProdExp_TwoSided_Codes

namespace RandProdExp.TwoSided

/-!
# The polynomially parametrized diagram `α_M^X, β_M^X` and real sign witnesses

Chattopadhyay, Ringach, Spooner, *Product Expansion of Random Codes via Analytic Techniques*,
STOC 2027 submission, §4.3, pp. 30–32: Definition 4.6 (dual message spaces `U_P`), Fact 4.7
(Equation (12)), Definitions 4.9–4.11; `N_M` of Lemma 6.16 (p. 41).

Everything is written for matrices `G_i ∈ R^{k_i × n}` over an arbitrary commutative ring `R`.
Taking `R = ℤ[X]` and `G_i = X_i` (the matrix of indeterminates, `formalMatrix`) gives the formal
diagram of Definitions 4.9–4.10; substituting matrices over a field for the indeterminates (a
specialization) gives the same diagram with those matrices in place of `X_i`.

* `U_P = ⊗_{i ∈ I} R^{k_i}` (`U_∅ = R`) has the basis indexed by tuples `v` with `v i ∈ Fin (k i)` for
  `i ∈ I` and `v i = none` for `i ∉ I` (`TensorIdx` with `Compat`).
* `U_M = ⊕_{P ∈ P∩(M)} U_P` has basis `UIdx M k`; `E_M = ⊕_{P ⊊ Q in P∩(M)} U_P` has basis `EIdx M k`;
  `U_{[D]} = ⊗_{i ∈ [D]} R^{k_i}` has basis `(i : Fin D) → Fin (k i)`.
* The insertion `τ_{P→Q}(u) = u ⊗ ⊗_{j ∈ J∖I} x_j(a_j)` of Equation (12) has matrix entries
  `insCoeff G p q w v = [w = v on I] · Π_{j ∈ J∖I} G_j(w_j, a_j)`.
-/

variable {D n : ℕ}

/-- Tensor indices: `v i ∈ Fin (k i)` on free coordinates, `none` elsewhere. -/
abbrev TensorIdx (k : Fin D → ℕ) := (i : Fin D) → Option (Fin (k i))

/-- `v` is a basis index of `U_P` for the plane index `p`: `v i` is defined exactly on the free
coordinates of `p`. -/
def Compat (k : Fin D → ℕ) (p : PlaneIdx D n) (v : TensorIdx k) : Prop :=
  ∀ i, (v i).isSome = true ↔ p i = none

/-- Basis of `U_M = ⊕_{P ∈ P∩(M)} U_P`. -/
def UIdx (M : Set (Fin D → Fin n)) (k : Fin D → ℕ) : Type :=
  {y : PlaneIdx D n × TensorIdx k // y.1 ∈ capIdx M ∧ Compat k y.1 y.2}

/-- Basis of `E_M = ⊕_{P, Q ∈ P∩(M), P ⊊ Q} U_P`: triples `(P, Q, v)` with `v` a basis index of `U_P`. -/
def EIdx (M : Set (Fin D → Fin n)) (k : Fin D → ℕ) : Type :=
  {e : PlaneIdx D n × PlaneIdx D n × TensorIdx k //
    e.1 ∈ capIdx M ∧ e.2.1 ∈ capIdx M ∧ planeOf e.1 ⊂ planeOf e.2.1 ∧ Compat k e.1 e.2.2}

noncomputable instance (M : Set (Fin D → Fin n)) (k : Fin D → ℕ) : Fintype (UIdx M k) := by
  classical
  unfold UIdx
  infer_instance

noncomputable instance (M : Set (Fin D → Fin n)) (k : Fin D → ℕ) : DecidableEq (UIdx M k) :=
  Classical.decEq _

noncomputable instance (M : Set (Fin D → Fin n)) (k : Fin D → ℕ) : Fintype (EIdx M k) := by
  classical
  unfold EIdx
  infer_instance

noncomputable instance (M : Set (Fin D → Fin n)) (k : Fin D → ℕ) : DecidableEq (EIdx M k) :=
  Classical.decEq _

/-- The entry `G_j(r, c)` of a matrix at a defined row index `r` and anchor column `c`
(`0` when either is undefined, which never happens where it is used). -/
def colEntry {R : Type} [CommRing R] {k : Fin D → ℕ} (G : (i : Fin D) → Matrix (Fin (k i)) (Fin n) R)
    (j : Fin D) : Option (Fin (k j)) → Option (Fin n) → R
  | some r, some c => G j r c
  | _, _ => 0

open Classical in
/-- Matrix entry `(w, v)` of the insertion map `τ_{P→Q} : U_P → U_Q` of Equation (12) for
`P = P(I, a) ⊆ Q = P(J, b)` (plane indices `p`, `q`): `u ↦ u ⊗ ⊗_{j ∈ J∖I} g_j(a_j)`, where
`g_j(c)` is the `c`-th column of `G_j`. -/
noncomputable def insCoeff {R : Type} [CommRing R] {k : Fin D → ℕ}
    (G : (i : Fin D) → Matrix (Fin (k i)) (Fin n) R) (p q : PlaneIdx D n) (w v : TensorIdx k) : R :=
  (if ∀ i, p i = none → w i = v i then 1 else 0) *
    ∏ j : Fin D, (if q j = none ∧ p j ≠ none then colEntry G j (w j) (p j) else 1)

open Classical in
/-- The matrix of `α_M^G : E_M → U_M`, `e_{P,Q}(u) ↦ e_P(u) − e_Q(τ_{P→Q}(u))` (Definition 4.10,
Equation (13)). -/
noncomputable def alphaMat {R : Type} [CommRing R] {k : Fin D → ℕ} (M : Set (Fin D → Fin n))
    (G : (i : Fin D) → Matrix (Fin (k i)) (Fin n) R) : Matrix (UIdx M k) (EIdx M k) R :=
  fun y e =>
    (if y.1.1 = e.1.1 ∧ y.1.2 = e.1.2.2 then 1 else 0) -
      (if y.1.1 = e.1.2.1 then insCoeff G e.1.1 e.1.2.1 y.1.2 e.1.2.2 else 0)

/-- The matrix of `β_M^G : U_M → U_{[D]}`, `(u_P)_P ↦ Σ_P τ_{P→[n]^D}(u_P)` (Definition 4.10,
Equation (13)). -/
noncomputable def betaMat {R : Type} [CommRing R] {k : Fin D → ℕ} (M : Set (Fin D → Fin n))
    (G : (i : Fin D) → Matrix (Fin (k i)) (Fin n) R) :
    Matrix ((i : Fin D) → Fin (k i)) (UIdx M k) R :=
  fun w y => insCoeff G y.1.1 (fun _ => none) (fun i => some (w i)) y.1.2

/-- The induced map `β̄_M^G : Coker α_M^G → U_{[D]}` is injective, i.e. `ker β_M^G ⊆ Im α_M^G`
(Definition 4.10). -/
def BarInjective {R : Type} [CommRing R] {k : Fin D → ℕ} (M : Set (Fin D → Fin n))
    (G : (i : Fin D) → Matrix (Fin (k i)) (Fin n) R) : Prop :=
  LinearMap.ker (betaMat M G).mulVecLin ≤ LinearMap.range (alphaMat M G).mulVecLin

/-- `N_M := dim U_M = Σ_{P = P(I,a) ∈ P∩(M)} Π_{i ∈ I} k_i` (Lemma 6.16). -/
noncomputable def dimUM (M : Set (Fin D → Fin n)) (k : Fin D → ℕ) : ℕ :=
  ∑ p ∈ capIdx M, ∏ i ∈ freeCoords p, k i

/-- The indeterminates `X = (X^{(i)}_{r,j})_{i ∈ [D], r ∈ [k_i], j ∈ [n]}` (Definition 4.9). -/
abbrev Var (k : Fin D → ℕ) (n : ℕ) := Σ i : Fin D, Fin (k i) × Fin n

/-- The formal matrices `X_i ∈ ℤ[X]^{k_i × n}` with entries `X^{(i)}_{r,j}` (Definition 4.9);
`alphaMat M (formalMatrix k n)` and `betaMat M (formalMatrix k n)` are `α_M^X` and `β_M^X`. -/
noncomputable def formalMatrix (k : Fin D → ℕ) (n : ℕ) :
    (i : Fin D) → Matrix (Fin (k i)) (Fin n) (MvPolynomial (Var k n) ℤ) :=
  fun i r c => MvPolynomial.X ⟨i, r, c⟩

/-- The value `f(x)` of a polynomial `f ∈ ℤ[X]` at a specialization `x = (x_i)`, `x_i ∈ K^{k_i × n}`. -/
noncomputable def specialize {K : Type} [CommRing K] {k : Fin D → ℕ}
    (x : (i : Fin D) → Matrix (Fin (k i)) (Fin n) K) (f : MvPolynomial (Var k n) ℤ) : K :=
  MvPolynomial.eval₂ (Int.castRingHom K) (fun v => x v.1 v.2.1 v.2.2) f

/-- Sign matrices `σ = (σ^{(i)})_{i ∈ [D]}`, `σ^{(i)} ∈ {−1, 1}^{k_i × n}` (`ℤˣ = {±1}`). -/
abbrev SignTuple (k : Fin D → ℕ) (n : ℕ) := (i : Fin D) → Matrix (Fin (k i)) (Fin n) ℤˣ

/-- The sign matrices as integer matrices. -/
def signsInt {k : Fin D → ℕ} (σ : SignTuple k n) : (i : Fin D) → Matrix (Fin (k i)) (Fin n) ℤ :=
  fun i r c => ((σ i r c : ℤˣ) : ℤ)

/-- The sign matrices as real matrices. -/
def signsReal {k : Fin D → ℕ} (σ : SignTuple k n) : (i : Fin D) → Matrix (Fin (k i)) (Fin n) ℝ :=
  fun i r c => (((σ i r c : ℤˣ) : ℤ) : ℝ)

/-- **Real sign witness** (Definition 4.11): sign matrices at whose specialization over `ℝ` the map
`β̄_M` is injective (no rank condition). -/
def IsRealSignWitness (M : Set (Fin D → Fin n)) {k : Fin D → ℕ} (σ : SignTuple k n) : Prop :=
  BarInjective M (signsReal σ)

/-- The row-space code `Im(x^⊤) ⊆ K^n` of a matrix `x ∈ K^{k × n}`. -/
def rowSpace {K : Type} [Field K] {k : ℕ} (x : Matrix (Fin k) (Fin n) K) : Submodule K (Fin n → K) :=
  Submodule.span K (Set.range x)

end RandProdExp.TwoSided


