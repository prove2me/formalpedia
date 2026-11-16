-- Prove2me | Definitions.Def_OptGaussTomo_Supplement_mulOp
-- name    : OptGaussTomo_Supplement_mulOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:42:30.779204+00:00
-- url     : https://prove2.me/theorems/ed4539d8-595e-4165-94dd-e8623ae1b4f0
-- title:
--   Operators on $\ell^2(X)$ as coefficient arrays: products, boundedness, commutants, unitaries, projections, finite rank
-- statement:
--   Let $\mathcal H=\ell^2(X)$ for a countable index set $X$, with its standard orthonormal basis $\{|x\rangle\}$. An operator $M$ is recorded by its coefficient array $M_{ij}=\langle i|M|j\rangle$, and this definition file fixes the elementary notions used in Appendix E.1:
--
--   1. the **product** $(MN)_{ij}=\sum_k M_{ik}N_{kj}$;
--   2. $M$ is **bounded** ($M\in B(\mathcal H)$) if there is $C$ with $\|Mz\|^2\le C\|z\|^2$ for every finitely supported vector $z$;
--   3. $M$ is **positive** if every finite quadratic form $\sum_{i,j}\bar z_iM_{ij}z_j$ is real and nonnegative;
--   4. the **commutant** of a set $S$ of operators is $S'=\{M\in B(\mathcal H): MN=NM\ \text{for all } N\in S\}$;
--   5. $U$ is **unitary** if $UU^\dagger=U^\dagger U=I$;
--   6. $Q$ is an **orthogonal projection** if $Q^\dagger=Q$ and $Q^2=Q$;
--   7. $M$ has **finite rank** if $M=\sum_{k=1}^n|u_k\rangle\langle v_k|$ for finitely many $u_k,v_k\in\ell^2(X)$;
--   8. a family $(Q_k)_{k\in K}$ satisfies $\sum_kQ_k=I$ **strongly** if for every $v\in\ell^2(X)$ the finite partial sums $\sum_{k\in F}Q_kv$ converge to $v$ in norm along the finite subsets $F\subseteq K$.
--
--   These are the standard operator-theoretic notions on a separable Hilbert space, in coordinates.
--
--   **Formalization Note** The product is a `tsum`; it is used only where the series converges absolutely (bounded or trace-class factors, or a finite-rank factor), where it is the matrix of the operator product.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), App. E.1, pp.62–64 (commutant, double commutant, projections)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.RealRegisters (Hilbert)
open Matrix

namespace OptGaussTomo.Supplement

/-- **Product of coefficient arrays** (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen,
*Optimal tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version,
sha256 0f7548a2…, App. E.1, pp.62–64). An operator on the separable Hilbert space `ℓ²(X)` is
represented by its coefficient array `M i j = ⟨i|M|j⟩`; the product is
`(M N) i j = ∑ₖ M i k N k j`.

**Formalization Note.** The series is a `tsum`. It is used only for products in which it
converges absolutely (bounded times bounded, trace class times bounded, finite rank times
anything), where it is the matrix of the operator product. -/
noncomputable def mulOp {X : Type} (M N : Matrix X X ℂ) : Matrix X X ℂ :=
  fun i j => ∑' k, M i k * N k j

/-- A coefficient array is a **bounded operator** on `ℓ²(X)` (an element of `B(H)`): there is a
constant `C` with `‖M z‖² ≤ C ‖z‖²` for every finitely supported vector `z`, tested on every
finite set of output coordinates. -/
def IsBoundedCoeff {X : Type} (M : Matrix X X ℂ) : Prop :=
  ∃ C : ℝ, ∀ (s t : Finset X) (z : X → ℂ),
    ∑ i ∈ t, ‖∑ j ∈ s, M i j * z j‖ ^ 2 ≤ C * ∑ j ∈ s, ‖z j‖ ^ 2

/-- A coefficient array is **positive** (as a form): every finite quadratic form
`∑ᵢⱼ conj(zᵢ) M i j zⱼ` is real and nonnegative (the convention of the published `IsDensity`). -/
def IsPosCoeff {X : Type} (M : Matrix X X ℂ) : Prop :=
  ∀ (s : Finset X) (z : X → ℂ),
    (∑ i ∈ s, ∑ j ∈ s, star (z i) * M i j * z j).im = 0 ∧
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (z i) * M i j * z j).re

/-- The **commutant** `S′` of a set `S` of operators: the bounded operators commuting with every
element of `S` (App. E.1, p.63). -/
def commutant {X : Type} (S : Set (Matrix X X ℂ)) : Set (Matrix X X ℂ) :=
  {M | IsBoundedCoeff M ∧ ∀ N ∈ S, mulOp M N = mulOp N M}

/-- A coefficient array is **unitary**: `U U† = I` and `U† U = I` (rows and columns orthonormal). -/
def IsUnitaryCoeff {X : Type} [DecidableEq X] (U : Matrix X X ℂ) : Prop :=
  mulOp U Uᴴ = 1 ∧ mulOp Uᴴ U = 1

/-- A coefficient array is an **orthogonal projection**: `Q† = Q` and `Q Q = Q`. -/
def IsProjCoeff {X : Type} (Q : Matrix X X ℂ) : Prop :=
  Qᴴ = Q ∧ mulOp Q Q = Q

/-- A coefficient array has **finite rank**: it is a finite sum of rank-one operators
`|uₖ⟩⟨vₖ|` with `uₖ, vₖ ∈ ℓ²(X)`. -/
def IsFiniteRank {X : Type} (M : Matrix X X ℂ) : Prop :=
  ∃ (n : ℕ) (u v : Fin n → Hilbert X), ∀ i j, M i j = ∑ k, u k i * star (v k j)

/-- A family `(Q k)_{k ∈ K}` **sums to the identity strongly**, `∑ₖ Qₖ = I`: for every vector
`v ∈ ℓ²(X)` the finite partial sums `∑_{k∈F} Qₖ v` converge to `v` in the `ℓ²` norm along the
directed set of finite subsets `F ⊆ K` (unconditional convergence). -/
def SumsToIdStrongly {X K : Type} (Q : K → Matrix X X ℂ) : Prop :=
  ∀ v : Hilbert X, ∀ ε : ℝ, 0 < ε → ∃ F : Finset K, ∀ F' : Finset K, F ⊆ F' →
    ∃ w : Hilbert X, (∀ i, w i = v i - ∑ k ∈ F', ∑' j, Q k i j * v j) ∧ ‖w‖ < ε

end OptGaussTomo.Supplement


