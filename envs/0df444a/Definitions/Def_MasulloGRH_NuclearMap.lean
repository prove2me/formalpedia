-- Prove2me | Definitions.Def_MasulloGRH_NuclearMap
-- name    : MasulloGRH_NuclearMap
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T15:22:10.393826+00:00
-- url     : https://prove2.me/theorems/8b8c0a12-3cfa-45ae-810d-9b4e3465ef81
-- title:
--   Nuclear maps between locally convex spaces (Grothendieck): Banach discs and nuclear representations $T=\sum_n\lambda_n\langle\cdot,\varphi_n\rangle y_n$
-- statement:
--   This file defines **nuclear maps** between topological vector spaces in the sense of Grothendieck, together with the Banach discs and nuclear representations they are built from. All vector spaces are over $\mathbb C$; in the source $E$ and $F$ are Hausdorff locally convex spaces.
--
--   1. Let $B$ be a subset of a topological vector space $F$, and let $p_B(y)=\inf\{r>0:\ y\in rB\}$ be its Minkowski functional. $B$ is a **Banach disc** if it is non-empty, bounded, circled (balanced) and convex, and its linear span $F_B=\bigcup_{m\ge 1}mB$ equipped with $p_B$ is a Banach space: $p_B(y)=0$ only for $y=0$, and every $p_B$-Cauchy sequence in $F_B$ converges for $p_B$ to a point of $F_B$.
--   2. Let $T:E\to F$ be a continuous linear map. A **nuclear representation** of $T$ is a triple of sequences $(\lambda_n)$ in $\mathbb C$, $(\varphi_n)$ in the dual $E'$ and $(y_n)$ in $F$ such that $\sum_n|\lambda_n|<\infty$, the sequence $(\varphi_n)$ is equicontinuous, all $y_n$ lie in one Banach disc $B$ of $F$, and
--   $$Tx=\sum_{n}\lambda_n\,\langle x,\varphi_n\rangle_{E,E'}\;y_n\qquad\text{for all }x\in E.$$
--   3. $T$ is **nuclear** if it admits a nuclear representation.
--
--   The source first defines nuclearity by a factorization: $T$ is nuclear if there are a convex circled $0$-neighbourhood $U\subseteq E$ and a Banach disc $B\subseteq F$ with $T(U)\subseteq B$ such that the induced map $\widehat E_U\to F_B$ between Banach spaces is nuclear; Lemma C.3.1.2 states that this is equivalent to the existence of a representation as in item 2, which is the form used for all computations (compactness of nuclear maps, the nuclear trace $\sum_n\lambda_n\langle y_n,\varphi_n\rangle$ of §C.3.2). Nuclear maps are the building block of nuclear spaces and of the trace computations of the paper; on a Hilbert space the nuclear endomorphisms are exactly the trace-class operators.
--
--   **Formalization Note.** `MasulloGRH.IsBanachDisc B`, `MasulloGRH.IsNuclearRepr T c φ y` and `MasulloGRH.IsNuclearMap T`. Nuclearity is defined by the series characterization of Lemma C.3.1.2 (equation (C.3.1.3)), not by the factorization through $\widehat E_U\to F_B$. The sequences are indexed by $\mathbb N$ (starting at $0$) with one common index, and the series is required to converge unconditionally in $F$ (`HasSum`); since it converges absolutely in the Banach space $F_B$, this is no restriction. $p_B$ is Mathlib's `gauge B` for the underlying real vector space; boundedness is von Neumann boundedness; completeness of $(F_B,p_B)$ is expressed by Cauchy sequences. The definitions are stated for arbitrary topologies on $E$ and $F$; the theorems using them assume Hausdorff locally convex spaces.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 693–694, §C.3.1 (definition of Banach discs and of nuclear maps) and Lemma C.3.1.2, (C.3.1.3); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, 2nd ed., Springer, Ch. III, 7.1, Remark

import Mathlib

/-!
# Nuclear maps between topological vector spaces (Grothendieck)

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix C, §C.3.1
(pp. 693–694): the definition of Banach discs and of nuclear maps between locally convex spaces,
and Lemma C.3.1.2, equation (C.3.1.3), which recalls
[H. H. Schaefer, M. P. Wolff, *Topological Vector Spaces*, 2nd ed., Ch. III, 7.1, Remark].

All vector spaces are over `ℂ`.  The Minkowski functional of a set `B` is Mathlib's `gauge B`,
taken for the underlying real vector space structure: `gauge B y = inf {r > 0 | y ∈ r • B}`.

* `MasulloGRH.IsBanachDisc B`: `B` is a Banach disc, i.e. a non-empty bounded convex circled set
  whose linear span `F_B`, normed by the Minkowski functional of `B`, is a Banach space.
* `MasulloGRH.IsNuclearRepr T c φ y`: the data `(c, φ, y)` form a nuclear representation
  `T = ∑ₙ cₙ ⟨·, φₙ⟩ yₙ` of the continuous linear map `T`, as in (C.3.1.3).
* `MasulloGRH.IsNuclearMap T`: `T` is a nuclear map, i.e. it has a nuclear representation.
-/

namespace MasulloGRH

open Filter Topology

section

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- `B` is a **Banach disc** of the topological vector space `F` (§C.3.1, p. 693): a non-empty,
bounded, circled (balanced) and convex subset `B` such that its linear span `F_B = ⋃ₘ m B`,
equipped with the Minkowski functional `p_B = gauge B`, is a Banach space.  The last two clauses
say that `p_B` is a norm on `F_B` (it vanishes only at `0`) and that `(F_B, p_B)` is complete
(every `p_B`-Cauchy sequence of `F_B` converges for `p_B` to a point of `F_B`). -/
def IsBanachDisc (B : Set F) : Prop :=
  B.Nonempty ∧ Bornology.IsVonNBounded ℂ B ∧ Balanced ℂ B ∧ Convex ℝ B ∧
    (∀ y ∈ Submodule.span ℂ B, gauge B y = 0 → y = 0) ∧
    ∀ u : ℕ → F, (∀ n, u n ∈ Submodule.span ℂ B) →
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, gauge B (u m - u n) < ε) →
      ∃ y ∈ Submodule.span ℂ B, Tendsto (fun n => gauge B (u n - y)) atTop (𝓝 0)

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- `(c, φ, y)` is a **nuclear representation** of the continuous linear map `T : E → F`
(Lemma C.3.1.2, equation (C.3.1.3)): the scalars `cₙ` are absolutely summable, the continuous
linear functionals `φₙ` on `E` form an equicontinuous sequence, the vectors `yₙ` lie in one Banach
disc of `F`, and `T x = ∑ₙ cₙ φₙ(x) yₙ` for every `x ∈ E` (unconditional convergence in `F`). -/
def IsNuclearRepr (T : E →L[ℂ] F) (c : ℕ → ℂ) (φ : ℕ → StrongDual ℂ E) (y : ℕ → F) : Prop :=
  Summable (fun n => ‖c n‖) ∧
    Equicontinuous (fun (n : ℕ) (x : E) => φ n x) ∧
    (∃ B : Set F, IsBanachDisc B ∧ ∀ n, y n ∈ B) ∧
    ∀ x : E, HasSum (fun n => (c n * φ n x) • y n) (T x)

/-- The continuous linear map `T : E → F` is **nuclear** (§C.3.1 and Lemma C.3.1.2): it admits a
nuclear representation `T = ∑ₙ cₙ ⟨·, φₙ⟩ yₙ` with `∑ₙ |cₙ| < ∞`, `(φₙ)` equicontinuous in `E'`
and `(yₙ)` contained in a Banach disc of `F`. -/
def IsNuclearMap (T : E →L[ℂ] F) : Prop :=
  ∃ (c : ℕ → ℂ) (φ : ℕ → StrongDual ℂ E) (y : ℕ → F), IsNuclearRepr T c φ y

end

end MasulloGRH


