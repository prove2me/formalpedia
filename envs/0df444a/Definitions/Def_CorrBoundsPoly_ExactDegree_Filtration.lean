-- Prove2me | Definitions.Def_CorrBoundsPoly_ExactDegree_Filtration
-- name    : CorrBoundsPoly_ExactDegree_Filtration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:57:18.513376+00:00
-- url     : https://prove2.me/theorems/88cf63a8-84c9-4128-a3fb-06a1bbed1bc3
-- title:
--   §2.1 — coordinate-compatible rational filtrations of $B$, operator shifts, the associated graded space, symbols, leading shift; $h(R)$
-- statement:
--   Let $B=\mathbb F_2[x_1,\dots,x_m]/(x_i^2-x_i)$, identified by evaluation with all functions $\mathbb F_2^m\to\mathbb F_2$ (dimension $L=2^m$), and let $\mu_f:B\to B$, $g\mapsto fg$.
--
--   A **finite rationally indexed filtration** of a vector space $V$ is an increasing family $(F_s)_{s\in\mathbb Q}$ of subspaces with finitely many thresholds $q_1<\dots<q_a$: $F_s=0$ for $s<q_1$, $F_s=V$ for $s\ge q_a$, and $F_s=F_{q_i}$ for $q_i\le s<q_{i+1}$ (at a threshold the new, larger subspace is used). Write $F_{s-}=\bigcup_{u<s}F_u$. A filtration of $B$ is **coordinate-compatible** if
--   $$x_jF_s\subseteq F_{s+1}\qquad(j\in[m],\ s\in\mathbb Q).$$
--
--   A linear operator $A$ has **shift at most** $D\in\mathbb Q$ if $AF_s\subseteq F_{s+D}$ for every $s$. Its **leading shift** is the smallest such $D$. With $\operatorname{gr}_s=F_s/F_{s-}$ and the external direct sum $\operatorname{gr}_F=\bigoplus_{s\in\mathbb Q}\operatorname{gr}_s$, the **degree-$D$ symbol** of an operator $A$ of shift at most $D$ is
--   $$\operatorname{gr}_D(A):\operatorname{gr}_F\to\operatorname{gr}_F,\qquad \sum_s(u_s+F_{s-})\mapsto\sum_s(Au_s+F_{(s+D)-}),$$
--   the summand $Au_s+F_{(s+D)-}$ lying in $\operatorname{gr}_{s+D}$. When $D$ is the leading shift of $\mu_f$, $\operatorname{gr}_D(\mu_f)$ is the **leading operator** of $\mu_f$.
--
--   Finally, for an operator $R$ on a finite-dimensional space $U$, $h(R)=\dim U-2\operatorname{rank}R$ (used for square-zero $R$ in Lemma 2.2).
--
--   These are the objects of the general leading-rank criterion (Theorem 2.3).
--
--   **Formalization Note** `BFun m` is `(Fin m → ZMod 2) → ZMod 2` with pointwise operations, `coord j` is $x_j$, `mulOp f` is $\mu_f$. A `RatFiltration K V` carries `F : ℚ → Submodule K V`, monotonicity and a finite nonempty `thresholds` set with: `F s = ⊥` below every threshold, `F s = ⊤` at or above every threshold, and `F s = F u` whenever `s ≤ u` and no threshold lies in `(s, u]` (thresholds at which nothing changes are allowed; they describe the same family). `Fminus s` is `⨆ u < s, F u`, the union of the increasing family. `grPiece s` is `F s` modulo `Fminus s`, `Gr` is `DirectSum ℚ grPiece`, and `symbol Φ A D h` (it takes the proof `h` of shift at most `D`) is assembled from the induced maps `grPiece s → grPiece (s + D)`; the small lemma `map_Fminus_le` (`A F_{s−} ⊆ F_{(s+D)−}`) makes these well defined. `IsLeadingShift Φ A D` says: shift at most `D`, and shift at most `D'` for no `D' < D`. `hOp R` is `finrank U − 2 · finrank (range R)` in `ℤ`.
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), §2.1, pp. 18–20 (PDF 20–22), Eq. (2.1); §1.4, p. 18 (PDF 20); Lemma 2.2, p. 21 (PDF 23)

import Mathlib

namespace CorrBoundsPoly.ExactDegree

/-! Xin Li, *More on Correlation Bounds for Polynomials*, STOC 2027 submission (manuscript sha256
aa4ef6f7…), §2.1, pp. 18–20 (PDF 20–22), Eq. (2.1); §1.4, p. 18 (PDF 20); Lemma 2.2, p. 21.

The Boolean function algebra `B`, multiplication operators, finite rationally indexed
filtrations, coordinate compatibility, operator shifts, the associated graded space, the
degree-`D` symbol, the leading shift, and `h(R) = dim U − 2 rank R`. -/

/-- The Boolean function algebra `B = F₂[x_1,…,x_m]/(x_i² − x_i)`, identified (by evaluation, as on
p. 26) with all functions `F₂^m → F₂`, with pointwise operations. Its dimension is `L = 2^m`. -/
abbrev BFun (m : ℕ) : Type := (Fin m → ZMod 2) → ZMod 2

/-- The coordinate function `x_j ∈ B`. -/
def coord {m : ℕ} (j : Fin m) : BFun m := fun x => x j

/-- `µ_f : B → B`, `h ↦ f h`, multiplication by `f` in `B`. -/
def mulOp {m : ℕ} (f : BFun m) : BFun m →ₗ[ZMod 2] BFun m :=
  LinearMap.mulLeft (ZMod 2) f

/-- A **finite rationally indexed filtration** of a vector space `V` (p. 18): an increasing family
`(F_s)_{s ∈ ℚ}` of subspaces and a finite nonempty set of thresholds `q_1 < ⋯ < q_a` such that
`F_s = 0` before the first threshold, `F_s = V` from the last threshold on, and `F_s` is
constant on every interval `[q_i, q_{i+1})` (right-continuous: at a threshold the new subspace
is used), i.e. `F_s = F_u` whenever no threshold lies in `(s, u]`. -/
structure RatFiltration (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  /-- the subspace `F_s` of elements of weight at most `s` -/
  F : ℚ → Submodule K V
  mono : Monotone F
  /-- the finitely many thresholds at which the subspace may change -/
  thresholds : Finset ℚ
  thresholds_nonempty : thresholds.Nonempty
  eq_bot_below : ∀ s : ℚ, (∀ q ∈ thresholds, s < q) → F s = ⊥
  eq_top_above : ∀ s : ℚ, (∀ q ∈ thresholds, q ≤ s) → F s = ⊤
  const_between : ∀ s u : ℚ, s ≤ u → (∀ q ∈ thresholds, ¬ (s < q ∧ q ≤ u)) → F s = F u

namespace RatFiltration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `F_{s−} = ⋃_{u < s} F_u` (a union of an increasing family, hence its supremum). -/
def Fminus (Φ : RatFiltration K V) (s : ℚ) : Submodule K V :=
  ⨆ (u : ℚ) (_ : u < s), Φ.F u

/-- A linear operator `A` has **shift at most** `D ∈ ℚ` if `A F_s ⊆ F_{s+D}` for every `s`. -/
def HasShiftLE (Φ : RatFiltration K V) (A : V →ₗ[K] V) (D : ℚ) : Prop :=
  ∀ s : ℚ, (Φ.F s).map A ≤ Φ.F (s + D)

/-- `D` is the **leading shift** of `A`: `A` has shift at most `D` and has shift at most `D'` for no
`D' < D` (D is the smallest shift bound, i.e. the largest weight increase that actually occurs). -/
def IsLeadingShift (Φ : RatFiltration K V) (A : V →ₗ[K] V) (D : ℚ) : Prop :=
  Φ.HasShiftLE A D ∧ ∀ D' : ℚ, D' < D → ¬ Φ.HasShiftLE A D'

/-- The graded piece `gr_s = F_s / F_{s−}` (quotient of the subspace `F_s` by `F_{s−} ∩ F_s`,
which is `F_{s−}` since the family is increasing). -/
abbrev grPiece (Φ : RatFiltration K V) (s : ℚ) : Type _ :=
  ↥(Φ.F s) ⧸ (Φ.Fminus s).comap (Φ.F s).subtype

/-- The associated graded space `gr_F = ⨁_{s ∈ ℚ} F_s / F_{s−}` (external direct sum, finitely
supported tuples). -/
abbrev Gr (Φ : RatFiltration K V) : Type _ :=
  DirectSum ℚ fun s => Φ.grPiece s

/-- Structural fact used to define the symbol: shift at most `D` sends `F_{s−}` into
`F_{(s+D)−}` (p. 20, first display of the proof of Lemma 2.1). -/
theorem map_Fminus_le (Φ : RatFiltration K V) {A : V →ₗ[K] V} {D : ℚ} (h : Φ.HasShiftLE A D)
    (s : ℚ) : (Φ.Fminus s).map A ≤ Φ.Fminus (s + D) := by
  unfold Fminus
  rw [Submodule.map_le_iff_le_comap]
  refine iSup₂_le fun u hu => ?_
  rw [← Submodule.map_le_iff_le_comap]
  exact (h u).trans (le_iSup₂_of_le (u + D) (by linarith) le_rfl)

/-- The component `T_s : F_s/F_{s−} → F_{s+D}/F_{(s+D)−}`, `u + F_{s−} ↦ A u + F_{(s+D)−}`. -/
noncomputable def symbolPiece (Φ : RatFiltration K V) {A : V →ₗ[K] V} {D : ℚ}
    (h : Φ.HasShiftLE A D) (s : ℚ) : Φ.grPiece s →ₗ[K] Φ.grPiece (s + D) :=
  Submodule.mapQ _ _
    (A.restrict (p := Φ.F s) (q := Φ.F (s + D)) fun x hx => h s (Submodule.mem_map_of_mem hx))
    (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hx ⊢
      exact Φ.map_Fminus_le h s (Submodule.mem_map_of_mem hx))

/-- The **degree-`D` symbol** (degree-`D` graded operator) `gr_D(A) : gr_F → gr_F`,
`∑_s (u_s + F_{s−}) ↦ ∑_s (A u_s + F_{(s+D)−})`, of an operator `A` of shift at most `D`. When
`D` is the leading shift of `µ_f`, this is the **leading operator** of `µ_f`. -/
noncomputable def symbol (Φ : RatFiltration K V) (A : V →ₗ[K] V) (D : ℚ)
    (h : Φ.HasShiftLE A D) : Φ.Gr →ₗ[K] Φ.Gr :=
  DirectSum.toModule K ℚ Φ.Gr fun s =>
    (DirectSum.lof K ℚ (fun s => Φ.grPiece s) (s + D)) ∘ₗ Φ.symbolPiece h s

end RatFiltration

/-- **Coordinate compatibility, Eq. (2.1)**: `x_j F_s ⊆ F_{s+1}` for every `j ∈ [m]` and `s ∈ ℚ`. -/
def CoordCompatible {m : ℕ} (Φ : RatFiltration (ZMod 2) (BFun m)) : Prop :=
  ∀ (j : Fin m) (s : ℚ), ∀ g ∈ Φ.F s, coord j * g ∈ Φ.F (s + 1)

/-- `h(R) = dim U − 2 rank R` for an operator `R` on a finite-dimensional space `U` (Lemma 2.2,
p. 21; it is used for square-zero `R`). -/
noncomputable def hOp {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
    (R : U →ₗ[K] U) : ℤ :=
  (Module.finrank K U : ℤ) - 2 * (Module.finrank K (LinearMap.range R) : ℤ)

end CorrBoundsPoly.ExactDegree


