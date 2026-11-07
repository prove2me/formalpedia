-- Prove2me | Definitions.Def_LIPAlgorithm_minShell
-- name    : LIPAlgorithm_minShell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:51.988913+00:00
-- url     : https://prove2.me/theorems/4c172975-2fbf-4977-9c4c-a2a92680173c
-- title:
--   The shortest-vector shell, well-rounded and integral lattices, $\mathrm{Iso}(L_1,L_2)$
-- statement:
--   For a lattice $L\subset\mathbb R^n$, the shell is $\mathrm{Min}(L)=\{x\in L:\|x\|=\lambda_1(L)\}$. The lattice is **well-rounded** if $\mathrm{span}(\mathrm{Min}(L))=\mathrm{span}(L)$, and **integral** if $\langle x,y\rangle\in\mathbb Z$ for all $x,y\in L$. For full-rank lattices,
--
--   $$\mathrm{Iso}(L_1,L_2)=\{O\in O_n(\mathbb R):OL_1=L_2\}.$$
--
--   The whole analysis of the algorithm runs on the shell of a well-rounded lattice.
--
--   **Formalization Note** $\lambda_1$ is the published $\texttt{RegevLWE.SmoothingLB.lambda1}$. The shell excludes $0$, which matters only for the rank-zero lattice.
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), §2.1, p.9; Definition 2.3, p.10

import Mathlib
import Definitions.Def_RegevLWE_SmoothingLB_Lattice

namespace LIPAlgorithm

/-- Euclidean `n`-space, where the paper's lattices live (§2.1, p.9). -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The shortest-vector shell `Min(L) = {x ∈ L : ‖x‖ = λ₁(L)}` (§2.1, p.9).

**Formalization Note.** The clause `x ≠ 0` changes nothing for a lattice of rank `n ≥ 1`, where
`λ₁(L) > 0`. It only keeps the shell of the rank-zero lattice empty, where `λ₁` is the `sInf` of the empty
set. -/
def minShell {n : ℕ} (L : Submodule ℤ (E n)) : Set (E n) :=
  {x | x ∈ L ∧ x ≠ 0 ∧ ‖x‖ = RegevLWE.SmoothingLB.lambda1 L}

/-- "A lattice is well-rounded if span(Min(L)) = span(L)" (§2.1, p.9). -/
def IsWellRounded {n : ℕ} (L : Submodule ℤ (E n)) : Prop :=
  Submodule.span ℝ (minShell L) = Submodule.span ℝ (L : Set (E n))

/-- "We work with integral lattices: ⟨x, y⟩ ∈ Z for all x, y ∈ L" (§2.1, p.9). -/
def IsIntegralLattice {n : ℕ} (L : Submodule ℤ (E n)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, ∃ z : ℤ, inner ℝ x y = (z : ℝ)

/-- `Iso(L₁, L₂) = {O ∈ Oₙ(ℝ) : OL₁ = L₂}` (Definition 2.3, p.10).

**Formalization Note.** `Oₙ(ℝ)` is the type of linear isometric equivalences of `ℝⁿ`. -/
def isoLat {n : ℕ} (L₁ L₂ : Submodule ℤ (E n)) : Set (E n ≃ₗᵢ[ℝ] E n) :=
  {O | (fun x => O x) '' (L₁ : Set (E n)) = (L₂ : Set (E n))}

end LIPAlgorithm


