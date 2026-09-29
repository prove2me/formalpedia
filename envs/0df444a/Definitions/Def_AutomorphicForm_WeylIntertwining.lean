-- Prove2me | Definitions.Def_AutomorphicForm_WeylIntertwining
-- name    : AutomorphicForm_WeylIntertwining
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/f80c2dec-e752-5585-bb00-1b903120f09e
-- title:
--   Weyl element and adelic unipotent intertwining integral for GL2​
-- statement:
--   Over a field $K$, `gl2Weyl` is the element of $\mathrm{GL}_2(K)$ given by the matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, packaged as a unit with itself as two-sided inverse; the accompanying lemmas record that its underlying matrix is $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and that it is its own inverse in $\mathrm{GL}_2(K)$, i.e. the unsigned Weyl representative is an involution. The remaining definitions are made over a Dedekind domain $R$ with fraction field $K$, with a measurable space structure fixed on the adele ring $\mathbb{A} =$ `NumberField.AdeleRing R K`. Here `adelicWeyl` is the image of `gl2Weyl` under `globalPoints`, the group homomorphism $\mathrm{GL}_2(K) \to \mathrm{GL}_2(\mathbb{A})$ induced entrywise by the structure map $K \to \mathbb{A}$; thus it is $w = \begin{pmatrix}0&1\\1&0\end{pmatrix}$ viewed adelically.
--
--   Given a measure $\nu$ on $\mathbb{A}$, a function $f : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ and $g \in \mathrm{GL}_2(\mathbb{A})$, `weylIntertwiningIntegral` is the Bochner integral
--   $$\int_{\mathbb{A}} f\bigl(w^{-1}\, u(x)\, g\bigr)\, d\nu(x),$$
--   where $u(x) =$ `unipotentGL2 x` is $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, so that the unipotent radical is parametrised by the additive group of $\mathbb{A}$ and integration takes place over that parameter rather than over a quotient. The measure is an arbitrary argument, with no Haar or invariance hypothesis imposed. Two degenerate evaluations are proved: for a probability measure the integral of the constant function $c$ is $c$ at every $g$, and against the zero measure the integral vanishes for every $f$ and $g$. No integrability, convergence, meromorphic continuation or intertwining statement is asserted.
--
--   **Relation to Mathlib.** Mathlib supplies `Matrix.GeneralLinearGroup` and the adele ring; the Weyl representative, its adelic image and the unipotent intertwining integral are the project's own notions, built on the project's `globalPoints` and `unipotentGL2`.
--
--   **Where it is used.** These are part of the project's vocabulary for automorphic forms on adelic $\mathrm{GL}_2$, alongside the constant-term integral along the adelic unipotent subgroup and the cuspidality predicate, which enter the automorphic side of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_WeylIntertwining.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Matrix MeasureTheory

namespace AutomorphicForm

section WeylElement

variable {K : Type*} [Field K]

def gl2Weyl : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[simp] theorem gl2Weyl_val :
    ((gl2Weyl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

theorem gl2Weyl_inv : (gl2Weyl : GL (Fin 2) K)⁻¹ = gl2Weyl := Units.ext rfl

end WeylElement

section Intertwining

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [MeasurableSpace (NumberField.AdeleRing R K)]

def adelicWeyl : AdelicGL2 R K :=
  globalPoints R K gl2Weyl

def weylIntertwiningIntegral (ν : Measure (NumberField.AdeleRing R K))
    (f : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) : ℂ :=
  ∫ x, f ((adelicWeyl R K)⁻¹ * unipotentGL2 x * g) ∂ν

theorem weylIntertwiningIntegral_const (ν : Measure (NumberField.AdeleRing R K))
    [IsProbabilityMeasure ν] (c : ℂ) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K ν (fun _ => c) g = c := by
  unfold weylIntertwiningIntegral
  simp [integral_const, measureReal_def]

theorem weylIntertwiningIntegral_zero_measure (f : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K 0 f g = 0 := by
  unfold weylIntertwiningIntegral
  simp

end Intertwining

end AutomorphicForm


