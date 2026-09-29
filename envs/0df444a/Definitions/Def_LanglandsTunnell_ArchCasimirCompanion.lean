-- Prove2me | Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
-- name    : LanglandsTunnell_ArchCasimirCompanion
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/238f2dce-8959-56ae-9d6a-48632e78f27c
-- title:
--   Casimir operator and eigenvalue condition for real archimedean data
-- statement:
--   Fix a real archimedean parameter $P$ (`RealArchParam`, either a principal parameter $(u_1,a_1,u_2,a_2)$ or a discrete one $(u,k)$ with $1\le k$) and work with functions $W$ on $2\times 2$ real matrices with values in $\mathbb{C}$.
--
--   For each of the three directions `H`, `E`, `Fm` of [`AutomorphicForm.ArchDir`](../def/AutomorphicForm_ArchDerivCasimir.html#L67) there is a one-parameter subgroup of $\mathrm{GL}_2(\mathbb{R})$, namely `archFlowMatrix`: $t\mapsto \operatorname{diag}(e^{t},e^{-t})$, $t \mapsto \begin{pmatrix}1&t\\0&1\end{pmatrix}$ and $t \mapsto \begin{pmatrix}1&0\\t&1\end{pmatrix}$ respectively. `matrixFlowDeriv d W` is the right-translation derivative along the $d$-th of these, the function $x \mapsto \frac{d}{dt}\big|_{t=0} W\big(x\cdot \mathrm{archFlowMatrix}\,d\,t\big)$, taken with Mathlib's `deriv` of a function of one real variable, so it is defined (as $0$) also where no derivative exists. `matrixCasimir W` is the combination
--   $$-\Big(\tfrac14 D_H D_H W - \tfrac12 D_H W + D_E D_{Fm} W\Big),$$
--   with $D_H, D_E, D_{Fm}$ the three flow derivatives; this is term for term the normalisation used for the adelic operator `archCasimirAt` at a real place.
--
--   For a datum $d : \mathrm{ArchDatumR}\ P$ — whose fields give a Whittaker-type function $W$, smooth on the invertible locus, with a unipotent transformation law, a central law, an entire zeta package with functional equation and finite order, and decay bounds, but no differential equation — the predicate `IsCasimirEigen d` asserts the missing spectral law: for every real $2\times2$ matrix $x$ with $\det x \neq 0$,
--   $$(\mathrm{matrixCasimir}\ W)(x) = P.\mathrm{laplaceEigenvalue}\cdot W(x),$$
--   where the eigenvalue is $\tfrac14-\big(\tfrac{u_1-u_2}{2}\big)^2$ in the principal case and $(1-k^2)/4$ in the discrete case.
--
--   Auxiliary results record that both `matrixFlowDeriv` and `matrixCasimir` annihilate constants, construct `zeroDatum P`, the datum with $W\equiv 0$ (all structure fields satisfied with zeta function identically $0$ and abscissa $0$), and verify that it satisfies `IsCasimirEigen`, so the predicate is inhabited for every $P$.
--
--   **Relation to Mathlib.** Mathlib has no Casimir operator for $\mathrm{GL}_2$ or archimedean Whittaker data; these notions are the project's own, built on Mathlib's one-variable `deriv`.
--
--   **Where it is used.** The predicate supplies the archimedean differential equation that the real Whittaker data entering the converse-theorem construction of automorphic forms on $\mathrm{GL}_2$ must satisfy, matching the chosen archimedean parameter; that construction is what turns the Langlands–Tunnell $L$-data into an automorphic form, and hence gives modularity of the mod $3$ representation used in the proof of Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_ArchCasimirCompanion.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.Converse.ArchCasimir

def matrixFlowDeriv (d : AutomorphicForm.ArchDir) (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ → ℂ :=
  fun x => deriv (fun t : ℝ => W (x * (AutomorphicForm.archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ))) 0

def matrixCasimir (W : Matrix (Fin 2) (Fin 2) ℝ → ℂ) : Matrix (Fin 2) (Fin 2) ℝ → ℂ :=
  -((1 / 4 : ℂ) • matrixFlowDeriv .H (matrixFlowDeriv .H W) - (1 / 2 : ℂ) • matrixFlowDeriv .H W +
    matrixFlowDeriv .E (matrixFlowDeriv .Fm W))

def IsCasimirEigen {P : RealArchParam} (d : ArchDatumR P) : Prop :=
  ∀ x : Matrix (Fin 2) (Fin 2) ℝ, x.det ≠ 0 → matrixCasimir d.W x = P.laplaceEigenvalue * d.W x

theorem matrixFlowDeriv_const (d : AutomorphicForm.ArchDir) (c : ℂ) :
    matrixFlowDeriv d (fun _ => c) = fun _ => 0 := by
  funext x
  simp [matrixFlowDeriv]

theorem matrixCasimir_const (c : ℂ) : matrixCasimir (fun _ => c) = fun _ => 0 := by
  funext x
  simp [matrixCasimir, matrixFlowDeriv_const]

def zeroDatum (P : RealArchParam) : ArchDatumR P where
  W := fun _ => 0
  smooth := show ContDiffOn ℝ (⊤ : ℕ∞) (fun _ => (0 : ℂ)) ArchR.glSet from contDiffOn_const
  unip_law := fun _ _ => (mul_zero _).symm
  central_law := fun _ _ _ => (mul_zero _).symm
  zetaEntire := fun _ _ _ _ => 0
  zetaEntire_differentiable := fun _ _ _ => differentiable_const 0
  zeta_abscissa := 0
  zeta_integrable := fun g u a s _ _ => by
    have h : ArchR.zetaIntegrand (fun _ => (0 : ℂ)) g u a s = fun _ => 0 := funext fun y => by
      simp [ArchR.zetaIntegrand]
    rw [h]
    exact MeasureTheory.integrable_zero _ _ _
  zeta_eq := fun _ _ _ _ _ _ => by simp [ArchR.zetaIntegrand]
  functional_equation := fun _ _ _ _ _ => (mul_zero _).symm
  zetaEntire_finiteOrder := fun _ _ _ _ _ => ⟨0, 0, fun _ _ _ => by simp⟩
  decay_top := fun _ _ => ⟨0, fun _ _ _ _ => by
    rw [show ArchR.asPi (fun _ => (0 : ℂ)) = fun _ => 0 from rfl, iteratedFDerivWithin_fun_zero]
    simp⟩
  decay_zero := fun _ => ⟨0, 0, fun _ _ _ _ _ => by
    rw [show ArchR.asPi (fun _ => (0 : ℂ)) = fun _ => 0 from rfl, iteratedFDerivWithin_fun_zero]
    simp⟩

theorem isCasimirEigen_zero (P : RealArchParam) : IsCasimirEigen (zeroDatum P) := by
  intro x _
  show matrixCasimir (fun _ => (0 : ℂ)) x = P.laplaceEigenvalue * 0
  rw [matrixCasimir_const]
  simp

end LanglandsTunnell.Converse.ArchCasimir

end


