-- Prove2me | Definitions.Def_TFIMPhaseDiagram_Classical_traceSetup
-- name    : TFIMPhaseDiagram_Classical_traceSetup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:02:51.495876+00:00
-- url     : https://prove2.me/theorems/fc0adce3-e545-4cc2-a421-7fd32f6f210f
-- title:
--   Trace-identity setup and genuine matrix norms
-- statement:
--   For a Pauli string $P$, define $S=\{i:P_i\in\{X,Y\}\}$, its number of $Y$ factors, the product path measure $\nu$, and the longitudinally tilted product cycle measure $\widetilde\nu$. These use the laws shared by every statement.
--   $$\nu=\bigotimes_i\nu_{\eta_i,1_{i\in S}},\qquad \widetilde\nu=\bigotimes_iT_{(h_i/M)\mathbf1}\widehat\nu_i.$$
--   The Trotter constant is $2\max_i(\sum_{j\ne i}|J_{ij}|+|h_i|)$. The complex Euclidean operator norm is the supremum of $\|Ax\|_2$ on the unit sphere, and the Schatten-1 norm is the sum of the square roots of the eigenvalues of $A^\dagger A$.
--
--   These are the source's norms, rather than the entrywise matrix norm. They are used in positive dimensions only.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, (6)–(9), pp.6–7; §2, p.5; Proposition 32, p.27

import Definitions.Def_TFIMPhaseDiagram_Classical_cycles

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
attribute [local instance] Classical.propDecidable

def flipSet {n : ℕ} (P : Fin n → Pauli) : Finset (Fin n) :=
  Finset.univ.filter (fun i => hasFlip (P i))
def yCount {n : ℕ} (P : Fin n → Pauli) : ℕ := (Finset.univ.filter (fun i => P i = .Y)).card
def nu {n : ℕ} (η : Fin n → ℝ) (P : Fin n → Pauli) : Measure (Fin n → PathData) :=
  Measure.pi (fun i => pathLaw (η i) (hasFlip (P i)))
def nuTilde {n M : ℕ} (h η : Fin n → ℝ) (P : Fin n → Pauli) : Measure (Fin n → Spins M) :=
  Measure.pi (fun i => pathCycleLaw (η i) (hasFlip (P i)) (fun _ => .finite (h i / M)))
def trotterConstant {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : ℝ :=
  2 * ⨆ i, ((∑ j ∈ Finset.univ.erase i, |J i j|) + |h i|)

def euclideanOpNorm {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  sSup {r | ∃ x : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧
    r = ‖WithLp.toLp 2 (A.mulVec (fun i => x i))‖}
def schattenOne {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i)
end TFIMPhaseDiagram.Classical


