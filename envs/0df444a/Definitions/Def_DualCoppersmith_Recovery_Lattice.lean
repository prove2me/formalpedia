-- Prove2me | Definitions.Def_DualCoppersmith_Recovery_Lattice
-- name    : DualCoppersmith_Recovery_Lattice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:54:35.324546+00:00
-- url     : https://prove2.me/theorems/23ccf162-882d-4340-a048-9704ba6f2969
-- title:
--   Modular kernel, integral scaling and root vector
-- statement:
--   Let $A$ be the matrix of the total-degree shifts, with $n$ monomial columns. Define
--
--   $$K=\{z\in\mathbb Z^n:Az\equiv0\pmod{p^m}\},\qquad \rho=\operatorname{lcm}_{\alpha\in T_t}X^\alpha,\qquad L_X^\perp=\{((\rho/X^\alpha)z_\alpha)_\alpha:z\in K\}.$$
--
--   The diagonal factors are the exact positive integer quotients $\rho/X^\alpha$. For statements about an integer vector $r$, the module also defines $z_r=(r^\alpha)_\alpha$ and $v_r=((\rho/X^\alpha)r^\alpha)_\alpha$. These are derived objects, not input data for the recovery algorithm.
--
--   The kernel is an actual integer submodule cut out by divisibility of each matrix-row pairing. Its real embedding and diagonal image define the Euclidean lattice. Since $p^m\mathbb Z^n\subseteq K$, it has full rank; positivity of the bounds makes every diagonal factor positive. These facts follow from the construction and are not instance fields. Trivial $p^m x^\alpha$ rows impose no further modular conditions.
-- source:
--   Taehun Kang, Jebin Kim, Changmin Lee, JeongHwan Lee, STOC 2027 submission #1253 (October 2026), p. 8, Definition 3.1 and root-vector display (PDF p. 9)

import Mathlib
import Definitions.Def_DualCoppersmith_Recovery_Instance
import Definitions.Def_LLLFactor_RedBasis_Setting

set_option autoImplicit false

namespace DualCoppersmith.Recovery

open LLLFactor.RedBasis

noncomputable def integerKernel (I : Instance) (P : Parameters I) :
    Submodule ℤ (Fin (dimension I P) → ℤ) where
  carrier := {z | ∀ q, (I.p : ℤ) ^ P.m ∣ ∑ j, coefficientMatrix I P q j * z j}
  zero_mem' := by simp
  add_mem' := by
    intro z y hz hy q
    simpa only [Pi.add_apply, mul_add, Finset.sum_add_distrib] using dvd_add (hz q) (hy q)
  smul_mem' := by
    intro c z hz q
    simpa only [Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum]
      using dvd_mul_of_dvd_right (hz q) c

noncomputable def integerEmbedding (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] Vec n where
  toFun z := WithLp.toLp 2 (fun j => (z j : ℝ))
  map_add' := by intro z y; ext j; simp
  map_smul' := by intro c z; ext j; simp

noncomputable def kernelLattice (I : Instance) (P : Parameters I) :
    Submodule ℤ (Vec (dimension I P)) :=
  (integerKernel I P).map (integerEmbedding (dimension I P))

noncomputable def boundMonomial (I : Instance) (P : Parameters I)
    (j : Fin (dimension I P)) : ℕ :=
  ∏ i, I.X i ^ (exponent I P j i)

noncomputable def rho (I : Instance) (P : Parameters I) : ℕ :=
  Finset.univ.lcm (boundMonomial I P)

/-- Exact integer quotient; every denominator divides the positive lcm. -/
noncomputable def diagonalFactor (I : Instance) (P : Parameters I)
    (j : Fin (dimension I P)) : ℕ :=
  rho I P / boundMonomial I P j

noncomputable def diagonalMap (I : Instance) (P : Parameters I) :
    Vec (dimension I P) →ₗ[ℝ] Vec (dimension I P) where
  toFun v := WithLp.toLp 2 (fun j => (diagonalFactor I P j : ℝ) * v j)
  map_add' := by intro v w; ext j; simp [mul_add]
  map_smul' := by intro c v; ext j; simp [mul_left_comm]

/-- Definition 3.1: image of the actual modular kernel under the diagonal map. -/
noncomputable def scaledLattice (I : Instance) (P : Parameters I) :
    Submodule ℤ (Vec (dimension I P)) :=
  (kernelLattice I P).map ((diagonalMap I P).restrictScalars ℤ)

noncomputable def monomialRoot (I : Instance) (P : Parameters I)
    (r : Fin I.ell → ℤ) : Fin (dimension I P) → ℤ :=
  fun j => ∏ i, r i ^ (exponent I P j i)

noncomputable def rootVector (I : Instance) (P : Parameters I)
    (r : Fin I.ell → ℤ) : Vec (dimension I P) :=
  diagonalMap I P (integerEmbedding (dimension I P) (monomialRoot I P r))

end DualCoppersmith.Recovery


