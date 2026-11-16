-- Prove2me | Definitions.Def_SuperRamanujan227_Main_Supplement_LPS
-- name    : SuperRamanujan227_Main_Supplement_LPS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:43:53.769612+00:00
-- url     : https://prove2.me/theorems/bbef031a-2525-4a0c-829b-0bee937185ca
-- title:
--   Arithmetic LPS Cayley adjacency with both projective vertex groups
-- statement:
--   For distinct primes $p,q\equiv1\pmod4$, choose $\iota\in\mathbb F_q$ with $\iota^2=-1$. The generators are all integral quadruples $(a_0,a_1,a_2,a_3)$ of squared norm $p$, with $a_0>0$ odd and the other coordinates even. Each gives the projective class of
--
--   $$
--   \begin{pmatrix}a_0+\iota a_1&a_2+\iota a_3\\-a_2+\iota a_3&a_0-\iota a_1\end{pmatrix}.
--   $$
--
--   The vertex set consists of determinant-square classes in $\operatorname{PGL}_2(\mathbb F_q)$ when $p$ is a square modulo $q$, and all projective classes otherwise. The first group is canonically $\operatorname{PSL}_2(\mathbb F_q)$. For vertices $u,v$, the adjacency entry counts the generator quadruples whose projective matrix takes $u$ to $v$ by right multiplication. Multiplicities are retained even when distinct quadruples have the same projective image. The published quaternion shell supplies the finite norm-$p$ labels with positive odd real coordinate; the imaginary coordinates are explicitly filtered to be even, as in the source. For $p\equiv1\pmod4$, their evenness also follows from the norm congruence, so the filter discards no source generator. Its finite search box $[-p,p]^4$ contains every generator. Invertibility is tested by existence of a general-linear representative; admissible parameters give determinant $p\ne0$, so no generator is lost.
--
--   The actual finite vertex set is enumerated by $\operatorname{Fin}(n)$, where $n$ is its cardinality, and the two-sided parameter uses the spectral definition above. The number of vertices is $q(q^2-1)/2$ or $q(q^2-1)$ according to the residue case. Conjugate generator pairs give inverse labels and count loops twice. No connectedness, regularity, Hecke realization, or spectral bound is an assumption of this definition. This is the arithmetic object needed to state A.1 for the entire family.
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), pp. 25–27, Appendix A, construction X^{p,q} as in [LPS88] and [DSV03] cited there

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Definitions.Def_SuperRamanujan227_Main_Supplement_Spectral

namespace SuperRamanujan227.Main.Supplement

/-- Reduction of the Hamilton quaternion through a chosen square root i of -1 modulo q. -/
def quaternionMatrix (q : ℕ) (i : ZMod q) (a : QEC.Coding.TannerLiftedProduct.LPSQuaternion) :
    Matrix (Fin 2) (Fin 2) (ZMod q) :=
  !![(a.a : ZMod q) + i * a.b, (a.c : ZMod q) + i * a.d;
     -(a.c : ZMod q) + i * a.d, (a.a : ZMod q) - i * a.b]

/-- PSL₂ when p is a square modulo q; PGL₂ otherwise. No expansion property is assumed. -/
def LPSVertex (p q : ℕ) :=
  {g : Matrix.ProjGenLinGroup (Fin 2) (ZMod q) // IsSquare (p : ZMod q) → QEC.Coding.BalancedProduct.LPSArithmetic.ProjectiveDetIsSquare g}

instance lpsPGLFinite (q : ℕ) [Fact q.Prime] :
    Finite (Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

noncomputable instance lpsVertexFintype (p q : ℕ) [Fact q.Prime] : Fintype (LPSVertex p q) :=
  by
    unfold LPSVertex
    exact Fintype.ofFinite _

/-- Actual number of vertices. Equal to q(q²-1)/2 in the residue case and q(q²-1) otherwise. -/
noncomputable def lpsOrder (p q : ℕ) [Fact q.Prime] : ℕ := Fintype.card (LPSVertex p q)

/-- Actual Cayley adjacency multiplicity: count quaternion generators, not distinct projective
images. Invertibility is tested rather than assumed; for admissible p≠q every generator has
determinant p≠0. Inverse generators pair loops, so the diagonal counts loops twice. -/
noncomputable def lpsAdj (p q : ℕ) (i : ZMod q) (u v : LPSVertex p q) : ℕ := by
  classical
  exact ((QEC.Coding.TannerLiftedProduct.lpsQuaternionShell p).filter fun a =>
    Even a.b ∧ Even a.c ∧ Even a.d ∧ ∃ A : Matrix.GeneralLinearGroup (Fin 2) (ZMod q),
      (A : Matrix (Fin 2) (Fin 2) (ZMod q)) = quaternionMatrix q i a ∧
      u.val * Matrix.ProjGenLinGroup.mk A = v.val).card

/-- Relabel the actual vertex set by Fin n; no graph properties enter the enumeration. -/
noncomputable def lpsAdjFin (p q : ℕ) [Fact q.Prime] (i : ZMod q) :
    Matrix (Fin (lpsOrder p q)) (Fin (lpsOrder p q)) ℕ :=
  fun u v => lpsAdj p q i ((Fintype.equivFin (LPSVertex p q)).symm u)
    ((Fintype.equivFin (LPSVertex p q)).symm v)

/-- The actual two-sided spectral parameter of X^{p,q}, using the published root ordering. -/
noncomputable def lpsLambda (p q : ℕ) [Fact q.Prime] (i : ZMod q) : ℝ :=
  nontrivialRadius (lpsAdjFin p q i)

end SuperRamanujan227.Main.Supplement


