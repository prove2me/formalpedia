-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
-- name    : LanglandsTunnell_CubicInduction_JacquetVector3
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/461403fb-9ecf-5f3e-8456-e07d305f3dc4
-- title:
--   Gaussians and archimedean Jacquet vectors for cubic induction
-- statement:
--   Four definitions and two identities, all in the namespace `LanglandsTunnell.CubicInduction`, set up the archimedean ingredients of a Godement-type integral on $2\times 3$ and $3\times 3$ real matrices. First, `gaussian3` sends a real $2\times 3$ matrix $M$ to $\exp\bigl(-\pi\sum_{i\in\mathrm{Fin}\,2}\sum_{b\in\mathrm{Fin}\,3}M_{ib}^{2}\bigr)$, viewed as a complex number, and `polyGauss3` is the set of those functions $S$ on real $2\times 3$ matrices which are of the form $M\mapsto p\bigl((M_{ib})_{i,b}\bigr)\cdot\mathrm{gaussian3}(M)$ for some polynomial $p$ in the six entries with complex coefficients; `gaussian3_mem_polyGauss3` records that the Gaussian itself lies in this set.
--
--   Next, for an additive character $\psi$ of the infinite adele ring of $\mathbb{Q}$, a function $S$ as above, a real $2\times 2$ matrix $h$ and a real $3\times 3$ matrix $m$, `godementInner3` is the integral over $v\in\mathbb{R}^{2}$ of $S\bigl(h\cdot N(v)\bigr)\,\psi(-v_{1})$, where $N(v)$ is the $2\times 3$ matrix with rows $m_{0\bullet}+v_{0}m_{2\bullet}$ and $m_{1\bullet}+v_{1}m_{2\bullet}$, and $-v_{1}$ is sent into the infinite adeles by the real embedding [`AutomorphicForm.StandardKernel.ofReal`](../def/AutomorphicForm_SmoothingKernel.html#L774). Given in addition a real archimedean parameter $P$ with datum $D$ (whose field `D.W` is the Whittaker function on real $2\times 2$ matrices), a complex exponent $u_{3}$, a sign $a_{3}\in\mathbb{Z}/2$, a real $a$ and $g\in \mathrm{GL}_3$ of the infinite adeles of $\mathbb{Q}$, `jacquetIntegrand3` is the function of a real $2\times 2$ array $e$ given by
--   $$\mathrm{godementInner3}(\psi,S,e,\mathrm{realMat}(g))\cdot\mathrm{quasiChar}(u_{3}+2,a_{3})(\det e)\cdot|\det e|^{-2}\cdot D.W\bigl(\mathrm{diagOne}(a)\,e^{-1}\bigr),$$
--   where $\mathrm{quasiChar}(u,a)(y)=|y|^{u}$ times $\mathrm{sign}(y)$ when $a\neq 0$, $\mathrm{diagOne}(a)=\begin{pmatrix}a&0\\0&1\end{pmatrix}$, and $\mathrm{realMat}(g)$ is the real $3\times 3$ matrix of entries of $g$ at the real place. Finally `jacquetVector3` multiplies $\mathrm{quasiChar}(u_{3}+1,a_{3})(\det \mathrm{realMat}(g))$ by the integral of this integrand over all real $2\times 2$ arrays, and `jacquetVector3_eq` states that equality as a lemma. No integrability hypotheses are imposed: the Bochner integrals are taken as they stand.
--
--   **Relation to Mathlib.** Mathlib has Gaussian integrals and Schwartz space but no space of polynomial-times-Gaussian functions on $2\times 3$ matrices, and no Godement–Jacquet or Whittaker-vector machinery; all the notions here are the project's own.
--
--   **Where it is used.** These are the archimedean local data for the $\mathrm{GL}_3$ integrals used in the cubic-induction part of the route to the Langlands–Tunnell theorem, which in turn supplies the modularity of the mod $3$ representation needed to start the Frey-curve argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_JacquetVector3.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_SmoothingKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField LanglandsTunnell.Converse LanglandsTunnell.Converse.ArchR

namespace LanglandsTunnell.CubicInduction

def gaussian3 (M : Matrix (Fin 2) (Fin 3) ℝ) : ℂ :=
  (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ b : Fin 3, M i b ^ 2)) : ℂ)

def polyGauss3 : Set (Matrix (Fin 2) (Fin 3) ℝ → ℂ) :=
  {S | ∃ p : MvPolynomial (Fin 2 × Fin 3) ℂ,
    S = fun M => MvPolynomial.eval (fun v : Fin 2 × Fin 3 => ((M v.1 v.2 : ℝ) : ℂ)) p * gaussian3 M}

theorem gaussian3_mem_polyGauss3 : gaussian3 ∈ polyGauss3 :=
  ⟨MvPolynomial.C 1, by funext M; simp⟩

def godementInner3 (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (h : Matrix (Fin 2) (Fin 2) ℝ) (m : Matrix (Fin 3) (Fin 3) ℝ) : ℂ :=
  ∫ v : Fin 2 → ℝ,
    S (h * Matrix.of ![fun b => m 0 b + v 0 * m 2 b, fun b => m 1 b + v 1 * m 2 b]) *
      ψ (AutomorphicForm.StandardKernel.ofReal (-(v 1)))

def jacquetIntegrand3 {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) (e : Fin 2 → Fin 2 → ℝ) : ℂ :=
  godementInner3 ψ S (Matrix.of e) (AutomorphicForm.StandardKernel.realMat g) *
    quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
      D.W (diagOne a * (Matrix.of e)⁻¹)

def jacquetVector3 {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) : ℂ :=
  quasiChar (u₃ + 1) a₃ (AutomorphicForm.StandardKernel.realMat g).det *
    ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ S g e

theorem jacquetVector3_eq {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ)
    (ψ : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetVector3 D u₃ a₃ a ψ S g =
      quasiChar (u₃ + 1) a₃ (AutomorphicForm.StandardKernel.realMat g).det *
        ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ a ψ S g e :=
  rfl

end LanglandsTunnell.CubicInduction


