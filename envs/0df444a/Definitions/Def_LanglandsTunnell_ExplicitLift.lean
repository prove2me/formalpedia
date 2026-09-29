-- Prove2me | Definitions.Def_LanglandsTunnell_ExplicitLift
-- name    : LanglandsTunnell_ExplicitLift
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/822be9b2-b37f-5a57-aff3-7ac0e79e524c
-- title:
--   Explicit lifts of two GL₂(𝔽₃) generators to ℤ[√−2]
-- statement:
--   The module fixes, once and for all, the explicit matrix data used for a characteristic-zero lift of mod-3 matrix groups. First, `red` is the ring homomorphism $\mathbb{Z}[\sqrt{-2}] \to \mathbb{Z}/3$ obtained from Mathlib's universal property `Zsqrtd.lift` applied to the element $-1$ of $\mathbb{Z}/3$, together with the auxiliary decidable computation `neg_one_sq_eq_neg_two` showing $(-1)\cdot(-1) = -2$ in $\mathbb{Z}/3$; thus `red` is the unique ring map sending $\sqrt{-2} \mapsto -1$, and in particular $1 + \sqrt{-2}$ lies in its kernel, the prime of norm $3$.
--
--   Then four explicit $2\times 2$ matrices are named. Over $\mathbb{Z}/3$: $\bar s =$ `sbar` $= \begin{pmatrix}-1 & 1\\ -1 & 0\end{pmatrix}$, of determinant $1$, and $\bar t =$ `tbar` $= \begin{pmatrix}1 & -1\\ 1 & 1\end{pmatrix}$, of determinant $-1$. Over $\mathbb{Z}[\sqrt{-2}]$ (entries written in the coordinates $\langle a,b\rangle = a + b\sqrt{-2}$ of Mathlib's `Zsqrtd`): `Slift` $= \begin{pmatrix}-1 & 1\\ -1 & 0\end{pmatrix}$, the entrywise integral lift of $\bar s$, and `Tlift` $= \begin{pmatrix}1 & -1\\ -\sqrt{-2} & -1+\sqrt{-2}\end{pmatrix}$, whose entrywise image under `red` is $\bar t$ and whose determinant is $-1$.
--
--   The module contains data only: apart from the one-line congruence `neg_one_sq_eq_neg_two` needed to build `red`, nothing is asserted or proved here about the orders of these matrices, about the reduction of `Slift` and `Tlift`, or about the group they generate; those facts are established in the theorems that use these matrices.
--
--   **Relation to Mathlib.** Built directly on Mathlib: the ring $\mathbb{Z}[\sqrt{-2}]$ is Mathlib's `Zsqrtd`, `red` is produced by `Zsqrtd.lift`, and the matrices use Mathlib's `!![…]` notation. The particular choices of generators and lifts are the project's own data.
--
--   **Where it is used.** These matrices supply the explicit section of $\mathrm{GL}_2(\mathbb{Z}[\sqrt{-2}]) \to \mathrm{GL}_2(\mathbb{F}_3)$ used in the Langlands–Tunnell input to the argument: a mod-3 representation is lifted to a characteristic-zero (odd, octahedral-type) representation to which Tunnell's theorem applies, giving the modularity of the residual mod-3 representation. These definitions underlie the statements on the existence of such a lift and on weight-two modularity in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_ExplicitLift.lean

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace FLT.ExplicitLift

open Matrix Zsqrtd

theorem neg_one_sq_eq_neg_two : (-1 : ZMod 3) * (-1) = ((-2 : ℤ) : ZMod 3) := by decide

noncomputable def red : ℤ√(-2) →+* ZMod 3 :=
  Zsqrtd.lift ⟨-1, neg_one_sq_eq_neg_two⟩

def sbar : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![-1, 1; -1, 0]

def tbar : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, -1; 1, 1]

def Slift : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) := !![⟨-1, 0⟩, ⟨1, 0⟩; ⟨-1, 0⟩, ⟨0, 0⟩]

def Tlift : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) := !![⟨1, 0⟩, ⟨-1, 0⟩; ⟨0, -1⟩, ⟨-1, 1⟩]

end FLT.ExplicitLift


