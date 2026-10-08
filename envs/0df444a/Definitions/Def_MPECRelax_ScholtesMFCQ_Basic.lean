-- Prove2me | Definitions.Def_MPECRelax_ScholtesMFCQ_Basic
-- name    : MPECRelax_ScholtesMFCQ_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:18.815984+00:00
-- url     : https://prove2.me/theorems/dcd548b8-0a31-433b-9bd0-85a4d5c37a63
-- title:
--   (1), (2), Definitions 2.1, 2.4, R^S(t): the MPEC, the NLP, positive-linear dependence, MFCQ, TNLP(x*), MPEC-MFCQ, Scholtes' relaxed program
-- statement:
--   This file sets up the objects of Hoheisel, Kanzow and Schwartz's analysis of Scholtes' relaxation method.
--
--   **Standard nonlinear programs (2).** An NLP on $\mathbb R^n$ consists of an objective $f$, inequality constraints $g_i(x)\le 0$ ($i\in\iota$) and equality constraints $h_j(x)=0$ ($j\in\kappa$), with finite index sets. A point $x$ is *feasible* if all constraints hold. The *active set* is $I_g(x)=\{i \mid g_i(x)=0\}$.
--
--   1. **Positive-linear dependence (Definition 2.1).** For $I_1\subseteq\iota$, $I_2\subseteq\kappa$, the family $\{\nabla g_i(x)\mid i\in I_1\}\cup\{\nabla h_j(x)\mid j\in I_2\}$ is *positive-linearly dependent* if there are scalars $\alpha_i\ge 0$ ($i\in I_1$) and $\beta_j$ ($j\in I_2$), not all zero, with
--   $$\sum_{i\in I_1}\alpha_i\nabla g_i(x)+\sum_{j\in I_2}\beta_j\nabla h_j(x)=0 .$$
--   Otherwise it is *positive-linearly independent*.
--   2. **MFCQ (p. 3).** $x$ satisfies the Mangasarian–Fromovitz constraint qualification if the gradients $\nabla h_j(x)$ ($j\in\kappa$) are linearly independent and there is $d\in\mathbb R^n$ with $\nabla g_i(x)^Td<0$ for all $i\in I_g(x)$ and $\nabla h_j(x)^Td=0$ for all $j$.
--
--   **The MPEC (1).** Minimize $f(x)$ subject to $g_i(x)\le 0$ ($i=1,\dots,m$), $h_i(x)=0$ ($i=1,\dots,p$), $G_i(x)\ge 0$, $H_i(x)\ge 0$, $G_i(x)H_i(x)=0$ ($i=1,\dots,l$); its feasible set is $X$. The data are assumed continuously differentiable (the paper's standing assumption, p. 1). At a point $x^*$ the index sets are
--   $$I_g=\{i\mid g_i(x^*)=0\},\quad I_{0+}=\{i\mid G_i(x^*)=0<H_i(x^*)\},\quad I_{00}=\{i\mid G_i(x^*)=H_i(x^*)=0\},\quad I_{+0}=\{i\mid G_i(x^*)>0=H_i(x^*)\},$$
--   and, for the relaxed program (p. 9), $I_G(x)=\{i\mid G_i(x)=0\}$, $I_H(x)=\{i\mid H_i(x)=0\}$, $I_{GH}(x;t)=\{i\mid H_i(x)G_i(x)=t\}$.
--
--   3. **TNLP$(x^*)$ and MPEC-MFCQ (p. 6, Definition 2.4).** The tightened program TNLP$(x^*)$ minimizes $f$ subject to $g_i\le 0$ (all $i$), $h_i=0$ (all $i$), $G_i=0,\ H_i\ge 0$ ($i\in I_{0+}$), $G_i\ge0,\ H_i=0$ ($i\in I_{+0}$), $G_i=H_i=0$ ($i\in I_{00}$). MPEC-MFCQ holds at $x^*$ if standard MFCQ holds for TNLP$(x^*)$ at $x^*$.
--   4. **Scholtes' relaxed program $R^S(t)$ (p. 8).** Minimize $f(x)$ subject to $g_i(x)\le 0$, $h_j(x)=0$, $G_i(x)\ge 0$, $H_i(x)\ge 0$, $G_i(x)H_i(x)\le t$; its feasible set is $X^S(t)$. "Standard MFCQ for $R^S(t)$" is MFCQ for this NLP.
--
--   These objects are the vocabulary of Theorem 3.2: MPEC-MFCQ at a feasible point of the MPEC implies standard MFCQ for $R^S(t)$ near that point.
--
--   **Formalization Note.** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`, so $\nabla f(x)^Td$ is the inner product of `gradient f x` with $d$; indices $1,\dots,m$ become `Fin m` (0-based), and $m,p,l$ may be $0$. Families of gradients are indexed families (repeated vectors count as dependent), not sets. In Definition 2.1, "not all of them being zero" is read as "not all of the $\alpha_i$ and $\beta_j$ are zero", and coefficients outside $I_1$, $I_2$ are set to zero. TNLP$(x^*)$ is an NLP whose constraint index types are `Fin m ⊕ I_0+ ⊕ I_+0` (inequalities $g_i$, $-H_i$, $-G_i$) and `Fin p ⊕ (I_0+ ∪ I_00) ⊕ (I_+0 ∪ I_00)` (equalities $h_i$, $G_i$, $H_i$), so only the constraints the paper lists exist; none is padded by a zero function. $R^S(t)$ is an NLP with inequalities `Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l` ($g_i$, $-G_i$, $-H_i$, $G_iH_i-t$) and equalities $h_j$. The C¹ standing assumption is the predicate `IsC1`, carried as a hypothesis by the theorems that need it. The NLP layer (the structure, feasibility, active set, positive-linear dependence and MFCQ) is the shared module `MPECRelax.ScholtesConv.NLP`, imported rather than redeclared; this file adds the MPEC layer and $R^S(t)$ on top of it.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, pp. 1–9: (1) p. 1, (2) p. 2, MFCQ p. 3, Definition 2.1 p. 4, index sets p. 5, TNLP and Definition 2.4 p. 6, R^S(t) p. 8, I_G, I_H, I_GH p. 9

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP

namespace MPECRelax.ScholtesMFCQ

open Filter Topology
open scoped RealInnerProductSpace

/-- The MPEC (1): minimize `f` subject to `g_i ≤ 0` (`i < m`), `h_i = 0` (`i < p`),
`G_i ≥ 0`, `H_i ≥ 0`, `G_i H_i = 0` (`i < l`). -/
structure MPEC (n m p l : ℕ) where
  f : MPECRelax.ScholtesConv.E n → ℝ
  g : Fin m → MPECRelax.ScholtesConv.E n → ℝ
  h : Fin p → MPECRelax.ScholtesConv.E n → ℝ
  G : Fin l → MPECRelax.ScholtesConv.E n → ℝ
  H : Fin l → MPECRelax.ScholtesConv.E n → ℝ

namespace MPEC

variable {n m p l : ℕ}

/-- Standing assumption (p. 1): all data are continuously differentiable. -/
def IsC1 (P : MPEC n m p l) : Prop :=
  ContDiff ℝ 1 P.f ∧ (∀ i, ContDiff ℝ 1 (P.g i)) ∧ (∀ i, ContDiff ℝ 1 (P.h i)) ∧
    (∀ i, ContDiff ℝ 1 (P.G i)) ∧ ∀ i, ContDiff ℝ 1 (P.H i)

/-- `x ∈ X`, the feasible set of the MPEC (1). -/
def Feasible (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Prop :=
  (∀ i, P.g i x ≤ 0) ∧ (∀ i, P.h i x = 0) ∧
    ∀ i, 0 ≤ P.G i x ∧ 0 ≤ P.H i x ∧ P.G i x * P.H i x = 0

/-- `I_g(x) = {i | g_i(x) = 0}`. -/
def Ig (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Set (Fin m) := {i | P.g i x = 0}

/-- `I_0+ = {i | G_i(x) = 0, H_i(x) > 0}`. -/
def I0p (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Set (Fin l) := {i | P.G i x = 0 ∧ 0 < P.H i x}

/-- `I_00 = {i | G_i(x) = 0, H_i(x) = 0}`. -/
def I00 (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Set (Fin l) := {i | P.G i x = 0 ∧ P.H i x = 0}

/-- `I_+0 = {i | G_i(x) > 0, H_i(x) = 0}`. -/
def Ip0 (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Set (Fin l) := {i | 0 < P.G i x ∧ P.H i x = 0}

/-- `I_G(x) = {i | G_i(x) = 0}` (p. 9). -/
def IG (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Set (Fin l) := {i | P.G i x = 0}

/-- `I_H(x) = {i | H_i(x) = 0}` (p. 9). -/
def IH (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) : Set (Fin l) := {i | P.H i x = 0}

/-- `I_GH(x; t) = {i | H_i(x) G_i(x) = t}` (p. 9). -/
def IGH (P : MPEC n m p l) (x : MPECRelax.ScholtesConv.E n) (t : ℝ) : Set (Fin l) := {i | P.H i x * P.G i x = t}

/-- The tightened program TNLP(x*) (p. 6), as an NLP whose constraints are exactly those
listed in the paper (subtype index sets, no padding): inequalities `g_i ≤ 0` (all `i`),
`-H_i ≤ 0` (`i ∈ I_0+`), `-G_i ≤ 0` (`i ∈ I_+0`); equalities `h_j = 0` (all `j`),
`G_i = 0` (`i ∈ I_0+ ∪ I_00`), `H_i = 0` (`i ∈ I_+0 ∪ I_00`). -/
def TNLP (P : MPEC n m p l) (xs : MPECRelax.ScholtesConv.E n) :
    MPECRelax.ScholtesConv.NLP n (Fin m ⊕ ↥(P.I0p xs) ⊕ ↥(P.Ip0 xs))
      (Fin p ⊕ ↥(P.I0p xs ∪ P.I00 xs) ⊕ ↥(P.Ip0 xs ∪ P.I00 xs)) where
  f := P.f
  g := Sum.elim P.g (Sum.elim (fun i x => -P.H i x) (fun i x => -P.G i x))
  h := Sum.elim P.h (Sum.elim (fun i => P.G i) (fun i => P.H i))

/-- Definition 2.4: MPEC-MFCQ holds at `xs` if standard MFCQ holds for TNLP(xs) at `xs`. -/
def MPEC_MFCQ (P : MPEC n m p l) (xs : MPECRelax.ScholtesConv.E n) : Prop := (P.TNLP xs).IsMFCQ xs

/-- Scholtes' relaxed program R^S(t) (p. 8) as an NLP: inequalities `g_i ≤ 0`,
`-G_i ≤ 0`, `-H_i ≤ 0`, `G_i H_i - t ≤ 0`; equalities `h_j = 0`. Its feasible set is
`X^S(t)`. -/
def RS (P : MPEC n m p l) (t : ℝ) : MPECRelax.ScholtesConv.NLP n (Fin m ⊕ Fin l ⊕ Fin l ⊕ Fin l) (Fin p) where
  f := P.f
  g := Sum.elim P.g (Sum.elim (fun i x => -P.G i x)
         (Sum.elim (fun i x => -P.H i x) (fun i x => P.G i x * P.H i x - t)))
  h := P.h

end MPEC

end MPECRelax.ScholtesMFCQ


