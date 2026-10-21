-- Prove2me | Definitions.Def_InconsistentDR_Shadow_Operators
-- name    : InconsistentDR_Shadow_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:39.365887+00:00
-- url     : https://prove2.me/theorems/f66c6abc-ed7c-4d7a-9e37-d6bd4d448b85
-- title:
--   (3), (4a), (4b), (5), (8), (12), (14), (15), (18), pp. 2–7 — Douglas–Rachford operator, J_{A⁻¹}, D and R, least-norm points, (12), Z, K, S, paramonotonicity, Fejér pairs
-- statement:
--   This file fixes the operator-theoretic objects of the paper for set-valued operators $A, B : X \rightrightarrows X$ on a real inner product space $X$ (encoded as `X → Set X`), and single-valued maps $J_A, J_B : X \to X$ playing the role of their resolvents.
--
--   1. **Range.** $\operatorname{ran} A = \bigcup_{x\in X} Ax$ (p. 2). The domain $\operatorname{dom}A = \{x \mid Ax \neq \varnothing\}$ is the published `dom`.
--   2. **Reflected resolvent and inverse resolvent.** $R_A = 2J_A - \mathrm{Id}$ (p. 2) and $J_{A^{-1}} = \mathrm{Id} - J_A$, the latter by the inverse resolvent identity $J_A + J_{A^{-1}} = \mathrm{Id}$ (8).
--   3. **Douglas–Rachford operator** (3):
--   $$T = T_{A,B} = \mathrm{Id} - J_A + J_B R_A .$$
--   4. **Projection of $0$.** $p = P_C(0)$ is encoded as a least-norm point of $C$: $p \in C$ and $\|p\| \le \|c\|$ for all $c \in C$. It is used for the closed convex sets $C = \overline{\operatorname{ran}}(\mathrm{Id}-T)$ (giving $v$, (4a)), $\overline{D}$ and $\overline{R}$ (giving $v_D$, $v_R$, (4b)).
--   5. **The sets $D$ and $R$** (5): $D = \operatorname{dom}A - \operatorname{dom}B$ and $R = \operatorname{ran}A + \operatorname{ran}B$.
--   6. **The standing assumption (12)** (p. 6):
--   $$\overline{\operatorname{ran}}(\mathrm{Id}-T) = \overline{D\cap R} = \overline{D}\cap\overline{R}.$$
--   7. **Fixed points.** $\operatorname{Fix}F = \{x \mid Fx = x\}$.
--   8. **Solution sets of the normal problem** $0 \in -v + Ax + B(x-v)$ (13): the primal set
--   $$Z = \{x \mid 0 \in -v + Ax + B(x - v)\}\quad(14),(49),$$
--   the dual set (15), unfolded, $K = \{k \mid \exists z,\ k \in -v + Az,\ -k \in B(z - v)\}$, and the extended solution set (18) $\mathcal S = \{(z,k) \mid -k \in B(z-v),\ k \in -v + Az\}$.
--   9. **Paramonotonicity** (p. 7, footnote 1): $A$ is monotone, and whenever $u \in Ax$, $w \in Ay$ and $\langle x - y, u - w\rangle = 0$, also $w \in Ax$ and $u \in Ay$.
--   10. **Fejér monotonicity in $X\times X$.** A sequence $(p_n, q_n)_n$ is Fejér monotone with respect to $C \subseteq X \times X$ when for every $(c_1,c_2) \in C$ and every $n$,
--   $$\|p_{n+1}-c_1\|^2 + \|q_{n+1}-c_2\|^2 \le \|p_n - c_1\|^2 + \|q_n - c_2\|^2 .$$
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** The resolvents are not constructed here: theorems take maps `JA JB` together with the published characterization `IsResolvent 1 A JA`. The dual set $K$ of (15), $((-v+A)^{-1} + (B(\cdot - v))^{-\circledcirc})^{-1}(0)$, is stored in the unfolded form above (put $y = -z$ in $(B(\cdot-v))^{-\circledcirc}k = \{y \mid -k \in B(-y-v)\}$). Fejér monotonicity writes out the Hilbert norm $\|(a,b)\|^2 = \|a\|^2 + \|b\|^2$ of $X\times X$, because Lean's product type carries the sup norm.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), pp. 2–7, (3), (4a), (4b), (5), (8), (12), (14), (15), (18), footnote 1 p. 7

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

namespace InconsistentDR.Shadow

open scoped Pointwise InnerProductSpace
open ThreeOpSplitting.Convergence

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The range `ran A := ⋃ₓ A x` of a set-valued operator (p. 2). -/
def ran (A : X → Set X) : Set X := {u | ∃ x, u ∈ A x}

/-- The reflected resolvent `R_A = 2 J_A − Id` (p. 2), built from the resolvent map `J = J_A`. -/
def refl (J : X → X) (x : X) : X := (2 : ℝ) • J x - x

/-- The resolvent of the inverse, `J_{A⁻¹} = Id − J_A`, by the inverse resolvent identity (8). -/
def resInv (J : X → X) (x : X) : X := x - J x

/-- The Douglas–Rachford operator `T = Id − J_A + J_B R_A` of (3), from the resolvents
`JA = J_A` and `JB = J_B`. -/
def drT (JA JB : X → X) (x : X) : X := x - JA x + JB (refl JA x)

/-- `p` is the projection of `0` onto `C`, encoded as a least-norm point of `C` (it is used only
with `C` a closed convex set, where the least-norm point exists and is unique). -/
def IsMinNormPt (C : Set X) (p : X) : Prop := p ∈ C ∧ ∀ c ∈ C, ‖p‖ ≤ ‖c‖

/-- `D := dom A − dom B` (5). -/
def setD (A B : X → Set X) : Set X := dom A - dom B

/-- `R := ran A + ran B` (5). -/
def setR (A B : X → Set X) : Set X := ran A + ran B

/-- The standing assumption (12), p. 6:
`cl ran(Id − T) = cl(D ∩ R) = cl D ∩ cl R`, with `T` the Douglas–Rachford operator of the
resolvents `JA`, `JB` of `A`, `B`. -/
def Standing12 (A B : X → Set X) (JA JB : X → X) : Prop :=
  closure (Set.range fun x => x - drT JA JB x) = closure (setD A B ∩ setR A B) ∧
    closure (setD A B ∩ setR A B) = closure (setD A B) ∩ closure (setR A B)

/-- The fixed-point set `Fix F = {x | F x = x}`. -/
def FixSet (F : X → X) : Set X := {x | F x = x}

/-- The primal solution set `Z` of the normal problem, (14) = (49):
`Z = {x | 0 ∈ −v + A x + B(x − v)}`. -/
def solZ (A B : X → Set X) (v : X) : Set X :=
  {x | ∃ a ∈ A x, ∃ b ∈ B (x - v), -v + a + b = 0}

/-- The dual solution set `K` of the normal problem, (15), unfolded:
`K = {k | ∃ z, k ∈ −v + A z and −k ∈ B(z − v)}`. -/
def solK (A B : X → Set X) (v : X) : Set X :=
  {k | ∃ z, k + v ∈ A z ∧ -k ∈ B (z - v)}

/-- The extended solution set `S` of (18): `{(z, k) | −k ∈ B(z − v), k ∈ −v + A z}`. -/
def solS (A B : X → Set X) (v : X) : Set (X × X) :=
  {p | -p.2 ∈ B (p.1 - v) ∧ p.2 + v ∈ A p.1}

/-- Paramonotonicity (p. 7, footnote 1): `A` is monotone, and whenever `u ∈ A x`, `w ∈ A y` and
`⟨x − y, u − w⟩ = 0`, also `w ∈ A x` and `u ∈ A y`. -/
def IsParamonotone (A : X → Set X) : Prop :=
  IsMonotoneOp A ∧
    ∀ x y u w : X, u ∈ A x → w ∈ A y → ⟪x - y, u - w⟫_ℝ = 0 → w ∈ A x ∧ u ∈ A y

/-- Fejér monotonicity of the pair sequence `(p n, q n)` in the Hilbert product `X × X` with
respect to `C ⊆ X × X`: for every `c ∈ C` and every `n`,
`‖p (n+1) − c.1‖² + ‖q (n+1) − c.2‖² ≤ ‖p n − c.1‖² + ‖q n − c.2‖²`. (The Hilbert norm of the
product is written out, since Lean's `X × X` carries the sup norm.) -/
def IsFejerPair (p q : ℕ → X) (C : Set (X × X)) : Prop :=
  ∀ c ∈ C, ∀ n : ℕ,
    ‖p (n + 1) - c.1‖ ^ 2 + ‖q (n + 1) - c.2‖ ^ 2 ≤ ‖p n - c.1‖ ^ 2 + ‖q n - c.2‖ ^ 2

end InconsistentDR.Shadow


