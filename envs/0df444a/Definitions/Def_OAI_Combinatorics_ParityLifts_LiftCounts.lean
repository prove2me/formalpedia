-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
-- name    : OAI_Combinatorics_ParityLifts_LiftCounts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:03:56.721219+00:00
-- url     : https://prove2.me/theorems/dafb4e72-6d3d-41b5-b0d6-79f5b9a14892
-- title:
--   Tag equations for homomorphisms into parity lifts
-- statement:
--   This file translates homomorphisms into a parity lift into solutions of a linear system over $\mathbb{F}_2=\mathbb{Z}/2\mathbb{Z}$.
--
--   Let $T$ be a graph on a finite vertex set $A$, let $G$ be a graph on a set $V$ with a homomorphism $\tau\colon G\to T$, and let $b\colon A\to\mathbb{F}_2$. Recall that the parity lift $X_b$ has as vertices the pairs $(u,z)$ with $u\in V$ and $z\in\mathbb{F}_2^{N_T(\tau(u))}$ satisfying $\sum_{a'\in N_T(\tau(u))}z(a')=b(\tau(u))$ (the *tags* of $u$), and that $(u,z)\sim(v,w)$ if and only if $uv\in E(G)$ and $z(\tau(v))=w(\tau(u))$. From item 2 on, $V$ is finite, $F$ is a graph on a finite set $W$, $\varphi\colon F\to G$ is a homomorphism, and $a=\tau\circ\varphi$.
--
--   1. **Projection.** The map $\pi_b\colon X_b\to G$, $(u,z)\mapsto u$, is a graph homomorphism.
--   2. **Lift equations.** The unknowns are bits $z_{x,a'}$, one for each $x\in W$ and each template neighbour $a'\in N_T(a(x))$. The lift equations for $\varphi$ and $b$ are
--   $$
--   \sum_{a'\in N_T(a(x))}z_{x,a'}=b(a(x))\quad(x\in W),\qquad z_{x,a(y)}=z_{y,a(x)}\quad(x,y\in W,\ xy\in E(F)),
--   $$
--   and $\mathrm{Sol}_b(\varphi)$ denotes the finite set of their solutions. The zero family lies in $\mathrm{Sol}_0(\varphi)$.
--   3. **Homomorphisms as solutions.** A solution $z\in\mathrm{Sol}_b(\varphi)$ defines the homomorphism $F\to X_b$, $x\mapsto(\varphi(x),z_{x,\cdot})$, and this gives a bijection
--   $$
--   \mathrm{Hom}(F,X_b)\;\cong\;\bigl\{(\varphi,z):\ \varphi\in\mathrm{Hom}(F,G),\ z\in\mathrm{Sol}_b(\varphi)\bigr\},\qquad f\mapsto(\pi_b\circ f,\ \text{the tags of } f).
--   $$
--   4. **Translation to the homogeneous system.** For a fixed solution $v\in\mathrm{Sol}_b(\varphi)$, the map $z\mapsto z-v$ is a bijection $\mathrm{Sol}_b(\varphi)\to\mathrm{Sol}_0(\varphi)$.
--   5. **Homomorphism counts.** $\hom(F,H)$ is the number of graph homomorphisms from $F$ to a finite graph $H$.
--   6. **Matrix form.** The equations are indexed by $W\sqcup\vec E(F)$: one row for each vertex of $F$ and one for each dart, i.e. each ordered pair $(x,y)$ with $xy\in E(F)$, so that every edge contributes two rows. The $\mathbb{F}_2$-linear constraint map $M$ and the right-hand side $c_b$ are
--   $$
--   (Mz)_x=\sum_{a'\in N_T(a(x))}z_{x,a'},\qquad (Mz)_{(x,y)}=z_{x,a(y)}+z_{y,a(x)},\qquad (c_b)_x=b(a(x)),\qquad (c_b)_{(x,y)}=0 .
--   $$
--
--   By items 3 and 4, $\hom(F,X_b)=\sum_{\varphi\in\mathrm{Hom}(F,G)}|\mathrm{Sol}_b(\varphi)|$, and every nonempty $\mathrm{Sol}_b(\varphi)$ has exactly $|\mathrm{Sol}_0(\varphi)|$ elements. This is the mechanism behind the comparison $\hom(F,X_b)\le\hom(F,X_0)$ of two parity lifts, with strict inequality exactly when some projected system is unsolvable; the matrix form $Mz=c_b$ makes that unsolvability accessible to linear duality over $\mathbb{F}_2$.
--
--   **Formalization Note** $\mathbb{F}_2$ is `Bit := ZMod 2`. The items correspond to `liftProjection`; `Variables`, `LiftEquations`, `Solutions`, `zeroSolution`; `solutionHom` and `homSolutionsEquiv`; `homogeneousTranslate`; `homCount`; and `EquationRow F` (the sum of `W` and `F.Dart`) with `constraintMap` and `constraintRHS`. The two `Fintype` instances are plumbing, and the section `BinaryDuality` contains no declarations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/LiftCounts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/LiftCounts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts

namespace OAI

namespace ParityWL

open scoped BigOperators

section Lifts

variable {A V : Type} [Fintype A] (T : SimpleGraph A) (G : SimpleGraph V)

noncomputable def liftProjection (τ : G →g T) (b : A → Bit) :
    liftGraph T G τ b →g G where
  toFun := Sigma.fst
  map_rel' := fun h => h.1

end Lifts

section LiftCounts

open scoped Classical

variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

abbrev Variables := (x : W) → T.neighborSet (τ (φ x)) → Bit

noncomputable instance variablesFintype : Fintype (Variables T G F τ φ) := by
  classical
  unfold Variables
  infer_instance

noncomputable def LiftEquations (b : A → Bit) (z : Variables T G F τ φ) : Prop :=
  (∀ x, ∑ v, z x v = b (τ (φ x))) ∧
  (∀ x y (h : F.Adj x y),
    z x ⟨τ (φ y), τ.map_adj (φ.map_adj h)⟩ =
      z y ⟨τ (φ x), τ.map_adj (φ.map_adj h.symm)⟩)

noncomputable def Solutions (b : A → Bit) :=
  {z : Variables T G F τ φ // LiftEquations T G F τ φ b z}

noncomputable instance solutionsFintype (b : A → Bit) :
    Fintype (Solutions T G F τ φ b) := by
  classical
  unfold Solutions
  infer_instance

noncomputable def zeroSolution : Solutions T G F τ φ (fun _ => 0) :=
  ⟨fun _ _ => 0, by classical simp [LiftEquations]⟩

noncomputable def solutionHom (b : A → Bit) (z : Solutions T G F τ φ b) :
    F →g liftGraph T G τ b where
  toFun x := ⟨φ x, ⟨z.1 x, z.2.1 x⟩⟩
  map_rel' := by
    intro x y h
    exact ⟨φ.map_adj h, z.2.2 x y h⟩

noncomputable def homSolutionsEquiv (b : A → Bit) :
    (F →g liftGraph T G τ b) ≃ ((φ : F →g G) × Solutions T G F τ φ b) where
  toFun f := ⟨(liftProjection T G τ b).comp f,
    ⟨fun x => (f x).2.1,
      ⟨fun x => (f x).2.2, fun x y h => (f.map_adj h).2⟩⟩⟩
  invFun p := solutionHom T G F τ p.1 b p.2
  left_inv f := by
    apply RelHom.ext
    intro x
    rfl
  right_inv p := by
    rcases p with ⟨φ, z, hz⟩
    rfl

noncomputable def homogeneousTranslate (b : A → Bit) (v : Solutions T G F τ φ b) :
    Solutions T G F τ φ b ≃ Solutions T G F τ φ (fun _ => 0) where
  toFun z := ⟨z.1 - v.1, by
    classical
    constructor
    · intro x
      change ∑ w, (z.1 x w - v.1 x w) = 0
      rw [Finset.sum_sub_distrib, z.2.1 x, v.2.1 x, sub_self]
    · intro x y h
      change z.1 x _ - v.1 x _ = z.1 y _ - v.1 y _
      rw [z.2.2 x y h, v.2.2 x y h]⟩
  invFun z := ⟨z.1 + v.1, by
    classical
    constructor
    · intro x
      change ∑ w, (z.1 x w + v.1 x w) = b (τ (φ x))
      rw [Finset.sum_add_distrib, z.2.1 x, v.2.1 x, zero_add]
    · intro x y h
      change z.1 x _ + v.1 x _ = z.1 y _ + v.1 y _
      rw [z.2.2 x y h, v.2.2 x y h]⟩
  left_inv z := by
    apply Subtype.ext
    exact sub_add_cancel z.1 v.1
  right_inv z := by
    apply Subtype.ext
    exact add_sub_cancel_right z.1 v.1

noncomputable def homCount {U : Type} [Fintype U] (H : SimpleGraph U) : ℕ := by
  classical
  exact Fintype.card (F →g H)

abbrev EquationRow := W ⊕ F.Dart

noncomputable def constraintMap :
    Variables T G F τ φ →ₗ[Bit] (EquationRow F → Bit) where
  toFun z := fun row => match row with
    | .inl x => ∑ v, z x v
    | .inr d =>
      z d.fst ⟨τ (φ d.snd), τ.map_adj (φ.map_adj d.adj)⟩ +
        z d.snd ⟨τ (φ d.fst), τ.map_adj (φ.map_adj d.adj.symm)⟩
  map_add' z w := by
    funext row
    cases row with
    | inl x => exact Finset.sum_add_distrib
    | inr d => dsimp; ring
  map_smul' a z := by
    funext row
    cases row with
    | inl x =>
      change (∑ v, a * z x v) = a * ∑ v, z x v
      exact (Finset.mul_sum ..).symm
    | inr d => dsimp; ring

noncomputable def constraintRHS (b : A → Bit) : EquationRow F → Bit
  | .inl x => b (τ (φ x))
  | .inr _ => 0

end LiftCounts

section BinaryDuality

variable {E H : Type} [AddCommGroup E] [Module Bit E] [AddCommGroup H] [Module Bit H]

end BinaryDuality

end ParityWL

end OAI


