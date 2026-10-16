-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
-- name    : OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:17:26.314804+00:00
-- url     : https://prove2.me/theorems/0548aec0-a82b-4998-ad77-5f84f044b579
-- title:
--   The normalized permanent pairing of two $n$-tuples and its multilinearity
-- statement:
--   Let $X$ and $Y$ be sets, $n\in\mathbb{N}$, and $B:X\times Y\to\mathbb{C}$ an arbitrary function. Write $S_n$ for the symmetric group on $\{0,\dots,n-1\}$. For $x=(x_0,\dots,x_{n-1})\in X^n$ and $y=(y_0,\dots,y_{n-1})\in Y^n$ the *normalized permanent pairing* is
--   $$\mathrm{per}_B(x,y)=\frac{1}{n!}\sum_{\sigma\in S_n}\ \prod_{i=0}^{n-1}B\bigl(x_i,y_{\sigma(i)}\bigr),$$
--   that is, $1/n!$ times the permanent of the $n\times n$ matrix $\bigl(B(x_i,y_j)\bigr)_{0\le i,j<n}$. For $n=0$ its value is $1$. The file establishes:
--
--   1. **Symmetry in each family.** For every $\tau\in S_n$, $\mathrm{per}_B(x,y\circ\tau)=\mathrm{per}_B(x,y)$ and $\mathrm{per}_B(x\circ\tau,y)=\mathrm{per}_B(x,y)$, where $(y\circ\tau)_i=y_{\tau(i)}$.
--   2. **Transposition.** For the transposed function $B^{\top}(y',x')=B(x',y')$ one has $\mathrm{per}_{B^{\top}}(y,x)=\mathrm{per}_B(x,y)$.
--   3. **Constant families.** If all entries of the second family equal $y\in Y$, then $\mathrm{per}_B(x,(y,\dots,y))=\prod_{i=0}^{n-1}B(x_i,y)$; likewise $\mathrm{per}_B((x,\dots,x),y)=\prod_{i=0}^{n-1}B(x,y_i)$ for $x\in X$.
--   4. **Multilinearity.** Now let $X,Y$ be complex vector spaces and $B$ bilinear. For fixed $x$ the map $y\mapsto\mathrm{per}_B(x,y)$ is an $n$-linear form on $Y$, and for fixed $y$ the map $x\mapsto\mathrm{per}_B(x,y)$ is an $n$-linear form on $X$. Together they give an $n$-linear map from $X^n$ into the space of $n$-linear forms on $Y$,
--   $$x\longmapsto\bigl(y\mapsto\mathrm{per}_B(x,y)\bigr),$$
--   whose values are invariant under permutations of the arguments $y_0,\dots,y_{n-1}$.
--
--   The normalized permanent is the formula for the pairing between products $x_0\cdots x_{n-1}$ and $y_0\cdots y_{n-1}$ in symmetric powers induced by a bilinear form $B$; for $X=V^*$, $Y=V$ and $B(\varphi,v)=\varphi(v)$ it gives the classical duality between $\mathrm{Sym}^n(V^*)$ and $\mathrm{Sym}^n V$. The symmetry and multilinearity properties are exactly what is needed to descend it to symmetric powers.
--
--   **Formalization Note** Tuples are functions on `Fin n`. `permanentPairing n B x y` works for arbitrary types and an arbitrary function `B`; for bilinear `B`, `permanentPairingRight`, `permanentPairingLeft` and `permanentPairingMultilinear` package the same quantity as multilinear maps in the right family, the left family, and both (the last with values in multilinear maps).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/PermanentPairing.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/PermanentPairing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem346

universe u v w z

/-- The normalized permanent of a pairing on two indexed families. -/
def permanentPairing {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : Fin n → X) (y : Fin n → Y) : ℂ :=
  (n.factorial : ℂ)⁻¹ * ∑ σ : Equiv.Perm (Fin n), ∏ i, B (x i) (y (σ i))

theorem permanentPairing_perm_right {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : Fin n → X) (y : Fin n → Y)
    (τ : Equiv.Perm (Fin n)) :
    permanentPairing n B x (fun i => y (τ i)) = permanentPairing n B x y := by
  classical
  unfold permanentPairing
  congr 1
  simpa only [Equiv.coe_mulLeft, Equiv.Perm.mul_apply] using
    (Equiv.sum_comp (Equiv.mulLeft τ)
      (fun σ : Equiv.Perm (Fin n) => ∏ i, B (x i) (y (σ i))))

theorem permanentPairing_perm_left {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : Fin n → X) (y : Fin n → Y)
    (τ : Equiv.Perm (Fin n)) :
    permanentPairing n B (fun i => x (τ i)) y = permanentPairing n B x y := by
  classical
  unfold permanentPairing
  congr 1
  calc
    (∑ σ : Equiv.Perm (Fin n), ∏ i, B (x (τ i)) (y (σ i))) =
        ∑ σ : Equiv.Perm (Fin n), ∏ i, B (x i) (y ((σ * τ⁻¹) i)) := by
      apply Finset.sum_congr rfl
      intro σ _
      simpa only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
        (Equiv.prod_comp τ (fun i => B (x i) (y ((σ * τ⁻¹) i))))
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, B (x i) (y (σ i)) := by
      simpa only [Equiv.coe_mulRight] using
        (Equiv.sum_comp (Equiv.mulRight τ⁻¹)
          (fun σ : Equiv.Perm (Fin n) => ∏ i, B (x i) (y (σ i))))

/-- Transposing the underlying pairing transposes the two families. -/
theorem permanentPairing_flip {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : Fin n → X) (y : Fin n → Y) :
    permanentPairing n (fun y x => B x y) y x = permanentPairing n B x y := by
  classical
  unfold permanentPairing
  congr 1
  calc
    (∑ σ : Equiv.Perm (Fin n), ∏ i, B (x (σ i)) (y i)) =
        ∑ σ : Equiv.Perm (Fin n), ∏ i, B (x i) (y (σ⁻¹ i)) := by
      apply Finset.sum_congr rfl
      intro σ _
      simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using
        (Equiv.prod_comp σ (fun i => B (x i) (y (σ⁻¹ i))))
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, B (x i) (y (σ i)) := by
      exact Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))
        (fun σ : Equiv.Perm (Fin n) => ∏ i, B (x i) (y (σ i)))

@[simp] theorem permanentPairing_const_right {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : Fin n → X) (y : Y) :
    permanentPairing n B x (fun _ => y) = ∏ i, B (x i) y := by
  classical
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp [permanentPairing, Fintype.card_perm, hn]

@[simp] theorem permanentPairing_const_left {X : Type u} {Y : Type v} (n : ℕ)
    (B : X → Y → ℂ) (x : X) (y : Fin n → Y) :
    permanentPairing n B (fun _ => x) y = ∏ i, B x (y i) := by
  rw [← permanentPairing_flip n B]
  exact permanentPairing_const_right n (fun y x => B x y) y x

section Multilinear

variable {X : Type u} {Y : Type v}
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- The permanent pairing as a multilinear map in its right family. -/
def permanentPairingRight (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (x : Fin n → X) : MultilinearMap ℂ (fun _ : Fin n => Y) ℂ :=
  (n.factorial : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin n),
      ((MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap (fun i => B (x i))).domDomCongr σ

@[simp] theorem permanentPairingRight_apply (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (y : Fin n → Y) :
    permanentPairingRight n B x y = permanentPairing n (fun x y => B x y) x y := by
  classical
  simp [permanentPairingRight, permanentPairing]

/-- The permanent pairing as a multilinear map in its left family. -/
def permanentPairingLeft (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (y : Fin n → Y) : MultilinearMap ℂ (fun _ : Fin n => X) ℂ :=
  (n.factorial : ℂ)⁻¹ •
    ∑ σ : Equiv.Perm (Fin n),
      (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
        (fun i => B.flip (y (σ i)))

@[simp] theorem permanentPairingLeft_apply (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (y : Fin n → Y) :
    permanentPairingLeft n B y x = permanentPairing n (fun x y => B x y) x y := by
  classical
  simp [permanentPairingLeft, permanentPairing]

/-- Both families of the permanent pairing are multilinear. -/
def permanentPairingMultilinear (n : ℕ) (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) :
    MultilinearMap ℂ (fun _ : Fin n => X)
      (MultilinearMap ℂ (fun _ : Fin n => Y) ℂ) where
  toFun := permanentPairingRight n B
  map_update_add' x i a b := by
    ext y
    simpa only [add_apply, permanentPairingRight_apply,
      ← permanentPairingLeft_apply] using
      (permanentPairingLeft n B y).map_update_add x i a b
  map_update_smul' x i c a := by
    ext y
    simpa only [smul_apply, permanentPairingRight_apply,
      ← permanentPairingLeft_apply] using
      (permanentPairingLeft n B y).map_update_smul x i c a

@[simp] theorem permanentPairingMultilinear_apply (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (y : Fin n → Y) :
    permanentPairingMultilinear n B x y =
      permanentPairing n (fun x y => B x y) x y :=
  permanentPairingRight_apply n B x y

theorem permanentPairingMultilinear_perm_right (n : ℕ)
    (B : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (x : Fin n → X) (y : Fin n → Y)
    (τ : Equiv.Perm (Fin n)) :
    permanentPairingMultilinear n B x (fun i => y (τ i)) =
      permanentPairingMultilinear n B x y := by
  simpa only [permanentPairingMultilinear_apply] using
    permanentPairing_perm_right n (fun x y => B x y) x y τ

end Multilinear

end Problem346

end

end OAI


