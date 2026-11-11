-- Prove2me | Definitions.Def_GPTIP632_Classical_Systems
-- name    : GPTIP632_Classical_Systems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:11.591449+00:00
-- url     : https://prove2.me/theorems/0e17ce96-33da-4c81-8cda-7000033575cc
-- title:
--   Systems, states, effects, minimal and maximal tensor products, composites, and the classical system $\Delta_n$
-- statement:
--   A **system** $A$ of a general probabilistic theory is a triple $(V_A, V_A^+, u_A)$: a finite-dimensional real vector space $V_A$, a cone $V_A^+\subseteq V_A$ of unnormalised states that is closed, convex, pointed ($V_A^+\cap(-V_A^+)=\{0\}$) and generating ($V_A^+-V_A^+=V_A$), and a **unit effect** $u_A$, a linear functional strictly positive on $V_A^+\setminus\{0\}$. Here $V_A=\mathbb R^{\iota}$ for a finite index set $\iota$ of coordinates, and $u_A$ is a coordinate vector, so that $u_A(\omega)=\sum_i u_{A,i}\,\omega_i$.
--
--   The **states** are $\Omega_A=\{\omega\in V_A^+ : u_A(\omega)=1\}$ and the **effects** are the functionals $f$ with $0\le f(\omega)\le1$ for every state $\omega$. The dual cone is $C^*=\{f : f(\omega)\ge0\ \forall\omega\in C\}$.
--
--   For systems $A$, $B$, in the product coordinates $\iota_A\times\iota_B$, with $(\alpha\otimes\beta)(i,j)=\alpha_i\beta_j$,
--
--   $$
--   C_A\otimes_{\min}C_B=\Big\{\sum_k\alpha_k\otimes\beta_k : \alpha_k\in C_A,\ \beta_k\in C_B\Big\},\qquad
--   C_A\otimes_{\max}C_B=\{\xi : (f\otimes g)(\xi)\ge0\ \ \forall f\in C_A^*,\ g\in C_B^*\}.
--   $$
--
--   A **composite** of $A$ and $B$ is a system $AB$ whose coordinates are identified with $\iota_A\times\iota_B$ (local tomography, $V_{AB}=V_A\otimes V_B$), with $u_{AB}=u_A\otimes u_B$ and $V_A^+\otimes_{\min}V_B^+\subseteq V_{AB}^+\subseteq V_A^+\otimes_{\max}V_B^+$.
--
--   The **classical system** $\Delta_n$ has $V=\mathbb R^n$, $V^+=\mathbb R^n_{\ge0}$ and $u(\omega)=\sum_i\omega_i$; its states are the probability vectors. For a system $B$, $(V_B^+)^{\oplus n}$ is the set of $\xi$ on $\{1,\dots,n\}\times\iota_B$ whose every block $\xi(i,\cdot)$ lies in $V_B^+$.
--
--   These are the objects of Fact B.10 and the building blocks of the theories below.
--
--   **Formalization Note** A system is a structure over a coordinate type `ι` (finite, with decidable equality); its unit is a vector paired by `pair`. A composite is required to be a system, which loses nothing by Fact B.7. The proofs in the file only show that $\Delta_n$ is a system.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, pp.13–15 (PDF pp.15–17), §A.2 eq. (1), Definition B.1, Example B.2, Definition B.6, Fact B.10 (the direct sum)

import Mathlib

/-!
# Systems of a general probabilistic theory, in coordinates

Kishor Bharti, *Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical
Theories*, STOC 2027 submission #632 (October 2026), §A.2 (p.13, PDF p.15), Definition B.1
(pp.13–14, PDF pp.15–16), Example B.2 (p.14, PDF p.16), Definition B.6 (p.15, PDF p.17).

A system carries a finite coordinate index type `ι`, so `V_A = ι → ℝ`, and its unit effect is a
coordinate vector paired with states by the dot product. Coordinates are part of the data, because
assumption (T4) speaks of matrix entries in a fixed basis.
-/

namespace GPTIP632.Classical

/-- The pairing `f(ω) = ∑_i f_i ω_i` of a coordinate functional with a coordinate vector. -/
def pair {ι : Type} [Fintype ι] (f ω : ι → ℝ) : ℝ := ∑ i, f i * ω i

/-- **Definition B.1 (System)**, p.13: a triple `(V_A, V_A⁺, u_A)` with `V_A = ι → ℝ` for a finite
index type `ι`, a closed, convex, pointed and generating cone `V_A⁺ ⊆ V_A`, and a unit effect
`u_A` strictly positive on `V_A⁺ \ {0}`. -/
structure System where
  /-- the coordinate index type: `V_A = ι → ℝ` -/
  ι : Type
  [fintype : Fintype ι]
  [decEq : DecidableEq ι]
  /-- the cone `V_A⁺` of unnormalised states -/
  cone : Set (ι → ℝ)
  /-- the unit effect `u_A`, as a coordinate vector -/
  unit : ι → ℝ
  cone_closed : IsClosed cone
  cone_zero : (0 : ι → ℝ) ∈ cone
  cone_add : ∀ x ∈ cone, ∀ y ∈ cone, x + y ∈ cone
  cone_smul : ∀ c : ℝ, 0 ≤ c → ∀ x ∈ cone, c • x ∈ cone
  /-- pointed: `V⁺ ∩ (−V⁺) = {0}` -/
  cone_pointed : ∀ x ∈ cone, -x ∈ cone → x = 0
  /-- generating: `V⁺ − V⁺ = V` -/
  cone_generating : ∀ v : ι → ℝ, ∃ a ∈ cone, ∃ b ∈ cone, v = a - b
  /-- `u_A` is strictly positive on `V_A⁺ \ {0}` -/
  unit_pos : ∀ x ∈ cone, x ≠ 0 → 0 < pair unit x

attribute [instance] System.fintype System.decEq

namespace System

/-- Definition B.1: the states `Ω_A = {ω ∈ V_A⁺ : u_A(ω) = 1}`. -/
def states (A : System) : Set (A.ι → ℝ) := {ω | ω ∈ A.cone ∧ pair A.unit ω = 1}

/-- Definition B.1: the effects `E_A = {f : 0 ≤ f(ω) ≤ 1 for all ω ∈ Ω_A}`. -/
def effects (A : System) : Set (A.ι → ℝ) :=
  {f | ∀ ω ∈ A.states, 0 ≤ pair f ω ∧ pair f ω ≤ 1}

/-- §A.2: the dual cone `C* = {f : f(ω) ≥ 0 for all ω ∈ C}` of `V_A⁺`. -/
def dualCone (A : System) : Set (A.ι → ℝ) := {f | ∀ ω ∈ A.cone, 0 ≤ pair f ω}

end System

/-- The product vector `α ⊗ β` in product coordinates: `(α ⊗ β)(i, j) = α_i β_j`. -/
def tensorVec {ι κ : Type} (α : ι → ℝ) (β : κ → ℝ) : ι × κ → ℝ := fun p => α p.1 * β p.2

/-- **Eq. (1), minimal tensor product**, p.13: `C_A ⊗_min C_B = cone{α ⊗ β : α ∈ C_A, β ∈ C_B}`,
the set of nonnegative combinations of products, in product coordinates `ι_A × ι_B`. A nonnegative
coefficient is absorbed into the factor `α_k ∈ C_A`, so the cone is the set of finite sums
`∑_k α_k ⊗ β_k` (the empty sum is `0`). -/
def minTensor (A B : System) : Set (A.ι × B.ι → ℝ) :=
  {ξ | ∃ (m : ℕ) (α : Fin m → A.ι → ℝ) (β : Fin m → B.ι → ℝ),
    (∀ k, α k ∈ A.cone) ∧ (∀ k, β k ∈ B.cone) ∧ ξ = ∑ k, tensorVec (α k) (β k)}

/-- **Eq. (1), maximal tensor product**, p.13:
`C_A ⊗_max C_B = {ξ : (f ⊗ g)(ξ) ≥ 0 for all f ∈ C_A*, g ∈ C_B*}`. -/
def maxTensor (A B : System) : Set (A.ι × B.ι → ℝ) :=
  {ξ | ∀ f ∈ A.dualCone, ∀ g ∈ B.dualCone, 0 ≤ pair (tensorVec f g) ξ}

/-- The cone of a system `C`, read in other coordinates `κ` through a coordinate bijection
`e : C.ι ≃ κ`: a vector `ξ : κ → ℝ` lies in it iff `ξ ∘ e` lies in `V_C⁺`. -/
def pullCone (C : System) {κ : Type} (e : C.ι ≃ κ) : Set (κ → ℝ) := {ξ | (ξ ∘ e) ∈ C.cone}

/-- **Definition B.6 (Composite)**, p.15: a composite of `A` and `B` is a system `AB` with
`V_AB = V_A ⊗ V_B` (its coordinates are identified with `ι_A × ι_B` by `e`; this is local
tomography, (T1)), `u_AB = u_A ⊗ u_B`, and a cone with `V_A⁺ ⊗_min V_B⁺ ⊆ V_AB⁺ ⊆ V_A⁺ ⊗_max V_B⁺`.
Requiring `AB` to be a system loses nothing: Fact B.7 shows these conditions make it one. -/
structure Composite (A B : System) where
  /-- the composite system `AB` -/
  sys : System
  /-- the identification `V_AB = V_A ⊗ V_B` in product coordinates -/
  e : sys.ι ≃ A.ι × B.ι
  unit_eq : ∀ k, sys.unit k = A.unit (e k).1 * B.unit (e k).2
  min_le : minTensor A B ⊆ pullCone sys e
  le_max : pullCone sys e ⊆ maxTensor A B

/-- **Example B.2 (Classical systems)**, p.14: the classical `n`-level system `Δ_n`, with
`V = ℝⁿ`, `V⁺ = ℝⁿ_{≥0}` and `u(ω) = ∑_i ω_i`. -/
def Delta (n : ℕ) : System where
  ι := Fin n
  cone := {ω | ∀ i, 0 ≤ ω i}
  unit := fun _ => 1
  cone_closed := by
    have : {ω : Fin n → ℝ | ∀ i, 0 ≤ ω i} = ⋂ i, {ω | 0 ≤ ω i} := by ext; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  cone_zero := fun _ => le_refl _
  cone_add := fun x hx y hy i => add_nonneg (hx i) (hy i)
  cone_smul := fun c hc x hx i => mul_nonneg hc (hx i)
  cone_pointed := fun x hx hnx => by
    funext i
    have h1 := hx i
    have h2 := hnx i
    simp only [Pi.neg_apply] at h2
    simp only [Pi.zero_apply]
    linarith
  cone_generating := fun v =>
    ⟨fun i => max (v i) 0, fun i => le_max_right _ _, fun i => max (-v i) 0,
      fun i => le_max_right _ _, by funext i; simp [max_zero_sub_max_neg_zero_eq_self]⟩
  unit_pos := fun x hx hne => by
    unfold pair
    simp only [one_mul]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      exact hne (funext fun i => by
        by_contra hi
        exact h ⟨i, hi⟩)
    exact Finset.sum_pos' (fun j _ => hx j) ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hx i) (Ne.symm hi)⟩

/-- The direct sum `(V_B⁺)^{⊕n}` in coordinates `Fin n × ι_B`: the vectors whose `i`-th block
`ξ(i, ·)` lies in `V_B⁺` for every `i` (Fact B.10, p.15). -/
def blockCone (n : ℕ) (B : System) : Set (Fin n × B.ι → ℝ) :=
  {ξ | ∀ i, (fun j => ξ (i, j)) ∈ B.cone}

end GPTIP632.Classical


