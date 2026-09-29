-- Prove2me | Definitions.Def_CerednikDrinfeld_OmegaOrdAt
-- name    : CerednikDrinfeld_OmegaOrdAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/88d09d6b-e6d4-52e7-9674-58d137b13aaa
-- title:
--   Coordinate function and order of vanishing on the Drinfeld upper half-plane
-- statement:
--   Throughout, $K_0$ and $K$ are fields with $K$ a $K_0$-algebra carrying a valuation with values in a linearly ordered commutative group with zero $\Gamma_0$, and $\varpi$ is a `PseudoUniformizer K₀ K`, i.e. an element of $K_0$ whose value is strictly between $0$ and $1$ and such that every nonzero element of $K_0$ has value squeezed between $v(\varpi)^N$ and $v(\varpi)^{-N}$ for some $N$. Here $\Omega =$ `upperHalfPlane K₀ K` is the complement in $K$ of the image of $K_0$, and `holRing ϖ` is the subring of functions $\Omega \to K$ whose restriction to each affinoid $\Omega_n =$ `affinoid ϖ n` is a uniform limit of evaluations of pole-free rational pairs with uniformly bounded values.
--
--   The first declaration records that the coordinate $z \mapsto z$ belongs to `holRing ϖ`: on each $\Omega_n$ it is given by the rational pair $X/1$, which is pole-free there and bounded by $v(\varpi^{-n})$ by the defining inequality of the affinoid. This gives `coord ϖ`, an element of `holRing ϖ`, and, for a point $z \in \Omega$, `coordSub ϖ z` $=$ `coord ϖ` $- z$, the holomorphic function $w \mapsto w - z$, which vanishes at $w = z$.
--
--   For $F \in$ `holRing ϖ` and $z \in \Omega$, `ordAt ϖ F z` is defined as the supremum, taken in $\mathbb{N}$, of the set of $n$ with $(w-z)^n \mid F$ in the ring `holRing ϖ`, that is, of those $n$ for which $F = (w-z)^n G$ with $G$ holomorphic on $\Omega$. Accompanying lemmas unfold this definition, note that $n = 0$ always belongs to the set, give the upper bound $\operatorname{ord}_z F \le N$ whenever every admissible exponent is $\le N$, and give the lower bound $n \le \operatorname{ord}_z F$ from a divisibility $(w-z)^n \mid F$ together with boundedness above of the exponent set. Since the supremum is the $\mathbb{N}$-valued one, an exponent set that is unbounded above yields the value $0$; no analytic finiteness statement is asserted here.
--
--   **Relation to Mathlib.** `holRing`, the affinoids and the pseudo-uniformizer are the project's own notions. The order of vanishing is defined directly as an $\mathbb{N}$-valued `sSup` over a divisibility set rather than through Mathlib's multiplicity API, so the value at an exponent set unbounded above is $0$.
--
--   **Where it is used.** These definitions provide the divisor bookkeeping for rigid-analytic functions on the Drinfeld upper half-plane used in the Čerednik–Drinfeld description of Shimura curves via Mumford quotients, on the way to the modular-curve input of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_OmegaOrdAt.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CerednikDrinfeld.Omega

namespace CerednikDrinfeld.Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

theorem coord_mem_holRing : (fun z : ↥(upperHalfPlane K₀ K) => (z : K)) ∈ holRing ϖ := by
  intro n
  have h := isHolOn_ratPair (S := affinoid ϖ n) ⟨Polynomial.X, 1⟩ (fun z _ => by simp)
    ⟨algebraMap K₀ K (ϖ.ϖ⁻¹ ^ n), fun z hz => by
      have := ((mem_affinoid_iff' ϖ n z).1 hz).1
      simpa [RatPair.evalAt, map_pow, map_inv₀] using this⟩
  convert h using 1
  funext z
  simp [restrictAffinoid, RatPair.evalAt]

def coord : ↥(holRing ϖ) := ⟨fun z => (z : K), coord_mem_holRing ϖ⟩

@[simp] theorem coord_apply (z : ↥(upperHalfPlane K₀ K)) : (coord ϖ : ↥(upperHalfPlane K₀ K) → K) z = (z : K) := rfl

def coordSub (z : ↥(upperHalfPlane K₀ K)) : ↥(holRing ϖ) :=
  coord ϖ - algebraMap K ↥(holRing ϖ) (z : K)

@[simp] theorem coordSub_apply (z w : ↥(upperHalfPlane K₀ K)) :
    (coordSub ϖ z : ↥(upperHalfPlane K₀ K) → K) w = (w : K) - (z : K) := rfl

theorem coordSub_apply_self (z : ↥(upperHalfPlane K₀ K)) :
    (coordSub ϖ z : ↥(upperHalfPlane K₀ K) → K) z = 0 := sub_self _

def ordAt (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) : ℕ :=
  sSup {n : ℕ | coordSub ϖ z ^ n ∣ F}

theorem ordAt_def (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) :
    ordAt ϖ F z = sSup {n : ℕ | coordSub ϖ z ^ n ∣ F} := rfl

theorem zero_mem_setOf_pow_dvd (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) :
    (0 : ℕ) ∈ {n : ℕ | coordSub ϖ z ^ n ∣ F} := by
  simp

theorem ordAt_le_of_forall_le (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) (N : ℕ)
    (h : ∀ n : ℕ, coordSub ϖ z ^ n ∣ F → n ≤ N) : ordAt ϖ F z ≤ N :=
  csSup_le ⟨0, zero_mem_setOf_pow_dvd ϖ F z⟩ (fun n hn => h n hn)

theorem le_ordAt_of_pow_dvd (F : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) {n : ℕ}
    (hn : coordSub ϖ z ^ n ∣ F) (hb : BddAbove {n : ℕ | coordSub ϖ z ^ n ∣ F}) : n ≤ ordAt ϖ F z :=
  le_csSup hb hn

end CerednikDrinfeld.Omega

end


