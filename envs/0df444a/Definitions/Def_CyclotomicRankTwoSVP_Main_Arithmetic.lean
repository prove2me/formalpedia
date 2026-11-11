-- Prove2me | Definitions.Def_CyclotomicRankTwoSVP_Main_Arithmetic
-- name    : CyclotomicRankTwoSVP_Main_Arithmetic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:50:31.394689+00:00
-- url     : https://prove2.me/theorems/8eb282d0-a924-42c0-9a2a-3e0c00ce84d6
-- title:
--   Cyclotomic fields, canonical norms, coefficient maps, ideals and Reed–Solomon lattices
-- statement:
--   For a conductor $q$, let $K=\mathbb Q(\zeta_q)$ and $O_K=\mathbb Z[\zeta_q]$. The chosen primitive root is fixed once per conductor. For a field element $v$, the canonical squared norm and coefficient evaluation are
--
--   $$N(v)=\sum_{\sigma:K\hookrightarrow\mathbb C}|\sigma(v)|^2,\qquad [z]=\sum_{a\in\mathbb F_q}z_a\zeta_q^a.$$
--
--   The sum includes every embedding, with no conjugate-pair normalization. The product squared norm is $N_2(y)=N(y_1)+N(y_2)$. Rational and integer coefficient maps are separate. Set $\pi=1-\zeta_q$ and $\mathfrak a_{q,k}=\pi^kO_K$, using the actual ring multiplication and additive subgroup of the field. The Reed–Solomon lattice consists of integer vectors with syndrome $(\sum_a z_aa^j)_{0\le j<k}=0$ over $\mathbb F_q$; its zero-sum subgroup additionally has integer coefficient sum zero. Power-sum fibers consist of all tuples with the prescribed moments of degrees $1,\ldots,k-1$.
--
--   First squared minima and squared distances are infima of the actual squared norm values. The statements use them only on nonzero source lattices or nonempty ideal translates, where minima are attained and these values agree with the source. The root is set to zero at conductor zero solely to totalize the raw input model; every mathematical cyclotomic statement excludes this case. These definitions provide the shared arithmetic interface for the mission.
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), §§2.1–2.4 and §3.1, printed pp. 5–10 / PDF pp. 6–11, Lemma 2.2, definitions of X_{k,m}, H_q(k), L_{q,k}, a_{q,k}

import Mathlib

noncomputable section

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

abbrev K (q : ℕ) := CyclotomicField q ℚ

def zeta (q : ℕ) : K q :=
  if hq : q = 0 then 0 else by
    letI : NeZero q := ⟨hq⟩
    letI : NeZero (q : ℚ) := ⟨Nat.cast_ne_zero.mpr hq⟩
    letI : IsCyclotomicExtension {q} ℚ (K q) := CyclotomicField.isCyclotomicExtension q ℚ
    exact IsCyclotomicExtension.zeta q ℚ (K q)

def OK (q : ℕ) : Subalgebra ℤ (K q) := Algebra.adjoin ℤ {zeta q}

def canonicalInner {q : ℕ} (y y' : K q) : ℝ :=
  ∑ σ : K q →ₐ[ℚ] ℂ, (σ y * star (σ y')).re

def N {q : ℕ} (y : K q) : ℝ := ∑ σ : K q →ₐ[ℚ] ℂ, ‖σ y‖ ^ 2

def N₂ {q : ℕ} (y : K q × K q) : ℝ := N y.1 + N y.2

def evalQ {q : ℕ} [NeZero q] (z : ZMod q → ℚ) : K q :=
  ∑ a, algebraMap ℚ (K q) (z a) * zeta q ^ a.val

def evalZ {q : ℕ} [NeZero q] (z : ZMod q → ℤ) : K q :=
  ∑ a, (z a : K q) * zeta q ^ a.val

def coeffNorm {q : ℕ} [NeZero q] (z : ZMod q → ℤ) : ℝ := ∑ a, (z a : ℝ) ^ 2

def coeffSum {q : ℕ} [NeZero q] (z : ZMod q → ℤ) : ℤ := ∑ a, z a

def binary {q : ℕ} [NeZero q] (z : ZMod q → ℤ) : Prop := ∀ a, z a = 0 ∨ z a = 1

def pi (q : ℕ) [NeZero q] : K q := 1 - zeta q

/-- The actual principal ideal as an additive subgroup of the field. -/
def idealGroup (q k : ℕ) [NeZero q] : AddSubgroup (K q) where
  carrier := {v | ∃ r : K q, r ∈ OK q ∧ v = pi q ^ k * r}
  zero_mem' := ⟨0, (OK q).zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
    exact ⟨r + s, (OK q).add_mem hr hs, by ring⟩
  neg_mem' := by
    rintro x ⟨r, hr, rfl⟩
    exact ⟨-r, (OK q).neg_mem hr, by ring⟩

def idealSet (q k : ℕ) [NeZero q] : Set (K q) := idealGroup q k

def syndrome {q : ℕ} (k : ℕ) [NeZero q] (z : ZMod q → ℤ) : Fin k → ZMod q :=
  fun j => ∑ a, (z a : ZMod q) * a ^ j.val

def RSLattice (q k : ℕ) [NeZero q] : AddSubgroup (ZMod q → ℤ) where
  carrier := {z | syndrome k z = 0}
  zero_mem' := by ext j; simp [syndrome]
  add_mem' := by
    intro x y hx hy
    ext j
    have hx' := congrFun hx j
    have hy' := congrFun hy j
    simpa [syndrome, Int.cast_add, add_mul, Finset.sum_add_distrib] using congrArg₂ (· + ·) hx' hy'
  neg_mem' := by
    intro x hx
    ext j
    have hx' := congrFun hx j
    simpa [syndrome] using congrArg Neg.neg hx'

def zeroSumRS (q k : ℕ) [NeZero q] : AddSubgroup (ZMod q → ℤ) :=
  (RSLattice q k) ⊓
    { carrier := {z | coeffSum z = 0}
      zero_mem' := by simp [coeffSum]
      add_mem' := by intro x y hx hy; simpa [coeffSum, Finset.sum_add_distrib] using congrArg₂ (· + ·) hx hy
      neg_mem' := by intro x hx; simpa [coeffSum] using congrArg Neg.neg hx }

/-- Squared first minimum as an infimum; only used on nonzero discrete source lattices. -/
def firstSquared {α : Type*} [Zero α] (normSq : α → ℝ) (S : Set α) : ℝ :=
  sInf {t | ∃ v ∈ S, v ≠ 0 ∧ t = normSq v}

def distanceSquared {q : ℕ} (v : K q) (S : Set (K q)) : ℝ :=
  sInf {t | ∃ y ∈ S, t = N (v - y)}

def powerSumFiber (q k m : ℕ) [NeZero q] (b : Fin (k - 1) → ZMod q) : Finset (Fin m → ZMod q) :=
  Finset.univ.filter fun z => ∀ j, ∑ r, z r ^ (j.val + 1) = b j

end CyclotomicRankTwoSVP.Main


