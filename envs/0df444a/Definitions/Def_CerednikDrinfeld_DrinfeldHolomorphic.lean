-- Prove2me | Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
-- name    : CerednikDrinfeld_DrinfeldHolomorphic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/e5ed0583-2b4c-5f24-be66-7b7b2426fe5b
-- title:
--   Rigid holomorphic functions on Drinfeld's upper half plane
-- statement:
--   Fix a field $K_0$, a valued field $K$ (values in a linearly ordered commutative group with zero) and a $K_0$-algebra structure on $K$. A `PseudoUniformizer` is a structure carrying an element $\varpi \in K_0$ together with proofs that $0 < v(\varpi) < 1$ and that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N$. For such a $\varpi$, `affinoid` $n$ is the set of $z \in K$ with $v(z) \le v(\varpi)^{-n}$ and $v(z-a) \ge v(\varpi)^{n}$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$; `mem_affinoid_iff'` removes the restriction on $a$, `affinoid_mono` records monotonicity in $n$, and each affinoid lies in `upperHalfPlane K₀ K`, the complement of the image of $K_0$ in $K$. `IsExhausted` is the predicate that these sets cover the upper half plane; it is defined, not asserted.
--
--   Rational functions are handled through presentations: a `RatPair` is a pair of polynomials over $K$, with pole-freeness on a set, evaluation $z \mapsto \mathrm{num}(z)/\mathrm{den}(z)$, sum, product, negation and constants defined on presentations, homogenisation `homog` of a polynomial in a chosen degree $D$ (so that its value at $z$ is $(cz+d)^D P((az+b)/(cz+d))$), the resulting Möbius pull-back along $g \in \mathrm{GL}_2(K_0)$, and the coefficientwise image under a ring automorphism of $K$. `IsHolOn K S f`, for $f$ on a subset $S \subseteq K$, asserts the existence of a sequence of `RatPair`s, pole-free on $S$, whose values on $S$ are bounded by a single $v(b)$ uniformly in the index, converging to $f$ uniformly on $S$; uniform convergence is tested through `vRestrict`, the restriction of the valuation to its value group, whose unit group indexes a basis of the uniformity. These functions form a subring `holOn K S`, and `holRing ϖ` is the subring of functions on the upper half plane holomorphic in this sense on every affinoid; `holSubalgebra` makes it a $K$-algebra and `merField ϖ` is its fraction field.
--
--   $\mathrm{PGL}_2(K_0)$ acts on the upper half plane by Möbius transformations; `exists_mapsTo_affinoid` produces, for each $g$ and $n$, an index $m$ with $g(\Omega_n) \subseteq \Omega_m$ (by explicit valuation estimates on the entries and determinant of a lift, with $m = 3n + 3N$), whence precomposition with $g^{-1}$ preserves `holRing` and gives a `MulSemiringAction` commuting with the $K$-action. An `IsometricAut K₀ K` is a structure carrying a ring automorphism of $K$ together with proofs that it preserves $v$ and fixes $K_0$ pointwise; such automorphisms form a group, preserve each affinoid, commute with the Möbius action, act on `holRing` coefficientwise, and thereby map to `Mumford.AmbientSemilinearAut K PGL(2, K₀)` of the holomorphic ring, by a group homomorphism. Finally, for an abstract $\rho : G \to \mathrm{PGL}_2(K_0)$, `HolRingOf ϖ ρ` is a type synonym of `holRing ϖ` carrying the $G$-action obtained along $\rho$, with the corresponding semilinear automorphisms.
--
--   **Relation to Mathlib.** Mathlib has no rigid analytic geometry and no Drinfeld upper half plane; the ring of holomorphic functions is built here from scratch, using only Mathlib's valued-field topology and `TendstoUniformly`. Rational functions are not taken from Mathlib's `RatFunc` but presented as pairs of polynomials (`RatPair`), so that pole-freeness and Möbius pull-back can be stated on a chosen presentation.
--
--   **Where it is used.** The ring defined here is the coefficient ring for the Mumford-quotient layer of the Čerednik–Drinfeld description: its fraction field `merField ϖ` carries the actions of a discrete group $G$ (through $\rho$) and of the isometric automorphisms of $K$ over $K_0$, whose invariants are the Mumford field and its type-preserving variant, giving the $p$-adic uniformisation of Shimura curves used on the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_DrinfeldHolomorphic.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open Filter CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace CerednikDrinfeld.Omega

variable (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

structure PseudoUniformizer where

  ϖ : K₀
  pos : 0 < Valued.v (algebraMap K₀ K ϖ)
  lt_one : Valued.v (algebraMap K₀ K ϖ) < 1
  scale : ∀ a : K₀, a ≠ 0 → ∃ N : ℕ, Valued.v (algebraMap K₀ K ϖ) ^ N ≤ Valued.v (algebraMap K₀ K a) ∧
    Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ))⁻¹ ^ N

variable {K₀ K} (ϖ : PseudoUniformizer K₀ K)

def affinoid (n : ℕ) : Set K :=
  {z | Valued.v z ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n ∧
    ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
      (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ Valued.v (z - algebraMap K₀ K a)}

theorem affinoid_subset_upperHalfPlane (n : ℕ) : affinoid ϖ n ⊆ upperHalfPlane K₀ K := by
  rintro z ⟨hz₁, hz₂⟩
  rw [mem_upperHalfPlane_iff]
  rintro a rfl
  have h := hz₂ a hz₁
  rw [sub_self, map_zero, le_zero_iff] at h
  exact pow_ne_zero n ϖ.pos.ne' h

theorem affinoid_mono : Monotone (affinoid ϖ) := by
  refine monotone_nat_of_le_succ fun n => ?_
  rintro z ⟨hz₁, hz₂⟩
  have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ≤ 1 := ϖ.lt_one.le
  have hinv : 1 ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := (one_le_inv₀ ϖ.pos).2 hp1
  have hup : (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ (n + 1) :=
    pow_le_pow_right₀ hinv (Nat.le_succ n)
  have hdown : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n :=
    pow_le_pow_right_of_le_one' hp1 (Nat.le_succ n)
  refine ⟨hz₁.trans hup, fun a ha => ?_⟩
  rcases le_or_gt (Valued.v (algebraMap K₀ K a)) ((Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n) with h | h
  · exact hdown.trans (hz₂ a h)
  ·
    have hza : Valued.v z < Valued.v (-(algebraMap K₀ K a)) := by rw [Valuation.map_neg]; exact hz₁.trans_lt h
    have heq : Valued.v (z - algebraMap K₀ K a) = Valued.v (algebraMap K₀ K a) := by
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ hza, Valuation.map_neg]
    rw [heq]
    have h1 : (1 : Γ₀) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := one_le_pow₀ hinv
    exact ((pow_le_one₀ zero_le' hp1).trans (h1.trans h.le))

theorem mem_affinoid_iff' (n : ℕ) (z : K) :
    z ∈ affinoid ϖ n ↔ Valued.v z ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n ∧
      ∀ a : K₀, (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n ≤ Valued.v (z - algebraMap K₀ K a) := by
  constructor
  · rintro ⟨hz₁, hz₂⟩
    refine ⟨hz₁, fun a => ?_⟩
    rcases le_or_gt (Valued.v (algebraMap K₀ K a)) ((Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n) with h | h
    · exact hz₂ a h
    · have hp1 : Valued.v (algebraMap K₀ K ϖ.ϖ) ≤ 1 := ϖ.lt_one.le
      have hinv : 1 ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ := (one_le_inv₀ ϖ.pos).2 hp1
      have hza : Valued.v z < Valued.v (-(algebraMap K₀ K a)) := by rw [Valuation.map_neg]; exact hz₁.trans_lt h
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_right _ hza, Valuation.map_neg]
      exact (pow_le_one₀ zero_le' hp1).trans ((one_le_pow₀ hinv).trans h.le)
  · rintro ⟨hz₁, hz₂⟩
    exact ⟨hz₁, fun a _ => hz₂ a⟩

def IsExhausted : Prop := ∀ z ∈ upperHalfPlane K₀ K, ∃ n, z ∈ affinoid ϖ n

structure RatPair (K : Type) [Field K] where

  num : Polynomial K

  den : Polynomial K

namespace RatPair

def IsPoleFreeOn (S : Set K) (r : RatPair K) : Prop := ∀ z ∈ S, r.den.eval z ≠ 0

def evalAt (r : RatPair K) (z : K) : K := r.num.eval z / r.den.eval z

def const (c : K) : RatPair K := ⟨Polynomial.C c, 1⟩

def add (p q : RatPair K) : RatPair K := ⟨p.num * q.den + q.num * p.den, p.den * q.den⟩

def mul (p q : RatPair K) : RatPair K := ⟨p.num * q.num, p.den * q.den⟩

def neg (p : RatPair K) : RatPair K := ⟨-p.num, p.den⟩

theorem isPoleFreeOn_const (S : Set K) (c : K) : (const c).IsPoleFreeOn S := fun z _ => by
  simp [const]

theorem isPoleFreeOn_add {S : Set K} {p q : RatPair K} (hp : p.IsPoleFreeOn S) (hq : q.IsPoleFreeOn S) :
    (add p q).IsPoleFreeOn S := fun z hz => by
  simp only [add, Polynomial.eval_mul]
  exact mul_ne_zero (hp z hz) (hq z hz)

theorem isPoleFreeOn_mul {S : Set K} {p q : RatPair K} (hp : p.IsPoleFreeOn S) (hq : q.IsPoleFreeOn S) :
    (mul p q).IsPoleFreeOn S := fun z hz => by
  simp only [mul, Polynomial.eval_mul]
  exact mul_ne_zero (hp z hz) (hq z hz)

theorem isPoleFreeOn_neg {S : Set K} {p : RatPair K} (hp : p.IsPoleFreeOn S) : (neg p).IsPoleFreeOn S := hp

@[simp] theorem evalAt_const (c z : K) : (const c).evalAt z = c := by simp [const, evalAt]

theorem evalAt_add {p q : RatPair K} {z : K} (hp : p.den.eval z ≠ 0) (hq : q.den.eval z ≠ 0) :
    (add p q).evalAt z = p.evalAt z + q.evalAt z := by
  simp only [add, evalAt, Polynomial.eval_add, Polynomial.eval_mul]
  field_simp

theorem evalAt_mul (p q : RatPair K) (z : K) : (mul p q).evalAt z = p.evalAt z * q.evalAt z := by
  simp only [mul, evalAt, Polynomial.eval_mul]
  rw [div_mul_div_comm]

@[simp] theorem evalAt_neg (p : RatPair K) (z : K) : (neg p).evalAt z = -p.evalAt z := by
  simp [neg, evalAt, neg_div]

def homog (a b c d : K) (D : ℕ) (P : Polynomial K) : Polynomial K :=
  ∑ i ∈ Finset.range (D + 1), Polynomial.C (P.coeff i) * (Polynomial.C a * Polynomial.X + Polynomial.C b) ^ i *
    (Polynomial.C c * Polynomial.X + Polynomial.C d) ^ (D - i)

theorem eval_homog {a b c d : K} {D : ℕ} {P : Polynomial K} (hD : P.natDegree ≤ D) (z : K) (hcd : c * z + d ≠ 0) :
    (homog a b c d D P).eval z = (c * z + d) ^ D * P.eval ((a * z + b) / (c * z + d)) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hD), Finset.mul_sum, homog, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
  rw [div_pow, pow_sub₀ _ hcd hi']
  field_simp

def pullback (g : GL (Fin 2) K₀) (r : RatPair K) : RatPair K :=
  ⟨homog (algebraMap K₀ K (g 0 0)) (algebraMap K₀ K (g 0 1)) (algebraMap K₀ K (g 1 0)) (algebraMap K₀ K (g 1 1))
      (max r.num.natDegree r.den.natDegree) r.num,
   homog (algebraMap K₀ K (g 0 0)) (algebraMap K₀ K (g 0 1)) (algebraMap K₀ K (g 1 0)) (algebraMap K₀ K (g 1 1))
      (max r.num.natDegree r.den.natDegree) r.den⟩

theorem pullback_den_eval {z : K} (hz : z ∈ upperHalfPlane K₀ K) (g : GL (Fin 2) K₀) (r : RatPair K) :
    (pullback g r).den.eval z =
      (algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1)) ^ (max r.num.natDegree r.den.natDegree) *
        r.den.eval (moebius K₀ K g z) := by
  rw [pullback, eval_homog (le_max_right _ _) z (moebius_denom_ne_zero_of_mem K₀ hz g), moebius]

theorem evalAt_pullback {z : K} (hz : z ∈ upperHalfPlane K₀ K) (g : GL (Fin 2) K₀) (r : RatPair K) :
    (pullback g r).evalAt z = r.evalAt (moebius K₀ K g z) := by
  have hcd := moebius_denom_ne_zero_of_mem K₀ hz g
  rw [evalAt, evalAt, pullback_den_eval hz, pullback,
    eval_homog (le_max_left _ _) z hcd, ← moebius, mul_div_mul_left _ _ (pow_ne_zero _ hcd)]

theorem isPoleFreeOn_pullback {S S' : Set K} (hS : S ⊆ upperHalfPlane K₀ K) (g : GL (Fin 2) K₀)
    (hmaps : Set.MapsTo (moebius K₀ K g) S S') (r : RatPair K) (hr : r.IsPoleFreeOn S') :
    (pullback g r).IsPoleFreeOn S := fun z hz => by
  rw [pullback_den_eval (hS hz)]
  exact mul_ne_zero (pow_ne_zero _ (moebius_denom_ne_zero_of_mem K₀ (hS hz) g)) (hr _ (hmaps hz))

def map (s : K ≃+* K) (r : RatPair K) : RatPair K := ⟨r.num.map (s : K →+* K), r.den.map (s : K →+* K)⟩

theorem map_den_eval (s : K ≃+* K) (r : RatPair K) (z : K) : (r.map s).den.eval (s z) = s (r.den.eval z) := by
  rw [map, Polynomial.eval_map]; exact Polynomial.eval₂_hom (s : K →+* K) z

theorem map_num_eval (s : K ≃+* K) (r : RatPair K) (z : K) : (r.map s).num.eval (s z) = s (r.num.eval z) := by
  rw [map, Polynomial.eval_map]; exact Polynomial.eval₂_hom (s : K →+* K) z

theorem evalAt_map (s : K ≃+* K) (r : RatPair K) (z : K) : (r.map s).evalAt (s z) = s (r.evalAt z) := by
  rw [evalAt, evalAt, map_den_eval, map_num_eval, map_div₀]

end RatPair

section Hol

variable (K)

abbrev vRestrict : Valuation K (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v (R := K)))) := (Valued.v (R := K)).restrict

theorem v_le_iff_vRestrict_le (x y : K) : Valued.v x ≤ Valued.v y ↔ vRestrict K x ≤ vRestrict K y :=
  (Valuation.isEquiv_restrict (Valued.v (R := K))).le_iff_le

theorem v_lt_iff_vRestrict_lt (x y : K) : Valued.v x < Valued.v y ↔ vRestrict K x < vRestrict K y :=
  (Valuation.isEquiv_restrict (Valued.v (R := K))).lt_iff_lt

theorem tendstoUniformly_iff_vRestrict {α : Type} (F : ℕ → α → K) (f : α → K) :
    TendstoUniformly F f atTop ↔
      ∀ γ : (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v (R := K))))ˣ, ∀ᶠ k in atTop, ∀ z, vRestrict K (F k z - f z) < γ := by
  rw [(Filter.atTop_basis).tendstoUniformly_iff (Valued.hasBasis_uniformity K Γ₀)]
  constructor
  · intro h γ
    obtain ⟨j, -, hj⟩ := h γ trivial
    exact Filter.eventually_atTop.2 ⟨j, fun k hk z => hj hk z⟩
  · intro h γ _
    obtain ⟨j, hj⟩ := Filter.eventually_atTop.1 (h γ)
    exact ⟨j, trivial, fun k hk z => hj k hk z⟩

def IsHolOn (S : Set K) (f : ↥S → K) : Prop :=
  ∃ r : ℕ → RatPair K, (∀ k, (r k).IsPoleFreeOn S) ∧
    (∃ b : K, ∀ k (z : ↥S), Valued.v ((r k).evalAt z) ≤ Valued.v b) ∧
    TendstoUniformly (fun k (z : ↥S) => (r k).evalAt z) f atTop

variable {K}

theorem isHolOn_ratPair {S : Set K} (r : RatPair K) (hr : r.IsPoleFreeOn S)
    (hb : ∃ b : K, ∀ z ∈ S, Valued.v (r.evalAt z) ≤ Valued.v b) : IsHolOn K S (fun z => r.evalAt z) := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨fun _ => r, fun _ => hr, ⟨b, fun _ z => hb z z.2⟩, ?_⟩
  rw [tendstoUniformly_iff_vRestrict]
  intro γ
  exact Filter.Eventually.of_forall fun k z => by simp

theorem IsHolOn.const (S : Set K) (c : K) : IsHolOn K S (fun _ => c) := by
  have := isHolOn_ratPair (S := S) (RatPair.const c) (RatPair.isPoleFreeOn_const S c) ⟨c, fun z _ => by simp⟩
  simpa using this

theorem exists_bound (b b' : K) : ∃ B : K, B ≠ 0 ∧ Valued.v b ≤ Valued.v B ∧ Valued.v b' ≤ Valued.v B ∧ 1 ≤ Valued.v B := by
  rcases le_total (Valued.v b) (Valued.v b') with h | h
  · rcases le_total (Valued.v b') 1 with h1 | h1
    · exact ⟨1, one_ne_zero, by rw [map_one]; exact h.trans h1, by rw [map_one]; exact h1, by rw [map_one]⟩
    · exact ⟨b', fun h0 => by rw [h0, map_zero] at h1; exact not_lt.2 h1 zero_lt_one, h, le_rfl, h1⟩
  · rcases le_total (Valued.v b) 1 with h1 | h1
    · exact ⟨1, one_ne_zero, by rw [map_one]; exact h1, by rw [map_one]; exact h.trans h1, by rw [map_one]⟩
    · exact ⟨b, fun h0 => by rw [h0, map_zero] at h1; exact not_lt.2 h1 zero_lt_one, le_rfl, h, h1⟩

theorem IsHolOn.bounded {S : Set K} {f : ↥S → K} (h : IsHolOn K S f) : ∃ B : K, ∀ z, Valued.v (f z) ≤ Valued.v B := by
  obtain ⟨r, -, ⟨b, hb⟩, hlim⟩ := h
  rw [tendstoUniformly_iff_vRestrict] at hlim
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 (hlim 1)
  obtain ⟨B, -, hbB, -, h1B⟩ := exists_bound b b
  refine ⟨B, fun z => ?_⟩
  rw [v_le_iff_vRestrict_le]
  have h1 : vRestrict K ((r k).evalAt z - f z) < 1 := hk k le_rfl z
  have : f z = (r k).evalAt z - ((r k).evalAt z - f z) := by ring
  rw [this]
  refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
  · exact (v_le_iff_vRestrict_le K _ _).1 ((hb k z).trans hbB)
  · exact h1.le.trans (by rw [← map_one (vRestrict K)]; exact (v_le_iff_vRestrict_le K _ _).1 (by rwa [map_one]))

theorem IsHolOn.neg {S : Set K} {f : ↥S → K} (h : IsHolOn K S f) : IsHolOn K S (-f) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := h
  refine ⟨fun k => (r k).neg, fun k => RatPair.isPoleFreeOn_neg (hr k), ⟨b, fun k z => ?_⟩, ?_⟩
  · rw [RatPair.evalAt_neg, Valuation.map_neg]; exact hb k z
  · rw [tendstoUniformly_iff_vRestrict] at hlim ⊢
    intro γ
    filter_upwards [hlim γ] with k hk z
    rw [RatPair.evalAt_neg, Pi.neg_apply, show -(r k).evalAt z - -f z = -((r k).evalAt z - f z) by ring,
      Valuation.map_neg]
    exact hk z

theorem IsHolOn.add {S : Set K} {f g : ↥S → K} (hf : IsHolOn K S f) (hg : IsHolOn K S g) : IsHolOn K S (f + g) := by
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  obtain ⟨q, hq, ⟨d, hd⟩, hlim'⟩ := hg
  obtain ⟨B, -, hbB, hdB, -⟩ := exists_bound b d
  refine ⟨fun k => (r k).add (q k), fun k => RatPair.isPoleFreeOn_add (hr k) (hq k), ⟨B, fun k z => ?_⟩, ?_⟩
  · rw [RatPair.evalAt_add (hr k z z.2) (hq k z z.2)]
    exact (Valuation.map_add _ _ _).trans (max_le ((hb k z).trans hbB) ((hd k z).trans hdB))
  · rw [tendstoUniformly_iff_vRestrict] at hlim hlim' ⊢
    intro γ
    filter_upwards [hlim γ, hlim' γ] with k hk hk' z
    rw [RatPair.evalAt_add (hr k z z.2) (hq k z z.2), Pi.add_apply,
      show (r k).evalAt z + (q k).evalAt z - (f z + g z) = ((r k).evalAt z - f z) + ((q k).evalAt z - g z) by ring]
    exact Valuation.map_add_lt _ (hk z) (hk' z)

theorem IsHolOn.mul {S : Set K} {f g : ↥S → K} (hf : IsHolOn K S f) (hg : IsHolOn K S g) : IsHolOn K S (f * g) := by
  obtain ⟨bg, hbg⟩ := hg.bounded
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf
  obtain ⟨q, hq, ⟨d, hd⟩, hlim'⟩ := hg
  refine ⟨fun k => (r k).mul (q k), fun k => RatPair.isPoleFreeOn_mul (hr k) (hq k), ⟨b * d, fun k z => ?_⟩, ?_⟩
  · rw [RatPair.evalAt_mul, Valuation.map_mul, Valuation.map_mul]
    exact mul_le_mul' (hb k z) (hd k z)
  · rw [tendstoUniformly_iff_vRestrict] at hlim hlim' ⊢
    intro γ
    obtain ⟨B, hB0, hbB, hbgB, -⟩ := exists_bound b bg
    have hwB : vRestrict K B ≠ 0 := by rwa [ne_eq, map_eq_zero]
    let c' : (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v (R := K))))ˣ := Units.mk0 _ hwB
    filter_upwards [hlim (γ / c'), hlim' (γ / c')] with k hk hk' z
    rw [RatPair.evalAt_mul, Pi.mul_apply,
      show (r k).evalAt z * (q k).evalAt z - f z * g z =
        (r k).evalAt z * ((q k).evalAt z - g z) + g z * ((r k).evalAt z - f z) by ring]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul]
      calc vRestrict K ((r k).evalAt ↑z) * vRestrict K ((q k).evalAt ↑z - g z)
          < (c' : MonoidWithZeroHom.ValueGroup₀ _) * ((γ / c' : (MonoidWithZeroHom.ValueGroup₀ _)ˣ) : MonoidWithZeroHom.ValueGroup₀ _) :=
            mul_lt_mul_of_le_of_lt_of_nonneg_of_pos ((v_le_iff_vRestrict_le K _ _).1 ((hb k z).trans hbB)) (hk' z) zero_le'
              (Units.zero_lt c')
        _ = γ := by rw [Units.val_div_eq_div_val, mul_div_cancel₀ _ c'.ne_zero]
    · rw [Valuation.map_mul]
      calc vRestrict K (g z) * vRestrict K ((r k).evalAt ↑z - f z)
          < (c' : MonoidWithZeroHom.ValueGroup₀ _) * ((γ / c' : (MonoidWithZeroHom.ValueGroup₀ _)ˣ) : MonoidWithZeroHom.ValueGroup₀ _) :=
            mul_lt_mul_of_le_of_lt_of_nonneg_of_pos ((v_le_iff_vRestrict_le K _ _).1 ((hbg z).trans hbgB)) (hk z) zero_le'
              (Units.zero_lt c')
        _ = γ := by rw [Units.val_div_eq_div_val, mul_div_cancel₀ _ c'.ne_zero]

theorem IsHolOn.one (S : Set K) : IsHolOn K S 1 := IsHolOn.const S 1
theorem IsHolOn.zero (S : Set K) : IsHolOn K S 0 := IsHolOn.const S 0

variable (K) in

def holOn (S : Set K) : Subring (↥S → K) where
  carrier := {f | IsHolOn K S f}
  mul_mem' hf hg := hf.mul hg
  one_mem' := IsHolOn.one S
  add_mem' hf hg := hf.add hg
  zero_mem' := IsHolOn.zero S
  neg_mem' hf := hf.neg

theorem mem_holOn_iff {S : Set K} (f : ↥S → K) : f ∈ holOn K S ↔ IsHolOn K S f := Iff.rfl

end Hol

def restrictAffinoid (n : ℕ) (f : ↥(upperHalfPlane K₀ K) → K) : ↥(affinoid ϖ n) → K :=
  f ∘ Set.inclusion (affinoid_subset_upperHalfPlane ϖ n)

def holRing : Subring (↥(upperHalfPlane K₀ K) → K) where
  carrier := {f | ∀ n, IsHolOn K (affinoid ϖ n) (restrictAffinoid ϖ n f)}
  mul_mem' hf hg := fun n => (hf n).mul (hg n)
  one_mem' := fun _ => IsHolOn.one _
  add_mem' hf hg := fun n => (hf n).add (hg n)
  zero_mem' := fun _ => IsHolOn.zero _
  neg_mem' hf := fun n => (hf n).neg

theorem mem_holRing_iff (f : ↥(upperHalfPlane K₀ K) → K) :
    f ∈ holRing ϖ ↔ ∀ n, IsHolOn K (affinoid ϖ n) (restrictAffinoid ϖ n f) := Iff.rfl

theorem const_mem_holRing (c : K) : (fun _ => c : ↥(upperHalfPlane K₀ K) → K) ∈ holRing ϖ := fun _ =>
  IsHolOn.const _ c

def holSubalgebra : Subalgebra K (↥(upperHalfPlane K₀ K) → K) :=
  { holRing ϖ with algebraMap_mem' := fun c => const_mem_holRing ϖ c }

instance holRingAlgebra : Algebra K ↥(holRing ϖ) := (holSubalgebra ϖ).algebra

@[simp] theorem algebraMap_holRing_apply (c : K) (z : ↥(upperHalfPlane K₀ K)) :
    ((algebraMap K ↥(holRing ϖ) c : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) z = c := rfl

section Actions

variable [DecidableEq K]

instance pglOmegaAction : MulAction PGL(2, K₀) ↥(upperHalfPlane K₀ K) where
  smul g z := ⟨pmoebius K₀ g (z : K), pmoebius_mem_upperHalfPlane K₀ z.2 g⟩
  one_smul z := Subtype.ext (pmoebius_one K₀ (z : K))
  mul_smul g h z := Subtype.ext (pmoebius_mul K₀ z.2 g h)

theorem coe_smul_upperHalfPlane (g : PGL(2, K₀)) (z : ↥(upperHalfPlane K₀ K)) :
    ((g • z : ↥(upperHalfPlane K₀ K)) : K) = pmoebius K₀ g (z : K) := rfl

def precomp (g : PGL(2, K₀)) (f : ↥(upperHalfPlane K₀ K) → K) : ↥(upperHalfPlane K₀ K) → K := fun z => f (g⁻¹ • z)

theorem precomp_one (f : ↥(upperHalfPlane K₀ K) → K) : precomp (1 : PGL(2, K₀)) f = f :=
  funext fun z => by rw [precomp, inv_one, one_smul]

theorem precomp_mul (g h : PGL(2, K₀)) (f : ↥(upperHalfPlane K₀ K) → K) :
    precomp (g * h) f = precomp g (precomp h f) :=
  funext fun z => by simp only [precomp, mul_inv_rev, mul_smul]

section Stab

local notation "𝔭" => Valued.v (algebraMap K₀ K ϖ.ϖ)

omit [DecidableEq K] in
private theorem p_le_one : 𝔭 ≤ 1 := ϖ.lt_one.le

omit [DecidableEq K] in
private theorem one_le_P : 1 ≤ 𝔭⁻¹ := (one_le_inv₀ ϖ.pos).2 (p_le_one ϖ)

omit [DecidableEq K] in
private theorem p_pow_anti {i j : ℕ} (h : i ≤ j) : 𝔭 ^ j ≤ 𝔭 ^ i := pow_le_pow_right_of_le_one' (p_le_one ϖ) h

omit [DecidableEq K] in
private theorem P_pow_mono {i j : ℕ} (h : i ≤ j) : 𝔭⁻¹ ^ i ≤ 𝔭⁻¹ ^ j := pow_le_pow_right₀ (one_le_P ϖ) h

omit [DecidableEq K] in
private theorem P_pow_mul_p_pow (i : ℕ) : 𝔭⁻¹ ^ i * 𝔭 ^ i = 1 := by
  rw [← mul_pow, inv_mul_cancel₀ ϖ.pos.ne', one_pow]

omit [DecidableEq K] in

private theorem exists_common_scale (l : List K₀) :
    ∃ N : ℕ, ∀ e ∈ l, e ≠ 0 → 𝔭 ^ N ≤ Valued.v (algebraMap K₀ K e) ∧ Valued.v (algebraMap K₀ K e) ≤ 𝔭⁻¹ ^ N := by
  induction l with
  | nil => exact ⟨0, fun e he => by simp at he⟩
  | cons x l ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases hx : x = 0
    · exact ⟨N, fun e he hne => by
        rcases List.mem_cons.1 he with rfl | he
        · exact absurd hx hne
        · exact hN e he hne⟩
    · obtain ⟨M, hM₁, hM₂⟩ := ϖ.scale x hx
      refine ⟨max N M, fun e he hne => ?_⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨(p_pow_anti ϖ (le_max_right N M)).trans hM₁, hM₂.trans (P_pow_mono ϖ (le_max_right N M))⟩
      · exact ⟨(p_pow_anti ϖ (le_max_left N M)).trans (hN e he hne).1,
          (hN e he hne).2.trans (P_pow_mono ϖ (le_max_left N M))⟩

omit [DecidableEq K] in

private theorem linear_lower {n : ℕ} {z : K} (hz : z ∈ affinoid ϖ n) (α β : K₀) (hα : α ≠ 0) :
    Valued.v (algebraMap K₀ K α) * 𝔭 ^ n ≤ Valued.v (algebraMap K₀ K α * z + algebraMap K₀ K β) := by
  have hα' : algebraMap K₀ K α ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have : algebraMap K₀ K α * z + algebraMap K₀ K β = algebraMap K₀ K α * (z - algebraMap K₀ K (-(β / α))) := by
    rw [map_neg, map_div₀, sub_neg_eq_add, mul_add, mul_div_cancel₀ _ hα']
  rw [this, Valuation.map_mul]
  exact mul_le_mul_right (((mem_affinoid_iff' ϖ n z).1 hz).2 _) _

omit [DecidableEq K] in

private theorem linear_upper {n : ℕ} {z : K} (hz : Valued.v z ≤ 𝔭⁻¹ ^ n) (α β : K) :
    Valued.v (α * z + β) ≤ max (Valued.v α * 𝔭⁻¹ ^ n) (Valued.v β) :=
  (Valuation.map_add _ _ _).trans (max_le_max (by rw [Valuation.map_mul]; exact mul_le_mul_right hz _) le_rfl)

theorem exists_mapsTo_affinoid (g : PGL(2, K₀)) (n : ℕ) :
    ∃ m : ℕ, Set.MapsTo (pmoebius K₀ g) (affinoid ϖ n) (affinoid ϖ m) := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | _ γ =>
  obtain ⟨N, hN⟩ := exists_common_scale ϖ [γ 0 0, γ 0 1, γ 1 0, γ 1 1, Matrix.det (γ : Matrix (Fin 2) (Fin 2) K₀)]
  refine ⟨3 * n + 3 * N, fun z hz => ?_⟩
  have hzΩ : z ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n hz
  have hz1 : Valued.v z ≤ 𝔭⁻¹ ^ n := ((mem_affinoid_iff' ϖ n z).1 hz).1
  set a := γ 0 0 with ha; set b := γ 0 1 with hb; set c := γ 1 0 with hc; set d := γ 1 1 with hd
  have hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) K₀) = a * d - b * c := by rw [Matrix.det_fin_two]
  have hdet0 : a * d - b * c ≠ 0 := hdet ▸ γ.det_ne_zero
  have hcd : algebraMap K₀ K c * z + algebraMap K₀ K d ≠ 0 := moebius_denom_ne_zero_of_mem K₀ hzΩ γ
  rw [pmoebius_mk K₀ γ z hcd, moebius]

  have sa := hN a (by simp); have sb := hN b (by simp); have sc := hN c (by simp); have sd := hN d (by simp)
  have sdet := hN (Matrix.det (γ : Matrix (Fin 2) (Fin 2) K₀)) (by simp)
  rw [hdet] at sdet
  have hP1 := one_le_P ϖ
  have hp1 := p_le_one ϖ

  have hden_lo : 𝔭 ^ (n + N) ≤ Valued.v (algebraMap K₀ K c * z + algebraMap K₀ K d) := by
    by_cases hc0 : c = 0
    · have hd0 : d ≠ 0 := fun hd0 => hdet0 (by rw [hc0, hd0, mul_zero, mul_zero, sub_zero])
      rw [hc0, map_zero, zero_mul, zero_add]
      exact (p_pow_anti ϖ (Nat.le_add_left N n)).trans (sd hd0).1
    · calc 𝔭 ^ (n + N) = 𝔭 ^ N * 𝔭 ^ n := by rw [pow_add, mul_comm]
        _ ≤ Valued.v (algebraMap K₀ K c) * 𝔭 ^ n := mul_le_mul_left (sc hc0).1 _
        _ ≤ _ := linear_lower ϖ hz c d hc0
  have entry_le : ∀ e : K₀, (e ≠ 0 → 𝔭 ^ N ≤ Valued.v (algebraMap K₀ K e) ∧ Valued.v (algebraMap K₀ K e) ≤ 𝔭⁻¹ ^ N) →
      Valued.v (algebraMap K₀ K e) ≤ 𝔭⁻¹ ^ N := fun e he => by
    by_cases h0 : e = 0
    · rw [h0, map_zero, map_zero]; exact zero_le'
    · exact (he h0).2
  have hlin_up : ∀ α β : K₀, Valued.v (algebraMap K₀ K α) ≤ 𝔭⁻¹ ^ N → Valued.v (algebraMap K₀ K β) ≤ 𝔭⁻¹ ^ N →
      Valued.v (algebraMap K₀ K α * z + algebraMap K₀ K β) ≤ 𝔭⁻¹ ^ (n + N) := fun α β hα hβ => by
    refine (linear_upper ϖ hz1 _ _).trans (max_le ?_ ?_)
    · rw [pow_add, mul_comm]; exact mul_le_mul_right hα _
    · exact hβ.trans (P_pow_mono ϖ (Nat.le_add_left N n))
  have hden_up := hlin_up c d (entry_le c sc) (entry_le d sd)
  have hnum_up := hlin_up a b (entry_le a sa) (entry_le b sb)
  rw [mem_affinoid_iff']
  constructor
  ·
    rw [map_div₀, div_le_iff₀ (lt_of_lt_of_le (pow_pos ϖ.pos _) hden_lo)]
    refine hnum_up.trans ?_
    calc 𝔭⁻¹ ^ (n + N) = 𝔭⁻¹ ^ (3 * n + 3 * N) * 𝔭 ^ (2 * n + 2 * N) := by
          rw [show 3 * n + 3 * N = (n + N) + (2 * n + 2 * N) by ring, pow_add 𝔭⁻¹ (n + N) (2 * n + 2 * N), mul_assoc,
            P_pow_mul_p_pow, mul_one]
      _ ≤ 𝔭⁻¹ ^ (3 * n + 3 * N) * 𝔭 ^ (n + N) := mul_le_mul_right (p_pow_anti ϖ (by omega)) _
      _ ≤ 𝔭⁻¹ ^ (3 * n + 3 * N) * Valued.v (algebraMap K₀ K c * z + algebraMap K₀ K d) :=
          mul_le_mul_right hden_lo _
  ·
    intro t
    have hsub : (algebraMap K₀ K a * z + algebraMap K₀ K b) / (algebraMap K₀ K c * z + algebraMap K₀ K d) -
        algebraMap K₀ K t =
        (algebraMap K₀ K (a - t * c) * z + algebraMap K₀ K (b - t * d)) /
          (algebraMap K₀ K c * z + algebraMap K₀ K d) := by
      rw [eq_div_iff hcd, sub_mul, div_mul_cancel₀ _ hcd, map_sub, map_sub, map_mul, map_mul]; ring
    rw [hsub, map_div₀, le_div_iff₀ (lt_of_lt_of_le (pow_pos ϖ.pos _) hden_lo)]

    set α := a - t * c with hα
    set β := b - t * d with hβ
    have hkey : α * d - β * c = a * d - b * c := by rw [hα, hβ]; ring
    have hnum_lo : 𝔭 ^ (2 * n + 2 * N) ≤ Valued.v (algebraMap K₀ K α * z + algebraMap K₀ K β) := by
      have hdet_lo : 𝔭 ^ N ≤ Valued.v (algebraMap K₀ K (a * d - b * c)) := (sdet hdet0).1
      have hpN : 0 < 𝔭 ^ N := pow_pos ϖ.pos N

      have hmax : Valued.v (algebraMap K₀ K (a * d - b * c)) ≤
          max (Valued.v (algebraMap K₀ K α) * Valued.v (algebraMap K₀ K d))
            (Valued.v (algebraMap K₀ K β) * Valued.v (algebraMap K₀ K c)) := by
        rw [← hkey, map_sub, map_mul, map_mul, ← Valuation.map_mul, ← Valuation.map_mul]
        exact Valuation.map_sub _ _ _

      have step : ∀ (X E : K₀), 𝔭 ^ N ≤ Valued.v (algebraMap K₀ K X) * Valued.v (algebraMap K₀ K E) →
          Valued.v (algebraMap K₀ K E) ≤ 𝔭⁻¹ ^ N → 𝔭 ^ (2 * N) ≤ Valued.v (algebraMap K₀ K X) := fun X E h1 h2 => by
        calc 𝔭 ^ (2 * N) = 𝔭 ^ N * 𝔭 ^ N := by rw [two_mul, pow_add]
          _ ≤ (Valued.v (algebraMap K₀ K X) * 𝔭⁻¹ ^ N) * 𝔭 ^ N :=
              mul_le_mul_left (h1.trans (mul_le_mul_right h2 _)) _
          _ = Valued.v (algebraMap K₀ K X) := by rw [mul_assoc, P_pow_mul_p_pow, mul_one]
      have fin_lower : ∀ X : K₀, X ≠ 0 → 𝔭 ^ (2 * N) ≤ Valued.v (algebraMap K₀ K X) →
          𝔭 ^ (2 * n + 2 * N) ≤ Valued.v (algebraMap K₀ K X) * 𝔭 ^ n := fun X hX h => by
        calc 𝔭 ^ (2 * n + 2 * N) ≤ 𝔭 ^ (n + 2 * N) := p_pow_anti ϖ (by omega)
          _ = 𝔭 ^ (2 * N) * 𝔭 ^ n := by rw [add_comm, pow_add]
          _ ≤ _ := mul_le_mul_left h _
      rcases le_max_iff.1 hmax with hA | hB
      ·
        have hα0 : α ≠ 0 := by
          intro h0
          rw [h0, map_zero, map_zero, zero_mul] at hA
          exact hpN.ne' (le_zero_iff.1 (hdet_lo.trans hA))
        have hvα := step α d (hdet_lo.trans hA) (entry_le d sd)
        exact (fin_lower α hα0 hvα).trans (linear_lower ϖ hz α β hα0)
      ·
        have hvβ := step β c (hdet_lo.trans hB) (entry_le c sc)
        by_cases hα0 : α = 0
        · rw [hα0, map_zero, zero_mul, zero_add]
          exact (p_pow_anti ϖ (by omega : 2 * N ≤ 2 * n + 2 * N)).trans hvβ
        · rcases lt_or_ge (Valued.v (algebraMap K₀ K α * z)) (Valued.v (algebraMap K₀ K β)) with hlt | hge
          · rw [Valuation.map_add_eq_of_lt_right _ hlt]
            exact (p_pow_anti ϖ (by omega : 2 * N ≤ 2 * n + 2 * N)).trans hvβ
          ·
            have h1 : 𝔭 ^ (2 * N) ≤ Valued.v (algebraMap K₀ K α) * 𝔭⁻¹ ^ n :=
              hvβ.trans (hge.trans (by rw [Valuation.map_mul]; exact mul_le_mul_right hz1 _))
            have h2 : 𝔭 ^ (2 * N) * 𝔭 ^ n ≤ Valued.v (algebraMap K₀ K α) := by
              calc 𝔭 ^ (2 * N) * 𝔭 ^ n ≤ (Valued.v (algebraMap K₀ K α) * 𝔭⁻¹ ^ n) * 𝔭 ^ n := mul_le_mul_left h1 _
                _ = Valued.v (algebraMap K₀ K α) := by rw [mul_assoc, P_pow_mul_p_pow, mul_one]
            calc 𝔭 ^ (2 * n + 2 * N) = (𝔭 ^ (2 * N) * 𝔭 ^ n) * 𝔭 ^ n := by
                  rw [show 2 * n + 2 * N = 2 * N + n + n by ring, pow_add, pow_add]
              _ ≤ Valued.v (algebraMap K₀ K α) * 𝔭 ^ n := mul_le_mul_left h2 _
              _ ≤ _ := linear_lower ϖ hz α β hα0
    calc 𝔭 ^ (3 * n + 3 * N) * Valued.v (algebraMap K₀ K c * z + algebraMap K₀ K d)
        ≤ 𝔭 ^ (3 * n + 3 * N) * 𝔭⁻¹ ^ (n + N) := mul_le_mul_right hden_up _
      _ = 𝔭 ^ (2 * n + 2 * N) := by
          rw [show 3 * n + 3 * N = (2 * n + 2 * N) + (n + N) by ring, pow_add 𝔭 (2 * n + 2 * N) (n + N), mul_assoc,
            mul_comm (𝔭 ^ (n + N)), P_pow_mul_p_pow, mul_one]
      _ ≤ _ := hnum_lo

end Stab

theorem precomp_mem_holRing (g : PGL(2, K₀)) {f : ↥(upperHalfPlane K₀ K) → K} (hf : f ∈ holRing ϖ) :
    precomp g f ∈ holRing ϖ := by
  intro n
  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin 2) K₀, Matrix.ProjGenLinGroup.mk γ = g⁻¹ := by
    induction g⁻¹ using Matrix.ProjGenLinGroup.induction_on with
    | _ γ => exact ⟨γ, rfl⟩
  obtain ⟨m, hm⟩ := exists_mapsTo_affinoid ϖ g⁻¹ n
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf m
  have hΩ : affinoid ϖ n ⊆ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n

  have hpm : ∀ z : K, z ∈ upperHalfPlane K₀ K → pmoebius K₀ g⁻¹ z = moebius K₀ K γ z := fun z hz => by
    rw [← hγ, pmoebius_mk K₀ γ z (moebius_denom_ne_zero_of_mem K₀ hz γ)]
  have hmaps : Set.MapsTo (moebius K₀ K γ) (affinoid ϖ n) (affinoid ϖ m) := fun z hz => by
    rw [← hpm z (hΩ hz)]; exact hm hz
  refine ⟨fun k => (r k).pullback γ, fun k => RatPair.isPoleFreeOn_pullback hΩ γ hmaps (r k) (hr k),
    ⟨b, fun k z => ?_⟩, ?_⟩
  · rw [RatPair.evalAt_pullback (hΩ z.2)]
    exact hb k ⟨_, hmaps z.2⟩
  · rw [tendstoUniformly_iff_vRestrict] at hlim ⊢
    intro δ
    filter_upwards [hlim δ] with k hk z
    have hz' := hk ⟨_, hmaps z.2⟩
    rw [RatPair.evalAt_pullback (hΩ z.2)]

    have harg : (g⁻¹ • (⟨(z : K), hΩ z.2⟩ : ↥(upperHalfPlane K₀ K)) : ↥(upperHalfPlane K₀ K)) =
        ⟨moebius K₀ K γ z, affinoid_subset_upperHalfPlane ϖ m (hmaps z.2)⟩ :=
      Subtype.ext (hpm z (hΩ z.2))
    show vRestrict K ((r k).evalAt (moebius K₀ K γ ↑z) -
      f (g⁻¹ • (⟨(z : K), hΩ z.2⟩ : ↥(upperHalfPlane K₀ K)))) < δ
    rw [harg]
    exact hz'

instance holRingAction : MulSemiringAction PGL(2, K₀) ↥(holRing ϖ) where
  smul g f := ⟨precomp g f, precomp_mem_holRing ϖ g f.2⟩
  one_smul f := Subtype.ext (precomp_one (f : ↥(upperHalfPlane K₀ K) → K))
  mul_smul g h f := Subtype.ext (precomp_mul g h (f : ↥(upperHalfPlane K₀ K) → K))
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

@[simp] theorem coe_smul_holRing_apply (g : PGL(2, K₀)) (f : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) :
    ((g • f : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) z = (f : ↥(upperHalfPlane K₀ K) → K) (g⁻¹ • z) := rfl

instance holRingSMulCommClass : SMulCommClass PGL(2, K₀) K ↥(holRing ϖ) :=
  ⟨fun _ _ _ => rfl⟩

variable (K₀ K) in

structure IsometricAut where

  toRingEquiv : K ≃+* K
  isometry : ∀ x : K, Valued.v (toRingEquiv x) = Valued.v x
  fix : ∀ a : K₀, toRingEquiv (algebraMap K₀ K a) = algebraMap K₀ K a

namespace IsometricAut

omit [DecidableEq K] in
@[ext] theorem ext {s t : IsometricAut K₀ K} (h : s.toRingEquiv = t.toRingEquiv) : s = t := by
  cases s; cases t; congr

instance instGroup : Group (IsometricAut K₀ K) where
  mul s t := ⟨t.toRingEquiv.trans s.toRingEquiv, fun x => by
    rw [RingEquiv.coe_trans, Function.comp_apply, s.isometry, t.isometry],
    fun a => by rw [RingEquiv.coe_trans, Function.comp_apply, t.fix, s.fix]⟩
  one := ⟨RingEquiv.refl K, fun _ => rfl, fun _ => rfl⟩
  inv s := ⟨s.toRingEquiv.symm, fun x => by
    conv_rhs => rw [← s.toRingEquiv.apply_symm_apply x]; rw [s.isometry],
    fun a => by apply s.toRingEquiv.injective; rw [RingEquiv.apply_symm_apply, s.fix]⟩
  mul_assoc s t u := ext rfl
  one_mul s := ext (RingEquiv.ext fun _ => rfl)
  mul_one s := ext (RingEquiv.ext fun _ => rfl)
  inv_mul_cancel s := ext (RingEquiv.ext fun x => s.toRingEquiv.symm_apply_apply x)

omit [DecidableEq K] in
@[simp] theorem inv_toRingEquiv (s : IsometricAut K₀ K) : (s⁻¹).toRingEquiv = s.toRingEquiv.symm := rfl

omit [DecidableEq K] in
theorem mapsTo_upperHalfPlane (s : IsometricAut K₀ K) :
    Set.MapsTo s.toRingEquiv (upperHalfPlane K₀ K) (upperHalfPlane K₀ K) := by
  intro z hz
  rw [mem_upperHalfPlane_iff] at hz ⊢
  intro a ha
  apply hz a
  apply s.toRingEquiv.injective
  rw [s.fix a, ha]

omit [DecidableEq K] in
theorem mapsTo_affinoid (s : IsometricAut K₀ K) (n : ℕ) : Set.MapsTo s.toRingEquiv (affinoid ϖ n) (affinoid ϖ n) := by
  rintro z ⟨hz₁, hz₂⟩
  refine ⟨by rw [s.isometry]; exact hz₁, fun a ha => ?_⟩
  rw [← s.fix a, ← map_sub, s.isometry]
  exact hz₂ a ha

theorem comm_pmoebius (s : IsometricAut K₀ K) (g : PGL(2, K₀)) {z : K} (hz : z ∈ upperHalfPlane K₀ K) :
    s.toRingEquiv (pmoebius K₀ g z) = pmoebius K₀ g (s.toRingEquiv z) := by
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>
    have hsz : s.toRingEquiv z ∈ upperHalfPlane K₀ K := s.mapsTo_upperHalfPlane hz
    rw [pmoebius_mk K₀ g z (moebius_denom_ne_zero_of_mem K₀ hz g),
      pmoebius_mk K₀ g (s.toRingEquiv z) (moebius_denom_ne_zero_of_mem K₀ hsz g), moebius, moebius,
      map_div₀, map_add, map_add, map_mul, map_mul, s.fix, s.fix, s.fix, s.fix]

def funMap (s : IsometricAut K₀ K) : (↥(upperHalfPlane K₀ K) → K) ≃+* (↥(upperHalfPlane K₀ K) → K) where
  toFun f := fun z => s.toRingEquiv (f ⟨s.toRingEquiv.symm z, (s⁻¹).mapsTo_upperHalfPlane z.2⟩)
  invFun f := fun z => s.toRingEquiv.symm (f ⟨s.toRingEquiv z, s.mapsTo_upperHalfPlane z.2⟩)
  left_inv f := funext fun z => by simp
  right_inv f := funext fun z => by simp
  map_mul' f f' := funext fun z => map_mul s.toRingEquiv _ _
  map_add' f f' := funext fun z => map_add s.toRingEquiv _ _

omit [DecidableEq K] in
theorem vRestrict_map (s : IsometricAut K₀ K) (x : K) : vRestrict K (s.toRingEquiv x) = vRestrict K x :=
  le_antisymm ((v_le_iff_vRestrict_le K _ _).1 (s.isometry x).le) ((v_le_iff_vRestrict_le K _ _).1 (s.isometry x).ge)

omit [DecidableEq K] in

theorem funMap_mem_holRing (s : IsometricAut K₀ K) {f : ↥(upperHalfPlane K₀ K) → K} (hf : f ∈ holRing ϖ) :
    s.funMap f ∈ holRing ϖ := by
  intro n
  obtain ⟨r, hr, ⟨b, hb⟩, hlim⟩ := hf n
  have hmem : ∀ z : K, z ∈ affinoid ϖ n → s.toRingEquiv.symm z ∈ affinoid ϖ n := fun z hz =>
    (s⁻¹).mapsTo_affinoid ϖ n hz
  refine ⟨fun k => (r k).map s.toRingEquiv, fun k z hz => ?_, ⟨b, fun k z => ?_⟩, ?_⟩
  ·
    have h := RatPair.map_den_eval s.toRingEquiv (r k) (s.toRingEquiv.symm z)
    rw [RingEquiv.apply_symm_apply] at h
    rw [h, map_ne_zero]
    exact hr k _ (hmem z hz)
  ·
    have h := RatPair.evalAt_map s.toRingEquiv (r k) (s.toRingEquiv.symm z)
    rw [RingEquiv.apply_symm_apply] at h
    rw [h, s.isometry]
    exact hb k ⟨_, hmem z z.2⟩
  ·
    rw [tendstoUniformly_iff_vRestrict] at hlim ⊢
    intro γ
    filter_upwards [hlim γ] with k hk z
    have h := RatPair.evalAt_map s.toRingEquiv (r k) (s.toRingEquiv.symm z)
    rw [RingEquiv.apply_symm_apply] at h
    have hz' := hk ⟨_, hmem z z.2⟩
    rw [h]
    show vRestrict K (s.toRingEquiv ((r k).evalAt (s.toRingEquiv.symm ↑z)) -
      s.toRingEquiv (f ⟨s.toRingEquiv.symm z, (s⁻¹).mapsTo_upperHalfPlane
        (affinoid_subset_upperHalfPlane ϖ n z.2)⟩)) < γ
    rw [← map_sub, vRestrict_map]
    exact hz'

def coeffMap (s : IsometricAut K₀ K) : ↥(holRing ϖ) ≃+* ↥(holRing ϖ) where
  toFun f := ⟨s.funMap f, s.funMap_mem_holRing ϖ f.2⟩
  invFun f := ⟨(s⁻¹).funMap f, (s⁻¹).funMap_mem_holRing ϖ f.2⟩
  left_inv f := Subtype.ext (funext fun z => by simp [funMap])
  right_inv f := Subtype.ext (funext fun z => by simp [funMap])
  map_mul' f f' := Subtype.ext (map_mul s.funMap _ _)
  map_add' f f' := Subtype.ext (map_add s.funMap _ _)

omit [DecidableEq K] in
theorem coeffMap_algebraMap (s : IsometricAut K₀ K) (c : K) :
    s.coeffMap ϖ (algebraMap K ↥(holRing ϖ) c) = algebraMap K ↥(holRing ϖ) (s.toRingEquiv c) :=
  Subtype.ext (funext fun _ => rfl)

theorem coeffMap_smul (s : IsometricAut K₀ K) (g : PGL(2, K₀)) (f : ↥(holRing ϖ)) :
    s.coeffMap ϖ (g • f) = g • s.coeffMap ϖ f := by
  apply Subtype.ext
  funext z
  show s.toRingEquiv ((f : ↥(upperHalfPlane K₀ K) → K) (g⁻¹ • ⟨s.toRingEquiv.symm z, (s⁻¹).mapsTo_upperHalfPlane z.2⟩)) =
    s.toRingEquiv ((f : ↥(upperHalfPlane K₀ K) → K) ⟨s.toRingEquiv.symm ((g⁻¹ • z : ↥(upperHalfPlane K₀ K)) : K),
      (s⁻¹).mapsTo_upperHalfPlane (g⁻¹ • z).2⟩)
  congr 2
  apply congrArg
  apply Subtype.ext
  show pmoebius K₀ g⁻¹ (s.toRingEquiv.symm z) = s.toRingEquiv.symm (pmoebius K₀ g⁻¹ (z : K))
  have h := (s⁻¹).comm_pmoebius g⁻¹ z.2
  rw [inv_toRingEquiv] at h
  exact h.symm

def toAmbient (s : IsometricAut K₀ K) : Mumford.AmbientSemilinearAut K PGL(2, K₀) ↥(holRing ϖ) where
  base := s.toRingEquiv
  map := s.coeffMap ϖ
  map_algebraMap := s.coeffMap_algebraMap ϖ
  map_smul := fun g f => s.coeffMap_smul ϖ g f

end IsometricAut

end Actions

theorem iUnion_affinoid (h : IsExhausted ϖ) : (⋃ n, affinoid ϖ n) = upperHalfPlane K₀ K :=
  Set.Subset.antisymm (Set.iUnion_subset fun n => affinoid_subset_upperHalfPlane ϖ n)
    fun z hz => Set.mem_iUnion.2 (h z hz)

section Hom

variable [DecidableEq K]

def IsometricAut.toAmbientHom : IsometricAut K₀ K →* Mumford.AmbientSemilinearAut K PGL(2, K₀) ↥(holRing ϖ) where
  toFun s := s.toAmbient ϖ
  map_one' := Mumford.AmbientSemilinearAut.ext rfl
    (RingEquiv.ext fun f => Subtype.ext (funext fun _ => congrArg (f : ↥(upperHalfPlane K₀ K) → K) (Subtype.ext rfl)))
  map_mul' _ _ := Mumford.AmbientSemilinearAut.ext rfl
    (RingEquiv.ext fun _ => Subtype.ext (funext fun _ => rfl))

end Hom

section Glue

variable [DecidableEq K] {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

set_option linter.unusedVariables false in

def HolRingOf (ρ : G →* PGL(2, K₀)) : Type := ↥(holRing ϖ)

instance HolRingOf.instCommRing : CommRing (HolRingOf ϖ ρ) := inferInstanceAs (CommRing ↥(holRing ϖ))
instance HolRingOf.instAlgebra : Algebra K (HolRingOf ϖ ρ) := inferInstanceAs (Algebra K ↥(holRing ϖ))
instance HolRingOf.instMulSemiringAction : MulSemiringAction G (HolRingOf ϖ ρ) :=
  MulSemiringAction.compHom ↥(holRing ϖ) ρ
instance HolRingOf.instSMulCommClass : SMulCommClass G K (HolRingOf ϖ ρ) :=
  ⟨fun g c f => smul_comm (ρ g) c (show ↥(holRing ϖ) from f)⟩

omit [DecidableEq K] in
theorem HolRingOf.isDomain_iff : IsDomain (HolRingOf ϖ ρ) ↔ IsDomain ↥(holRing ϖ) := Iff.rfl

theorem HolRingOf.smul_def (g : G) (f : HolRingOf ϖ ρ) : g • f = (ρ g • (show ↥(holRing ϖ) from f) : ↥(holRing ϖ)) :=
  rfl

def toAmbientOf (s : IsometricAut K₀ K) : Mumford.AmbientSemilinearAut K G (HolRingOf ϖ ρ) where
  base := s.toRingEquiv
  map := s.coeffMap ϖ
  map_algebraMap := s.coeffMap_algebraMap ϖ
  map_smul := fun g f => s.coeffMap_smul ϖ (ρ g) f

def toAmbientOfHom : IsometricAut K₀ K →* Mumford.AmbientSemilinearAut K G (HolRingOf ϖ ρ) where
  toFun := toAmbientOf ϖ ρ
  map_one' := Mumford.AmbientSemilinearAut.ext rfl
    (RingEquiv.ext fun f => Subtype.ext (funext fun _ =>
      congrArg ((show ↥(holRing ϖ) from f) : ↥(upperHalfPlane K₀ K) → K) (Subtype.ext rfl)))
  map_mul' _ _ := Mumford.AmbientSemilinearAut.ext rfl
    (RingEquiv.ext fun _ => Subtype.ext (funext fun _ => rfl))

end Glue

abbrev merField : Type := FractionRing ↥(holRing ϖ)

end CerednikDrinfeld.Omega

end


