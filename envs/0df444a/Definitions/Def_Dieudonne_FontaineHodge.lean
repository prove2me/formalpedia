-- Prove2me | Definitions.Def_Dieudonne_FontaineHodge
-- name    : Dieudonne_FontaineHodge
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/56f73e5c-a690-5135-a01f-2c0da186ab70
-- title:
--   Fontaine's Hodge submodule of a Dieudonné module
-- statement:
--   Fix a prime $p$ and a ring homomorphism $\pi\colon\mathcal R\to A$ of commutative rings. A first group of lemmas records the ghost components of Witt vectors over $\mathcal R$: `ghostComponent_eq_sum` gives $\mathrm{gh}_n(X)=\sum_{i=0}^{n}p^iX_i^{p^{n-i}}$, with the elementary consequences that $\mathrm{gh}_n(X)\in(p^{n+1})$ as soon as $X_i\in(p)$ for all $i\le n$, that $\mathrm{gh}_{n-1}(X)\in(p^n)$ when $X_i\in(p)$ for $i<n$, and that $\mathrm{gh}_{n-1}(X)\in(p^n)$ implies $\mathrm{gh}_n(VX)\in(p^{n+1})$; ghost components commute with $W(f)$.
--
--   The central definition, `fontaineKer p n π`, is the additive subgroup of $W_n(A)$ consisting of those $a$ admitting a lift: some $X\in W(\mathcal R)$ with $W(\pi)(X)$ truncated to length $n$ equal to $a$ and $\mathrm{gh}_{n-1}(X)\in p^n\mathcal R$ — the division-free form of the vanishing of Fontaine's covector map $w$. It is all of $W_0(A)$ for $n=0$; if $\ker\pi\subseteq(p)$ the defining condition is independent of the chosen lift, and then (with $\pi$ surjective) membership may equivalently be tested on every lift. Membership is preserved by the Verschiebung-type maps `shift` and `shiftLE` between truncation levels, and reflected by them when $p$ is a non-zero-divisor in $\mathcal R$; it is functorial along a commuting square $\pi'\circ f=g\circ\pi$; and for $n=1$ with $p=0$ in $A$ only $0$ lies in it.
--
--   When $A$ is moreover an $R$-bialgebra, `fontaineHodgeLevel` is the induced subgroup of `wittHom R p n A`, and `fontaineHodgeAddSubgroup`, recorded as the $\mathbb Z$-submodule `fontaineHodge R p π` of $\mathrm{DieudonneModule}\,R\,p\,A=\varinjlim_n\mathrm{wittHom}$, is the set of classes $\mathrm{of}\,n\,x$ with $x$ in some level's kernel; under the hypotheses above membership of $\mathrm{of}\,n\,x$ is equivalent to $x\in$ `fontaineKer`, and the submodule is carried into the corresponding one by the Dieudonné-module map of a bialgebra homomorphism over a commuting square.
--
--   Finally `reduction 𝓞 k ℛ`$\colon r\mapsto 1\otimes r$ into $k\otimes_{\mathcal O}\mathcal R$ is shown to be surjective when $\mathcal O\to k$ is, to have kernel the image of $\ker(\mathcal O\to k)$, hence kernel $p\mathcal R$ and $p=0$ in $k\otimes_{\mathcal O}\mathcal R$ when that kernel is $(p)$.
--
--   **Relation to Mathlib.** Witt vectors, truncated Witt vectors, ghost components and Verschiebung are Mathlib's; the truncated-level maps `map`, `shift`, `shiftLE`, the groups `wittHom` and the colimit `DieudonneModule` come from the project's own Dieudonné modules. Mathlib has no notion of Honda system or of Fontaine's Hodge submodule, so `fontaineKer`, `fontaineHodgeLevel` and `fontaineHodge` are the project's own.
--
--   **Where it is used.** These subgroups furnish the candidate Hodge piece $L$ of a Honda system attached to a finite flat commutative $p$-group scheme, the special fibre appearing as $\mathrm{Spec}(k\otimes_{\mathcal O}\mathcal R)$ and $\pi$ as the reduction map. No part of Fontaine's classification theorem is asserted here; only the definition and its elementary compatibilities, for use in the Dieudonné-theoretic treatment of flat deformation conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Dieudonne_FontaineHodge.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Function

universe u v w u'

namespace Deformation

namespace WittGhost

variable {p : ℕ} [hp : Fact p.Prime] {ℛ : Type u} [CommRing ℛ]

theorem ghostComponent_eq_sum (n : ℕ) (X : WittVector p ℛ) :
    WittVector.ghostComponent n X =
      ∑ i ∈ Finset.range (n + 1), (p : ℛ) ^ i * X.coeff i ^ p ^ (n - i) := by
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial]

theorem ghostComponent_map {S : Type v} [CommRing S] (f : ℛ →+* S) (n : ℕ) (X : WittVector p ℛ) :
    WittVector.ghostComponent n (WittVector.map f X) = f (WittVector.ghostComponent n X) := by
  simp only [ghostComponent_eq_sum, map_sum, map_mul, map_pow, map_natCast, WittVector.map_coeff]

omit hp in
theorem succ_le_prime_pow (hp1 : 1 < p) (k : ℕ) : k + 1 ≤ p ^ k := Nat.lt_pow_self hp1

theorem pow_mul_pow_mem_span_pow {x : ℛ} (hx : x ∈ Ideal.span {(p : ℛ)}) {i n : ℕ} (hi : i ≤ n) :
    (p : ℛ) ^ i * x ^ p ^ (n - i) ∈ Ideal.span {(p : ℛ) ^ (n + 1)} := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hx
  rw [← hb, mul_pow, Ideal.mem_span_singleton]
  have hle : n + 1 ≤ i + p ^ (n - i) := by
    have := succ_le_prime_pow hp.out.one_lt (n - i)
    omega
  calc (p : ℛ) ^ (n + 1) ∣ (p : ℛ) ^ (i + p ^ (n - i)) := pow_dvd_pow _ hle
    _ = (p : ℛ) ^ i * (p : ℛ) ^ p ^ (n - i) := pow_add _ _ _
    _ ∣ (p : ℛ) ^ i * (b ^ p ^ (n - i) * (p : ℛ) ^ p ^ (n - i)) :=
        mul_dvd_mul_left _ (dvd_mul_left _ _)

theorem ghostComponent_mem_span_pow_of_forall_coeff_mem {n : ℕ} {X : WittVector p ℛ}
    (hX : ∀ i ≤ n, X.coeff i ∈ Ideal.span {(p : ℛ)}) :
    WittVector.ghostComponent n X ∈ Ideal.span {(p : ℛ) ^ (n + 1)} := by
  rw [ghostComponent_eq_sum]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  exact pow_mul_pow_mem_span_pow (hX i (Nat.le_of_lt_succ hi)) (Nat.le_of_lt_succ hi)

theorem ghostComponent_pred_mem_span_pow {n : ℕ} {X : WittVector p ℛ}
    (hX : ∀ i < n, X.coeff i ∈ Ideal.span {(p : ℛ)}) :
    WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n} := by
  cases n with
  | zero => simp
  | succ k =>
    exact ghostComponent_mem_span_pow_of_forall_coeff_mem fun i hi => hX i (Nat.lt_succ_of_le hi)

theorem ghostComponent_verschiebung_mem_span_pow {n : ℕ} {X : WittVector p ℛ}
    (hX : WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n}) :
    WittVector.ghostComponent n (WittVector.verschiebung X) ∈ Ideal.span {(p : ℛ) ^ (n + 1)} := by
  cases n with
  | zero => rw [WittVector.ghostComponent_zero_verschiebung]; exact zero_mem _
  | succ k =>
    rw [WittVector.ghostComponent_verschiebung, Ideal.mem_span_singleton, pow_succ']
    exact mul_dvd_mul_left _ (Ideal.mem_span_singleton.1 hX)

end WittGhost

namespace TruncWitt

section FontaineKer

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable {ℛ : Type u} [CommRing ℛ] {A : Type v} [CommRing A] (π : ℛ →+* A)

noncomputable def fontaineKer : AddSubgroup (TruncatedWittVector p n A) where
  carrier := {a | ∃ X : WittVector p ℛ, WittVector.truncate n (WittVector.map π X) = a ∧
    WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n}}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨X, rfl, hX⟩ ⟨Y, rfl, hY⟩
    exact ⟨X + Y, by simp, by rw [map_add]; exact add_mem hX hY⟩
  neg_mem' := by
    rintro a ⟨X, rfl, hX⟩
    exact ⟨-X, by simp, by rw [map_neg]; exact neg_mem hX⟩

variable {p n π}

theorem mem_fontaineKer_iff (a : TruncatedWittVector p n A) :
    a ∈ fontaineKer p n π ↔ ∃ X : WittVector p ℛ, WittVector.truncate n (WittVector.map π X) = a ∧
      WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n} :=
  Iff.rfl

theorem truncate_map_mem_fontaineKer {X : WittVector p ℛ}
    (hX : WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n}) :
    WittVector.truncate n (WittVector.map π X) ∈ fontaineKer p n π :=
  ⟨X, rfl, hX⟩

variable (p π) in

theorem fontaineKer_zero : fontaineKer p 0 π = ⊤ :=
  eq_top_iff.2 fun a _ => ⟨0, TruncatedWittVector.ext fun i => i.elim0, by simp⟩

theorem coeff_mem_ker_of_truncate_map_eq_zero {X : WittVector p ℛ}
    (h : WittVector.truncate n (WittVector.map π X) = 0) (i : ℕ) (hi : i < n) :
    X.coeff i ∈ RingHom.ker π := by
  rw [← RingHom.mem_ker, WittVector.mem_ker_truncate] at h
  rw [RingHom.mem_ker, ← WittVector.map_coeff]
  exact h i hi

theorem ghostComponent_pred_mem_of_truncate_map_eq (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)})
    {X Y : WittVector p ℛ}
    (h : WittVector.truncate n (WittVector.map π X) = WittVector.truncate n (WittVector.map π Y))
    (hY : WittVector.ghostComponent (n - 1) Y ∈ Ideal.span {(p : ℛ) ^ n}) :
    WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n} := by
  have hXY : WittVector.truncate n (WittVector.map π (X - Y)) = 0 := by
    rw [map_sub, map_sub, h, sub_self]
  have key : WittVector.ghostComponent (n - 1) (X - Y) ∈ Ideal.span {(p : ℛ) ^ n} :=
    WittGhost.ghostComponent_pred_mem_span_pow fun i hi =>
      hπ (coeff_mem_ker_of_truncate_map_eq_zero hXY i hi)
  have : X = X - Y + Y := (sub_add_cancel X Y).symm
  rw [this, map_add]
  exact add_mem key hY

theorem truncate_map_mem_fontaineKer_iff (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)})
    (X : WittVector p ℛ) :
    WittVector.truncate n (WittVector.map π X) ∈ fontaineKer p n π ↔
      WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n} :=
  ⟨fun ⟨_, hYX, hY⟩ => ghostComponent_pred_mem_of_truncate_map_eq hπ hYX.symm hY,
    truncate_map_mem_fontaineKer⟩

theorem exists_truncate_map_eq (hπs : Surjective π) (a : TruncatedWittVector p n A) :
    ∃ X : WittVector p ℛ, WittVector.truncate n (WittVector.map π X) = a := by
  obtain ⟨Z, rfl⟩ := WittVector.truncate_surjective p n A a
  obtain ⟨X, rfl⟩ := WittVector.map_surjective π hπs Z
  exact ⟨X, rfl⟩

theorem mem_fontaineKer_iff_forall (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π)
    (a : TruncatedWittVector p n A) :
    a ∈ fontaineKer p n π ↔ ∀ X : WittVector p ℛ, WittVector.truncate n (WittVector.map π X) = a →
      WittVector.ghostComponent (n - 1) X ∈ Ideal.span {(p : ℛ) ^ n} := by
  constructor
  · rintro ha X rfl
    exact (truncate_map_mem_fontaineKer_iff hπ X).1 ha
  · intro h
    obtain ⟨X, rfl⟩ := exists_truncate_map_eq hπs a
    exact truncate_map_mem_fontaineKer (h X rfl)

theorem truncate_map_verschiebung (X : WittVector p ℛ) :
    WittVector.truncate (n + 1) (WittVector.map π (WittVector.verschiebung X)) =
      shift (WittVector.truncate n (WittVector.map π X)) := by
  rw [WittVector.map_verschiebung, shift_truncate]

theorem shift_mem_fontaineKer {a : TruncatedWittVector p n A} (ha : a ∈ fontaineKer p n π) :
    shift a ∈ fontaineKer p (n + 1) π := by
  obtain ⟨X, rfl, hX⟩ := ha
  refine ⟨WittVector.verschiebung X, truncate_map_verschiebung X, ?_⟩
  rw [Nat.add_sub_cancel]
  exact WittGhost.ghostComponent_verschiebung_mem_span_pow hX

theorem shiftLE_mem_fontaineKer {m : ℕ} (h : n ≤ m) {a : TruncatedWittVector p n A}
    (ha : a ∈ fontaineKer p n π) : shiftLE h a ∈ fontaineKer p m π := by
  induction h with
  | refl => rwa [shiftLE_refl]
  | @step m h ih =>
    rw [← shiftLE_shiftLE h (Nat.le_succ m), shiftLE_succ]
    exact shift_mem_fontaineKer ih

theorem mem_fontaineKer_of_shift_mem (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ)
    (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π)
    {a : TruncatedWittVector p n A} (ha : shift a ∈ fontaineKer p (n + 1) π) :
    a ∈ fontaineKer p n π := by
  obtain ⟨X, rfl⟩ := exists_truncate_map_eq hπs a
  rw [← truncate_map_verschiebung, truncate_map_mem_fontaineKer_iff hπ, Nat.add_sub_cancel] at ha
  refine truncate_map_mem_fontaineKer ?_
  cases n with
  | zero => simp
  | succ k =>
    rw [WittVector.ghostComponent_verschiebung, Ideal.mem_span_singleton] at ha
    obtain ⟨c, hc⟩ := ha
    rw [Nat.add_sub_cancel, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩

    have h0 : (WittVector.ghostComponent k X - (p : ℛ) ^ (k + 1) * c) * (p : ℛ) = 0 := by
      rw [sub_mul, mul_comm, hc]; ring
    exact sub_eq_zero.1 (mem_nonZeroDivisors_iff_right.1 hp' _ h0)

theorem mem_fontaineKer_of_shiftLE_mem (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ)
    (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π) {m : ℕ} (h : n ≤ m)
    {a : TruncatedWittVector p n A} (ha : shiftLE h a ∈ fontaineKer p m π) :
    a ∈ fontaineKer p n π := by
  induction h with
  | refl => rwa [shiftLE_refl] at ha
  | @step m h ih =>
    rw [← shiftLE_shiftLE h (Nat.le_succ m), shiftLE_succ] at ha
    exact ih (mem_fontaineKer_of_shift_mem hp' hπ hπs ha)

theorem shiftLE_mem_fontaineKer_iff (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ)
    (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π) {m : ℕ} (h : n ≤ m)
    (a : TruncatedWittVector p n A) :
    shiftLE h a ∈ fontaineKer p m π ↔ a ∈ fontaineKer p n π :=
  ⟨mem_fontaineKer_of_shiftLE_mem hp' hπ hπs h, shiftLE_mem_fontaineKer h⟩

theorem map_mem_fontaineKer {ℛ' : Type w} [CommRing ℛ'] {A' : Type u'} [CommRing A']
    (f : ℛ →+* ℛ') (g : A →+* A') (π' : ℛ' →+* A') (hcomm : π'.comp f = g.comp π)
    {a : TruncatedWittVector p n A} (ha : a ∈ fontaineKer p n π) :
    map g a ∈ fontaineKer p n π' := by
  obtain ⟨X, rfl, hX⟩ := ha
  refine ⟨WittVector.map f X, ?_, ?_⟩
  · rw [map_truncate]
    congr 1
    ext i
    simp only [WittVector.map_coeff]
    exact (RingHom.congr_fun hcomm (X.coeff i))
  · rw [WittGhost.ghostComponent_map, Ideal.mem_span_singleton, ← map_natCast f p, ← map_pow]
    exact map_dvd f (Ideal.mem_span_singleton.1 hX)

theorem eq_zero_of_mem_fontaineKer_one (hA : (p : A) = 0) {a : TruncatedWittVector p 1 A}
    (ha : a ∈ fontaineKer p 1 π) : a = 0 := by
  obtain ⟨X, rfl, hX⟩ := ha
  rw [Nat.sub_self, WittVector.ghostComponent_apply, wittPolynomial_zero, MvPolynomial.aeval_X,
    pow_one] at hX
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hX
  refine TruncatedWittVector.ext fun i => ?_
  rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero, WittVector.map_coeff,
    show ((i : Fin 1) : ℕ) = 0 from Subsingleton.elim (α := Fin 1) i 0 ▸ rfl, ← hb, map_mul,
    map_natCast, hA, mul_zero]

end FontaineKer

end TruncWitt

section Hodge

variable (R : Type w) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable {ℛ : Type u} [CommRing ℛ] {A : Type v} [CommRing A] [Bialgebra R A] (π : ℛ →+* A)

open TruncWitt DieudonneModule

noncomputable def fontaineHodgeLevel : AddSubgroup (wittHom R p n A) :=
  (fontaineKer p n π).addSubgroupOf (wittHom R p n A)

variable {R p n π}

theorem mem_fontaineHodgeLevel_iff (x : wittHom R p n A) :
    x ∈ fontaineHodgeLevel R p n π ↔ (x : TruncatedWittVector p n A) ∈ fontaineKer p n π :=
  Iff.rfl

theorem wittHomShiftLE_mem_fontaineHodgeLevel {m : ℕ} (h : n ≤ m) {x : wittHom R p n A}
    (hx : x ∈ fontaineHodgeLevel R p n π) :
    wittHomShiftLE R p A h x ∈ fontaineHodgeLevel R p m π :=
  shiftLE_mem_fontaineKer h hx

variable (R p π) in

noncomputable def fontaineHodgeAddSubgroup : AddSubgroup (DieudonneModule R p A) where
  carrier := {z | ∃ (n : ℕ) (x : wittHom R p n A),
    (x : TruncatedWittVector p n A) ∈ fontaineKer p n π ∧ DieudonneModule.of R p A n x = z}
  zero_mem' := ⟨0, 0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, x, hx, rfl⟩ ⟨m, y, hy, rfl⟩
    refine ⟨max n m, wittHomShiftLE R p A (le_max_left n m) x +
      wittHomShiftLE R p A (le_max_right n m) y, ?_, ?_⟩
    · exact add_mem (shiftLE_mem_fontaineKer _ hx) (shiftLE_mem_fontaineKer _ hy)
    · rw [map_add, of_shiftLE, of_shiftLE]
  neg_mem' := by
    rintro _ ⟨n, x, hx, rfl⟩
    exact ⟨n, -x, neg_mem hx, map_neg _ _⟩

variable (R p π) in

noncomputable def fontaineHodge : Submodule ℤ (DieudonneModule R p A) :=
  (fontaineHodgeAddSubgroup R p π).toIntSubmodule

theorem mem_fontaineHodge_iff (z : DieudonneModule R p A) :
    z ∈ fontaineHodge R p π ↔ ∃ (n : ℕ) (x : wittHom R p n A),
      (x : TruncatedWittVector p n A) ∈ fontaineKer p n π ∧ DieudonneModule.of R p A n x = z :=
  Iff.rfl

theorem of_mem_fontaineHodge {x : wittHom R p n A}
    (hx : (x : TruncatedWittVector p n A) ∈ fontaineKer p n π) :
    DieudonneModule.of R p A n x ∈ fontaineHodge R p π :=
  ⟨n, x, hx, rfl⟩

theorem of_mem_fontaineHodge_iff (hp' : (p : ℛ) ∈ nonZeroDivisors ℛ)
    (hπ : RingHom.ker π ≤ Ideal.span {(p : ℛ)}) (hπs : Surjective π) (x : wittHom R p n A) :
    DieudonneModule.of R p A n x ∈ fontaineHodge R p π ↔
      (x : TruncatedWittVector p n A) ∈ fontaineKer p n π := by
  refine ⟨?_, of_mem_fontaineHodge⟩
  rintro ⟨m, y, hy, hxy⟩
  rw [of_eq_of_iff] at hxy
  have hy' : (wittHomShiftLE R p A (le_max_left m n) y : TruncatedWittVector p (max m n) A) ∈
      fontaineKer p (max m n) π := shiftLE_mem_fontaineKer _ hy
  rw [hxy] at hy'
  exact mem_fontaineKer_of_shiftLE_mem hp' hπ hπs (le_max_right m n) hy'

theorem map_fontaineHodge_le {ℛ' : Type u'} [CommRing ℛ'] {A' : Type v} [CommRing A'] [Bialgebra R A']
    (π' : ℛ' →+* A') (f : ℛ' →+* ℛ) (g : A' →ₐc[R] A)
    (hcomm : π.comp f = (g : A' →ₐ[R] A).toRingHom.comp π') :
    (fontaineHodge R p π').map (DieudonneModule.map R p g).toIntLinearMap ≤ fontaineHodge R p π := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨n, x, hx, rfl⟩ := hz
  refine ⟨n, wittHomMap p n g x, ?_, (map_of g x).symm⟩
  exact map_mem_fontaineKer f (g : A' →ₐ[R] A).toRingHom π hcomm hx

end Hodge

namespace SpecialFibre

open scoped TensorProduct
variable {𝓞 : Type u} [CommRing 𝓞] {k : Type v} [CommRing k] [Algebra 𝓞 k]
variable {ℛ : Type w} [CommRing ℛ] [Algebra 𝓞 ℛ]

variable (𝓞 k ℛ) in

noncomputable abbrev reduction : ℛ →+* k ⊗[𝓞] ℛ :=
  (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom

theorem reduction_apply (r : ℛ) : reduction 𝓞 k ℛ r = (1 : k) ⊗ₜ[𝓞] r := rfl

theorem reduction_surjective (hk : Surjective (algebraMap 𝓞 k)) :
    Surjective (reduction 𝓞 k ℛ) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a r =>
    obtain ⟨o, rfl⟩ := hk a
    refine ⟨o • r, ?_⟩
    rw [reduction_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact ⟨r + s, map_add _ _ _⟩

theorem ker_reduction (hk : Surjective (algebraMap 𝓞 k)) :
    RingHom.ker (reduction 𝓞 k ℛ) = (RingHom.ker (algebraMap 𝓞 k)).map (algebraMap 𝓞 ℛ) := by
  set I := RingHom.ker (algebraMap 𝓞 k) with hI
  apply le_antisymm
  ·
    set J : Ideal ℛ := I.map (algebraMap 𝓞 ℛ) with hJ
    have hle : RingHom.ker (algebraMap 𝓞 k) ≤
        RingHom.ker ((Ideal.Quotient.mk J).comp (algebraMap 𝓞 ℛ)) := by
      intro o ho
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ ho
    let κ₀ : k →+* ℛ ⧸ J := (algebraMap 𝓞 k).liftOfSurjective hk ⟨_, hle⟩
    have hκ₀ : ∀ o, κ₀ (algebraMap 𝓞 k o) = Ideal.Quotient.mk J (algebraMap 𝓞 ℛ o) := fun o =>
      (algebraMap 𝓞 k).liftOfRightInverse_comp_apply _ _ ⟨_, hle⟩ o
    let κ : k →ₐ[𝓞] ℛ ⧸ J :=
      { κ₀ with commutes' := fun o => (hκ₀ o).trans rfl }
    let Ψ : k ⊗[𝓞] ℛ →ₐ[𝓞] ℛ ⧸ J :=
      Algebra.TensorProduct.lift κ (Ideal.Quotient.mkₐ 𝓞 J) fun _ _ => Commute.all _ _
    intro r hr
    rw [RingHom.mem_ker, reduction_apply] at hr
    have : Ψ ((1 : k) ⊗ₜ[𝓞] r) = Ideal.Quotient.mk J r := by
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
    rw [hr, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  · rw [Ideal.map_le_iff_le_comap]
    intro o ho
    rw [RingHom.mem_ker] at ho
    rw [Ideal.mem_comap, RingHom.mem_ker, reduction_apply, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, ho,
      TensorProduct.zero_tmul]

theorem ker_reduction_eq_span (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) :
    RingHom.ker (reduction 𝓞 k ℛ) = Ideal.span {(p : ℛ)} := by
  rw [ker_reduction hk, hker, Ideal.map_span, Set.image_singleton, map_natCast]

theorem natCast_eq_zero (hk : Surjective (algebraMap 𝓞 k)) {p : ℕ}
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)}) : (p : k ⊗[𝓞] ℛ) = 0 := by
  have : (p : ℛ) ∈ RingHom.ker (reduction 𝓞 k ℛ) := by
    rw [ker_reduction_eq_span hk hker]; exact Ideal.mem_span_singleton_self _
  rwa [RingHom.mem_ker, map_natCast] at this

end SpecialFibre

end Deformation


