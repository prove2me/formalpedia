-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CoprimeActionTrivial
-- name    : OddOrder_GroupTheory_RepresentationTheory_CoprimeActionTrivial
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:26.983234+00:00
-- url     : https://prove2.me/theorems/7f49ab7a-0843-4821-90fe-c192e90f719f
-- title:
--   Coprime action: the trivial-action step (Bender–Glauberman App. A.3)
-- statement:
--   The single-step coprime-action lemma used in BG Appendix A (A.3). Let a finite group $G$ act by a representation $\rho$ on $V$ with $|G|$ invertible in $F$. If $W\le V$ is $G$-invariant and $G$ acts trivially on $W$ and on $V/W$, then $G$ acts trivially on $V$. This is the single-step version of Gorenstein (1968) Thm 3.4; applied inductively along a composition series it gives that triviality on all composition factors implies triviality overall. The proof expands $T=\rho(g)-1$ directly, without Maschke.
--
--   Main results: `coprime_action_trivial_step`, `coprime_action_trivial_relative_step` (relative version for $W\le U\le V$) and `coprime_action_trivial_chain` (chain version).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CoprimeActionTrivial.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CoprimeActionTrivial.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.GroupTheory.OrderOfElement

namespace OddOrder.GroupTheory.RepresentationTheory

section RelativeStep

variable {F : Type*} [Field F]

variable {V : Type*} [AddCommGroup V] [Module F V]

variable {G : Type*} [Group G] [Finite G]

/-- Aux: `T w = 0` なら `(1 + T)^n w = w` (`w` 上 `1+T` 恒等). -/
private lemma pow_one_add_apply_of_apply_zero
    (T : Module.End F V) {w : V} (hTw : T w = 0) :
    ∀ n : ℕ, (((1 : Module.End F V) + T) ^ n) w = w := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    have h_one_add_w : ((1 : Module.End F V) + T) w = w := by
      rw [LinearMap.add_apply, Module.End.one_apply, hTw, add_zero]
    rw [h_one_add_w, ih]

/-- Aux: `T (T u) = 0` なら `(1 + T)^n u = u + n • T u` (pointwise binomial). -/
private lemma pow_one_add_apply_of_apply_apply_zero
    (T : Module.End F V) {u : V} (hT2u : T (T u) = 0) :
    ∀ n : ℕ, (((1 : Module.End F V) + T) ^ n) u = u + n • T u := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply]
    have h_one_add_u : ((1 : Module.End F V) + T) u = u + T u := by
      rw [LinearMap.add_apply, Module.End.one_apply]
    rw [h_one_add_u, map_add, ih,
        pow_one_add_apply_of_apply_zero T hT2u k, succ_nsmul]
    abel

omit [Finite G] in
/-- **Relative coprime action step**: `W ≤ U ≤ V` (両 `Submodule F V`),
`G` が `W` 上自明 (`∀ g w ∈ W, ρ g w = w`) かつ `U` 上で「mod W で自明」
(`∀ g u ∈ U, ρ g u - u ∈ W`) なら `G` は `U` 上自明.

`coprime_action_trivial_step` の "U = ⊤" 一般化. 仮定 `[NeZero (Nat.card G : F)]`
は同じ ((|G| : F) ≠ 0).

証明: pointwise 版 binomial. `T := ρ g - 1`, `u ∈ U` で `T u ∈ W` (mod W),
`T (T u) = 0` (`G` triv on `W`), `(1+T)^m u = u + m • T u` で `m • T u = 0`,
`(m : F) ≠ 0` で `T u = 0` ⇒ `ρ g u = u`. -/
theorem coprime_action_trivial_relative_step
    (ρ : Representation F G V) [NeZero (Nat.card G : F)]
    {W U : Submodule F V}
    (hW_triv : ∀ (g : G) (w : V), w ∈ W → ρ g w = w)
    (hUW_triv : ∀ (g : G) (u : V), u ∈ U → ρ g u - u ∈ W) :
    ∀ (g : G) (u : V), u ∈ U → ρ g u = u := by
  intro g u huU
  set T : Module.End F V := (ρ g : Module.End F V) - 1 with hT_def
  have hTu : T u ∈ W := by
    change ρ g u - u ∈ W
    exact hUW_triv g u huU
  have hT2u : T (T u) = 0 := by
    have h1 : ρ g (T u) = T u := hW_triv g _ hTu
    change ((ρ g : Module.End F V) - 1) (T u) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, h1, sub_self]
  set m : ℕ := orderOf g with hm_def
  have h_pow_apply : (((1 : Module.End F V) + T) ^ m) u = u + m • T u :=
    pow_one_add_apply_of_apply_apply_zero T hT2u m
  have h_one_add_T : (1 : Module.End F V) + T = (ρ g : Module.End F V) := by
    rw [hT_def]; abel
  have h_pow_one : (((1 : Module.End F V) + T) ^ m) u = u := by
    rw [h_one_add_T]
    have hpow : (ρ g : Module.End F V) ^ m = ρ (g ^ m) := (map_pow ρ g m).symm
    rw [hpow, hm_def, pow_orderOf_eq_one, map_one, Module.End.one_apply]
  have h_m_T_u : m • T u = 0 := by
    have h_eq : u + m • T u = u := h_pow_apply.symm.trans h_pow_one
    have := h_eq.trans (add_zero u).symm
    exact add_left_cancel this
  have hm_dvd : m ∣ Nat.card G := orderOf_dvd_natCard g
  have h_m_ne_zero : (m : F) ≠ 0 := by
    intro h_zero
    apply NeZero.ne (Nat.card G : F)
    obtain ⟨k, hk⟩ := hm_dvd
    rw [hk, Nat.cast_mul, h_zero, zero_mul]
  have h_smul_T_u : (m : F) • T u = 0 := by
    rw [Nat.cast_smul_eq_nsmul]; exact h_m_T_u
  have h_T_u_zero : T u = 0 := by
    rcases smul_eq_zero.mp h_smul_T_u with h | h
    · exact absurd h h_m_ne_zero
    · exact h
  have h_diff : (ρ g : Module.End F V) u - u = 0 := by
    have h1 : T u = (ρ g : Module.End F V) u - u := by
      change ((ρ g : Module.End F V) - 1) u = _
      rw [LinearMap.sub_apply, Module.End.one_apply]
    rw [← h1]; exact h_T_u_zero
  exact sub_eq_zero.mp h_diff

omit [Finite G] in
/-- **Coprime action — chain version**: chain `s : Fin (n+1) → Submodule F V`
で `s 0 = ⊥`, `s (Fin.last n) = ⊤`, 各 quotient 上 `G` 自明
(`∀ g v ∈ s i.succ, ρ g v - v ∈ s i.castSucc`) なら `G` は `V` 全体自明.

monotonicity (`s i.castSucc ≤ s i.succ`) は `h_triv_quot` から間接的に従う
(`ρ g v ∈ s i.succ` 経由) ので仮定不要.

証明: 上向き帰納で `∀ i, ∀ v ∈ s i, ρ g v = v`. base `s 0 = ⊥` で trivial,
step `s i → s (i+1)` は `coprime_action_trivial_relative_step` を `W = s i.castSucc`,
`U = s i.succ` で適用. -/
theorem coprime_action_trivial_chain
    (ρ : Representation F G V) [NeZero (Nat.card G : F)]
    {n : ℕ} (s : Fin (n + 1) → Submodule F V)
    (h_bot : s 0 = ⊥) (h_top : s (Fin.last n) = ⊤)
    (h_triv_quot : ∀ (g : G) (i : Fin n) (v : V),
        v ∈ s i.succ → ρ g v - v ∈ s i.castSucc) :
    ∀ (g : G) (v : V), ρ g v = v := by
  suffices h_key : ∀ (i : Fin (n + 1)) (g : G) (v : V), v ∈ s i → ρ g v = v by
    intro g v
    exact h_key (Fin.last n) g v (by rw [h_top]; trivial)
  intro i
  induction i using Fin.induction with
  | zero =>
    intro g v hv
    rw [h_bot] at hv
    rw [(Submodule.mem_bot _).mp hv, map_zero]
  | succ j ih =>
    intro g v hv
    exact coprime_action_trivial_relative_step ρ
      (W := s j.castSucc) (U := s j.succ)
      (fun g' w hw => ih g' w hw)
      (fun g' u hu => h_triv_quot g' j u hu) g v hv

end RelativeStep

end OddOrder.GroupTheory.RepresentationTheory


