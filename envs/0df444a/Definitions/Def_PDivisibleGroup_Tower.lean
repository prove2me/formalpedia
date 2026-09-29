-- Prove2me | Definitions.Def_PDivisibleGroup_Tower
-- name    : PDivisibleGroup_Tower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/490dfdf1-ff16-5b77-9e6d-4c1568cffa45
-- title:
--   Multiplication by n and composite transitions in Hopf towers
-- statement:
--   Throughout, $R$ is a commutative ring and the bialgebras/Hopf algebras are commutative as rings. The first part of the module concerns multiplication by $n$. For a bialgebra $A$ over $R$, `nsmulAlgHom R A n` is the $n$-th power of the identity algebra endomorphism in the convolution monoid; here it is shown to satisfy $[m]^*\circ[n]^*=[mn]^*$, and, when $A$ is cocommutative, `nsmulBialgHom R A n : A →ₐc[R] A` is defined as the $n$-th convolution power of the identity bialgebra map, its underlying algebra map being `nsmulAlgHom R A n`; consequently $[n]^*$ is compatible with comultiplication. Recall from the basic module that `augIdeal R A` is the kernel of the counit and `torsionIdeal R A n` is the image of `augIdeal R A` under $[n]^*$.
--
--   The second part treats a single surjective bialgebra map $\pi\colon A\to B$: it preserves counits, its kernel lies in the augmentation ideal, and it carries `augIdeal R A` and `torsionIdeal R A n` onto the corresponding ideals of $B$; also `torsionIdeal R A n ≤ torsionIdeal R A m` whenever $m \mid n$. If moreover $\ker\pi=\,$`torsionIdeal R A n`, then $[n]^*_B$ equals the composite of the counit with the structure map $R\to B$, `torsionIdeal R B n` vanishes, every $R$-algebra map $B\to L$ is an $n$-torsion element of the convolution monoid, and an algebra map $A\to L$ factors through $\pi$ exactly when its $n$-th convolution power is trivial; precomposition with a surjective $\pi$ is injective, so such factorisations are unique.
--
--   The third part fixes a sequence of Hopf algebras $L_w$ with bialgebra maps $t_w\colon L_{w+1}\to L_w$. `transitionLE t v u : L (v + u) →ₐc[R] L v` is defined by recursion on $u$ as the composite $t_v\circ\cdots\circ t_{v+u-1}$, and `transitionOfLE t a b h` for $a \le b$ is the same map phrased with an inequality, using `levelCast` (transport of the Hopf algebra along an equality of indices) at the diagonal; the two agree after reindexing, they compose as expected and are surjective when each $t_w$ is. Under the standing hypotheses that each $t_w$ is surjective with kernel `torsionIdeal R (L (w+1)) (p ^ w)`, one obtains: $[p^w]^*$ on $L_w$ is the counit followed by the structure map, `torsionIdeal R (L w) (p ^ w) = ⊥`, the kernel of $L_b\to L_a$ is `torsionIdeal R (L b) (p ^ a)`, and an algebra map out of $L_b$ factors through $L_b\to L_a$ precisely when its $p^a$-th convolution power is trivial.
--
--   **Relation to Mathlib.** The convolution monoid structure on algebra and bialgebra homomorphisms (`WithConv`, `toConv`/`ofConv`) is Mathlib's; the multiplication-by-$n$ endomorphisms, the augmentation and torsion ideals, and towers of Hopf algebras with torsion-ideal kernels are the project's own notions.
--
--   **Where it is used.** These lemmas form the elementary interface for $p$-divisible groups presented as towers of Hopf algebras: they apply verbatim to the levels and transition maps of the structure [`PDivisibleGroup`](../def/PDivisibleGroup_Basic.html#L199), and also to raw tower data appearing in intermediate constructions, supplying exactness of the tower at arbitrary distance and the factorisation criterion for points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PDivisibleGroup_Tower.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

universe u v w x

namespace PDivisibleGroup.Hopf

section NSMulBialg

variable (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Bialgebra R A]

theorem nsmulAlgHom_comp_nsmulAlgHom (m n : ℕ) :
    (nsmulAlgHom R A m).comp (nsmulAlgHom R A n) = nsmulAlgHom R A (m * n) := by
  rw [nsmulAlgHom_mul]
  apply WithConv.toConv_injective
  rw [toConv_ofConv]
  exact (toConv_pow_eq_toConv_comp_nsmulAlgHom (nsmulAlgHom R A m) n).symm

theorem nsmulAlgHom_nsmulAlgHom_apply (m n : ℕ) (a : A) :
    nsmulAlgHom R A m (nsmulAlgHom R A n a) = nsmulAlgHom R A (m * n) a :=
  DFunLike.congr_fun (nsmulAlgHom_comp_nsmulAlgHom R A m n) a

variable [Coalgebra.IsCocomm R A]

noncomputable def nsmulBialgHom (n : ℕ) : A →ₐc[R] A := ((toConv (BialgHom.id R A)) ^ n).ofConv

theorem toAlgHom_nsmulBialgHom (n : ℕ) :
    (nsmulBialgHom R A n : A →ₐ[R] A) = nsmulAlgHom R A n := by
  have h := BialgHom.toAlgHom_convPow (toConv (BialgHom.id R A)) n
  apply WithConv.toConv_injective
  exact h

@[simp] theorem nsmulBialgHom_apply (n : ℕ) (a : A) : nsmulBialgHom R A n a = nsmulAlgHom R A n a :=
  DFunLike.congr_fun (toAlgHom_nsmulBialgHom R A n) a

theorem map_comp_comulAlgHom_nsmulAlgHom (n : ℕ) :
    (Algebra.TensorProduct.map (nsmulAlgHom R A n) (nsmulAlgHom R A n)).comp (comulAlgHom R A) =
      (comulAlgHom R A).comp (nsmulAlgHom R A n) := by
  have h := BialgHom.map_comp_comulAlgHom (nsmulBialgHom R A n)
  rw [toAlgHom_nsmulBialgHom] at h
  exact h

end NSMulBialg

section OneStep

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
variable {B : Type w} [CommRing B] [Bialgebra R B]

theorem counit_bialgHom_apply (π : A →ₐc[R] B) (a : A) : counit (R := R) (π a) = counit (R := R) a :=
  CoalgHomClass.counit_comp_apply π a

theorem ker_le_augIdeal (π : A →ₐc[R] B) : RingHom.ker (π : A →ₐ[R] B) ≤ augIdeal R A := by
  intro a ha
  rw [mem_augIdeal_iff, ← counit_bialgHom_apply π a, show π a = 0 from ha, map_zero]

theorem map_augIdeal_le (π : A →ₐc[R] B) : (augIdeal R A).map (π : A →ₐ[R] B) ≤ augIdeal R B := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change π a ∈ augIdeal R B
  rw [mem_augIdeal_iff, counit_bialgHom_apply, (mem_augIdeal_iff R A a).1 ha]

theorem map_augIdeal_of_surjective (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    (augIdeal R A).map (π : A →ₐ[R] B) = augIdeal R B := by
  refine le_antisymm (map_augIdeal_le π) fun b hb => ?_
  obtain ⟨a, rfl⟩ := hπ b
  have ha : a - algebraMap R A (counit (R := R) a) ∈ augIdeal R A :=
    sub_algebraMap_counit_mem_augIdeal R A a
  have hb0 : counit (R := R) a = 0 := by rwa [mem_augIdeal_iff, counit_bialgHom_apply] at hb
  have : (π : A →ₐ[R] B) (a - algebraMap R A (counit (R := R) a)) = π a := by
    rw [hb0, map_zero, sub_zero]; rfl
  rw [← this]
  exact Ideal.mem_map_of_mem _ ha

theorem bialgHom_mem_augIdeal (π : A →ₐc[R] B) {a : A} (ha : a ∈ augIdeal R A) : π a ∈ augIdeal R B := by
  rw [mem_augIdeal_iff, counit_bialgHom_apply, (mem_augIdeal_iff R A a).1 ha]

theorem map_torsionIdeal_le (π : A →ₐc[R] B) (n : ℕ) :
    (torsionIdeal R A n).map (π : A →ₐ[R] B) ≤ torsionIdeal R B n := by
  rw [torsionIdeal, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
  intro a ha
  change π (nsmulAlgHom R A n a) ∈ torsionIdeal R B n
  rw [← nsmulAlgHom_bialgHom_apply]
  exact nsmulAlgHom_mem_torsionIdeal R B (bialgHom_mem_augIdeal π ha) n

theorem map_torsionIdeal_of_surjective (π : A →ₐc[R] B) (hπ : Function.Surjective π) (n : ℕ) :
    (torsionIdeal R A n).map (π : A →ₐ[R] B) = torsionIdeal R B n := by
  refine le_antisymm (map_torsionIdeal_le π n) ?_
  rw [torsionIdeal, ← map_augIdeal_of_surjective π hπ, Ideal.map_le_iff_le_comap,
    Ideal.map_le_iff_le_comap]
  intro a ha
  change nsmulAlgHom R B n (π a) ∈ (torsionIdeal R A n).map (π : A →ₐ[R] B)
  rw [nsmulAlgHom_bialgHom_apply]
  exact Ideal.mem_map_of_mem _ (nsmulAlgHom_mem_torsionIdeal R A ha n)

theorem torsionIdeal_mul_le (m n : ℕ) : torsionIdeal R A (m * n) ≤ torsionIdeal R A m := by
  rw [torsionIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  change nsmulAlgHom R A (m * n) a ∈ torsionIdeal R A m
  rw [← nsmulAlgHom_nsmulAlgHom_apply]
  exact nsmulAlgHom_mem_torsionIdeal R A (nsmulAlgHom_mem_augIdeal R A ha n) m

theorem torsionIdeal_le_of_dvd {m n : ℕ} (h : m ∣ n) : torsionIdeal R A n ≤ torsionIdeal R A m := by
  obtain ⟨c, rfl⟩ := h
  exact torsionIdeal_mul_le m c

theorem nsmulAlgHom_eq_of_ker_eq_torsionIdeal (π : A →ₐc[R] B) (hπ : Function.Surjective π) (n : ℕ)
    (hker : RingHom.ker (π : A →ₐ[R] B) = torsionIdeal R A n) :
    nsmulAlgHom R B n = (Algebra.ofId R B).comp (counitAlgHom R B) := by
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hπ b
  have hdec : a = algebraMap R _ (counit (R := R) a) + (a - algebraMap R _ (counit (R := R) a)) := by
    abel
  have hkill : π (nsmulAlgHom R A n (a - algebraMap R _ (counit (R := R) a))) = 0 := by
    have hmem : nsmulAlgHom R A n (a - algebraMap R _ (counit (R := R) a)) ∈
        RingHom.ker (π : A →ₐ[R] B) := by
      rw [hker]
      exact nsmulAlgHom_mem_torsionIdeal R A (sub_algebraMap_counit_mem_augIdeal R A a) n
    exact hmem
  rw [nsmulAlgHom_bialgHom_apply]
  conv_lhs => rw [hdec]
  rw [map_add, map_add, nsmulAlgHom_algebraMap, hkill, add_zero, AlgHom.comp_apply, Algebra.ofId_apply,
    Bialgebra.counitAlgHom_apply, counit_bialgHom_apply]
  exact (π : A →ₐ[R] B).commutes _

theorem nsmulAlgHom_apply_of_ker_eq_torsionIdeal (π : A →ₐc[R] B) (hπ : Function.Surjective π) (n : ℕ)
    (hker : RingHom.ker (π : A →ₐ[R] B) = torsionIdeal R A n) (b : B) :
    nsmulAlgHom R B n b = algebraMap R B (counit (R := R) b) := by
  rw [nsmulAlgHom_eq_of_ker_eq_torsionIdeal π hπ n hker]
  rfl

theorem torsionIdeal_eq_bot_of_ker_eq_torsionIdeal (π : A →ₐc[R] B) (hπ : Function.Surjective π)
    (n : ℕ) (hker : RingHom.ker (π : A →ₐ[R] B) = torsionIdeal R A n) :
    torsionIdeal R B n = ⊥ := by
  rw [← le_bot_iff, torsionIdeal, Ideal.map_le_iff_le_comap]
  intro b hb
  change nsmulAlgHom R B n b ∈ (⊥ : Ideal B)
  rw [nsmulAlgHom_apply_of_ker_eq_torsionIdeal π hπ n hker, (mem_augIdeal_iff R B b).1 hb, map_zero]
  exact Ideal.zero_mem _

theorem point_pow_eq_one_of_ker_eq_torsionIdeal (π : A →ₐc[R] B) (hπ : Function.Surjective π) (n : ℕ)
    (hker : RingHom.ker (π : A →ₐ[R] B) = torsionIdeal R A n)
    {L : Type x} [CommRing L] [Algebra R L] (f : WithConv (B →ₐ[R] L)) : f ^ n = 1 := by
  have h := toConv_pow_eq_toConv_comp_nsmulAlgHom f.ofConv n
  rw [toConv_ofConv] at h
  rw [h, nsmulAlgHom_eq_of_ker_eq_torsionIdeal π hπ n hker, AlgHom.convOne_def, ← AlgHom.comp_assoc,
    Algebra.comp_ofId]

theorem comp_injective_of_surjective (π : A →ₐc[R] B) (hπ : Function.Surjective π)
    {L : Type x} [Semiring L] [Algebra R L] :
    Function.Injective fun g : B →ₐ[R] L => g.comp (π : A →ₐ[R] B) := by
  intro g g' hgg'
  refine AlgHom.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hπ b
  exact DFunLike.congr_fun hgg' a

theorem exists_comp_eq_of_pow_eq_one (π : A →ₐc[R] B) (hπ : Function.Surjective π) (n : ℕ)
    (hker : RingHom.ker (π : A →ₐ[R] B) = torsionIdeal R A n)
    {L : Type x} [CommRing L] [Algebra R L] (f : WithConv (A →ₐ[R] L)) (hf : f ^ n = 1) :
    ∃ g : B →ₐ[R] L, g.comp (π : A →ₐ[R] B) = f.ofConv := by
  have hle : RingHom.ker (π : A →ₐ[R] B).toRingHom ≤ RingHom.ker f.ofConv.toRingHom := by
    intro a ha
    have ha' : a ∈ torsionIdeal R A n := by
      rw [← hker]
      exact ha
    exact apply_eq_zero_of_mem_torsionIdeal_of_pow_eq_one R A f n hf ha'
  exact ⟨AlgHom.liftOfSurjective (π : A →ₐ[R] B) hπ f.ofConv hle, AlgHom.liftOfSurjective_comp _ _ _ _⟩

theorem exists_comp_eq_iff_pow_eq_one (π : A →ₐc[R] B) (hπ : Function.Surjective π) (n : ℕ)
    (hker : RingHom.ker (π : A →ₐ[R] B) = torsionIdeal R A n)
    {L : Type x} [CommRing L] [Algebra R L] (f : WithConv (A →ₐ[R] L)) :
    (∃ g : B →ₐ[R] L, g.comp (π : A →ₐ[R] B) = f.ofConv) ↔ f ^ n = 1 := by
  refine ⟨?_, exists_comp_eq_of_pow_eq_one π hπ n hker f⟩
  rintro ⟨g, hg⟩
  have hf : f = toConv (g.comp (π : A →ₐ[R] B)) := by rw [hg, toConv_ofConv]
  rw [hf, ← WithConv.ofConv_injective.eq_iff,
    show toConv (g.comp (π : A →ₐ[R] B)) = toConv ((toConv g).ofConv.comp (π : A →ₐ[R] B)) from rfl,
    ← convPow_comp_bialgHom, point_pow_eq_one_of_ker_eq_torsionIdeal π hπ n hker (toConv g),
    AlgHom.convOne_def, AlgHom.convOne_def]
  change ((Algebra.ofId R L).comp (counitAlgHom R B)).comp (π : A →ₐ[R] B) = _
  refine AlgHom.ext fun a => ?_
  change algebraMap R L (counit (R := R) (π a)) = algebraMap R L (counit (R := R) a)
  rw [counit_bialgHom_apply]

end OneStep

end PDivisibleGroup.Hopf

namespace PDivisibleGroup.Tower

variable {R : Type u} [CommRing R] {L : ℕ → Type v} [∀ w, CommRing (L w)] [∀ w, HopfAlgebra R (L w)]

noncomputable def transitionLE (t : ∀ w, L (w + 1) →ₐc[R] L w) (v : ℕ) : ∀ u : ℕ, L (v + u) →ₐc[R] L v
  | 0 => BialgHom.id R (L v)
  | u + 1 => (transitionLE t v u).comp (t (v + u))

variable (t : ∀ w, L (w + 1) →ₐc[R] L w)

@[simp] theorem transitionLE_zero (v : ℕ) : transitionLE t v 0 = BialgHom.id R (L v) := rfl

theorem transitionLE_succ (v u : ℕ) : transitionLE t v (u + 1) = (transitionLE t v u).comp (t (v + u)) := rfl

theorem transitionLE_succ_apply (v u : ℕ) (a : L (v + u + 1)) :
    transitionLE t v (u + 1) a = transitionLE t v u (t (v + u) a) := rfl

@[simp] theorem transitionLE_one (v : ℕ) : transitionLE t v 1 = t v := by
  rw [transitionLE_succ, transitionLE_zero]
  rfl

theorem counit_transitionLE (v u : ℕ) (a : L (v + u)) :
    counit (R := R) (transitionLE t v u a) = counit (R := R) a :=
  Hopf.counit_bialgHom_apply _ a

theorem transitionLE_surjective (ht : ∀ w, Function.Surjective (t w)) (v : ℕ) :
    ∀ u, Function.Surjective (transitionLE t v u)
  | 0 => Function.surjective_id
  | u + 1 => by
    rw [transitionLE_succ, BialgHom.coe_comp]
    exact (transitionLE_surjective ht v u).comp (ht (v + u))

section Exactness

variable {t} {p : ℕ}
variable (ht : ∀ w, Function.Surjective (t w))
  (hkerL : ∀ w, RingHom.ker (t w) = Hopf.torsionIdeal R (L (w + 1)) (p ^ w))

include ht hkerL

theorem nsmulAlgHom_pow_eq (w : ℕ) :
    Hopf.nsmulAlgHom R (L w) (p ^ w) = (Algebra.ofId R (L w)).comp (counitAlgHom R (L w)) :=
  Hopf.nsmulAlgHom_eq_of_ker_eq_torsionIdeal (t w) (ht w) (p ^ w) (hkerL w)

theorem nsmulAlgHom_pow_apply (w : ℕ) (b : L w) :
    Hopf.nsmulAlgHom R (L w) (p ^ w) b = algebraMap R (L w) (counit (R := R) b) :=
  Hopf.nsmulAlgHom_apply_of_ker_eq_torsionIdeal (t w) (ht w) (p ^ w) (hkerL w) b

theorem point_pow_eq_one (w : ℕ) {T : Type x} [CommRing T] [Algebra R T]
    (f : WithConv (L w →ₐ[R] T)) : f ^ (p ^ w) = 1 :=
  Hopf.point_pow_eq_one_of_ker_eq_torsionIdeal (t w) (ht w) (p ^ w) (hkerL w) f

theorem torsionIdeal_pow_self (w : ℕ) : Hopf.torsionIdeal R (L w) (p ^ w) = ⊥ :=
  Hopf.torsionIdeal_eq_bot_of_ker_eq_torsionIdeal (t w) (ht w) (p ^ w) (hkerL w)

theorem ker_transitionLE (v : ℕ) :
    ∀ u, RingHom.ker (transitionLE t v u) = Hopf.torsionIdeal R (L (v + u)) (p ^ v)
  | 0 => by
    show RingHom.ker (BialgHom.id R (L v)) = Hopf.torsionIdeal R (L v) (p ^ v)
    rw [torsionIdeal_pow_self ht hkerL v]
    ext a
    rw [RingHom.mem_ker, Ideal.mem_bot]
    rfl
  | u + 1 => by
    have ih := ker_transitionLE v u
    show RingHom.ker (transitionLE t v (u + 1)) = Hopf.torsionIdeal R (L (v + u + 1)) (p ^ v)
    change RingHom.ker ((transitionLE t v u : L (v + u) →ₐ[R] L v).toRingHom.comp
        (t (v + u) : L (v + u + 1) →ₐ[R] L (v + u)).toRingHom) = _
    rw [← RingHom.comap_ker]
    change Ideal.comap (t (v + u) : L (v + u + 1) →ₐ[R] L (v + u)) (RingHom.ker (transitionLE t v u)) = _
    rw [ih, ← Hopf.map_torsionIdeal_of_surjective (t (v + u)) (ht (v + u)) (p ^ v),
      Ideal.comap_map_of_surjective (t (v + u) : L (v + u + 1) →ₐ[R] L (v + u)) (ht (v + u))]
    refine le_antisymm (sup_le le_rfl ?_) le_sup_left
    intro a ha
    have ha' : a ∈ RingHom.ker (t (v + u)) := ha
    rw [hkerL (v + u)] at ha'
    exact Hopf.torsionIdeal_le_of_dvd (pow_dvd_pow p (Nat.le_add_right v u)) ha'

theorem mem_ker_transitionLE_iff (v u : ℕ) (a : L (v + u)) :
    transitionLE t v u a = 0 ↔ a ∈ Hopf.torsionIdeal R (L (v + u)) (p ^ v) := by
  rw [← ker_transitionLE ht hkerL v u, RingHom.mem_ker]

theorem exists_comp_transitionLE_eq (v u : ℕ) {T : Type x} [CommRing T] [Algebra R T]
    (f : WithConv (L (v + u) →ₐ[R] T)) (hf : f ^ (p ^ v) = 1) :
    ∃ g : L v →ₐ[R] T, g.comp (transitionLE t v u : L (v + u) →ₐ[R] L v) = f.ofConv :=
  Hopf.exists_comp_eq_of_pow_eq_one (transitionLE t v u) (transitionLE_surjective t ht v u) (p ^ v)
    (ker_transitionLE ht hkerL v u) f hf

theorem exists_comp_transitionLE_eq_iff (v u : ℕ) {T : Type x} [CommRing T] [Algebra R T]
    (f : WithConv (L (v + u) →ₐ[R] T)) :
    (∃ g : L v →ₐ[R] T, g.comp (transitionLE t v u : L (v + u) →ₐ[R] L v) = f.ofConv) ↔
      f ^ (p ^ v) = 1 :=
  Hopf.exists_comp_eq_iff_pow_eq_one (transitionLE t v u) (transitionLE_surjective t ht v u) (p ^ v)
    (ker_transitionLE ht hkerL v u) f

end Exactness

theorem comp_transitionLE_injective (ht : ∀ w, Function.Surjective (t w)) (v u : ℕ)
    {T : Type x} [Semiring T] [Algebra R T] :
    Function.Injective fun g : L v →ₐ[R] T => g.comp (transitionLE t v u : L (v + u) →ₐ[R] L v) :=
  Hopf.comp_injective_of_surjective (transitionLE t v u) (transitionLE_surjective t ht v u)

section OfLE

noncomputable def levelCast : ∀ {n m : ℕ}, n = m → (L n ≃ₐc[R] L m)
  | _, _, rfl => BialgEquiv.refl R _

@[simp] theorem levelCast_rfl (n : ℕ) : (levelCast rfl : L n ≃ₐc[R] L n) = BialgEquiv.refl R (L n) := rfl

noncomputable def transitionOfLE (a : ℕ) : ∀ b : ℕ, a ≤ b → (L b →ₐc[R] L a)
  | 0, h => ((levelCast (Nat.le_zero.1 h).symm : L 0 ≃ₐc[R] L a) : L 0 →ₐc[R] L a)
  | b + 1, h =>
    if hab : a = b + 1 then ((levelCast hab : L a ≃ₐc[R] L (b + 1)).symm : L (b + 1) →ₐc[R] L a)
    else (transitionOfLE a b (by omega)).comp (t b)

theorem transitionOfLE_self (a : ℕ) (h : a ≤ a) : transitionOfLE t a a h = BialgHom.id R (L a) := by
  cases a with
  | zero => rfl
  | succ a =>
    show (if hab : a + 1 = a + 1 then _ else _) = _
    rw [dif_pos rfl]
    rfl

theorem transitionOfLE_succ (a b : ℕ) (hab : a ≤ b) (h : a ≤ b + 1) :
    transitionOfLE t a (b + 1) h = (transitionOfLE t a b hab).comp (t b) := by
  show (if hab : a = b + 1 then _ else _) = _
  rw [dif_neg (by omega)]

theorem transitionOfLE_succ_self (a : ℕ) (h : a ≤ a + 1) : transitionOfLE t a (a + 1) h = t a := by
  rw [transitionOfLE_succ t a a le_rfl h, transitionOfLE_self]
  rfl

theorem transitionOfLE_eq_comp_left (a : ℕ) :
    ∀ (b : ℕ) (h : a + 1 ≤ b), transitionOfLE t a b (by omega) = (t a).comp (transitionOfLE t (a + 1) b h)
  | 0, h => absurd h (by omega)
  | b + 1, h => by
    by_cases hab : a = b
    · subst hab
      rw [transitionOfLE_succ_self, transitionOfLE_self]
      rfl
    · rw [transitionOfLE_succ t a b (by omega), transitionOfLE_succ t (a + 1) b (by omega),
        transitionOfLE_eq_comp_left a b (by omega)]
      rfl

theorem transitionOfLE_comp (a b : ℕ) (hab : a ≤ b) :
    ∀ (c : ℕ) (hbc : b ≤ c),
      (transitionOfLE t a b hab).comp (transitionOfLE t b c hbc) = transitionOfLE t a c (hab.trans hbc)
  | 0, hbc => by
    obtain rfl : b = 0 := Nat.le_zero.1 hbc
    obtain rfl : a = 0 := Nat.le_zero.1 hab
    rfl
  | c + 1, hbc => by
    by_cases hbc' : b = c + 1
    · subst hbc'
      rw [transitionOfLE_self]
      exact BialgHom.comp_id _
    · rw [transitionOfLE_succ t b c (by omega), transitionOfLE_succ t a c (by omega),
        ← BialgHom.comp_assoc, transitionOfLE_comp a b hab c (by omega)]

theorem transitionLE_eq_transitionOfLE (a : ℕ) :
    ∀ u : ℕ, transitionLE t a u = transitionOfLE t a (a + u) (Nat.le_add_right a u)
  | 0 => (transitionOfLE_self t a le_rfl).symm
  | u + 1 => by
    rw [transitionLE_succ, transitionLE_eq_transitionOfLE a u]
    exact (transitionOfLE_succ t a (a + u) (Nat.le_add_right a u) _).symm

theorem transitionOfLE_surjective (ht : ∀ w, Function.Surjective (t w)) (a : ℕ) :
    ∀ (b : ℕ) (h : a ≤ b), Function.Surjective (transitionOfLE t a b h)
  | 0, h => by
    obtain rfl : a = 0 := Nat.le_zero.1 h
    exact Function.surjective_id
  | b + 1, h => by
    by_cases hab : a = b + 1
    · subst hab
      rw [transitionOfLE_self]
      exact Function.surjective_id
    · rw [transitionOfLE_succ t a b (by omega), BialgHom.coe_comp]
      exact (transitionOfLE_surjective ht a b (by omega)).comp (ht b)

theorem counit_transitionOfLE (a b : ℕ) (h : a ≤ b) (x : L b) :
    counit (R := R) (transitionOfLE t a b h x) = counit (R := R) x :=
  Hopf.counit_bialgHom_apply _ x

variable {t} {p : ℕ}
variable (ht : ∀ w, Function.Surjective (t w))
  (hkerL : ∀ w, RingHom.ker (t w) = Hopf.torsionIdeal R (L (w + 1)) (p ^ w))

include ht hkerL

theorem ker_transitionOfLE (a : ℕ) :
    ∀ (b : ℕ) (h : a ≤ b), RingHom.ker (transitionOfLE t a b h) = Hopf.torsionIdeal R (L b) (p ^ a)
  | 0, h => by
    obtain rfl : a = 0 := Nat.le_zero.1 h
    rw [transitionOfLE_self, torsionIdeal_pow_self ht hkerL 0]
    ext x
    rw [RingHom.mem_ker, Ideal.mem_bot]
    rfl
  | b + 1, h => by
    by_cases hab : a = b + 1
    · subst hab
      rw [transitionOfLE_self, torsionIdeal_pow_self ht hkerL (b + 1)]
      ext x
      rw [RingHom.mem_ker, Ideal.mem_bot]
      rfl
    · have ih := ker_transitionOfLE a b (by omega)
      rw [transitionOfLE_succ t a b (by omega)]
      change RingHom.ker ((transitionOfLE t a b _ : L b →ₐ[R] L a).toRingHom.comp
          (t b : L (b + 1) →ₐ[R] L b).toRingHom) = _
      rw [← RingHom.comap_ker]
      change Ideal.comap (t b : L (b + 1) →ₐ[R] L b) (RingHom.ker (transitionOfLE t a b _)) = _
      rw [ih, ← Hopf.map_torsionIdeal_of_surjective (t b) (ht b) (p ^ a),
        Ideal.comap_map_of_surjective (t b : L (b + 1) →ₐ[R] L b) (ht b)]
      refine le_antisymm (sup_le le_rfl ?_) le_sup_left
      intro x hx
      have hx' : x ∈ RingHom.ker (t b) := hx
      rw [hkerL b] at hx'
      exact Hopf.torsionIdeal_le_of_dvd (pow_dvd_pow p (show a ≤ b by omega)) hx'

theorem mem_ker_transitionOfLE_iff (a b : ℕ) (h : a ≤ b) (x : L b) :
    transitionOfLE t a b h x = 0 ↔ x ∈ Hopf.torsionIdeal R (L b) (p ^ a) := by
  rw [← ker_transitionOfLE ht hkerL a b h, RingHom.mem_ker]

theorem exists_comp_transitionOfLE_eq (a b : ℕ) (h : a ≤ b) {T : Type x} [CommRing T] [Algebra R T]
    (f : WithConv (L b →ₐ[R] T)) (hf : f ^ (p ^ a) = 1) :
    ∃ g : L a →ₐ[R] T, g.comp (transitionOfLE t a b h : L b →ₐ[R] L a) = f.ofConv :=
  Hopf.exists_comp_eq_of_pow_eq_one (transitionOfLE t a b h) (transitionOfLE_surjective t ht a b h)
    (p ^ a) (ker_transitionOfLE ht hkerL a b h) f hf

end OfLE

end PDivisibleGroup.Tower


