-- Prove2me | Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
-- name    : AlgebraicGeometry_ThetaLevelGroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/0a4a7186-5646-5d1f-a1cf-99580766f66b
-- title:
--   Finite Heisenberg group, theta-level group, Schrödinger representation
-- statement:
--   Fix $g$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ and $d \in \mathbb{N}$, and write $H(\delta) = \prod_i \mathbb{Z}/\delta_i$ (`HH`). For each $i$, `iota` is the additive map $\mathbb{Z}/\delta_i \to \mathbb{Z}/2d$ obtained, when $\delta_i \mid 2d$, by lifting multiplication by $2d/\delta_i$, and is $0$ otherwise; `pair` is the resulting pairing $B(k,h) = \sum_i \iota_i(k_i h_i) \in \mathbb{Z}/2d$, shown to be additive in each argument, to vanish when either argument is $0$, to negate under negation of either argument, and to be symmetric. `Heis δ d` is the structure of triples $(a,h,k) \in \mathbb{Z}/2d \times H(\delta) \times H(\delta)$ with product $(a,h,k)(a',h',k') = (a+a'+B(k,h'),\,h+h',\,k+k')$, unit $(0,0,0)$ and inverse $(-a+B(k,h),-h,-k)$; it is made a group, and a finite type with decidable equality when $d$ and all $\delta_i$ are nonzero. The elements `cen a` $=(a,0,0)$, `theta h` $=(0,h,0)$, `eta k` $=(0,0,k)$ satisfy $(a,h,k) = \mathrm{cen}(a)\,\theta_h\,\eta_k$ and the commutation rule $\eta_k\theta_h = \mathrm{cen}(B(k,h))\,\theta_h\,\eta_k$. `Heis.Gam` is the subgroup of `MulAut (Heis δ d)` consisting of the automorphisms $\gamma$ with $\gamma(\mathrm{cen}\,a) = \mathrm{cen}\,a$ for all $a$, finite in the above situation.
--
--   Over a commutative ring $B$ with a chosen $\omega \in B$, `omegaPow` sends $a \in \mathbb{Z}/2d$ to $\omega^{a.\mathrm{val}}$ (the canonical representative); it is multiplicative and agrees with $n \mapsto \omega^n$ on natural numbers once $\omega^{2d}=1$. On $V = (H(\delta) \to B)$, `shiftOp h` is precomposition with $x \mapsto x-h$, `diagOp c` is pointwise multiplication by $c$, `thetaChar k` is $h \mapsto \omega^{B(k,h)}$, and `schrod z` is $\omega^{z.a} \cdot (\mathrm{shiftOp}\,z.h \circ \mathrm{diagOp}\,\chi_{z.k})$, so $(\mathrm{schrod}\,z\,v)(x) = \omega^{z.a}\,\omega^{B(z.k,\,x-z.h)}\,v(x-z.h)$. It sends $1$ to the identity and, assuming $\omega^{2d}=1$, is multiplicative; `schrodHom` bundles it as a monoid homomorphism $\mathrm{Heis}\,\delta\,d \to \mathrm{End}_B V$. Relative to a bijection $e : \mathrm{Fin}\,n \simeq H(\delta)$, `schrodMat z` has $(i,j)$ entry $\omega^{z.a + B(z.k, e_j)}$ if $e_i = e_j + z.h$ and $0$ otherwise. Finally `IsIntertwiner γ U` asserts that $U$ is a unit and $U \cdot \mathrm{schrodMat}(z) = \mathrm{schrodMat}(\gamma z) \cdot U$ for all $z$, and `inter γ` is a chosen intertwiner for $\gamma$ when one exists and the identity matrix otherwise, the two accompanying lemmas recording exactly these two cases.
--
--   **Relation to Mathlib.** Mathlib has no finite Heisenberg group, theta-level group or Schrödinger representation; these are the project's own definitions, built from Mathlib's `ZMod`, `MulAut`, `Subgroup`, `Matrix`, `Module.End` and the linear maps `LinearMap.funLeft` and `LinearMap.mulLeft`.
--
--   **Where it is used.** These are the basic algebraic objects for the project's treatment of theta level structures on polarised abelian schemes: the Heisenberg group with centre $\mathbb{Z}/2d$, its automorphisms fixing the centre pointwise, and the explicit Schrödinger model in which changes of theta frame are realised by intertwining matrices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ThetaLevelGroup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace AlgebraicGeometry.ThetaLevel

section Heis

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ)

abbrev HH : Type := (i : Fin g) → ZMod (δ i)

noncomputable def iota (i : Fin g) : ZMod (δ i) →+ ZMod (2 * d) :=
  if hdiv : δ i ∣ 2 * d then
    ZMod.lift (δ i)
      ⟨(AddMonoidHom.mulLeft ((2 * d / δ i : ℕ) : ZMod (2 * d))).comp (Int.castAddHom (ZMod (2 * d))), by
        change ((2 * d / δ i : ℕ) : ZMod (2 * d)) * (((δ i : ℕ) : ℤ) : ZMod (2 * d)) = 0
        rw [Int.cast_natCast, ← Nat.cast_mul, Nat.div_mul_cancel hdiv, ZMod.natCast_self]⟩
  else 0

theorem iota_natCast (i : Fin g) (hdiv : δ i ∣ 2 * d) (x : ℕ) :
    iota δ d i (x : ZMod (δ i)) = ((2 * d / δ i : ℕ) : ZMod (2 * d)) * (x : ZMod (2 * d)) := by
  rw [iota, dif_pos hdiv]
  have hx : ((x : ℤ) : ZMod (δ i)) = (x : ZMod (δ i)) := Int.cast_natCast x
  rw [← hx, ZMod.lift_coe]
  change ((2 * d / δ i : ℕ) : ZMod (2 * d)) * ((x : ℤ) : ZMod (2 * d)) = _
  rw [Int.cast_natCast]

noncomputable def pair (k h : HH δ) : ZMod (2 * d) := ∑ i, iota δ d i (k i * h i)

theorem pair_add_left (k k' h : HH δ) : pair δ d (k + k') h = pair δ d k h + pair δ d k' h := by
  simp only [pair, Pi.add_apply, add_mul, map_add, Finset.sum_add_distrib]

theorem pair_add_right (k h h' : HH δ) : pair δ d k (h + h') = pair δ d k h + pair δ d k h' := by
  simp only [pair, Pi.add_apply, mul_add, map_add, Finset.sum_add_distrib]

theorem pair_zero_left (h : HH δ) : pair δ d 0 h = 0 := by
  simp [pair]

theorem pair_zero_right (k : HH δ) : pair δ d k 0 = 0 := by
  simp [pair]

theorem pair_neg_right (k h : HH δ) : pair δ d k (-h) = -pair δ d k h := by
  simp only [pair, Pi.neg_apply, mul_neg, map_neg, Finset.sum_neg_distrib]

theorem pair_neg_left (k h : HH δ) : pair δ d (-k) h = -pair δ d k h := by
  simp only [pair, Pi.neg_apply, neg_mul, map_neg, Finset.sum_neg_distrib]

theorem pair_comm (k h : HH δ) : pair δ d k h = pair δ d h k := by
  simp only [pair, mul_comm]

@[ext]
structure Heis : Type where
  a : ZMod (2 * d)
  h : HH δ
  k : HH δ

namespace Heis

variable {δ} {d}

instance instMul : Mul (Heis δ d) := ⟨fun z z' => ⟨z.a + z'.a + pair δ d z.k z'.h, z.h + z'.h, z.k + z'.k⟩⟩
instance instOne : One (Heis δ d) := ⟨⟨0, 0, 0⟩⟩
instance instInv : Inv (Heis δ d) := ⟨fun z => ⟨-z.a + pair δ d z.k z.h, -z.h, -z.k⟩⟩

@[simp] theorem mul_a (z z' : Heis δ d) : (z * z').a = z.a + z'.a + pair δ d z.k z'.h := rfl
@[simp] theorem mul_h (z z' : Heis δ d) : (z * z').h = z.h + z'.h := rfl
@[simp] theorem mul_k (z z' : Heis δ d) : (z * z').k = z.k + z'.k := rfl
@[simp] theorem one_a : (1 : Heis δ d).a = 0 := rfl
@[simp] theorem one_h : (1 : Heis δ d).h = 0 := rfl
@[simp] theorem one_k : (1 : Heis δ d).k = 0 := rfl
@[simp] theorem inv_a (z : Heis δ d) : z⁻¹.a = -z.a + pair δ d z.k z.h := rfl
@[simp] theorem inv_h (z : Heis δ d) : z⁻¹.h = -z.h := rfl
@[simp] theorem inv_k (z : Heis δ d) : z⁻¹.k = -z.k := rfl

instance instGroup : Group (Heis δ d) where
  mul_assoc z z' z'' := by
    refine Heis.ext ?_ ?_ ?_
    · simp only [mul_a, mul_h, mul_k, pair_add_left, pair_add_right]; abel
    · simp only [mul_h]; abel
    · simp only [mul_k]; abel
  one_mul z := by refine Heis.ext ?_ ?_ ?_ <;> simp [pair_zero_left]
  mul_one z := by refine Heis.ext ?_ ?_ ?_ <;> simp [pair_zero_right]
  inv_mul_cancel z := by
    refine Heis.ext ?_ ?_ ?_
    · simp only [mul_a, inv_a, inv_k, one_a, pair_neg_left]; abel
    · simp only [mul_h, inv_h, one_h, neg_add_cancel]
    · simp only [mul_k, inv_k, one_k, neg_add_cancel]

instance instFintype [NeZero d] [∀ i, NeZero (δ i)] : Fintype (Heis δ d) :=
  Fintype.ofEquiv (ZMod (2 * d) × HH δ × HH δ)
    { toFun := fun p => ⟨p.1, p.2.1, p.2.2⟩, invFun := fun z => ⟨z.a, z.h, z.k⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

instance instDecidableEq : DecidableEq (Heis δ d) := fun z z' =>
  decidable_of_iff (z.a = z'.a ∧ z.h = z'.h ∧ z.k = z'.k)
    ⟨fun hh => Heis.ext hh.1 hh.2.1 hh.2.2, fun hh => by subst hh; exact ⟨rfl, rfl, rfl⟩⟩

def cen (a : ZMod (2 * d)) : Heis δ d := ⟨a, 0, 0⟩

@[simp] theorem cen_a (a : ZMod (2 * d)) : (cen a : Heis δ d).a = a := rfl
@[simp] theorem cen_h (a : ZMod (2 * d)) : (cen a : Heis δ d).h = 0 := rfl
@[simp] theorem cen_k (a : ZMod (2 * d)) : (cen a : Heis δ d).k = 0 := rfl

theorem cen_mul (a : ZMod (2 * d)) (z : Heis δ d) : cen a * z = ⟨a + z.a, z.h, z.k⟩ := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, pair_zero_left]

theorem mul_cen (a : ZMod (2 * d)) (z : Heis δ d) : z * cen a = ⟨z.a + a, z.h, z.k⟩ := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, pair_zero_right]

def theta (h : HH δ) : Heis δ d := ⟨0, h, 0⟩

def eta (k : HH δ) : Heis δ d := ⟨0, 0, k⟩

@[simp] theorem theta_a (h : HH δ) : (theta h : Heis δ d).a = 0 := rfl
@[simp] theorem theta_h (h : HH δ) : (theta h : Heis δ d).h = h := rfl
@[simp] theorem theta_k (h : HH δ) : (theta h : Heis δ d).k = 0 := rfl
@[simp] theorem eta_a (k : HH δ) : (eta k : Heis δ d).a = 0 := rfl
@[simp] theorem eta_h (k : HH δ) : (eta k : Heis δ d).h = 0 := rfl
@[simp] theorem eta_k (k : HH δ) : (eta k : Heis δ d).k = k := rfl

theorem cen_mul_theta_mul_eta (z : Heis δ d) : cen z.a * theta z.h * eta z.k = z := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, theta, eta, pair_zero_left, pair_zero_right]

theorem eta_mul_theta (h k : HH δ) : (eta k * theta h : Heis δ d) = cen (pair δ d k h) * theta h * eta k := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [cen, theta, eta, pair_zero_left, pair_zero_right]

variable (δ d) in

def Gam : Subgroup (MulAut (Heis δ d)) where
  carrier := {γ | ∀ a, γ (cen a) = cen a}
  mul_mem' := by
    intro γ γ' hγ hγ' a
    show γ (γ' (cen a)) = cen a
    rw [hγ', hγ]
  one_mem' := by intro a; rfl
  inv_mem' := by
    intro γ hγ a
    show γ.symm (cen a) = cen a
    rw [MulEquiv.symm_apply_eq]
    exact (hγ a).symm

instance Gam.instFinite [NeZero d] [∀ i, NeZero (δ i)] : Finite (Gam δ d) := by
  have : Finite (MulAut (Heis δ d)) :=
    Finite.of_injective (fun γ : MulAut (Heis δ d) => γ.toEquiv)
      (fun _ _ hh => MulEquiv.ext (fun x => congrFun (congrArg (⇑) hh) x))
  infer_instance

instance Gam.instFintype [NeZero d] [∀ i, NeZero (δ i)] : Fintype (Gam δ d) :=
  Fintype.ofFinite _

end Heis

end Heis

section Schrodinger

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B)

def omegaPow (a : ZMod (2 * d)) : B := ω ^ a.val

omit [NeZero d] in
theorem omegaPow_zero : omegaPow d B ω 0 = 1 := by
  simp [omegaPow]

theorem omegaPow_aux_pow_mod_eq {M : Type} [Monoid M] (x : M) {m : ℕ} (hx : x ^ m = 1) (n : ℕ) :
    x ^ (n % m) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, hx, one_pow, mul_one]

theorem omegaPow_add (hω : ω ^ (2 * d) = 1) (a b : ZMod (2 * d)) :
    omegaPow d B ω (a + b) = omegaPow d B ω a * omegaPow d B ω b := by
  simp only [omegaPow]
  rw [ZMod.val_add, omegaPow_aux_pow_mod_eq ω hω, pow_add]

omit [NeZero d] in
theorem omegaPow_natCast (hω : ω ^ (2 * d) = 1) (n : ℕ) :
    omegaPow d B ω (n : ZMod (2 * d)) = ω ^ n := by
  simp only [omegaPow]
  rw [ZMod.val_natCast, omegaPow_aux_pow_mod_eq ω hω]

def thetaChar (k : HH δ) : HH δ → B := fun h => omegaPow d B ω (pair δ d k h)

def shiftOp (h : HH δ) : (HH δ → B) →ₗ[B] (HH δ → B) := LinearMap.funLeft B B (fun x => x - h)

def diagOp (c : HH δ → B) : (HH δ → B) →ₗ[B] (HH δ → B) := LinearMap.mulLeft B c

@[simp] theorem shiftOp_apply (h : HH δ) (v : HH δ → B) (x : HH δ) : shiftOp δ B h v x = v (x - h) := rfl

@[simp] theorem diagOp_apply (c : HH δ → B) (v : HH δ → B) (x : HH δ) : diagOp δ B c v x = c x * v x := rfl

def schrod (z : Heis δ d) : (HH δ → B) →ₗ[B] (HH δ → B) :=
  omegaPow d B ω z.a • (shiftOp δ B z.h ∘ₗ diagOp δ B (thetaChar δ d B ω z.k))

omit [NeZero d] in
theorem schrod_apply (z : Heis δ d) (v : HH δ → B) (x : HH δ) :
    schrod δ d B ω z v x = omegaPow d B ω z.a * (thetaChar δ d B ω z.k (x - z.h) * v (x - z.h)) := by
  simp [schrod]

theorem schrod_mul (hω : ω ^ (2 * d) = 1) (z z' : Heis δ d) :
    schrod δ d B ω (z * z') = schrod δ d B ω z ∘ₗ schrod δ d B ω z' := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp only [LinearMap.comp_apply, schrod_apply, Heis.mul_a, Heis.mul_h, Heis.mul_k, thetaChar,
    pair_add_left]
  have hx : x - (z.h + z'.h) = x - z.h - z'.h := by abel
  rw [hx, show pair δ d z.k (x - z.h - z'.h) = pair δ d z.k (x - z.h) + -pair δ d z.k z'.h by
    rw [sub_eq_add_neg (x - z.h), pair_add_right, pair_neg_right]]
  simp only [omegaPow_add d B ω hω]

  have hcancel : omegaPow d B ω (pair δ d z.k z'.h) * omegaPow d B ω (-pair δ d z.k z'.h) = 1 := by
    rw [← omegaPow_add d B ω hω, add_neg_cancel, omegaPow_zero]

  set A := omegaPow d B ω z.a
  set A' := omegaPow d B ω z'.a
  set P := omegaPow d B ω (pair δ d z.k z'.h)
  set Q := omegaPow d B ω (-pair δ d z.k z'.h)
  set R1 := omegaPow d B ω (pair δ d z.k (x - z.h))
  set R2 := omegaPow d B ω (pair δ d z'.k (x - z.h - z'.h))
  set w := v (x - z.h - z'.h)
  calc A * A' * P * (R1 * Q * R2 * w) = (P * Q) * (A * (R1 * (A' * (R2 * w)))) := by ring
    _ = A * (R1 * (A' * (R2 * w))) := by rw [hcancel, one_mul]

omit [NeZero d] in
theorem schrod_one : schrod δ d B ω 1 = LinearMap.id := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp [schrod_apply, thetaChar, pair_zero_left, omegaPow_zero]

def schrodHom (hω : ω ^ (2 * d) = 1) : Heis δ d →* Module.End B (HH δ → B) where
  toFun := schrod δ d B ω
  map_one' := schrod_one δ d B ω
  map_mul' z z' := by rw [schrod_mul δ d B ω hω]; rfl

end Schrodinger

section Matrices

variable {g : ℕ} (δ : Fin g → ℕ) (d : ℕ) (B : Type) [CommRing B] (ω : B) {n : ℕ} (e : Fin n ≃ HH δ)

def schrodMat (z : Heis δ d) : Matrix (Fin n) (Fin n) B :=
  fun i j => if e i = e j + z.h then omegaPow d B ω (z.a + pair δ d z.k (e j)) else 0

theorem schrodMat_apply (z : Heis δ d) (i j : Fin n) :
    schrodMat δ d B ω e z i j = if e i = e j + z.h then omegaPow d B ω (z.a + pair δ d z.k (e j)) else 0 := rfl

def IsIntertwiner (γ : MulAut (Heis δ d)) (U : Matrix (Fin n) (Fin n) B) : Prop :=
  IsUnit U ∧ ∀ z : Heis δ d, U * schrodMat δ d B ω e z = schrodMat δ d B ω e (γ z) * U

def inter (γ : MulAut (Heis δ d)) : Matrix (Fin n) (Fin n) B := by
  classical
  exact if hU : ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U then hU.choose else 1

theorem isIntertwiner_inter (γ : MulAut (Heis δ d)) (hU : ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U) :
    IsIntertwiner δ d B ω e γ (inter δ d B ω e γ) := by
  classical
  rw [inter, dif_pos hU]
  exact hU.choose_spec

theorem inter_of_not_exists (γ : MulAut (Heis δ d)) (hU : ¬ ∃ U : Matrix (Fin n) (Fin n) B, IsIntertwiner δ d B ω e γ U) :
    inter δ d B ω e γ = 1 := by
  classical
  rw [inter, dif_neg hU]

end Matrices

end AlgebraicGeometry.ThetaLevel

end


