-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:59.970086+00:00
-- url     : https://prove2.me/theorems/93eea160-0b7d-4a0a-8182-9c5eb423b3b2
-- title:
--   Septic Character Injective
-- statement:
--   Definitions and structural lemmas for Septic Character Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/SepticCharacterInjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__8d4277abb339
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_face__944b82dcaa95
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_N_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex
def dbl {A U : Type} [CommGroup A] [CommGroup U] (θ : A → A → A → U) (σ : A → U) (x : A) : U := θ x x⁻¹ x / σ x
def mulq {A U : Type} [CommGroup A] [CommGroup U] (θ : A → A → A → U) (σ : A → U) (n : ℕ) (x : A) : U :=
  ∏ i ∈ Finset.range n, cubN θ i 1 x x / dbl θ σ x ^ i
theorem sym_of_mul {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (hθ : IsCub θ) {σ : A → U} (h1 : σ 1 = 1)
    (h : ∀ x y, σ (x * y) * θ x x⁻¹ y⁻¹ = σ x * σ y * θ y y⁻¹ x) :
    (∀ x, σ x * σ x⁻¹ = 1) ∧
      ∀ x y u, θ x⁻¹ y⁻¹ u⁻¹ * σ (x * y) * σ (x * u) * σ (y * u) = θ x y u * σ (x * y * u) * σ x * σ y * σ u := by
  refine ⟨fun x => ?_, fun x y u => ?_⟩
  · have := h x x⁻¹
    rw [mul_inv_cancel, h1, inv_inv, one_mul, hθ.s01 x⁻¹] at this
    exact (mul_eq_right.1 this.symm)
  · have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a := E (h (x * y) u); have b := E (h x u); have c := E (h y u)
    have d := hθ.compat x y u u⁻¹
    have k1 := hθ.coc x y (x * y)⁻¹ u⁻¹
    have k2 := hθ.coc y y⁻¹ x⁻¹ u⁻¹
    have r : ∀ z, θ u u⁻¹ z = θ z u u⁻¹ := fun z => by rw [hθ.s12, hθ.s01]
    rw [mul_inv_cancel, hθ.face₃] at d
    rw [show y * (x * y)⁻¹ = x⁻¹ by rw [mul_inv, mul_comm x⁻¹, mul_inv_cancel_left]] at k1
    rw [mul_inv_cancel, hθ.face, mul_comm y⁻¹, ← mul_inv, hθ.s01 y⁻¹] at k2
    have d := E d; have k1 := E k1; have k2 := E k2
    apply Additive.ofMul.injective
    simp only [r, ofMul_mul, ofMul_one] at a b c d k1 k2 ⊢
    linear_combination (norm := abel) b + c - a - d + k1 - k2
structure NumB (O : Type) [CommRing O] where
  A : Type
  [grp : CommGroup A]
  θ : A → A → A → Oˣ
  cub : IsCub θ
  σ : A → Oˣ
  σ_one : σ 1 = 1
  σ_mul : ∀ x y, σ (x * y) * θ x x⁻¹ y⁻¹ = σ x * σ y * θ y y⁻¹ x
  σ_inv : ∀ x, σ x * σ x⁻¹ = 1 := (sym_of_mul cub σ_one σ_mul).1
  σ_cub : ∀ x y u, θ x⁻¹ y⁻¹ u⁻¹ * σ (x * y) * σ (x * u) * σ (y * u) = θ x y u * σ (x * y * u) * σ x * σ y * σ u :=
    (sym_of_mul cub σ_one σ_mul).2
  th : A → O
attribute [instance] NumB.grp
structure NumD (O : Type) [CommRing O] extends NumB O where
  X : Type
  [add : AddCommGroup X]
  [free : Module.Free ℤ X]
  [fin : Module.Finite ℤ X]
  c : X → A
  c_add : ∀ a b, c (a + b) = c a * c b
  ψ : X → Oˣ
  even : ∀ χ, ψ (-χ) * σ (c χ) = ψ χ
  bimult : ∀ a a' b, ψ (a + a' + b) / ψ (a + a') / ψ b * θ (c a) (c a') (c b) =
    (ψ (a + b) / ψ a / ψ b) * (ψ (a' + b) / ψ a' / ψ b)
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
namespace NumB
variable (B : NumB O)
def weil (k : ℕ) (b b' : B.A) : Oˣ := cubN B.θ k 1 b' b / cubN B.θ k 1 b b'
def uV (k : ℕ) (a b x : B.A) : Oˣ := cubN B.θ k a b x / B.θ a x b
def wS (k : ℕ) (b : B.A) (ψy yg : Oˣ) : Oˣ :=
  ψy * mulq B.θ B.σ k b / (yg * cubN B.θ k 1 b b / dbl B.θ B.σ b ^ k) ^ ((k - 1) / 2)
def mth (m : ℕ) (x : B.A) : O := B.th (x ^ m) * ((mulq B.θ B.σ m x)⁻¹ : Oˣ)
def uth (m : ℕ) (b x : B.A) : O := (B.uV (m ^ 2) 1 b x * B.wS (m ^ 2) b 1 1 : Oˣ) * B.mth m (x * b)
structure Iso (B' B : NumB O) where
  φ : B'.A ≃* B.A
  h : B'.A → Oˣ
  h_one : h 1 = 1
  θ_eq : ∀ x y u, B.θ (φ x) (φ y) (φ u) * h (x * y) * h (x * u) * h (y * u) = B'.θ x y u * h (x * y * u) * h x * h y * h u
  σ_eq : ∀ x, B.σ (φ x) * h x = B'.σ x * h x⁻¹
  lam : Oˣ
  th_eq : ∀ x, B.th (φ x) = (lam * h x : Oˣ) * B'.th x
end NumB
namespace NumD
variable (N : NumD O)
def τ (a b : N.X) : Oˣ := N.ψ (a + b) / N.ψ a / N.ψ b
@[simp] theorem c_zero : N.c 0 = 1 := by
  have := N.c_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm
theorem c_neg (a : N.X) : N.c (-a) = (N.c a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← N.c_add, neg_add_cancel, N.c_zero])
theorem τ_symm (a b : N.X) : N.τ a b = N.τ b a := by
  simp only [τ, add_comm a b, div_right_comm]
theorem τ_add_left (a a' b : N.X) :
    N.τ (a + a') b * N.θ (N.c a) (N.c a') (N.c b) = N.τ a b * N.τ a' b := N.bimult a a' b
theorem τ_add_right (a b b' : N.X) :
    N.τ a (b + b') * N.θ (N.c b) (N.c b') (N.c a) = N.τ a b * N.τ a b' := by
  rw [N.τ_symm a, N.τ_symm a, N.τ_symm a, N.τ_add_left]
@[simp] theorem τ_zero_left (b : N.X) : N.τ 0 b = 1 := by
  have := N.τ_add_left 0 0 b
  rw [add_zero, N.c_zero, N.cub.face, mul_one] at this
  exact mul_eq_left.1 this.symm
@[simp] theorem τ_zero_right (a : N.X) : N.τ a 0 = 1 := by rw [N.τ_symm, N.τ_zero_left]
@[simp] theorem ψ_zero : N.ψ 0 = 1 := by
  have := N.τ_zero_left 0
  simpa [τ] using this
@[ext] structure Gt where
  b : N.A
  s : N.X → Oˣ
  mult : ∀ χ χ', s (χ + χ') * N.θ (N.c χ) (N.c χ') b = s χ * s χ'
instance : CommGroup N.Gt where
  mul g g' := ⟨g.b * g'.b, fun χ => g.s χ * g'.s χ / N.θ (N.c χ) g.b g'.b, fun χ χ' => by
    have a := congrArg Additive.ofMul (N.cub.compat (N.c χ) (N.c χ') g.b g'.b)
    have b := congrArg Additive.ofMul (g.mult χ χ')
    have c := congrArg Additive.ofMul (g'.mult χ χ')
    rw [N.c_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a b c ⊢
    linear_combination (norm := abel) b + c - a⟩
  one := ⟨1, fun _ => 1, fun χ χ' => by rw [N.cub.face₃]⟩
  inv g := ⟨g.b⁻¹, fun χ => N.θ (N.c χ) g.b g.b⁻¹ / g.s χ, fun χ χ' => by
    have a := N.cub.compat (N.c χ) (N.c χ') g.b g.b⁻¹
    rw [mul_inv_cancel, N.cub.face₃, one_mul] at a
    replace a := congrArg Additive.ofMul a
    have b := congrArg Additive.ofMul (g.mult χ χ')
    rw [N.c_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a b ⊢
    linear_combination (norm := abel) a - b⟩
  mul_assoc g g' g'' := by
    refine Gt.ext (mul_assoc g.b g'.b g''.b) (funext fun χ => ?_)
    change g.s χ * g'.s χ / N.θ (N.c χ) g.b g'.b * g''.s χ / N.θ (N.c χ) (g.b * g'.b) g''.b =
      g.s χ * (g'.s χ * g''.s χ / N.θ (N.c χ) g'.b g''.b) / N.θ (N.c χ) g.b (g'.b * g''.b)
    have r : ∀ x y, N.θ x y (N.c χ) = N.θ (N.c χ) x y := fun x y => by rw [N.cub.s12, N.cub.s01]
    have a := N.cub.coc g.b g'.b g''.b (N.c χ)
    simp only [r] at a
    replace a := congrArg Additive.ofMul a
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a ⊢
    linear_combination (norm := abel) -a
  one_mul g := by
    refine Gt.ext (one_mul g.b) (funext fun χ => ?_)
    change 1 * g.s χ / N.θ (N.c χ) 1 g.b = g.s χ
    rw [N.cub.face₂, one_mul, div_one]
  mul_one g := by
    refine Gt.ext (mul_one g.b) (funext fun χ => ?_)
    change g.s χ * 1 / N.θ (N.c χ) g.b 1 = g.s χ
    rw [N.cub.face₃, mul_one, div_one]
  inv_mul_cancel g := by
    refine Gt.ext (inv_mul_cancel g.b) (funext fun χ => ?_)
    change N.θ (N.c χ) g.b g.b⁻¹ / g.s χ * g.s χ / N.θ (N.c χ) g.b⁻¹ g.b = 1
    rw [div_mul_cancel, N.cub.s12, div_self']
  mul_comm g g' := by
    refine Gt.ext (mul_comm g.b g'.b) (funext fun χ => ?_)
    change g.s χ * g'.s χ / N.θ (N.c χ) g.b g'.b = g'.s χ * g.s χ / N.θ (N.c χ) g'.b g.b
    rw [N.cub.s12, mul_comm]
namespace Gt
variable {N}
@[simp] theorem mul_b (g g' : N.Gt) : (g * g').b = g.b * g'.b := rfl
theorem mul_s (g g' : N.Gt) (χ : N.X) : (g * g').s χ = g.s χ * g'.s χ / N.θ (N.c χ) g.b g'.b := rfl
@[simp] theorem one_b : (1 : N.Gt).b = 1 := rfl
@[simp] theorem generator_inv_base (χ : N.X) : (1 : N.Gt).s χ = 1 := rfl
@[simp] theorem inv_b (g : N.Gt) : g⁻¹.b = g.b⁻¹ := rfl
@[simp] theorem s_zero (g : N.Gt) : g.s 0 = 1 := by
  have := g.mult 0 0
  rw [add_zero, N.c_zero, N.cub.face, mul_one] at this
  exact mul_eq_left.1 this.symm
@[simp] theorem pow_b (g : N.Gt) (k : ℕ) : (g ^ k).b = g.b ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, mul_b, ih]
end Gt
def projB : N.Gt →* N.A where
  toFun g := g.b
  map_one' := rfl
  map_mul' _ _ := rfl
@[simp] theorem projB_apply (g : N.Gt) : N.projB g = g.b := rfl
def io (y : N.X) : N.Gt := ⟨N.c y, fun χ => N.τ y χ, fun χ χ' => N.τ_add_right y χ χ'⟩
@[simp] theorem io_b (y : N.X) : (N.io y).b = N.c y := rfl
@[simp] theorem io_s (y χ : N.X) : (N.io y).s χ = N.τ y χ := rfl
theorem io_add (a b : N.X) : N.io (a + b) = N.io a * N.io b := by
  refine Gt.ext (N.c_add a b) (funext fun χ => ?_)
  rw [Gt.mul_s, io_s, io_s, io_s, io_b, io_b, ← N.τ_add_left, N.cub.s12 (N.c a), N.cub.s01 (N.c a),
    mul_div_cancel_right]
def ioHom : Multiplicative N.X →* N.Gt :=
  MonoidHom.mk' (fun y => N.io y.toAdd) fun a b => N.io_add a.toAdd b.toAdd
@[simp] theorem ioHom_apply (y : Multiplicative N.X) : N.ioHom y = N.io y.toAdd := rfl
@[simp] theorem io_zero : N.io 0 = 1 := N.ioHom.map_one
theorem io_neg (a : N.X) : N.io (-a) = (N.io a)⁻¹ := N.ioHom.map_inv (Multiplicative.ofAdd a)
theorem io_nsmul (k : ℕ) (a : N.X) : N.io (k • a) = N.io a ^ k := N.ioHom.map_pow (Multiplicative.ofAdd a) k
def tor (t : Multiplicative N.X →* Oˣ) : N.Gt := ⟨1, fun χ => t (Multiplicative.ofAdd χ), fun χ χ' => by
  rw [N.cub.face₃, mul_one, ofAdd_add, map_mul]⟩
@[simp] theorem tor_b (t : Multiplicative N.X →* Oˣ) : (N.tor t).b = 1 := rfl
@[simp] theorem torus_generator_apply (t : Multiplicative N.X →* Oˣ) (χ : N.X) : (N.tor t).s χ = t (Multiplicative.ofAdd χ) := rfl
theorem tor_mul (t t' : Multiplicative N.X →* Oˣ) : N.tor (t * t') = N.tor t * N.tor t' := by
  refine Gt.ext (mul_one (1 : N.A)).symm (funext fun χ => ?_)
  rw [Gt.mul_s, tor_b, tor_b, N.cub.face₃, div_one]
  rfl
def torHom : (Multiplicative N.X →* Oˣ) →* N.Gt := MonoidHom.mk' N.tor N.tor_mul
@[simp] theorem torHom_apply (t : Multiplicative N.X →* Oˣ) : N.torHom t = N.tor t := rfl
@[simp] theorem tor_one : N.tor 1 = 1 := N.torHom.map_one
theorem tor_pow (t : Multiplicative N.X →* Oˣ) (k : ℕ) : N.tor (t ^ k) = N.tor t ^ k := N.torHom.map_pow t k
def QT (k : ℕ) : Subgroup (Multiplicative N.X × N.Gt) where
  carrier := {p | p.2 ^ k = N.io p.1.toAdd}
  mul_mem' {p p'} h h' := by
    change (p.2 * p'.2) ^ k = N.io (p.1.toAdd + p'.1.toAdd)
    rw [mul_pow, N.io_add, (show p.2 ^ k = _ from h), (show p'.2 ^ k = _ from h')]
  one_mem' := by
    change (1 : N.Gt) ^ k = N.io 0
    rw [one_pow, N.io_zero]
  inv_mem' {p} h := by
    change p.2⁻¹ ^ k = N.io (-p.1.toAdd)
    rw [inv_pow, N.io_neg, (show p.2 ^ k = _ from h)]
theorem mem_QT {k : ℕ} {p : Multiplicative N.X × N.Gt} : p ∈ N.QT k ↔ p.2 ^ k = N.io p.1.toAdd := Iff.rfl
def qTriv (k : ℕ) (z : N.X) : N.QT k := ⟨(Multiplicative.ofAdd (k • z), N.io z), (N.io_nsmul k z).symm⟩
def qTor {k : ℕ} (t : Multiplicative N.X →* Oˣ) (ht : t ^ k = 1) : N.QT k :=
  ⟨(1, N.tor t), by rw [mem_QT, ← N.tor_pow, ht, N.tor_one]; exact N.io_zero.symm⟩
def QEq {k : ℕ} (p p' : N.QT k) : Prop :=
  ∃ z : N.X, p'.1.1.toAdd = p.1.1.toAdd + k • z ∧ p'.1.2 = p.1.2 * N.io z
def tk {k : ℕ} (p p' : N.QT k) : Oˣ := p.1.2.s p'.1.1.toAdd * cubN N.θ k 1 p'.1.2.b p.1.2.b
def wp {k : ℕ} (p p' : N.QT k) : Oˣ := N.tk p p' / N.tk p' p
theorem wp_qTor {k : ℕ} (t : Multiplicative N.X →* Oˣ) (ht : t ^ k = 1) (p' : N.QT k) :
    N.wp (N.qTor t ht) p' = t p'.1.1 := by
  have a : cubN N.θ k 1 1 p'.1.2.b = 1 := Finset.prod_eq_one fun _ _ => N.cub.face₂ _ _
  change t p'.1.1 * cubN N.θ k 1 p'.1.2.b 1 / (p'.1.2.s 0 * cubN N.θ k 1 1 p'.1.2.b) = _
  rw [a, N.cub.N_one, Gt.s_zero, mul_one, mul_one, div_one]
def wQ {k : ℕ} (p : N.QT k) : Oˣ := N.wS k p.1.2.b (N.ψ p.1.1.toAdd) (p.1.2.s p.1.1.toAdd)
def vt (g : N.Gt) (χ : N.X) : O := (N.ψ χ * g.s χ : Oˣ) * N.th (N.c χ * g.b)
def txT (m : ℕ) (p : N.QT (m ^ 2)) (χ : N.X) : O :=
  (N.wQ p / mulq N.θ N.σ m p.1.2.b : Oˣ) * N.vt (p.1.2 ^ m) χ
def tx [TopologicalSpace O] (m : ℕ) (p : N.QT (m ^ 2)) : O := ∑' χ, N.txT m p χ
def FE (k : ℕ) (s : N.X → N.A → O) : Prop :=
  ∀ μ α x, s (α + k • μ) x = (N.uV k (N.c α) (N.c μ) x * N.ψ μ ^ k * N.τ μ α : Oˣ) * s α (x * N.c μ)
def phi {k : ℕ} (p : N.QT k) (w : Oˣ) (s : N.X → N.A → O) : N.X → N.A → O := fun α x =>
  (N.uV k (N.c (α - p.1.1.toAdd)) p.1.2.b x * p.1.2.s (α - p.1.1.toAdd) * w : Oˣ) * s (α - p.1.1.toAdd) (x * p.1.2.b)
def vth : N.X → N.A → O := fun α x => (N.ψ α : O) * N.th (x * N.c α)
structure Iso (N' N : NumD O) extends NumB.Iso N'.toNumB N.toNumB where
  e : N'.X ≃+ N.X
  c_eq : ∀ χ, N.c (e χ) = φ (N'.c χ)
  ψ_eq : ∀ χ, N.ψ (e χ) * h (N'.c χ) = N'.ψ χ
def Iso.Rel {N' N : NumD O} (I : Iso N' N) (g' : N'.Gt) (g : N.Gt) : Prop :=
  g.b = I.φ g'.b ∧ ∀ χ, g.s (I.e χ) * I.h (N'.c χ * g'.b) = g'.s χ * I.h (N'.c χ) * I.h g'.b
end NumD
structure NumD.Int {C : Type} [NormedField C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ) : Prop where
  θ : ∀ x y u, ‖(N.θ x y u : C)‖ = 1
  σ : ∀ x, ‖(N.σ x : C)‖ = 1
  th : ∀ x, ‖N.th x‖ ≤ 1
  ψ : ∀ χ, ‖(N.ψ χ : C)‖ = Real.exp (-q χ)
  pos : Filter.Tendsto q Filter.cofinite Filter.atTop
structure NumB.Tors {C : Type} [NormedField C] (B : NumB C) (n g : ℕ) : Prop where
  div : ∀ x : B.A, ∃ y, y ^ n = x
  str : ∀ j : ℕ, Nonempty ((powMonoidHom (n ^ j) : B.A →* B.A).ker ≃* Multiplicative (Fin (2 * g) → ZMod (n ^ j)))
  nondeg : ∀ (j : ℕ) (b : B.A), b ^ n ^ j = 1 → (∀ b', b' ^ n ^ j = 1 → B.weil (n ^ j) b b' = 1) → b = 1
  good : ∀ a : B.A, ∃ t, t ^ n = 1 ∧ ‖B.th (a * t)‖ = 1
  sep : ∀ (j : ℕ), 1 ≤ j → ∀ (x x' : B.A) (l : C), l ≠ 0 →
    (∀ b, b ^ (n ^ j) ^ 2 = 1 → B.uth (n ^ j) b x = l * B.uth (n ^ j) b x') → x = x'
namespace NumB
def regauge (B : NumB O) (h : B.A → Oˣ) (h₁ : h 1 = 1) : NumB O where
  A := B.A
  θ x y u := B.θ x y u * h (x * y) * h (x * u) * h (y * u) / (h (x * y * u) * h x * h y * h u)
  cub :=
    { face := fun x y => by
        apply Additive.ofMul.injective
        simp only [B.cub.face, one_mul, h₁, ofMul_mul, ofMul_div, ofMul_one]
        abel
      s01 := fun x y z => by
        apply Additive.ofMul.injective
        simp only [B.cub.s01 x y z, mul_comm y x, ofMul_mul, ofMul_div]
        abel
      s12 := fun x y z => by
        apply Additive.ofMul.injective
        simp only [B.cub.s12 x y z, mul_comm z y, mul_right_comm x z y, ofMul_mul, ofMul_div]
        abel
      coc := fun x x' x'' y => by
        have a := congrArg Additive.ofMul (B.cub.coc x x' x'' y)
        apply Additive.ofMul.injective
        simp only [← mul_assoc x, ← mul_assoc (x * x'), ofMul_mul, ofMul_div] at a ⊢
        linear_combination (norm := abel) a }
  σ x := B.σ x * h x / h x⁻¹
  σ_one := by rw [B.σ_one, inv_one, one_mul, div_self']
  σ_mul x y := by
    have a := congrArg Additive.ofMul (B.σ_mul x y)
    apply Additive.ofMul.injective
    simp only [mul_inv_cancel, one_mul, h₁, mul_inv, mul_comm y x, mul_comm y⁻¹ x, ofMul_mul, ofMul_div, ofMul_one] at a ⊢
    linear_combination (norm := abel) a
  th x := ((h x)⁻¹ : Oˣ) * B.th x
def regaugeIso (B : NumB O) (h : B.A → Oˣ) (h₁ : h 1 = 1) : Iso (B.regauge h h₁) B where
  φ := MulEquiv.refl B.A
  h := h
  h_one := h₁
  θ_eq (x y u : B.A) := by
    change B.θ x y u * h (x * y) * h (x * u) * h (y * u) =
      B.θ x y u * h (x * y) * h (x * u) * h (y * u) / (h (x * y * u) * h x * h y * h u) * h (x * y * u) * h x * h y * h u
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  σ_eq (x : B.A) := (div_mul_cancel _ _).symm
  lam := 1
  th_eq (x : B.A) := by
    change B.th x = ((1 * h x : Oˣ) : O) * (((h x)⁻¹ : Oˣ) * B.th x)
    rw [one_mul, Units.mul_inv_cancel_left]
def triv (A : Type) [CommGroup A] (f : A → O) : NumB O where
  A := A
  θ _ _ _ := 1
  cub := ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  σ _ := 1
  σ_one := rfl
  σ_mul _ _ := by simp
  th := f
end NumB
namespace NumD
def regauge (N : NumD O) (h : N.A → Oˣ) (h₁ : h 1 = 1) : NumD O where
  toNumB := N.toNumB.regauge h h₁
  X := N.X
  c := N.c
  c_add := N.c_add
  ψ χ := N.ψ χ * h (N.c χ)
  even χ := by
    change N.ψ (-χ) * h (N.c (-χ)) * (N.σ (N.c χ) * h (N.c χ) / h (N.c χ)⁻¹) = N.ψ χ * h (N.c χ)
    have a := congrArg Additive.ofMul (N.even χ)
    apply Additive.ofMul.injective
    simp only [N.c_neg, ofMul_mul, ofMul_div] at a ⊢
    linear_combination (norm := abel) a
  bimult a a' b := by
    change _ * (N.θ (N.c a) (N.c a') (N.c b) * h (N.c a * N.c a') * h (N.c a * N.c b) * h (N.c a' * N.c b) /
      (h (N.c a * N.c a' * N.c b) * h (N.c a) * h (N.c a') * h (N.c b))) = _
    have e := congrArg Additive.ofMul (N.bimult a a' b)
    apply Additive.ofMul.injective
    simp only [N.c_add, ofMul_mul, ofMul_div] at e ⊢
    linear_combination (norm := abel) e
def regaugeIso (N : NumD O) (h : N.A → Oˣ) (h₁ : h 1 = 1) : Iso (N.regauge h h₁) N where
  toIso := N.toNumB.regaugeIso h h₁
  e := AddEquiv.refl N.X
  c_eq _ := rfl
  ψ_eq _ := rfl
end NumD
def tate (q : Oˣ) : NumD O where
  toNumB := NumB.triv PUnit fun _ => 1
  X := ℤ
  c _ := 1
  c_add _ _ := rfl
  ψ n := q ^ n ^ 2
  even n := by
    change q ^ (-n) ^ 2 * 1 = _
    rw [neg_sq, mul_one]
  bimult a a' b := by
    change _ * 1 = _
    simp only [mul_one, div_eq_mul_inv, ← zpow_neg, ← zpow_add]
    congr 1
    ring
theorem tate_τ (q : Oˣ) (a b : ℤ) : (tate q).τ a b = q ^ (2 * a * b) := by
  change q ^ (a + b) ^ 2 / q ^ a ^ 2 / q ^ b ^ 2 = _
  simp only [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
  congr 1
  ring
def tateQ (r : Oˣ) (k : ℕ) (y : ℤ) : (tate (r ^ k)).QT k :=
  ⟨(Multiplicative.ofAdd y, (tate (r ^ k)).tor (zpowersHom Oˣ (r ^ (2 * y)))), by
    refine ((tate (r ^ k)).tor_pow _ k).symm.trans ?_
    refine NumD.Gt.ext rfl (funext fun (χ : ℤ) => ?_)
    refine Eq.trans ?_ (tate_τ (r ^ k) y χ).symm
    change ((r ^ (2 * y)) ^ χ) ^ k = _
    simp only [← zpow_natCast, ← zpow_mul]
    congr 1
    ring⟩
def tateForm {C : Type} [NormedField C] (q : Cˣ) : QuadraticMap ℤ ℤ ℝ :=
  (LinearMap.toSpanSingleton ℤ ℝ (-Real.log ‖(q : C)‖)).compQuadraticMap QuadraticMap.sq
namespace Level3
abbrev A₃ := Multiplicative (ZMod 3 × ZMod 3)
def carry (a : ℕ) : ZMod 3 := ((a / 3 : ℕ) : ZMod 3)
def cube (x y u : A₃) : Multiplicative (ZMod 3) := Multiplicative.ofAdd
  (- carry (x.toAdd.1.val + y.toAdd.1.val + u.toAdd.1.val) * (x.toAdd.2 + y.toAdd.2 + u.toAdd.2)
    + carry (x.toAdd.1.val + y.toAdd.1.val) * (x.toAdd.2 + y.toAdd.2)
    + carry (x.toAdd.1.val + u.toAdd.1.val) * (x.toAdd.2 + u.toAdd.2)
    + carry (y.toAdd.1.val + u.toAdd.1.val) * (y.toAdd.2 + u.toAdd.2))
def sym (x : A₃) : Multiplicative (ZMod 3) :=
  Multiplicative.ofAdd (- carry (x.toAdd.1.val + (-x.toAdd.1).val) * x.toAdd.2)
theorem isCub_cube : IsCub cube := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem sym_one : sym 1 = 1 := by decide +kernel
theorem sym_mul : ∀ x y, sym (x * y) * cube x x⁻¹ y⁻¹ = sym x * sym y * cube y y⁻¹ x := by decide +kernel
def bun (f : Multiplicative (ZMod 3) →* Oˣ) (s : A₃ → O) : NumB O where
  A := A₃
  θ x y u := f (cube x y u)
  cub := ⟨fun x y => by rw [isCub_cube.face, map_one], fun x y z => by rw [isCub_cube.s01],
    fun x y z => by rw [isCub_cube.s12], fun x x' x'' y => by rw [← map_mul, ← map_mul, isCub_cube.coc]⟩
  σ x := f (sym x)
  σ_one := by rw [sym_one, map_one]
  σ_mul x y := by rw [← map_mul, sym_mul, map_mul, map_mul]
  th := s
def pt (n : ℤ) : A₃ := Multiplicative.ofAdd ((n : ZMod 3), (0 : ZMod 3))
def dat (f : Multiplicative (ZMod 3) →* Oˣ) (s : A₃ → O) (q : Oˣ) : NumD O where
  toNumB := bun f s
  X := ℤ
  c := pt
  c_add a b := by
    change pt (a + b) = pt a * pt b
    simp only [pt, ← ofAdd_add, Prod.mk_add_mk, add_zero, Int.cast_add]
  ψ n := q ^ n ^ 2
  even n := by
    have e : sym (pt n) = 1 := by simp [sym, pt]
    change q ^ (-n) ^ 2 * f (sym (pt n)) = _
    rw [e, map_one, neg_sq, mul_one]
  bimult a a' b := by
    have e : cube (pt a) (pt a') (pt b) = 1 := by simp [cube, pt]
    change _ * f (cube (pt a) (pt a') (pt b)) = _
    rw [e, map_one]
    simp only [mul_one, div_eq_mul_inv, ← zpow_neg, ← zpow_add]
    congr 1
    ring
def chi7 : Multiplicative (ZMod 3) →* (ZMod 7)ˣ :=
  MonoidHom.mk' (fun a => (⟨2, 4, by decide, by decide⟩ : (ZMod 7)ˣ) ^ a.toAdd.val) (by decide +kernel)
end Level3
example (r ζ : Oˣ) (k : ℕ) (hζ : zpowersHom Oˣ ζ ^ k = 1) (y : ℤ) :
    (tate (r ^ k)).wp ((tate (r ^ k)).qTor (zpowersHom Oˣ ζ) hζ) (tateQ r k y) = ζ ^ y :=
  NumD.wp_qTor _ _ _ _
example (A : Type) [CommGroup A] (f : A → O) (h : A → Oˣ) (h₁ : h 1 = 1) (x : A) :
    dbl ((NumB.triv A f).regauge h h₁).θ ((NumB.triv A f).regauge h h₁).σ x = h (x * x) / h x ^ 4 := by
  change 1 * h (x * x⁻¹) * h (x * x) * h (x⁻¹ * x) / (h (x * x⁻¹ * x) * h x * h x⁻¹ * h x) / (1 * h x / h x⁻¹) = _
  apply Additive.ofMul.injective
  simp only [mul_inv_cancel, inv_mul_cancel, one_mul, h₁, ofMul_mul, ofMul_div, ofMul_one, ofMul_pow]
  abel
example (q : Oˣ) : ((tate q).io (1 : ℤ)).s (1 : ℤ) = q ^ (2 : ℤ) := tate_τ q 1 1
end GlobalTheory.Ex
end


