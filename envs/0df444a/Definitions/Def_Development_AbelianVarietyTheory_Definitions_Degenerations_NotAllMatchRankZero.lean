-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:37.309358+00:00
-- url     : https://prove2.me/theorems/91674392-46a6-45c2-8fd4-2a392beef752
-- title:
--   Not All Match Rank Zero
-- statement:
--   Definitions and structural lemmas for Not All Match Rank Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Theorems.Thm_GlobalTheory_Ex_NumD_Gt_pow_s
import Theorems.Thm_GlobalTheory_Ex_NumD_qEq_equivalence
import Theorems.Thm_GlobalTheory_Ex_NumD_wp_swap

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
variable {O : Type} [CommRing O]
namespace NumD
variable (N : NumD O)
structure Form (k : ℕ) where
  be : LinearMap.BilinForm ℤ N.X
  symm : ∀ y z, be y z = be z y
  pos : ∀ y, y ≠ 0 → 0 < be y y
  dvd : ∀ y z, (2 * k : ℤ) ∣ be y z
open scoped BigOperators in
variable {O : Type} [CommRing O] in
variable (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.NumD.Form.half_add {N : _root_.GlobalTheory.Ex.NumD O} {k : ℕ}
    (β : N.Form k) (x y : N.X) :
    β.be (x + y) (x + y) / 2 =
      β.be x x / 2 + β.be y y / 2 +
        β.be x y := by
  have hsum : β.be (x + y) (x + y) = β.be x x +
      β.be y y + 2 * β.be x y := by
    simp only [map_add, LinearMap.add_apply, β.symm y x]
    ring
  have hx : (2 : ℤ) ∣ β.be x x :=
    dvd_trans (dvd_mul_right 2 (k : ℤ)) (β.dvd x x)
  have hy : (2 : ℤ) ∣ β.be y y :=
    dvd_trans (dvd_mul_right 2 (k : ℤ)) (β.dvd y y)
  omega
open scoped BigOperators in
variable {O : Type} [CommRing O] in
variable (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.NumD.Form.div_mul {N : _root_.GlobalTheory.Ex.NumD O}
    {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k)
    (x y : N.X) :
    β.be x y / j * j = β.be x y :=
  Int.ediv_mul_cancel (dvd_trans (Int.natCast_dvd_natCast.2 hj)
    (dvd_trans (dvd_mul_left (k : ℤ) 2) (β.dvd x y)))
open scoped BigOperators in
variable {O : Type} [CommRing O] in
variable (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.NumD.Form.div_add {N : _root_.GlobalTheory.Ex.NumD O} {k : ℕ}
    (β : N.Form k) {j : ℕ} (hj : j ∣ k)
    (x y z : N.X) :
    β.be x (y + z) / j =
      β.be x y / j + β.be x z / j := by
  rw [map_add]
  exact Int.add_ediv_of_dvd_left (dvd_trans (Int.natCast_dvd_natCast.2 hj)
    (dvd_trans (dvd_mul_left (k : ℤ) 2) (β.dvd x y)))
def twist {k : ℕ} (β : N.Form k) (u : Oˣ) : NumD O :=
  { N with ψ := fun χ => N.ψ χ * u ^ (β.be χ χ / 2)
           even := fun χ => by
             simp only [map_neg, LinearMap.neg_apply, neg_neg]
             rw [← N.even χ]; exact mul_right_comm _ _ _
           bimult := fun a a' b => by
             have h := N.bimult a a' b
             have e : ∀ x y : N.X, N.ψ (x + y) * u ^ (β.be (x + y) (x + y) / 2) / (N.ψ x * u ^ (β.be x x / 2)) /
                 (N.ψ y * u ^ (β.be y y / 2)) = N.ψ (x + y) / N.ψ x / N.ψ y * u ^ β.be x y := fun x y => by
               rw [β.half_add, zpow_add, zpow_add]
               apply Additive.ofMul.injective
               simp only [ofMul_mul, ofMul_div]; abel
             rw [e, e, e, mul_right_comm, h, map_add, LinearMap.add_apply, zpow_add]
             exact mul_mul_mul_comm _ _ _ _ }
open scoped BigOperators in
variable {O : Type} [CommRing O] in
variable (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.NumD.twist_τ {k : ℕ} (β : N.Form k) (u : Oˣ)
    (x y : N.X) :
    (N.twist β u).τ x y =
      N.τ x y * u ^ β.be x y := by
  show N.ψ (x + y) * u ^ (β.be (x + y) (x + y) / 2) /
      (N.ψ x * u ^ (β.be x x / 2)) /
      (N.ψ y * u ^ (β.be y y / 2)) =
    N.ψ (x + y) / N.ψ x / N.ψ y *
      u ^ β.be x y
  rw [β.half_add, zpow_add, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel
def twG {k : ℕ} (β : N.Form k) (u : Oˣ) (g : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b) : (N.twist β u).Gt :=
  ⟨g.b, fun z => g.s z * u ^ l z, fun (χ χ' : N.X) => by
    show g.s (χ + χ') * u ^ l (χ + χ') * N.θ (N.c χ) (N.c χ') g.b = g.s χ * u ^ l χ * (g.s χ' * u ^ l χ')
    rw [mul_right_comm, g.mult, hl, zpow_add]; exact mul_mul_mul_comm _ _ _ _⟩
open scoped BigOperators in
variable {O : Type} [CommRing O] in
variable (N : _root_.GlobalTheory.Ex.NumD O) in

theorem _root_.GlobalTheory.Ex.NumD.twG_pow {k : ℕ} (β : N.Form k) (u : Oˣ)
    (g : N.Gt) (l : N.X → ℤ)
    (hl : ∀ a b, l (a + b) = l a + l b) (n : ℕ) :
    (N.twG β u g l hl ^ n).b =
        (g ^ n).b ∧
      ∀ z : N.X,
        (N.twG β u g l hl ^ n).s z = (g ^ n).s z * u ^ (l z * n) := by
  have hθ : ∀ a b c, (N.twist β u).θ a b c = N.θ a b c :=
    fun _ _ _ => rfl
  have hc : ∀ χ, (N.twist β u).c χ = N.c χ :=
    fun _ => rfl
  have hb : (N.twG β u g l hl).b =
      g.b := rfl
  have hs : ∀ z, (N.twG β u g l hl).s z = g.s z * u ^ l z := fun _ => rfl
  induction n with
  | zero =>
    refine ⟨?_, fun z => ?_⟩
    · rw [pow_zero, pow_zero, _root_.GlobalTheory.Ex.NumD.Gt.one_b (N := N.twist β u),
        _root_.GlobalTheory.Ex.NumD.Gt.one_b (N := N)]
      rfl
    · rw [pow_zero, pow_zero]
      refine (_root_.GlobalTheory.Ex.NumD.Gt.generator_inv_base (N := N.twist β u) z).trans ?_
      rw [_root_.GlobalTheory.Ex.NumD.Gt.generator_inv_base (N := N)]
      simp
  | succ n ih =>
    refine ⟨?_, fun z => ?_⟩
    · rw [pow_succ, pow_succ, _root_.GlobalTheory.Ex.NumD.Gt.mul_b (N := N.twist β u),
        _root_.GlobalTheory.Ex.NumD.Gt.mul_b (N := N), ih.1, hb]
      rfl
    · rw [pow_succ, pow_succ]
      refine (_root_.GlobalTheory.Ex.NumD.Gt.mul_s (N := N.twist β u)
        (N.twG β u g l hl ^ n) (N.twG β u g l hl)
        z).trans ?_
      rw [_root_.GlobalTheory.Ex.NumD.Gt.mul_s (N := N), hθ]
      erw [hc, ih.1, ih.2 z, hb, hs]
      push_cast
      rw [mul_add, mul_one, zpow_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div]; abel
def twQ {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (p : N.QT j) : (N.twist β u).QT j :=
  ⟨(p.1.1, N.twG β u p.1.2 (fun z => β.be p.1.1.toAdd z / j) (β.div_add hj _)), by
    have h : p.1.2 ^ j = N.io p.1.1.toAdd := p.2
    have h' := N.twG_pow β u p.1.2 (fun z => β.be p.1.1.toAdd z / j) (β.div_add hj _) j
    refine NumD.Gt.ext (h'.1.trans (by rw [h]; rfl)) (funext fun (z : N.X) => (h'.2 z).trans ?_)
    rw [h, β.div_mul hj]; exact (N.twist_τ β u _ z).symm⟩
def evT (m : ℕ) (p : N.QT (m ^ 2)) (h : N.Gt) (χ : N.X) : O :=
  (h.s p.1.1.toAdd * cubN N.θ (m ^ 2) 1 p.1.2.b h.b * N.wQ p / mulq N.θ N.σ m (h.b * p.1.2.b) : Oˣ) *
    N.vt ((h * p.1.2) ^ m) χ
def ev [TopologicalSpace O] (m : ℕ) (p : N.QT (m ^ 2)) (h : N.Gt) : O := ∑' χ, N.evT m p h χ
def arcTx (be : LinearMap.BilinForm ℤ N.X) (m : ℕ) (p : N.QT (m ^ 2)) : PowerSeries O :=
  PowerSeries.mk fun n => ∑ᶠ (χ : N.X) (_ : be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) = n), N.txT m p χ
def arcEv (be : LinearMap.BilinForm ℤ N.X) (m : ℕ) (p : N.QT (m ^ 2)) {j : ℕ} (q : N.QT j) (s : ℕ) : PowerSeries O :=
  PowerSeries.mk fun n => ∑ᶠ (χ : N.X) (_ : be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) +
    be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j + s = n), N.evT m p q.1.2 χ
structure Hom {O' : Type} [CommRing O'] (f : O →+* O') (N : NumD O) (N' : NumD O') where
  φ : N.A →* N'.A
  h : N.A → O'ˣ
  h_one : h 1 = 1
  θ_eq : ∀ x y u, N'.θ (φ x) (φ y) (φ u) * h (x * y) * h (x * u) * h (y * u) =
    Units.map f.toMonoidHom (N.θ x y u) * h (x * y * u) * h x * h y * h u
  σ_eq : ∀ x, N'.σ (φ x) * h x = Units.map f.toMonoidHom (N.σ x) * h x⁻¹
  lam : O'ˣ
  th_eq : ∀ x, N'.th (φ x) = (lam * h x : O'ˣ) * f (N.th x)
  e : N.X ≃+ N'.X
  c_eq : ∀ χ, N'.c (e χ) = φ (N.c χ)
  ψ_eq : ∀ χ, N'.ψ (e χ) * h (N.c χ) = Units.map f.toMonoidHom (N.ψ χ)
def Hom.Rel {O' : Type} [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : Hom f N N') (g : N.Gt) (g' : N'.Gt) : Prop :=
  g'.b = I.φ g.b ∧ ∀ χ, g'.s (I.e χ) * I.h (N.c χ * g.b) = Units.map f.toMonoidHom (g.s χ) * I.h (N.c χ) * I.h g.b
def InG {k : ℕ} (p : N.QT k) : Prop := ∃ z, p.1.1.toAdd = k • z
def InT {k : ℕ} (p : N.QT k) : Prop := ∃ p' : N.QT k, N.QEq p p' ∧ p'.1.1 = 1 ∧ p'.1.2.b = 1
end NumD
structure Match {C : Type} [NormedField C] (N N' : NumD C) (n : ℕ) where
  r : ∀ k : ℕ, N.QT k → N'.QT k → Prop
  tot : ∀ j p, ∃ p', r (n ^ j) p p'
  cotot : ∀ j p', ∃ p, r (n ^ j) p p'
  mul : ∀ k p q p' q', r k p p' → r k q q' → r k (p * q) (p' * q')
  eqv : ∀ k p q p' q', r k p p' → N.QEq p q → (r k q q' ↔ N'.QEq p' q')
  inj : ∀ k p q p', r k p p' → r k q p' → N.QEq p q
  incl : ∀ k k' (p : N.QT k) (p' : N'.QT k) (q : N.QT (k * k')) (q' : N'.QT (k * k')), k' ≠ 0 →
    q.1.1 = p.1.1 ^ k' → q.1.2 = p.1.2 → q'.1.1 = p'.1.1 ^ k' → q'.1.2 = p'.1.2 → (r k p p' ↔ r (k * k') q q')
  wp : ∀ k p q p' q', r k p p' → r k q q' → N'.wp p' q' = N.wp p q
  c₀ : C
  c₀_ne : c₀ ≠ 0
  tx : ∀ j p p', r ((n ^ j) ^ 2) p p' → N'.tx (n ^ j) p' = c₀ * N.tx (n ^ j) p
def AllMatch (P : ∀ {C : Type} [NontriviallyNormedField C] {N N' : NumD C} {n : ℕ}, Match N N' n → ℕ → ℕ → Prop) : Prop :=
  ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N N' : NumD C)
    (q : QuadraticMap ℤ N.X ℝ) (q' : QuadraticMap ℤ N'.X ℝ) (n g g' : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 →
    N.Int q → N'.Int q' → N.Tors n g → N'.Tors n g' → ∀ μ : Match N N' n, P μ g g'
namespace Match
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)
def A : Prop := ‖μ.c₀‖ = 1 ∧ ∀ j p p', μ.r (n ^ j) p p' → (N.InG p ↔ N'.InG p') ∧ (N.InT p ↔ N'.InT p')
def B (e : N.X ≃+ N'.X) : Prop := ∀ j p p', μ.r (n ^ j) p p' → ∃ z, p'.1.1.toAdd = e p.1.1.toAdd + n ^ j • z
def Term (e : N.X ≃+ N'.X) : Prop := ∀ j p p', μ.r ((n ^ j) ^ 2) p p' → p.1.1 = 1 → p'.1.1 = 1 →
  ∀ χ, N'.txT (n ^ j) p' (e χ) = μ.c₀ * N.txT (n ^ j) p χ
def OnB (I : NumB.Iso N.toNumB N'.toNumB) : Prop := ∀ j p p', μ.r (n ^ j) p p' → p.1.1 = 1 → p'.1.1 = 1 → p'.1.2.b = I.φ p.1.2.b
def OnG (I : NumD.Iso N N') : Prop := ∀ j p p', μ.r (n ^ j) p p' → p.1.1 = 1 → p'.1.1 = 1 → I.Rel p.1.2 p'.1.2
def OnQ (I : NumD.Iso N N') : Prop := ∀ j p p', p'.1.1.toAdd = I.e p.1.1.toAdd → I.Rel p.1.2 p'.1.2 → μ.r (n ^ j) p p'
end Match
namespace TateInh
def tateBe (q : Oˣ) (k : ℕ) (hk : k ≠ 0) : (tate q).Form k where
  be := ((2 * k : ℤ) • LinearMap.mul ℤ ℤ : LinearMap.BilinForm ℤ ℤ)
  symm (y z : ℤ) := by
    change (2 * k : ℤ) * (y * z) = (2 * k : ℤ) * (z * y)
    ring
  pos (y : ℤ) hy := by
    change 0 < (2 * k : ℤ) * (y * y)
    have : 0 < y * y := mul_self_pos.2 hy
    have : (0 : ℤ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    positivity
  dvd (y z : ℤ) := ⟨y * z, rfl⟩
def homOfIso {N N' : NumD O} (I : NumD.Iso N N') : NumD.Hom (RingHom.id O) N N' where
  φ := I.φ.toMonoidHom
  h := I.h
  h_one := I.h_one
  θ_eq := I.θ_eq
  σ_eq := I.σ_eq
  lam := I.lam
  th_eq := I.th_eq
  e := I.e
  c_eq := I.c_eq
  ψ_eq := I.ψ_eq
def tateHom {O' : Type} [CommRing O'] (f : O →+* O') (q : Oˣ) :
    NumD.Hom f (tate q) (tate (Units.map f.toMonoidHom q)) where
  φ := 1
  h _ := 1
  h_one := rfl
  θ_eq _ _ _ := by
    change (1 : O'ˣ) * 1 * 1 * 1 = Units.map f.toMonoidHom 1 * 1 * 1 * 1 * 1
    simp
  σ_eq _ := by
    change (1 : O'ˣ) * 1 = Units.map f.toMonoidHom 1 * 1
    simp
  lam := 1
  th_eq _ := by
    change (1 : O') = ((1 * 1 : O'ˣ) : O') * f 1
    simp
  e := AddEquiv.refl ℤ
  c_eq _ := rfl
  ψ_eq (n : ℤ) := by
    change Units.map f.toMonoidHom q ^ n ^ 2 * 1 = Units.map f.toMonoidHom (q ^ n ^ 2)
    rw [mul_one, map_zpow]
def sv {q : Oˣ} (g : (tate q).Gt) (a : ℤ) : Oˣ := g.s a
def yv {q : Oˣ} {k : ℕ} (p : (tate q).QT k) : ℤ := p.1.1.toAdd
theorem sv_add {q : Oˣ} (g : (tate q).Gt) (a b : ℤ) : sv g (a + b) = sv g a * sv g b :=
  (mul_one _).symm.trans (g.mult a b)
theorem tate_cub {q : Oˣ} (k : ℕ) (a b x : (tate q).A) : cubN (tate q).θ k a b x = 1 :=
  Finset.prod_eq_one fun _ _ => rfl
theorem sv_pow {q : Oˣ} (g : (tate q).Gt) (k : ℕ) (a : ℤ) : sv (g ^ k) a = sv g a ^ k := by
  have := g.pow_s k a
  rwa [tate_cub, mul_one] at this
theorem sv_mul {q : Oˣ} (g : (tate q).Gt) (k : ℕ) (a : ℤ) : sv g (k * a) = sv g a ^ k := by
  induction k with
  | zero => rw [Nat.cast_zero, zero_mul, pow_zero]; exact g.s_zero
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, sv_add, ih, pow_succ]
theorem sv_q {q : Oˣ} {k : ℕ} (p : (tate q).QT k) (a : ℤ) : sv p.1.2 a ^ k = q ^ (2 * yv p * a) := by
  rw [← sv_pow, (tate q).mem_QT.1 p.2]; exact tate_τ q _ a
theorem tate_qeq {q : Oˣ} {k : ℕ} {p p' : (tate q).QT k} (h : (tate q).QEq p p') :
    ∃ z : ℤ, yv p' = yv p + k * z ∧ ∀ a : ℤ, sv p'.1.2 a = sv p.1.2 a * q ^ (2 * z * a) := by
  obtain ⟨z, h1, h2⟩ := h
  refine ⟨z, h1.trans (congrArg (yv p + ·) (nsmul_eq_mul k (show ℤ from z))), fun a => ?_⟩
  rw [h2]; exact (div_one _).trans (congrArg (sv p.1.2 a * ·) (tate_τ q z a))
theorem tate_wp_eq {q : Oˣ} {k : ℕ} (p r : (tate q).QT k) : (tate q).wp p r = sv p.1.2 (yv r) / sv r.1.2 (yv p) := by
  simp only [NumD.wp, NumD.tk, tate_cub, mul_one]; rfl
theorem tate_wp {q : Oˣ} {k : ℕ} {p p' : (tate q).QT k} (h : (tate q).QEq p p') (r : (tate q).QT k) :
    (tate q).wp p' r = (tate q).wp p r := by
  obtain ⟨z, h1, h2⟩ := tate_qeq h
  rw [tate_wp_eq, tate_wp_eq, h2, h1, sv_add, sv_mul, sv_q, mul_right_comm 2 z, mul_right_comm 2 (yv r),
    mul_right_comm 2 z, mul_div_mul_right_eq_div]
theorem tate_txT {q : Oˣ} (m : ℕ) (p : (tate q).QT (m ^ 2)) (χ : ℤ) : (tate q).txT m p χ =
    ((q ^ yv p ^ 2 / sv p.1.2 (yv p) ^ ((m ^ 2 - 1) / 2) * (q ^ χ ^ 2 * sv p.1.2 χ ^ m) : Oˣ) : O) := by
  have a : ∀ x, dbl (tate q).θ (tate q).σ x = 1 := fun x => div_self' (1 : Oˣ)
  have b : ∀ n x, mulq (tate q).θ (tate q).σ n x = 1 := fun n x => by simp [mulq, a, tate_cub]
  simp only [NumD.txT, NumD.vt, NumD.wQ, NumB.wS, a, b, tate_cub, mul_one, one_pow, div_one]
  rw [← sv_pow p.1.2 m, Units.val_mul _ (q ^ χ ^ 2 * _)]
  exact congrArg _ (mul_one (_ : O))
theorem tate_tx [TopologicalSpace O] {q : Oˣ} {m : ℕ} (ho : Odd m) {p p' : (tate q).QT (m ^ 2)} (h : (tate q).QEq p p') :
    (tate q).tx m p' = (tate q).tx m p := by
  obtain ⟨z, h1, h2⟩ := tate_qeq h
  obtain ⟨r, hr⟩ : Odd (m ^ 2) := ho.pow
  have hr' : (m : ℤ) ^ 2 = 2 * r + 1 := by exact_mod_cast hr
  have e5 : (m ^ 2 - 1) / 2 = r := by omega
  refine Eq.trans (tsum_congr fun (χ : ℤ) => ?_) ((Equiv.addRight (m * z : ℤ)).tsum_eq fun χ : ℤ => (tate q).txT m p χ)
  change (tate q).txT m p' χ = (tate q).txT m p (χ + m * z : ℤ)
  rw [tate_txT, tate_txT, e5]
  congr 1
  have hz := sv_q p z
  rw [h2, h2, h1, sv_add, sv_add, sv_mul, sv_mul, hz, mul_pow (sv p.1.2 χ) (sv p.1.2 z ^ m), ← pow_mul, ← sq, hz]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow, ofMul_zpow, Nat.cast_pow]
  match_scalars
  · linear_combination (2 * yv p * z + (m : ℤ) ^ 2 * z ^ 2) * hr'
  all_goals ring
theorem qEq_incl (N : NumD O) {k k' : ℕ} (p p' : N.QT k) (q q' : N.QT (k * k')) (hk : k' ≠ 0)
    (a : q.1.1 = p.1.1 ^ k') (b : q.1.2 = p.1.2) (c : q'.1.1 = p'.1.1 ^ k') (d : q'.1.2 = p'.1.2) :
    N.QEq p p' ↔ N.QEq q q' := by
  refine exists_congr fun z => ?_
  rw [a, b, c, d, toAdd_pow, toAdd_pow, mul_comm k, mul_smul, ← smul_add]
  simp only [← natCast_zsmul]
  exact and_congr_left' (smul_right_inj (Int.natCast_ne_zero.2 hk)).symm
open scoped BigOperators in
variable {O : Type} [CommRing O] in

theorem _root_.GlobalTheory.Ex.TateInh.qEq_mul (N : _root_.GlobalTheory.Ex.NumD O) {k : ℕ}
    {p p' q q' : N.QT k} (h : N.QEq p p')
    (h' : N.QEq q q') :
    N.QEq (p * q) (p' * q') := by
  unfold _root_.GlobalTheory.Ex.NumD.QEq at *
  obtain ⟨z, hz1, hz2⟩ := h
  obtain ⟨z', hz1', hz2'⟩ := h'
  refine ⟨z + z', ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Prod.fst_mul, toAdd_mul, hz1, hz1', smul_add]
    abel
  · simp only [Subgroup.coe_mul, Prod.snd_mul, hz2, hz2', N.io_add]
    exact mul_mul_mul_comm _ _ _ _
def tateMatch {C : Type} [NormedField C] (q : Cˣ) (n : ℕ) (hn : Odd n) : Match (tate q) (tate q) n where
  r _ := (tate q).QEq
  tot _ p := ⟨p, ((tate q).qEq_equivalence _).refl p⟩
  cotot _ p := ⟨p, ((tate q).qEq_equivalence _).refl p⟩
  mul _ _ _ _ _ := qEq_mul _
  eqv k _ _ _ _ a b := have E := (tate q).qEq_equivalence k
    ⟨fun c => E.trans (E.symm a) (E.trans b c), fun c => E.trans (E.symm b) (E.trans a c)⟩
  inj k _ _ _ a b := have E := (tate q).qEq_equivalence k
    E.trans a (E.symm b)
  incl _ _ p p' r r' := qEq_incl _ p p' r r'
  wp _ _ _ _ _ a b := by rw [tate_wp a, NumD.wp_swap, tate_wp b, ← NumD.wp_swap]
  c₀ := 1
  c₀_ne := one_ne_zero
  tx _ _ _ h := by rw [one_mul]; exact tate_tx hn.pow h
def isoRefl (N : NumD O) : NumD.Iso N N where
  φ := MulEquiv.refl _
  h _ := 1
  h_one := rfl
  θ_eq _ _ _ := by simp
  σ_eq _ := rfl
  lam := 1
  th_eq _ := by simp
  e := AddEquiv.refl _
  c_eq _ := rfl
  ψ_eq _ := mul_one _
example (N : NumD O) (h : N.A → Oˣ) (h₁ : h 1 = 1) : (homOfIso (N.regaugeIso h h₁)).h = h := rfl
end TateInh
end GlobalTheory.Ex
end


