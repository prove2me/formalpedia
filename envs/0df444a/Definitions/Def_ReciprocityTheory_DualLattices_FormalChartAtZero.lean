-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_FormalChartAtZero
-- name    : ReciprocityTheory_DualLattices_FormalChartAtZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:54.547161+00:00
-- url     : https://prove2.me/theorems/5567c0b8-b4d3-4426-be43-c25668f8dde7
-- title:
--   Formal Chart At Zero
-- statement:
--   Definitions and structural lemmas for Formal Chart At Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/FormalChartAtZero.lean

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_HtLinStatement
import Definitions.Def_ReciprocityTheory_DualLattices_StThmAFull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix
namespace ReciprocityTheory.PGsh.Be2
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2
variable {R₀ : Type} [CommRing R₀]
def tEval {σ : Type} [Fintype σ] [DecidableEq σ] {S : Type} [CommRing S] [Algebra R₀ S] (N : ℕ)
    (f : MvPowerSeries σ R₀) (a : σ → S) : S :=
  ∑ e : σ → Fin N, algebraMap R₀ S (MvPowerSeries.coeff
    (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) f) * ∏ i, a i ^ (e i : ℕ)
open Classical in

def nEval {σ : Type} [Fintype σ] [DecidableEq σ] {S : Type} [CommRing S] [Algebra R₀ S]
    (f : MvPowerSeries σ R₀) (a : σ → S) : S :=
  if h : ∃ N, ∀ i, a i ^ N = 0 then tEval (Nat.find h) f a else 0
def fAdd {g : ℕ} {S : Type} [CommRing S] [Algebra R₀ S] (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀)
    (a b : Fin g → S) : Fin g → S :=
  fun k => nEval (F k) (Sum.elim a b)
def IsNilOver {R K : LAlg R₀} (ρ : LHom R K) : Prop :=
  Function.Surjective ρ.1 ∧ ∀ a ∈ RingHom.ker ρ.1, IsNilpotent a
lemma map_add_ker (B : BX R₀) {R K : LAlg R₀} (ρ : LHom R K) (x y : {x : B.G R // B.map ρ x = 0}) :
    B.map ρ (x.1 + y.1) = 0 := by
  rw [map_add, x.2, y.2, add_zero]
lemma map_nat_ker (B : BX R₀) {R R' K : LAlg R₀} (ρ : LHom R K) (ρ' : LHom R' K) (f : LHom R R')
    (hf : ρ'.comp f = ρ) (x : {x : B.G R // B.map ρ x = 0}) : B.map ρ' (B.map f x.1) = 0 := by
  rw [← B.map_comp, hf, x.2]
lemma map_tg_ker (B : BX R₀) {R S K : LAlg R₀} (ρ : LHom R K) (π : LHom R S) (hπ : π.SqZero)
    (ρS : LHom S K) (hfac : ρS.comp π = ρ) (w : B.gg ⊗[R₀] π.ker) : B.map ρ (B.tg π hπ w) = 0 := by
  rw [← hfac, B.map_comp, (B.tg_ker π hπ _).2 ⟨w, rfl⟩, map_zero]
structure FormalChartAtZero (B : BX R₀) (K : LAlg R₀) (g : ℕ) where
  F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀
  F_unit : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    fAdd F a 0 = a
  F_comm : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → fAdd F a b = fAdd F b a
  F_assoc : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b c : Fin g → S),
    (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → (∀ i, IsNilpotent (c i)) →
    fAdd F (fAdd F a b) c = fAdd F a (fAdd F b c)

  gb : Module.Basis (Fin g) R₀ B.gg
  χ : ∀ {R : LAlg R₀} (ρ : LHom R K), IsNilOver ρ →
    {x : B.G R // B.map ρ x = 0} ≃ (Fin g → maximalIdeal (R : Type))
  χ_add : ∀ {R : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ) (x y : {x : B.G R // B.map ρ x = 0}),
    (fun k => ((χ ρ hρ ⟨x.1 + y.1, map_add_ker B ρ x y⟩ k : maximalIdeal (R : Type)) : (R : Type))) =
      fAdd F (fun k => (χ ρ hρ x k : (R : Type))) (fun k => (χ ρ hρ y k : (R : Type)))
  χ_nat : ∀ {R R' : LAlg R₀} (ρ : LHom R K) (ρ' : LHom R' K) (hρ : IsNilOver ρ) (hρ' : IsNilOver ρ')
    (f : LHom R R') (hf : ρ'.comp f = ρ) (x : {x : B.G R // B.map ρ x = 0}) (k : Fin g),
    ((χ ρ' hρ' ⟨B.map f x.1, map_nat_ker B ρ ρ' f hf x⟩ k : maximalIdeal (R' : Type)) : (R' : Type)) =
      f.1 (χ ρ hρ x k : (R : Type))
  χ_tg : ∀ {R S : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ) (π : LHom R S) (hπ : π.SqZero)
    (ρS : LHom S K) (hfac : ρS.comp π = ρ) (w : B.gg) (i : π.ker) (k : Fin g),
    ((χ ρ hρ ⟨B.tg π hπ (w ⊗ₜ i), map_tg_ker B ρ π hπ ρS hfac _⟩ k : maximalIdeal (R : Type)) :
      (R : Type)) = gb.repr w k • (i : (R : Type))
structure SM (B : BX R₀) (K W : LAlg R₀) (ρW : LHom W K) : Prop where
  nil : IsNilOver ρW
  onto : Function.Surjective (B.map ρW)
abbrev algOf {O S : LAlg R₀} (s : LHom O S) : Algebra (O : Type) (S : Type) := s.1.toRingHom.toAlgebra
structure FIN (B : BX R₀) (O : LAlg R₀) (p : ℕ) where
  ι : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  AAx : ι → LAlg R₀
  sO : ∀ i, LHom O (AAx i)
  free : ∀ i, letI := algOf (sO i); Module.Free (O : Type) (AAx i : Type) ∧ Module.Finite (O : Type) (AAx i : Type)
  y : ∀ i, B.G (AAx i)
  y_p : ∀ i, p • y i = 0
  univ : ∀ (S : LAlg R₀) (s : LHom O S) (z : B.G S), p • z = 0 →
    ∃ i, ∃ φ : LHom (AAx i) S, φ.comp (sO i) = s ∧ B.map φ (y i) = z ∧
      ∀ j (φ' : LHom (AAx j) S), φ'.comp (sO j) = s → B.map φ' (y j) = z → j = i ∧ HEq φ' φ
  sep : ∀ i (f : (AAx i : Type)), (∀ φ : LHom (AAx i) O, φ.comp (sO i) = LHom.id O → φ.1 f = 0) → f = 0
  rank : (∑ i, (letI := algOf (sO i); Module.finrank (O : Type) (AAx i : Type))) =
    Nat.card {t : B.G O // p • t = 0}
attribute [instance] FIN.fι FIN.dι
def torP (B : BX R₀) (p : ℕ) (S : LAlg R₀) : AddSubgroup (B.G S) where
  carrier := {z | p • z = 0}
  add_mem' {a b} ha hb := by
    change p • a = 0 at ha
    change p • b = 0 at hb
    change p • (a + b) = 0
    rw [smul_add, ha, hb, add_zero]
  zero_mem' := smul_zero p
  neg_mem' {a} ha := by
    change p • a = 0 at ha
    change p • (-a) = 0
    rw [smul_neg, ha, neg_zero]
lemma mem_torP (B : BX R₀) (p : ℕ) {S : LAlg R₀} (z : B.G S) : z ∈ torP B p S ↔ p • z = 0 := Iff.rfl
lemma map_torP (B : BX R₀) (p : ℕ) {S S' : LAlg R₀} (f : LHom S S') (x : torP B p S) :
    B.map f (x : B.G S) ∈ torP B p S' := by
  refine (mem_torP B p _).2 ?_
  rw [← map_nsmul, (mem_torP B p _).1 x.2, map_zero]
lemma tg_torP (B : BX R₀) (p : ℕ) {R S : LAlg R₀} (π : LHom R S) (hπ : π.SqZero) (w : B.gg)
    (i : π.ker) (hi : p • i = 0) : B.tg π hπ (w ⊗ₜ i) ∈ torP B p R := by
  refine (mem_torP B p _).2 ?_
  rw [← map_nsmul, ← TensorProduct.tmul_smul, hi, TensorProduct.tmul_zero, map_zero]
structure OAct (B : BX R₀) (O : LAlg R₀) (p : ℕ) (E : Type) [CommRing E] where
  act : E → ∀ S : LAlg R₀, LHom O S → torP B p S →+ torP B p S
  act_one : ∀ S s x, act 1 S s x = x
  act_mul : ∀ a b S s x, act (a * b) S s x = act a S s (act b S s x)
  act_add : ∀ a b S s x, act (a + b) S s x = act a S s x + act b S s x
  act_nat : ∀ a {S S' : LAlg R₀} (s : LHom O S) (s' : LHom O S') (f : LHom S S'), f.comp s = s' →
    ∀ x, B.map f (act a S s x : B.G S) = act a S' s' ⟨B.map f x, map_torP B p f x⟩
  actL : E → B.gg →ₗ[R₀] B.gg
  act_tg : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (w : B.gg)
    (i : π.ker) (hi : p • i = 0),
    (act a R s ⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : B.G R) = B.tg π hπ (actL a w ⊗ₜ i)
def wS (p : ℕ) (n : ℕ) : MvPolynomial (Fin n) ℤ :=
  let q : MvPolynomial (Fin n) ℤ := (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p
  ∑ m ∈ q.support, MvPolynomial.monomial m (q.coeff m / (p : ℤ))
structure WData {p : ℕ} [Fact p.Prime] (Tw : ATowerL R₀ p) (K : LAlg R₀) where
  W : LAlg R₀
  ρW : LHom W K
  ρ1 : LHom (Tw.R 0) K
  ψ : LHom (Tw.R' 1) W
  πW : LHom W (Tw.R 0)
  πW_surj : Function.Surjective πW.1
  ρW_eq : ρ1.comp πW = ρW
  p_sq : ((p : (W : Type))) ^ 2 = 0
  ker_πW : RingHom.ker πW.1 = Ideal.span {(p : (W : Type))}
  ann_p : ∀ a : (W : Type), (p : (W : Type)) * a = 0 ↔ πW.1 a = 0
  compat : ∀ a, πW.1 (ψ.1 a) = (Tw.r 0).1 ((Tw.π 1).1 a)
  b : (W : Type)ˣ
  ξ_img : ψ.1 (Tw.ξ 1) = p * b
  Rb : Type
  [rb : CommRing Rb]
  [rbc : CharP Rb p]
  [rbp : PerfectRing Rb p]
  T : Rb →* (W : Type)
  decomp : ∀ w : (W : Type), ∃ c : Rb, ∃ c' : (W : Type), w = T c + p * c'
  witt_add : ∀ (n : ℕ) (a : Fin n → Rb), ∑ j, T (a j) =
    T (∑ j, a j) + p * T (MvPolynomial.eval₂ (Int.castRingHom Rb)
      (fun j => (frobeniusEquiv Rb p).symm (a j)) (wS p n))
  T_kill : ∀ c : Rb, πW.1 (T c) = 0 → T c = 0
attribute [instance] WData.rb WData.rbc WData.rbp
structure HodgeTateData (p : ℕ) [Fact p.Prime] (g : ℕ) (R : Type) [CommRing R] [Algebra ℤ_[p] R]
    (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : R) where
  ρ : Oe →ₐ[ℤ_[p]] Matrix (Ix g) (Ix g) ℤ_[p]
  ρL : Oe →+* Matrix (Fin g) (Fin g) R
  P : Matrix (Ix g) (Ix g) ℤ_[p]
  PL : Matrix (Fin g) (Fin g) R
  E : Matrix (Ix g) (Ix g) ℤ_[p]
  E_alternating : Eᵀ = -E ∧ ∀ i, E i i = 0
  isUnit_det_E : IsUnit E.det
  E_equivariant : ∀ a, (ρ a)ᵀ * E = E * ρ (σ a)
  projectors : P * P = P ∧ PL * PL = PL ∧ Pᵀ * E = E * P ∧
    (∀ a, P * ρ a = ρ a * P) ∧ ∀ a, PL * ρL a = ρL a * PL
  Ht : Matrix (Fin g) (Ix g) R
  Bt : Matrix (Fin g) (Ix g) R
  Ht_equivariant : (∀ a, Ht * (ρ a).map (algebraMap ℤ_[p] R) = (ρL (σ a))ᵀ * Ht) ∧
    Ht * P.map (algebraMap ℤ_[p] R) = PLᵀ * Ht
  form_eq_alt : Btᵀ * Ht - Htᵀ * Bt = cp • E.map (algebraMap ℤ_[p] R)
def ptOf (B : BX R₀) {O : LAlg R₀} {g : ℕ} {p : ℕ} (τ : Ix g → ℕ → B.G O) (t : Ix g → ZMod p) : B.G O :=
  ∑ j, (t j).val • τ j 0
structure Link {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw)
    [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
    {cp : (Tw.O : Type)} (H : HodgeTateData p g (Tw.O : Type) Oe σ cp) (gb : Module.Basis (Fin g) R₀ B.gg)
    (A : OAct B Tw.O p Oe) where
  τ : Ix g → ℕ → B.G Tw.O
  τ_tors : ∀ i n, (p ^ (n + 1)) • τ i n = 0
  τ_compat : ∀ i n, τ i n = p • τ i (n + 1)
  τ_basis : Function.Bijective (fun t : Ix g → ZMod p =>
    (⟨ptOf B τ t, by
      simp only [ptOf, Finset.smul_sum, smul_comm p]
      exact Finset.sum_eq_zero fun j _ => by
        have h := τ_tors j 0
        rw [zero_add, pow_one] at h
        rw [h, smul_zero]⟩ : {x : B.G Tw.O // p • x = 0}))
  ht : Ix g → B.gg →ₗ[R₀] (Tw.O : Type)
  bt : Ix g → B.gg ⊗[R₀] (Tw.O : Type)
  ht_spec : ∀ i n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
    ((Tw.q n).1.toLinearMap ∘ₗ ht i)
  bt_spec : ∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type)),
    B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
    (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
      LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i)
  Ht_eq : ∀ k i, H.Ht k i = ht i (gb k)
  Bt_eq : ∀ k i, H.Bt k i = (Module.Basis.baseChange (Tw.O : Type) gb).repr
    (TensorProduct.comm R₀ B.gg (Tw.O : Type) (bt i)) k
  E_spec : ∀ i j n, ∃ k : ℕ, (Tw.q n).1 (algebraMap ℤ_[p] (Tw.O : Type) (H.E i j)) = k ∧
    B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k)
  ρ_spec : ∀ a j, (A.act a Tw.O (LHom.id Tw.O) ⟨τ j 0, (mem_torP B p _).2 (by
      have h := τ_tors j 0
      rwa [zero_add, pow_one] at h)⟩ : B.G Tw.O) = ∑ k, (PadicInt.toZMod (H.ρ a k j)).val • τ k 0
  ρL_spec : ∀ a k l, H.ρL a k l = algebraMap R₀ (Tw.O : Type) (gb.repr (A.actL a (gb l)) k)
end ReciprocityTheory.PGsh.Be2


