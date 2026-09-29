-- Prove2me | Definitions.Def_CerednikDrinfeld_CartierStructureConstants
-- name    : CerednikDrinfeld_CartierStructureConstants
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/ec9085ef-0043-53e9-b5f5-b64874b2a2e8
-- title:
--   Homogeneous V-bases, structure constants of Π, universal lift ring
-- statement:
--   Fix a prime $p$, a commutative ring $B$, a ring homomorphism $j\colon \mathbb{Z}_{p^2}\to B$ (the Witt vectors of $\mathbb{F}_{p^2}$, written `Zp2 p`) and a formal $\mathcal{O}_D$-module $X$ over $B$ with underlying two-dimensional formal group $X.F$ and Cartier module `CartierModule p X.F`. Two predicates are defined. First, $\gamma\colon \{0,1\}\to$ `CartierModule p X.F` is a homogeneous $V$-basis, `IsHomogeneousVBasis X j γ`, when $\gamma_i$ lies in the graded piece `X.gradedPiece j i` — the additive subgroup of those $f$ with $\mathrm{endAct}(X.\mathrm{actEnd}(\tau(c)))f=\langle j(\tau(c))^{p^{i}}\rangle f$ for every $c\in\mathbb{F}_{p^2}$, where $\tau$ is the Teichmüller lift and $\langle\,\rangle$ is the Cartier-module homothety — and when the $2\times 2$ matrix of tangent vectors $\bigl(\mathrm{tangent}(\gamma_i)(k)\bigr)$ has unit determinant. Second, a family $a\colon\mathbb{N}\times\{0,1\}\to B$ consists of structure constants for $\gamma$, `HasStructureConstants X γ a`, when for every $i$ and every truncation order $N$ there exists a remainder $h$ with $\Pi\gamma_i=\sum_{m<N}V^m\langle a_{m,i}\rangle\gamma_{\pi(m,i)}+V^N h$, where $\Pi$ is the action of `X.varpiEnd`, $V$ is the integral Verschiebung `verschiebungInt`, and $\pi(m,i)=(m+i+1)\bmod 2$ (`piIndex`). This is the finite-order form of the $V$-adically convergent expansions; at $N=0$ the condition is vacuous for every $a$, and over a base of characteristic $p$ the expansions may equally be written with the usual Verschiebung.
--
--   Alongside these, for a coefficient ring $R$ and $u,v\in B$ the universal lift ring `LiftRing p R u v` is $R[X_b: b\in B]/(X_uX_v-p)$, with tautological elements $X_b$ satisfying $X_uX_v=p$; given $j\colon R\to B$ with $uv=p$ in $B$ there is a surjection to $B$ sending $X_b\mapsto b$ and restricting to $j$ on constants, and the lifted constants $X_{a_{m,i}}$ over $u=a_{0,0}$, $v=a_{0,1}$ map back to $a_{m,i}$ and satisfy $X_{a_{0,0}}X_{a_{0,1}}=p$. If multiplication by $p$ kills only $0$ in $R$ — as it does for $R=\mathbb{Z}_{p^2}$ — the same holds in the lift ring; this rests on three lemmas about $\mathrm{MvPolynomial}$ stating that a non-zero-divisor constant $\pi$ may be cancelled from membership in the ideal $(X_uX_v-C\pi)$. The remaining material is functoriality in the base: the integral Witt polynomial families commute with coefficient maps, `baseChangeEq` commutes with `verschiebungInt` and its iterates and transports $V$-expansions and tangent determinants, and accordingly graded pieces, homogeneous $V$-bases and structure constants push forward along a ring map $\varphi\colon B\to B'$, with $j$ replaced by $\varphi\circ j$ and $a$ by $\varphi(a)$.
--
--   **Relation to Mathlib.** Mathlib has no multivariable formal groups, Cartier modules or formal $\mathcal{O}_D$-modules; these notions, and the lift ring construction, are the project's own, built on Mathlib's `MvPolynomial`, `MvPowerSeries`, `WittVector` and `GaloisField`. The three cancellation lemmas for the ideal $(X_uX_v-C\pi)$ are general facts about multivariate polynomial rings, placed in Mathlib's `MvPolynomial` namespace.
--
--   **Where it is used.** These are the data through which Drinfeld's construction, as presented by Boutot and Carayol, is run: a special formal $\mathcal{O}_D$-module is described by a homogeneous $V$-basis of its Cartier module together with the expansion of $\Pi$ in that basis, and statements proved first over $p$-torsion-free $\mathbb{Z}_{p^2}$-algebras are transported to an arbitrary base by lifting the structure constants to the universal ring $R[X_b]/(X_uX_v-p)$. The resulting $p$-adic uniformisation of Shimura curves feeds the Čerednik–Drinfeld part of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_CartierStructureConstants.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v w

namespace MvFormalGroup

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ}
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]

namespace WittLaw

omit hp in

theorem map_coe_map_intCastRingHom {σ : Type*} (f : R →+* S) (Q : MvPolynomial σ ℤ) :
    MvPowerSeries.map f (((MvPolynomial.map (Int.castRingHom R) Q : MvPolynomial σ R)) :
      MvPowerSeries σ R) =
      ((MvPolynomial.map (Int.castRingHom S) Q : MvPolynomial σ S) : MvPowerSeries σ S) := by
  rw [← coe_mvPolynomial_map, MvPolynomial.map_map, RingHom.ext_int (f.comp (Int.castRingHom R))
    (Int.castRingHom S)]

theorem map_frobPolyFam (f : R →+* S) (n : ℕ) :
    MvPowerSeries.map f (frobPolyFam p R n) = frobPolyFam p S n := by
  rw [frobPolyFam_apply, frobPoly_eq_map, map_coe_map_intCastRingHom, ← frobPoly_eq_map, frobPolyFam_apply]

theorem map_nsmulFam (f : R →+* S) (n k : ℕ) :
    MvPowerSeries.map f (nsmulFam p R n k) = nsmulFam p S n k :=
  map_coe_map_intCastRingHom f _

end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d S}

theorem baseChangeEq_verschiebungInt [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (m : CartierModule p Φ) :
    baseChangeEq f h (verschiebungInt m) = verschiebungInt (baseChangeEq f h m) :=
  baseChangeEq_precomp f h isEndo_frobPolyFam isEndo_frobPolyFam (map_frobPolyFam f) m

theorem baseChangeEq_verschiebungInt_iterate [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (n : ℕ) (m : CartierModule p Φ) :
    baseChangeEq f h ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[n] m) =
      (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[n] (baseChangeEq f h m) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← baseChangeEq_verschiebungInt, ih]

theorem baseChangeEq_vExpansion [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    {ι : Type*} [Fintype ι] (N : ℕ) (c : Fin N → ι → R) (e : ι → CartierModule p Φ)
    (r : CartierModule p Φ) :
    baseChangeEq f h ((∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
        (∑ i, homothety (c m i) (e i))) + (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] r) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[m]
        (∑ i, homothety (f (c m i)) (baseChangeEq f h (e i)))) +
        (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[N] (baseChangeEq f h r) := by
  rw [(baseChangeEq (p := p) f h).map_add, map_sum (baseChangeEq (p := p) f h) _ Finset.univ,
    baseChangeEq_verschiebungInt_iterate]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [baseChangeEq_verschiebungInt_iterate, map_sum (baseChangeEq (p := p) f h) _ Finset.univ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact baseChangeEq_homothety f h _ _

theorem baseChangeEq_vExpansion_charP [Φ.IsComm] [Ψ.IsComm] [CharP R p] [CharP S p] (f : R →+* S)
    (h : Φ.map f = Ψ) {ι : Type*} [Fintype ι] (N : ℕ) (c : Fin N → ι → R)
    (e : ι → CartierModule p Φ) (r : CartierModule p Φ) :
    baseChangeEq f h ((∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Φ)))^[m]
        (∑ i, homothety (c m i) (e i))) + (⇑(verschiebung (p := p) (Φ := Φ)))^[N] r) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := Ψ)))^[m]
        (∑ i, homothety (f (c m i)) (baseChangeEq f h (e i)))) +
        (⇑(verschiebung (p := p) (Φ := Ψ)))^[N] (baseChangeEq f h r) := by
  rw [(baseChangeEq (p := p) f h).map_add, map_sum (baseChangeEq (p := p) f h) _ Finset.univ,
    baseChangeEq_verschiebung_iterate]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [baseChangeEq_verschiebung_iterate, map_sum (baseChangeEq (p := p) f h) _ Finset.univ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  exact baseChangeEq_homothety f h _ _

theorem det_tangent_baseChangeEq [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι ≃ Fin d) (e : ι → CartierModule p Φ) :
    (Matrix.of fun i i' => tangent (baseChangeEq f h (e i)) (σ i')).det =
      f (Matrix.of fun i i' => tangent (e i) (σ i')).det := by
  have hM : (Matrix.of fun i i' => tangent (baseChangeEq f h (e i)) (σ i')) =
      f.mapMatrix (Matrix.of fun i i' => tangent (e i) (σ i')) := by
    ext i i'
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, tangent_baseChangeEq]
  rw [hM, ← RingHom.map_det]

theorem isUnit_det_tangent_baseChangeEq [Φ.IsComm] [Ψ.IsComm] (f : R →+* S) (h : Φ.map f = Ψ)
    (e : Fin d → CartierModule p Φ) (he : IsUnit (Matrix.of fun i j => tangent (e i) j).det) :
    IsUnit (Matrix.of fun i j => tangent (baseChangeEq f h (e i)) j).det := by
  have h1 := det_tangent_baseChangeEq f h (Equiv.refl (Fin d)) e
  simp only [Equiv.refl_apply] at h1
  rw [h1]
  exact he.map f

end CartierModule

end MvFormalGroup

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R]

theorem eq_zero_of_C_mul_eq_zero {π : R} (hπ : ∀ r : R, π * r = 0 → r = 0) {g : MvPolynomial σ R}
    (h : C π * g = 0) : g = 0 := by
  ext e
  have he := congrArg (coeff e) h
  rw [coeff_C_mul, coeff_zero] at he
  rw [coeff_zero]
  exact hπ _ he

theorem exists_eq_C_mul_of_forall_dvd_coeff {π : R} {q : MvPolynomial σ R}
    (h : ∀ e, π ∣ coeff e q) : ∃ q₁ : MvPolynomial σ R, q = C π * q₁ := by
  classical
  choose c hc using h
  refine ⟨∑ e ∈ q.support, monomial e (c e), ?_⟩
  rw [Finset.mul_sum]
  conv_lhs => rw [as_sum q]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [C_mul_monomial, ← hc e]

theorem mem_span_of_C_mul_mem_span_X_mul_X_sub_C {π : R} (hπ : ∀ r : R, π * r = 0 → r = 0)
    (u v : σ) {g : MvPolynomial σ R}
    (h : C π * g ∈ Ideal.span {(X u * X v - C π : MvPolynomial σ R)}) :
    g ∈ Ideal.span {(X u * X v - C π : MvPolynomial σ R)} := by
  classical
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp h

  have hXq : q * X u * X v = C π * (g + q) := by
    have : q * (X u * X v - C π) = C π * g := hq
    linear_combination this

  have hdvd : ∀ e, π ∣ coeff e q := by
    intro e
    have hc := congrArg (coeff (e + Finsupp.single u 1 + Finsupp.single v 1)) hXq
    rw [coeff_mul_X, coeff_mul_X, coeff_C_mul] at hc
    exact ⟨_, hc⟩
  obtain ⟨q₁, rfl⟩ := exists_eq_C_mul_of_forall_dvd_coeff hdvd

  have hcancel : g + C π * q₁ = q₁ * X u * X v := by
    have h0 : C π * (g + C π * q₁ - q₁ * X u * X v) = 0 := by
      have := hXq
      linear_combination (-1 : MvPolynomial σ R) * this
    have := eq_zero_of_C_mul_eq_zero hπ h0
    linear_combination this
  refine Ideal.mem_span_singleton'.mpr ⟨q₁, ?_⟩
  linear_combination (-1 : MvPolynomial σ R) * hcancel

end MvPolynomial

namespace CerednikDrinfeld

namespace CartierLift

open MvPolynomial

variable (p : ℕ) (R : Type v) [CommRing R] {B : Type u}

def liftRel (u v : B) : MvPolynomial B R := X u * X v - C (p : R)

abbrev LiftRing (u v : B) : Type (max u v) := MvPolynomial B R ⧸ Ideal.span {liftRel p R u v}

variable {p R}

def liftVar (u v : B) (b : B) : LiftRing p R u v := Ideal.Quotient.mk _ (X b)

theorem liftVar_mul_liftVar (u v : B) :
    liftVar (p := p) (R := R) u v u * liftVar (p := p) (R := R) u v v = p := by
  rw [liftVar, liftVar, ← map_mul, ← map_natCast (Ideal.Quotient.mk (Ideal.span {liftRel p R u v})),
    ← MvPolynomial.C_eq_coe_nat]
  refine (Ideal.Quotient.eq).mpr (Ideal.subset_span ?_)
  simp [liftRel]

def liftHom [CommRing B] (j : R →+* B) (u v : B) (huv : u * v = p) : LiftRing p R u v →+* B :=
  Ideal.Quotient.lift _ (eval₂Hom j id) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, liftRel, map_sub, map_mul, eval₂Hom_X', eval₂Hom_X', eval₂Hom_C, map_natCast, id, id,
      huv, sub_self, mul_zero])

@[simp] theorem liftHom_liftVar [CommRing B] (j : R →+* B) (u v : B) (huv : u * v = p) (b : B) :
    liftHom j u v huv (liftVar u v b) = b := by
  rw [liftHom, liftVar, Ideal.Quotient.lift_mk, eval₂Hom_X']
  rfl

theorem liftHom_mk_C [CommRing B] (j : R →+* B) (u v : B) (huv : u * v = p) (r : R) :
    liftHom j u v huv (Ideal.Quotient.mk _ (C r)) = j r := by
  rw [liftHom, Ideal.Quotient.lift_mk, eval₂Hom_C]

theorem liftHom_comp_algebraMap [CommRing B] (j : R →+* B) (u v : B) (huv : u * v = p) :
    (liftHom j u v huv).comp (algebraMap R (LiftRing p R u v)) = j :=
  RingHom.ext fun r => liftHom_mk_C j u v huv r

theorem liftHom_surjective [CommRing B] (j : R →+* B) (u v : B) (huv : u * v = p) :
    Function.Surjective (liftHom j u v huv) :=
  fun b => ⟨liftVar u v b, liftHom_liftVar j u v huv b⟩

theorem natCast_mul_eq_zero (hR : ∀ r : R, (p : R) * r = 0 → r = 0) (u v : B) (x : LiftRing p R u v)
    (hx : (p : LiftRing p R u v) * x = 0) : x = 0 := by
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine MvPolynomial.mem_span_of_C_mul_mem_span_X_mul_X_sub_C hR u v ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, MvPolynomial.C_eq_coe_nat, map_natCast]
  exact hx

def liftConstants (a : ℕ → Fin 2 → B) (m : ℕ) (i : Fin 2) : LiftRing p R (a 0 0) (a 0 1) :=
  liftVar (a 0 0) (a 0 1) (a m i)

@[simp] theorem liftHom_liftConstants [CommRing B] (j : R →+* B) (a : ℕ → Fin 2 → B) (h : a 0 0 * a 0 1 = p)
    (m : ℕ) (i : Fin 2) : liftHom j (a 0 0) (a 0 1) h (liftConstants (p := p) a m i) = a m i :=
  liftHom_liftVar j _ _ h _

theorem liftConstants_zero_zero_mul (a : ℕ → Fin 2 → B) :
    liftConstants (p := p) (R := R) a 0 0 * liftConstants (p := p) (R := R) a 0 1 = p :=
  liftVar_mul_liftVar _ _

theorem zp2_natCast_mul_eq_zero [Fact p.Prime] (r : Zp2 p) (h : (p : Zp2 p) * r = 0) : r = 0 := by
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 (WittVector.p_nonzero p (GaloisField p 2))
  · exact h0

theorem natCast_mul_eq_zero_zp2 [Fact p.Prime] (u v : B) (x : LiftRing p (Zp2 p) u v)
    (hx : (p : LiftRing p (Zp2 p) u v) * x = 0) : x = 0 :=
  natCast_mul_eq_zero (zp2_natCast_mul_eq_zero (p := p)) u v x hx

end CartierLift

namespace FormalODModule

open MvPowerSeries MvFormalGroup MvFormalGroup.CartierModule SpecialFormal

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] {B' : Type v} [CommRing B']

theorem actEnd_map_toPowerSeries (φ : B →+* B') (X : FormalODModule p B) (a : Zp2 p) (i : Fin 2) :
    ((X.map φ).actEnd a).toPowerSeries i = MvPowerSeries.map φ ((X.actEnd a).toPowerSeries i) :=
  rfl

theorem varpiEnd_map_toPowerSeries (φ : B →+* B') (X : FormalODModule p B) (i : Fin 2) :
    ((X.map φ).varpiEnd).toPowerSeries i = MvPowerSeries.map φ (X.varpiEnd.toPowerSeries i) :=
  rfl

theorem baseChange_endAct_actEnd (φ : B →+* B') (X : FormalODModule p B) (a : Zp2 p)
    (f : CartierModule p X.F) :
    baseChange φ (endAct (X.actEnd a) f) = endAct ((X.map φ).actEnd a) (baseChange φ f) :=
  baseChangeEq_endAct φ rfl (actEnd_map_toPowerSeries φ X a) f

theorem baseChange_endAct_varpiEnd (φ : B →+* B') (X : FormalODModule p B) (f : CartierModule p X.F) :
    baseChange φ (endAct X.varpiEnd f) = endAct (X.map φ).varpiEnd (baseChange φ f) :=
  baseChangeEq_endAct φ rfl (varpiEnd_map_toPowerSeries φ X) f

theorem baseChange_mem_gradedPiece (φ : B →+* B') (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    {f : CartierModule p X.F} (hf : f ∈ X.gradedPiece j n) :
    baseChange φ f ∈ (X.map φ).gradedPiece (φ.comp j) n := by
  intro c
  rw [← baseChange_endAct_actEnd, hf c, baseChangeEq_homothety, RingHom.comp_apply, map_pow]
  rfl

def IsHomogeneousVBasis (X : FormalODModule p B) (j : Zp2 p →+* B) (γ : Fin 2 → CartierModule p X.F) :
    Prop :=
  (∀ i : Fin 2, γ i ∈ X.gradedPiece j i) ∧ IsUnit (Matrix.of fun i k => tangent (γ i) k).det

theorem IsHomogeneousVBasis.map (φ : B →+* B') {X : FormalODModule p B} {j : Zp2 p →+* B}
    {γ : Fin 2 → CartierModule p X.F} (h : X.IsHomogeneousVBasis j γ) :
    (X.map φ).IsHomogeneousVBasis (φ.comp j) fun i => baseChange φ (γ i) :=
  ⟨fun i => baseChange_mem_gradedPiece φ X j i (h.1 i), isUnit_det_tangent_baseChangeEq φ rfl γ h.2⟩

def piIndex (m : ℕ) (i : Fin 2) : Fin 2 := ⟨(m + i + 1) % 2, Nat.mod_lt _ two_pos⟩

@[simp] theorem piIndex_val (m : ℕ) (i : Fin 2) : (piIndex m i : ℕ) = (m + i + 1) % 2 := rfl

def HasStructureConstants (X : FormalODModule p B) (γ : Fin 2 → CartierModule p X.F)
    (a : ℕ → Fin 2 → B) : Prop :=
  ∀ (i : Fin 2) (N : ℕ), ∃ h : CartierModule p X.F,
    endAct X.varpiEnd (γ i) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[m]
        (homothety (a m i) (γ (piIndex m i)))) +
        (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] h

theorem HasStructureConstants.exists_eq {X : FormalODModule p B} {γ : Fin 2 → CartierModule p X.F}
    {a : ℕ → Fin 2 → B} (h : X.HasStructureConstants γ a) (i : Fin 2) (N : ℕ) :
    ∃ r : CartierModule p X.F, endAct X.varpiEnd (γ i) =
      (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[m]
        (homothety (a m i) (γ (piIndex m i)))) +
        (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] r :=
  h i N

theorem hasStructureConstants_order_zero (X : FormalODModule p B) (γ : Fin 2 → CartierModule p X.F)
    (a : ℕ → Fin 2 → B) (i : Fin 2) :
    ∃ h : CartierModule p X.F, endAct X.varpiEnd (γ i) =
      (∑ m : Fin 0, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[m]
        (homothety (a m i) (γ (piIndex m i)))) +
        (⇑(verschiebungInt (p := p) (Φ := X.F)))^[0] h :=
  ⟨endAct X.varpiEnd (γ i), by simp⟩

theorem HasStructureConstants.map (φ : B →+* B') {X : FormalODModule p B}
    {γ : Fin 2 → CartierModule p X.F} {a : ℕ → Fin 2 → B} (h : X.HasStructureConstants γ a) :
    (X.map φ).HasStructureConstants (fun i => baseChange φ (γ i)) fun m i => φ (a m i) := by
  intro i N
  obtain ⟨r, hr⟩ := h i N
  refine ⟨baseChange φ r, ?_⟩
  have key := congrArg (baseChange (p := p) (Φ := X.F) φ) hr
  rw [baseChange_endAct_varpiEnd, (baseChange (p := p) (Φ := X.F) φ).map_add,
    map_sum (baseChange (p := p) (Φ := X.F) φ) _ Finset.univ, baseChangeEq_verschiebungInt_iterate] at key
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [baseChangeEq_verschiebungInt_iterate, baseChangeEq_homothety]
  rfl

theorem HasStructureConstants.exists_eq_verschiebung [CharP B p] {X : FormalODModule p B}
    {γ : Fin 2 → CartierModule p X.F} {a : ℕ → Fin 2 → B} (h : X.HasStructureConstants γ a)
    (i : Fin 2) (N : ℕ) :
    ∃ r : CartierModule p X.F, endAct X.varpiEnd (γ i) =
      (∑ m : Fin N, (⇑(verschiebung (p := p) (Φ := X.F)))^[m]
        (homothety (a m i) (γ (piIndex m i)))) +
        (⇑(verschiebung (p := p) (Φ := X.F)))^[N] r := by
  obtain ⟨r, hr⟩ := h i N
  refine ⟨r, ?_⟩
  rw [hr, verschiebungInt_eq_verschiebung]

theorem liftHom_comp_liftConstants (j : Zp2 p →+* B) (a : ℕ → Fin 2 → B) (h : a 0 0 * a 0 1 = p) :
    (fun m i => CartierLift.liftHom j (a 0 0) (a 0 1) h
      (CartierLift.liftConstants (p := p) (R := Zp2 p) a m i)) = a := by
  funext m i
  exact CartierLift.liftHom_liftConstants j a h m i

end FormalODModule

end CerednikDrinfeld

end


