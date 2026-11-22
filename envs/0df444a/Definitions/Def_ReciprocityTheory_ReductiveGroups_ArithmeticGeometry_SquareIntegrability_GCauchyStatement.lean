-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:37.778811+00:00
-- url     : https://prove2.me/theorems/d76660be-7f0f-4ecc-a166-5a55c6d6ce11
-- title:
--   GCauchy Statement
-- statement:
--   Definitions and structural lemmas for GCauchy Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/GCauchyStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
abbrev Idx (dim : (E →+* ℂ) → ℕ) : Type := Σ τ : E →+* ℂ, Fin (dim τ)
abbrev Vsp (dim : (E →+* ℂ) → ℕ) : Type := EuclideanSpace ℂ (Idx dim)
def Hf {ι : Type} [Fintype ι] (v w : EuclideanSpace ℂ ι) : ℂ := ∑ i, v i * (starRingEnd ℂ) (w i)
def HC {ι : Type} [Fintype ι] {n : ℕ} (v w : Fin n → EuclideanSpace ℂ ι) : ℂ :=
  ∑ k, Hf (v k) (w k)
def act {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v : Vsp dim) : Vsp dim :=
  WithLp.toLp 2 fun i => i.1 (α : E) * v i
abbrev lat {ι : Type} [Fintype ι] {κ : Type} (b : Module.Basis κ ℝ (EuclideanSpace ℂ ι)) :
    Submodule ℤ (EuclideanSpace ℂ ι) :=
  Submodule.span ℤ (Set.range b)
variable (E) in

structure PT where

  dim : (E →+* ℂ) → ℕ
  r : ℕ
  dim_conj : ∀ τ, dim τ + dim (NumberField.ComplexEmbedding.conjugate τ) = r

  b : Module.Basis (Fin (2 * Fintype.card (Idx dim))) ℝ (Vsp dim)
  stable : ∀ (α : 𝓞 E) (x : Vsp dim), x ∈ lat b → act α x ∈ lat b

  integral : ∀ x y : Vsp dim, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k

  perfect : ∀ φ : lat b →+ ℤ, ∃ x ∈ lat b, ∀ y : lat b, (φ y : ℝ) = (Hf x (y : Vsp dim)).im

  eps : Vsp dim → ℤ
  eps_pm : ∀ x ∈ lat b, eps x = 1 ∨ eps x = -1
  eps_add : ∀ x ∈ lat b, ∀ y ∈ lat b,
    (eps (x + y) : ℝ) = eps x * eps y * Real.cos (Real.pi * (Hf x y).im)
  eps_iso : ∀ x ∈ lat b, (∀ α : 𝓞 E, (Hf (act α x) x).im = 0) → eps x = 1
namespace PT
variable (X : PT E)
abbrev L : Submodule ℤ (Vsp X.dim) := lat X.b
variable (E) in

def f : ℕ := Module.finrank ℚ E / 2
variable (E) in

def rd : ℝ := |(NumberField.discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ))
def gA : ℕ := f E * X.r
def la1 : ℝ := sInf {t : ℝ | ∃ x ∈ X.L, x ≠ 0 ∧ t = ‖x‖}
def ph (th : ℝ) : ℝ := if X.la1 < th then 2 * f E / (rd E ^ 2 * X.la1 ^ 2) else 0
def Sec (q n : ℕ) : Submodule ℂ ((Fin n → Vsp X.dim) → ℂ) where
  carrier := {F | Differentiable ℂ F ∧ ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) →
    ∀ v, F (v + γ) = (∏ k, (X.eps (γ k) : ℂ)) ^ q *
      cexp (q * Real.pi * HC v γ + q * Real.pi * HC γ γ / 2) * F v}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨hF.add hG, fun γ hγ v => ?_⟩
    simp only [Pi.add_apply, hF' γ hγ v, hG' γ hγ v]; ring
  zero_mem' := ⟨differentiable_const 0, fun _ _ _ => by simp⟩
  smul_mem' := by
    rintro a F ⟨hF, hF'⟩
    refine ⟨hF.const_smul a, fun γ hγ v => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, hF' γ hγ v]; ring
def ptN2 (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ) (v : Fin n → Vsp X.dim) : ℝ :=
  ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * (HC v v).re)
def fd (n : ℕ) : Set (Fin n → Vsp X.dim) := {v | ∀ k, v k ∈ ZSpan.fundamentalDomain X.b}
def l2 (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ) : ℝ := ⨍ v in X.fd n, X.ptN2 q F v
def l2ip (q : ℕ) {n : ℕ} (F G : (Fin n → Vsp X.dim) → ℂ) : ℂ :=
  ⨍ v in X.fd n, F v * (starRingEnd ℂ) (G v) * (Real.exp (-(q * Real.pi) * (HC v v).re) : ℂ)
def U (q : ℕ) {n : ℕ} (a : Fin n → Vsp X.dim) (F : (Fin n → Vsp X.dim) → ℂ) :
    (Fin n → Vsp X.dim) → ℂ :=
  fun v => cexp (q * Real.pi * HC v a - q * Real.pi * HC a a / 2) * F (v - a)
end PT
def polyDeriv {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) (x : W) : ℂ :=
  ∑ m ∈ P.support, P.coeff m *
    iteratedFDeriv ℂ (Multiset.card (Finsupp.toMultiset m)) F x
      (fun k => u ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm)))
abbrev Letter (n : ℕ) (dim : (E →+* ℂ) → ℕ) : Type := Fin n × Idx dim
open Classical in

def dir {n : ℕ} {dim : (E →+* ℂ) → ℕ} (l : Letter n dim) : Fin n → Vsp dim :=
  Pi.single l.1 (EuclideanSpace.single l.2 1)
variable (E) in

structure Block (n : ℕ) (dim : (E →+* ℂ) → ℕ) where
  τ : E →+* ℂ
  i : ℕ
  hi : i ≤ dim τ
  c : ℕ
  hc : 1 ≤ c
  col : Fin i → Fin n
  col_inj : Function.Injective col
def Block.poly {n : ℕ} {dim : (E →+* ℂ) → ℕ} (B : Block E n dim) :
    MvPolynomial (Letter n dim) ℂ :=
  (Matrix.of fun a b : Fin B.i => MvPolynomial.X (B.col b, ⟨B.τ, Fin.castLE B.hi a⟩)).det ^ B.c
def P1 {n nb : ℕ} {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim) :
    MvPolynomial (Letter n dim) ℂ :=
  ∏ j, (bs j).poly
def DF {n nb : ℕ} {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim) : ℕ :=
  ∑ j, (bs j).i * (bs j).c
def Disj {n nb : ℕ} {dim : (E →+* ℂ) → ℕ} (bs : Fin nb → Block E n dim) : Prop :=
  ∀ j j', j ≠ j' → ∀ a a', (bs j).col a ≠ (bs j').col a'
section Par
variable (X : PT E)
def RR : ℝ := PT.rd E ^ 7
def dstar (m : ℕ) : ℕ := 2 * PT.f E * m
def th (q : ℕ) (R0 : ℝ) : ℝ := Real.sqrt (PT.f E * R0 ^ 2 * RR (E := E) ^ 3 / q)
def b0 (q : ℕ) (R0 : ℝ) : ℝ := q / (R0 ^ 2 * RR (E := E) ^ 4)
def t0 (q : ℕ) (R0 : ℝ) : ℝ := q * b0 (E := E) q R0
def M1 (m : ℕ) : ℝ := 90 * m ^ 2 * (dstar (E := E) m : ℝ) ^ 2 * PT.rd E
def omStar : ℝ := 2 * (PT.f E : ℝ) ^ ((3 : ℝ) / 2) * PT.rd E
def Cchi (m : ℕ) : ℝ := 8100 * m ^ 4 * (dstar (E := E) m : ℝ) ^ 4 * RR (E := E)
structure Par (DF : ℕ) where
  q : ℕ
  R0 : ℝ
  m : ℕ
  hq : 1 ≤ q
  hDF : 1 ≤ DF
  hfr : 2 ≤ PT.f E * X.r
  hm : ∃ τ, X.dim τ ≤ m
  hm1 : 1 ≤ m
  hmf : m ^ 4 ≤ PT.f E
  hfrd : (PT.f E : ℝ) ≤ PT.rd E
  hf2 : (PT.f E : ℝ) ^ 2 ≤ PT.rd E
  hrd : 16 ≤ PT.rd E
  hR0 : 270 ≤ R0 ^ 2 ∧ 90 * ((X.gA : ℝ) + DF) ≤ R0 ^ 2
  C1 : (dstar (E := E) m : ℝ) ^ 2 * omStar (E := E) * th (E := E) q R0 ^ 2 < 1
  C2 : 1 ≤ b0 (E := E) q R0
  C3 : M1 (E := E) m ≤ q / 2
  C4 : DF ≤ q
  C5 : 4 * (DF : ℝ) * (7 + Real.log (q * DF)) + dstar (E := E) m + 1 ≤ t0 (E := E) q R0
  C6 : (X.gA : ℝ) * Real.log 2 + 2 * dstar (E := E) m + 3 +
      (DF + 1) * (X.r * Real.log X.r + 3 * X.r + 3) ≤ t0 (E := E) q R0
variable {X} {DF : ℕ}
def Par.ph (P : Par X DF) : ℝ := X.ph (th (E := E) P.q P.R0)
def Par.Jbound (P : Par X DF) (n : ℕ) : ℝ :=
  (4 : ℝ)⁻¹ ^ n * (6 * (2 * (dstar (E := E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2))⁻¹ ^ n *
    (2 : ℝ)⁻¹ ^ ((X.r + 2) * DF) *
    Real.exp (-(2 * Real.pi * n * Cchi (E := E) P.m * P.ph / P.q))
def Par.p1 (P : Par X DF) : ℝ := 1 + X.gA * Real.log (1 + 6 * Real.sqrt (X.gA * P.q))
def Par.p2 (P : Par X DF) : ℝ := Real.log (2 * (3 * (dstar (E := E) P.m : ℝ)) ^ dstar (E := E) P.m)
def Par.p3 (P : Par X DF) : ℝ := X.r * (P.p1 + P.p2 + dstar (E := E) P.m)
def Par.ka0 (P : Par X DF) : ℝ := 4 * RR (E := E) * (dstar (E := E) P.m : ℝ) ^ 2
end Par
def JStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (n nb : ℕ)
    (bs : Fin nb → Block E n X.dim), Disj bs → ∀ P : Par X (DF bs),
    ∃ F ∈ X.Sec P.q n, X.l2 P.q F = 1 ∧ P.Jbound n ≤ ‖polyDeriv (P1 bs) dir F 0‖ ^ 2
def IsPi (X : PT E) (q : ℕ) (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim) : Prop :=
  (∀ α v, π (act α v) = act α (π v)) ∧ (∀ x ∈ X.L, π x ∈ X.L) ∧
    (∀ v w, Hf (π v) (π w) = q * Hf v w) ∧ (∀ x ∈ X.L, X.eps (π x) = X.eps x ^ q)
def s0 (X : PT E) {n : ℕ} (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    (Fin n → Vsp X.dim) → ℂ :=
  fun v => ∏ k, s fun _ => π (v k)
def IsReps (X : PT E) (q n : ℕ) (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim) (K : Finset (Fin n → Vsp X.dim)) :
    Prop :=
  (∀ b ∈ K, ∀ k, (q : ℂ) • b k ∈ X.L) ∧
    ∀ b : Fin n → Vsp X.dim, (∀ k, (q : ℂ) • b k ∈ X.L) →
      ∃! b' ∈ K, ∀ k, π (b k - b' k) ∈ X.L
def NStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (q n : ℕ) (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim),
    1 ≤ q → IsPi X q π → ∀ s ∈ X.Sec 1 1, s ≠ 0 → ∀ K, IsReps X q n π K →
      (∀ b ∈ K, X.U q b (s0 X π s) ∈ X.Sec q n) ∧
      (∀ b ∈ K, ∀ b' ∈ K, b ≠ b' → X.l2ip q (X.U q b (s0 X π s)) (X.U q b' (s0 X π s)) = 0) ∧
      (∀ b ∈ K, X.l2 q (X.U q b (s0 X π s)) = X.l2 1 s ^ n) ∧
      X.Sec q n ≤ Submodule.span ℂ ((fun b => X.U q b (s0 X π s)) '' (K : Set _))
def IStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (n nb : ℕ)
    (bs : Fin nb → Block E n X.dim), Disj bs → ∀ P : Par X (DF bs), ∀ π, IsPi X P.q π →
    ∀ s ∈ X.Sec 1 1, s ≠ 0 → ∀ K, IsReps X P.q n π K →
      P.Jbound n * X.l2 1 s ^ n ≤
        ∑ b ∈ K, ‖polyDeriv (P1 bs) dir (X.U P.q b (s0 X π s)) 0‖ ^ 2
def TStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF)
    (r1 : ℕ), 2 ≤ r1 → ∀ a : Fin X.r → Vsp X.dim, (∀ j, ((r1 : ℂ) ^ 2) • a j ∈ X.L) →
    (∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) →
    ∀ s ∈ X.Sec 1 1, s ≠ 0 →
      (0 < P.ph → ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
        Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) *
          Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4))) ∧
      (P.ph = 0 → ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
        Real.exp (X.r * P.p1))
structure GT (ι : Type) [Fintype ι] where
  b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι)
  integral : ∀ x y : EuclideanSpace ℂ ι, x ∈ lat b → y ∈ lat b → ∃ k : ℤ, (Hf x y).im = k
  perfect : ∀ φ : lat b →+ ℤ, ∃ x ∈ lat b, ∀ y : lat b, (φ y : ℝ) = (Hf x (y : EuclideanSpace ℂ ι)).im
  ka : EuclideanSpace ℂ ι → ℂ
  ka_abs : ∀ x ∈ lat b, ‖ka x‖ = 1
namespace GT
variable {ι : Type} [Fintype ι] (Y : GT ι)
def Sec (q : ℕ) : Submodule ℂ (EuclideanSpace ℂ ι → ℂ) where
  carrier := {F | Differentiable ℂ F ∧ ∀ γ ∈ lat Y.b, ∀ v,
    F (v + γ) = Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * F v}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨hF.add hG, fun γ hγ v => ?_⟩
    simp only [Pi.add_apply, hF' γ hγ v, hG' γ hγ v]; ring
  zero_mem' := ⟨differentiable_const 0, fun _ _ _ => by simp⟩
  smul_mem' := by
    rintro a F ⟨hF, hF'⟩
    refine ⟨hF.const_smul a, fun γ hγ v => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, hF' γ hγ v]; ring
def ptN2 (_Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) (v : EuclideanSpace ℂ ι) : ℝ :=
  ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)
def l2 (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : ℝ :=
  ⨍ v in ZSpan.fundamentalDomain Y.b, Y.ptN2 q F v
def la1 : ℝ := sInf {t : ℝ | ∃ x ∈ lat Y.b, x ≠ 0 ∧ t = ‖x‖}
end GT
def GSupStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q : ℕ), 1 ≤ q → ∀ F ∈ Y.Sec q, ∀ v,
    Y.ptN2 q F v ≤ 2 * (q : ℝ) ^ Fintype.card ι *
      (1 + 4 * Real.sqrt (2 * Fintype.card ι) / (Real.sqrt (q * Real.pi) * Y.la1)) ^
        (2 * Fintype.card ι) * Y.l2 q F
open Classical in

def GCauchyStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : EuclideanSpace ℂ ι → ℂ), Differentiable ℂ F →
    ∀ S : ℝ, (∀ v, ‖F v‖ ^ 2 * Real.exp (-Real.pi * ‖v‖ ^ 2) ≤ S) → ∀ α : ι →₀ ℕ,
      ‖polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) F 0‖ ≤
        Real.sqrt S * (Real.pi * Real.exp 1 * α.degree) ^ ((α.degree : ℝ) / 2)
end
end ReciprocityTheory.ChartRestriction.G.I2


