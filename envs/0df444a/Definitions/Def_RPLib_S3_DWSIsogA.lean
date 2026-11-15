-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogA
-- name    : RPLib_S3_DWSIsogA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:23:52.158002+00:00
-- url     : https://prove2.me/theorems/283a792a-01b9-47fa-9dbf-686311b43cd5
-- title:
--   Weight-two Ramanujan-Petersson library: the endomorphism ring of an elliptic curve over `F_q`
-- statement:
--   The endomorphism ring of an elliptic curve over `F_q`.
--
--   `W` is an elliptic curve over a finite field `F` (`q = #F`), `L ⊇ F` algebraically closed.
--
--   * An endomorphism of `E` is an additive map `φ : E(L) → E(L)` with a generic-point representative
--     `Φ ∈ W(L(E))`: `τ_S Φ = Φ + φ S` for all `S` (`HasGen`, `IsEndo`; the S2 `hE` condition).
--   * `endRing W L` : these form a subring of `AddMonoid.End E(L)` (`HasGen.comp` uses the S2 pullback).
--   * `endFq W L` : the endomorphisms commuting with the `q`-Frobenius `π` (`End_{F_q}(E)`); it contains
--     `rsE W L r s = r + s π` (`rsHom_mem_endFq`), in particular `piE W L = π` and every integer.
--   * `det_eq_deg` : `det (φ | E[n]) = deg φ`, `trace_eq_tr` : `tr (φ | E[n]) = tr φ := 1 + deg φ - deg (1 - φ)`.
--   * `deg_mul`, `deg_lin` (`deg (a + b φ) = a² + a b tr φ + b² deg φ`), `tr_sq_le` (`tr φ² ≤ 4 deg φ`),
--     **`ch`** (Cayley–Hamilton `φ² - tr φ φ + deg φ = 0`), `eq_zero_of_mul_eq_zero` (no zero divisors),
--     `intCast_eq_zero`, `tr_frob` (`tr π = a = q + 1 - #W(F)`), `frob_ch` (`π² - a π + q = 0`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S2_Hasse

/-!
# S3-DWS-Isog, part A: the endomorphism ring of an elliptic curve over `F_q`

`W` is an elliptic curve over a finite field `F` (`q = #F`), `L ⊇ F` algebraically closed.

* An endomorphism of `E` is an additive map `φ : E(L) → E(L)` with a generic-point representative
  `Φ ∈ W(L(E))`: `τ_S Φ = Φ + φ S` for all `S` (`HasGen`, `IsEndo`; the S2 `hE` condition).
* `endRing W L` : these form a subring of `AddMonoid.End E(L)` (`HasGen.comp` uses the S2 pullback).
* `endFq W L` : the endomorphisms commuting with the `q`-Frobenius `π` (`End_{F_q}(E)`); it contains
  `rsE W L r s = r + s π` (`rsHom_mem_endFq`), in particular `piE W L = π` and every integer.
* `det_eq_deg` : `det (φ | E[n]) = deg φ`, `trace_eq_tr` : `tr (φ | E[n]) = tr φ := 1 + deg φ - deg (1 - φ)`.
* `deg_mul`, `deg_lin` (`deg (a + b φ) = a² + a b tr φ + b² deg φ`), `tr_sq_le` (`tr φ² ≤ 4 deg φ`),
  **`ch`** (Cayley–Hamilton `φ² - tr φ φ + deg φ = 0`), `eq_zero_of_mul_eq_zero` (no zero divisors),
  `intCast_eq_zero`, `tr_frob` (`tr π = a = q + 1 - #W(F)`), `frob_ch` (`π² - a π + q = 0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Endo

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF torsModule

/-- `Φ` (a point of `W` over the function field) represents the additive map `φ` of `E(L)`. -/
def HasGen (φ : Pt W L →+ Pt W L) (Φ : (W.baseChange (FF W L)).toAffine.Point) : Prop :=
  ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) Φ = Φ + ιP W L (φ S)

/-- `φ` is an endomorphism of the elliptic curve: it has a generic-point representative. -/
def IsEndo (φ : Pt W L →+ Pt W L) : Prop :=
  ∃ Φ : (W.baseChange (FF W L)).toAffine.Point, HasGen φ Φ

lemma hasGen_zero : HasGen (0 : Pt W L →+ Pt W L) 0 := fun S => by
  rw [map_zero, AddMonoidHom.zero_apply, map_zero, add_zero]

lemma HasGen.add {φ ψ : Pt W L →+ Pt W L} {Φ Ψ : (W.baseChange (FF W L)).toAffine.Point}
    (h₁ : HasGen φ Φ) (h₂ : HasGen ψ Ψ) : HasGen (φ + ψ) (Φ + Ψ) := fun S => by
  rw [map_add, h₁ S, h₂ S, AddMonoidHom.add_apply, map_add]
  abel

lemma HasGen.neg {φ : Pt W L →+ Pt W L} {Φ : (W.baseChange (FF W L)).toAffine.Point}
    (h : HasGen φ Φ) : HasGen (-φ) (-Φ) := fun S => by
  rw [map_neg, h S, AddMonoidHom.neg_apply, map_neg, neg_add]

lemma hasGen_id : HasGen (AddMonoidHom.id (Pt W L)) (G W L) := fun S => by
  rw [map_tau_G W L S, pS, AddMonoidHom.id_apply]

lemma hasGen_frob : HasGen (RPLib.EllFq.frob W L) (piG W L) := fun S => map_tau_piG S

lemma hasGen_rs (r s : ℤ) : HasGen (rsHom W L r s) (PhiRS W L r s) := hE_rs r s

lemma map_ιP_of_algHom (ρ : FF W L →ₐ[L] FF W L) (C : Pt W L) :
    Point.map (W' := W.toAffine) (ρ.restrictScalars F) (ιP W L C) = ιP W L C := by
  have hcomp : (ρ.restrictScalars F).comp (ιF W L) = ιF W L := by
    apply AlgHom.ext
    intro a
    exact ρ.commutes a
  rw [ιP, Point.map_map, hcomp]

lemma HasGen.comp {φ ψ : Pt W L →+ Pt W L} {Φ Ψ : (W.baseChange (FF W L)).toAffine.Point}
    (h₁ : HasGen φ Φ) (h₂ : HasGen ψ Ψ) : IsEndo (φ.comp ψ) := by
  by_cases hψ : ψ = 0
  · refine ⟨0, ?_⟩
    have h0 : φ.comp ψ = 0 := by rw [hψ, AddMonoidHom.comp_zero]
    rw [h0]
    exact hasGen_zero
  · obtain ⟨ρ, e, hP⟩ := exists_isPull_of_hE Ψ ψ h₂ hψ
    refine ⟨Point.map (W' := W.toAffine) (ρ.restrictScalars F) Φ, fun S => ?_⟩
    have hc : ((tauHom W L S).restrictScalars F).comp (ρ.restrictScalars F) =
        (ρ.restrictScalars F).comp ((tauHom W L (ψ S)).restrictScalars F) := by
      apply AlgHom.ext
      intro f
      have h := hP.htau S f
      rw [tau_apply, tau_apply] at h
      exact h
    rw [Point.map_map, hc, ← Point.map_map, h₁ (ψ S), map_add, map_ιP_of_algHom]
    rfl

variable (W L) in
/-- The endomorphism ring of `E` (over `L`). -/
def endRing : Subring (AddMonoid.End (Pt W L)) where
  carrier := {φ | IsEndo φ}
  mul_mem' := by
    rintro φ ψ ⟨Φ, hΦ⟩ ⟨Ψ, hΨ⟩
    exact hΦ.comp hΨ
  one_mem' := ⟨G W L, hasGen_id⟩
  add_mem' := by
    rintro φ ψ ⟨Φ, hΦ⟩ ⟨Ψ, hΨ⟩
    exact ⟨Φ + Ψ, hΦ.add hΨ⟩
  zero_mem' := ⟨0, hasGen_zero⟩
  neg_mem' := by
    rintro φ ⟨Φ, hΦ⟩
    exact ⟨-Φ, hΦ.neg⟩

lemma mem_endRing {φ : AddMonoid.End (Pt W L)} : φ ∈ endRing W L ↔ IsEndo φ := Iff.rfl

variable (W L) in
/-- The Frobenius `π` as an element of the ring `AddMonoid.End E(L)`. -/
noncomputable abbrev piE : AddMonoid.End (Pt W L) := RPLib.EllFq.frob W L

variable (W L) in
/-- `r + s π` as an element of the ring `AddMonoid.End E(L)`. -/
noncomputable abbrev rsE (r s : ℤ) : AddMonoid.End (Pt W L) := rsHom W L r s

variable (W L) in
/-- `End_{F_q}(E)`: the endomorphisms commuting with the `q`-Frobenius `π`. -/
def endFq : Subring (AddMonoid.End (Pt W L)) :=
  endRing W L ⊓ Subring.centralizer {piE W L}

lemma mem_endFq {φ : AddMonoid.End (Pt W L)} :
    φ ∈ endFq W L ↔ φ ∈ endRing W L ∧ piE W L * φ = φ * piE W L := by
  rw [endFq, Subring.mem_inf, Subring.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]

lemma endFq_le : endFq W L ≤ endRing W L := inf_le_left

lemma rsHom_mem_endFq (r s : ℤ) : rsE W L r s ∈ endFq W L := by
  refine mem_endFq.mpr ⟨⟨PhiRS W L r s, hasGen_rs r s⟩, ?_⟩
  refine AddMonoidHom.ext fun P => ?_
  show RPLib.EllFq.frob W L (rsHom W L r s P) = rsHom W L r s (RPLib.EllFq.frob W L P)
  rw [rsHom_apply, rsHom_apply, map_add, map_zsmul, map_zsmul]

lemma frob_mem_endFq : piE W L ∈ endFq W L := by
  have h := rsHom_mem_endFq (W := W) (L := L) 0 1
  have he : rsE W L 0 1 = piE W L := rsHom_zero_one
  rwa [he] at h

lemma intCast_eq_rsHom (r : ℤ) : (r : AddMonoid.End (Pt W L)) = rsE W L r 0 :=
  AddMonoidHom.ext fun P => by
    show r • P = rsHom W L r 0 P
    rw [rsHom_apply, zero_smul, add_zero]

lemma one_sub_frob_eq : (1 : AddMonoid.End (Pt W L)) - piE W L = rsE W L 1 (-1) :=
  AddMonoidHom.ext fun P => by
    show P - RPLib.EllFq.frob W L P = rsHom W L 1 (-1) P
    rw [rsHom_apply, one_smul, neg_one_smul, ← sub_eq_add_neg]

/-! ### `E[n]` -/

lemma torsLin_mul (φ ψ : AddMonoid.End (Pt W L)) (n : ℕ) [NeZero n] :
    torsLin (φ * ψ) n = torsLin φ n * torsLin ψ n :=
  LinearMap.ext fun _ => Subtype.ext rfl

lemma torsLin_add (φ ψ : AddMonoid.End (Pt W L)) (n : ℕ) [NeZero n] :
    torsLin (φ + ψ) n = torsLin φ n + torsLin ψ n :=
  LinearMap.ext fun _ => Subtype.ext rfl

lemma torsLin_sub (φ ψ : AddMonoid.End (Pt W L)) (n : ℕ) [NeZero n] :
    torsLin (φ - ψ) n = torsLin φ n - torsLin ψ n :=
  LinearMap.ext fun _ => Subtype.ext rfl

lemma torsLin_one (n : ℕ) [NeZero n] :
    torsLin (1 : AddMonoid.End (Pt W L)) n = LinearMap.id :=
  LinearMap.ext fun _ => Subtype.ext rfl

lemma torsLin_intCast (r : ℤ) (n : ℕ) [NeZero n] :
    torsLin (r : AddMonoid.End (Pt W L)) n =
      (r : ZMod n) • (1 : Module.End (ZMod n) (RPLib.Torsion.tors (W.baseChange L) n)) := by
  rw [intCast_eq_rsHom, torsLin_rs, Int.cast_zero, zero_smul, add_zero]
  rfl

lemma torsLin_lin (a b : ℤ) (φ : AddMonoid.End (Pt W L)) (n : ℕ) [NeZero n] :
    torsLin ((a : AddMonoid.End (Pt W L)) + (b : AddMonoid.End (Pt W L)) * φ) n =
      (a : ZMod n) • LinearMap.id + (b : ZMod n) • torsLin φ n := by
  rw [torsLin_add, torsLin_mul, torsLin_intCast, torsLin_intCast, smul_mul_assoc, one_mul]
  rfl

lemma det_eq_deg {φ : AddMonoid.End (Pt W L)} (hφ : φ ∈ endRing W L) (n : ℕ) [NeZero n]
    (hn : (n : L) ≠ 0) : LinearMap.det (torsLin φ n) = (deg φ : ZMod n) := by
  by_cases h0 : φ = 0
  · have h1 : LinearMap.det (torsLin (0 : AddMonoid.End (Pt W L)) n) = 0 := det_torsLin_zero n hn
    have h2 : deg (0 : AddMonoid.End (Pt W L)) = 0 := deg_zero
    rw [h0, h1, h2, Nat.cast_zero]
  · obtain ⟨Φ, hΦ⟩ := hφ
    obtain ⟨ψ, e, hP⟩ := exists_isPull_of_hE Φ φ hΦ h0
    exact hP.det_eq_deg n hn

/-- The trace of an endomorphism, `tr φ = 1 + deg φ - deg (1 - φ)`. -/
noncomputable def tr (φ : AddMonoid.End (Pt W L)) : ℤ :=
  1 + deg φ - deg ((1 : AddMonoid.End (Pt W L)) - φ : AddMonoid.End (Pt W L))

lemma trace_eq_tr {φ : AddMonoid.End (Pt W L)} (hφ : φ ∈ endRing W L) (n : ℕ) [NeZero n]
    (hn : (n : L) ≠ 0) : LinearMap.trace (ZMod n) _ (torsLin φ n) = (tr φ : ZMod n) := by
  obtain ⟨b⟩ := exists_basis W L n hn
  have h1 := det_eq_deg (sub_mem (one_mem _) hφ) n hn
  have h2 := det_eq_deg hφ n hn
  have h3 := det_smul_id_add_smul b (torsLin φ n) 1 (-1)
  rw [one_smul, neg_one_smul, ← sub_eq_add_neg] at h3
  rw [torsLin_sub, torsLin_one, h3, h2] at h1
  rw [tr]
  push_cast
  linear_combination -h1

/-- **`deg (a + b φ) = a² + a b tr φ + b² deg φ`.** -/
theorem deg_lin (a b : ℤ) {φ : AddMonoid.End (Pt W L)} (hφ : φ ∈ endRing W L) :
    (deg ((a : AddMonoid.End (Pt W L)) + (b : AddMonoid.End (Pt W L)) * φ) : ℤ) =
      a ^ 2 + a * b * tr φ + b ^ 2 * deg φ := by
  refine int_eq_of_zmod F L fun n _ hn => ?_
  obtain ⟨b'⟩ := exists_basis W L n hn
  have hm : (a : AddMonoid.End (Pt W L)) + (b : AddMonoid.End (Pt W L)) * φ ∈ endRing W L :=
    add_mem (intCast_mem _ a) (mul_mem (intCast_mem _ b) hφ)
  have h1 := det_eq_deg hm n hn
  rw [torsLin_lin, det_smul_id_add_smul b', trace_eq_tr hφ n hn, det_eq_deg hφ n hn] at h1
  push_cast
  linear_combination -h1

/-- **`deg` is multiplicative.** -/
theorem deg_mul {φ ψ : AddMonoid.End (Pt W L)} (hφ : φ ∈ endRing W L) (hψ : ψ ∈ endRing W L) :
    deg (φ * ψ) = deg φ * deg ψ :=
  nat_eq_of_zmod L fun n _ hn => by
    rw [← det_eq_deg (mul_mem hφ hψ) n hn, torsLin_mul, map_mul, det_eq_deg hφ n hn,
      det_eq_deg hψ n hn, Nat.cast_mul]

/-- **`tr φ² ≤ 4 deg φ`.** -/
theorem tr_sq_le {φ : AddMonoid.End (Pt W L)} (hφ : φ ∈ endRing W L) :
    tr φ ^ 2 ≤ 4 * (deg φ : ℤ) := by
  have h := deg_lin (-tr φ) 2 hφ
  have h' : (deg (((-tr φ : ℤ) : AddMonoid.End (Pt W L)) + ((2 : ℤ) : AddMonoid.End (Pt W L)) * φ)
      : ℤ) = 4 * deg φ - tr φ ^ 2 := by
    rw [h]; ring
  have h0 : (0 : ℤ) ≤ (deg (((-tr φ : ℤ) : AddMonoid.End (Pt W L)) +
      ((2 : ℤ) : AddMonoid.End (Pt W L)) * φ) : ℤ) := Int.natCast_nonneg _
  linarith

/-- An endomorphism vanishing on every `E[n]` (`n` prime to `p`) is zero. -/
lemma eq_zero_of_torsLin {φ : AddMonoid.End (Pt W L)} (hφ : φ ∈ endRing W L)
    (h : ∀ (n : ℕ) [NeZero n], (n : L) ≠ 0 → torsLin φ n = 0) : φ = 0 := by
  by_contra h0
  obtain ⟨Φ, hΦ⟩ := hφ
  obtain ⟨ψ, e, hP⟩ := exists_isPull_of_hE Φ φ hΦ h0
  have hfin := hP.finite_ker
  obtain ⟨ℓ, hℓ1, hℓ⟩ :=
    Nat.exists_infinite_primes ({P : Pt W L | φ P = 0}.ncard + ringChar L + 1)
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hL : (ℓ : L) ≠ 0 := by
    intro hz
    have hd := (ringChar.spec L ℓ).mp hz
    rcases (Nat.dvd_prime hℓ).mp hd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · omega
  have hsub : ((RPLib.Torsion.tors (W.baseChange L) ℓ : AddSubgroup (Pt W L)) : Set (Pt W L)) ⊆
      {P : Pt W L | φ P = 0} := by
    intro P hP'
    exact congrArg Subtype.val (LinearMap.congr_fun (h ℓ hL) ⟨P, hP'⟩)
  have hc := Set.ncard_le_ncard hsub hfin
  have hcard : Nat.card (RPLib.Torsion.tors (W.baseChange L) ℓ) = ℓ ^ 2 :=
    RPLib.Torsion.card_tors ℓ hL
  have he : Nat.card (RPLib.Torsion.tors (W.baseChange L) ℓ) =
      ((RPLib.Torsion.tors (W.baseChange L) ℓ : AddSubgroup (Pt W L)) : Set (Pt W L)).ncard :=
    Nat.card_coe_set_eq _
  have hle : ℓ ≤ ℓ ^ 2 := Nat.le_self_pow (by norm_num) ℓ
  omega

/-- **Cayley–Hamilton**: `φ² - tr φ · φ + deg φ = 0` for every endomorphism. -/
theorem ch {φ : AddMonoid.End (Pt W L)} (hφ : φ ∈ endRing W L) :
    φ * φ - (tr φ : AddMonoid.End (Pt W L)) * φ + ((deg φ : ℤ) : AddMonoid.End (Pt W L)) = 0 := by
  have hm : φ * φ - (tr φ : AddMonoid.End (Pt W L)) * φ +
      ((deg φ : ℤ) : AddMonoid.End (Pt W L)) ∈ endRing W L :=
    add_mem (sub_mem (mul_mem hφ hφ) (mul_mem (intCast_mem _ _) hφ)) (intCast_mem _ _)
  refine eq_zero_of_torsLin hm fun n _ hn => ?_
  obtain ⟨b⟩ := exists_basis W L n hn
  have hc := sq_eq_trace_smul_sub b (torsLin φ n)
  rw [trace_eq_tr hφ n hn, det_eq_deg hφ n hn, sq] at hc
  rw [torsLin_add, torsLin_sub, torsLin_mul, torsLin_mul, torsLin_intCast, torsLin_intCast, hc,
    smul_mul_assoc, one_mul, Int.cast_natCast]
  abel

/-- **No zero divisors**: a nonzero endomorphism is surjective. -/
lemma eq_zero_of_mul_eq_zero {φ ψ : AddMonoid.End (Pt W L)} (hψ : ψ ∈ endRing W L)
    (hψ0 : ψ ≠ 0) (h : φ * ψ = 0) : φ = 0 := by
  obtain ⟨Ψ, hΨ⟩ := hψ
  obtain ⟨ρ, e, hP⟩ := exists_isPull_of_hE Ψ ψ hΨ hψ0
  refine AddMonoidHom.ext fun P => ?_
  obtain ⟨Q, rfl⟩ := hP.surjective P
  exact congrArg (fun f : AddMonoid.End (Pt W L) => f Q) h

lemma mul_eq_zero_iff {φ ψ : AddMonoid.End (Pt W L)} (hψ : ψ ∈ endRing W L) :
    φ * ψ = 0 ↔ φ = 0 ∨ ψ = 0 := by
  constructor
  · intro h
    by_cases hψ0 : ψ = 0
    · exact Or.inr hψ0
    · exact Or.inl (eq_zero_of_mul_eq_zero hψ hψ0 h)
  · rintro (h | h)
    · rw [h, zero_mul]
    · rw [h, mul_zero]

/-- `ℤ → End(E)` is injective. -/
lemma intCast_eq_zero {r : ℤ} (h : (r : AddMonoid.End (Pt W L)) = 0) : r = 0 := by
  have h1 : (deg (r : AddMonoid.End (Pt W L)) : ℤ) =
      r ^ 2 + RPLib.EllFq.trace W * r * 0 + (Fintype.card F : ℤ) * 0 ^ 2 := by
    rw [intCast_eq_rsHom]; exact deg_rsHom r 0
  have h2 : deg (0 : AddMonoid.End (Pt W L)) = 0 := deg_zero
  rw [h, h2, Nat.cast_zero] at h1
  have h3 : r ^ 2 = 0 := by linarith
  exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h3

/-- Torsion-freeness: `r φ = 0` with `r ≠ 0` forces `φ = 0`. -/
lemma eq_zero_of_intCast_mul {r : ℤ} (hr : r ≠ 0) {φ : AddMonoid.End (Pt W L)}
    (h : (r : AddMonoid.End (Pt W L)) * φ = 0) : φ = 0 := by
  have h' : φ * (r : AddMonoid.End (Pt W L)) = 0 := by
    rw [← (Int.cast_commute r φ).eq]; exact h
  exact eq_zero_of_mul_eq_zero (intCast_mem _ r) (fun h0 => hr (intCast_eq_zero h0)) h'

/-! ### Frobenius -/

theorem deg_frob' : deg (piE W L) = Fintype.card F := deg_frob

/-- **`tr π = a = q + 1 - #W(F)`.** -/
theorem tr_frob : tr (piE W L) = RPLib.EllFq.trace W := by
  have h1 : deg ((1 : AddMonoid.End (Pt W L)) - piE W L : AddMonoid.End (Pt W L)) =
      RPLib.EllFq.numPoints W := by
    rw [one_sub_frob_eq]; exact deg_one_sub_frob
  unfold tr
  rw [h1, deg_frob', RPLib.EllFq.trace_eq]
  ring

/-- **`π² - a π + q = 0`** in `End(E)`. -/
theorem frob_ch :
    piE W L * piE W L - (RPLib.EllFq.trace W : AddMonoid.End (Pt W L)) * piE W L +
      ((Fintype.card F : ℤ) : AddMonoid.End (Pt W L)) = 0 := by
  have h := ch (endFq_le frob_mem_endFq : piE W L ∈ endRing W L)
  rwa [tr_frob, deg_frob'] at h

end Endo

end RPLib.DWS


