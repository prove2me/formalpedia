-- Prove2me | Definitions.Def_RPLib_S4_CDPack14c
-- name    : RPLib_S4_CDPack14c
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:43:23.671193+00:00
-- url     : https://prove2.me/theorems/057374af-a70d-4fed-9709-f6d339e81487
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 14c of 71
-- statement:
--   Part 14c of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CP4a_Bridge`: S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack11
import Definitions.Def_RPLib_S4_CDPack14
import Definitions.Def_RPLib_S4_CDPack14b

/-!
# Curve-duality library package, part 14c of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CP4a_Bridge`: S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CP4a_Bridge =====
section

/-!
# S4-CP4a, part c: the trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)` (Core B as a hypothesis)

* `tatePicN`: the CoreA Tate coordinates at level `n` as a map `(ℤ/l^n)^s → Pic⁰(X̄)[l^n]`; bijective when
  `A = Pic(X̄)[l^∞]` is divisible (CB1), and `π` acts by `M mod l^n` (`tatePic_frob`).
* `CoreBHyp`: Core B (CB1 + CB2) as an explicit `Prop`: `A` is `l`-divisible, and every CoreA Tate matrix of `π`
  has characteristic polynomial `Π (X - ω_i) ∈ ℤ[X]` for the zeta roots `ω`.
* `trace_of_picEquiv`: for any `ZMod (l^n)`-module `H` with an additive `Φ : H ≃ Pic⁰(X̄)[l^n]` such that
  `π (Φ (f x)) = q Φ x`, `Tr(f^m | H) = 1 + q^m - N_m` (via `exists_tateEquivN`, `coords_key`, `trace_pow_of_coords`).
* `trace_frobPar` (review R4): with the F-equivariant Kummer isomorphism `H¹_par ≃ Pic⁰(X̄)[l^n]` (S4-Kummer),
  `Tr(F^m | H¹_par(Ū, ℤ/l^n)) = 1 + q^m - N_m` for the geometric Frobenius `F`, all `m ≥ 1`.
-/

set_option autoImplicit false

open Polynomial Matrix

namespace RamanujanPetersson.CP4a

open Places ZetaSB PicDescent RR CoreA CurveCoh Kummer

section LinAlg

variable {R : Type*} [CommRing R] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

theorem conj_pow' (e : M₁ ≃ₗ[R] M₂) (f : Module.End R M₁) (m : ℕ) : e.conj (f ^ m) = e.conj f ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Module.End.one_eq_id, LinearEquiv.conj_id]; rfl
  | succ m ih => rw [pow_succ, Module.End.mul_eq_comp, LinearEquiv.conj_comp, ih, pow_succ, Module.End.mul_eq_comp]

theorem toLin'_pow' {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n R) (m : ℕ) :
    Matrix.toLin' (G ^ m) = Matrix.toLin' G ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, Matrix.toLin'_one]; rfl
  | succ m ih => rw [pow_succ, Matrix.toLin'_mul, ih, pow_succ, Module.End.mul_eq_comp]

end LinAlg

section Abstract

variable {H : Type*} [AddCommGroup H] {L : ℕ} [Module (ZMod L) H] {s : ℕ}

/-- **Trace from coordinates.** If `Ψ : H ≃ (ℤ/L)^s` and `Mn (Ψ (f x)) = q Ψ x` (so `f` is `q Mn⁻¹` in
coordinates), `χ_Mn = P0 = Π (X - c_i)`, `0 ∉ c`, `{q / c_i} = {c_i}`, then `Tr(f^(k+1))` and `Σ c_i^(k+1)`
are one integer. -/
theorem trace_pow_of_coords [Fact (1 < L)] (Ψ : H ≃+ (Fin s → ZMod L)) (f : Module.End (ZMod L) H)
    (Mn : Matrix (Fin s) (Fin s) (ZMod L)) (q0 : ℕ) (hq : IsUnit (q0 : ZMod L))
    (hkey : ∀ x, Mn *ᵥ Ψ (f x) = (q0 : ZMod L) • Ψ x) (P0 : ℤ[X]) (hP0 : P0.Monic) (c : Multiset ℂ)
    (hc : P0.map (Int.castRingHom ℂ) = (c.map fun r => X - Polynomial.C r).prod)
    (hM : Mn.charpoly = P0.map (Int.castRingHom (ZMod L))) (h0 : (0 : ℂ) ∉ c)
    (hfe : c.map (fun x => (q0 : ℂ) / x) = c) :
    ∃ sk : ℕ → ℤ, ∀ k : ℕ, LinearMap.trace (ZMod L) H (f ^ (k + 1)) = (sk k : ZMod L) ∧
      (c.map (· ^ (k + 1))).sum = (sk k : ℂ) := by
  classical
  let ΨL : H ≃ₗ[ZMod L] (Fin s → ZMod L) := Ψ.toLinearEquiv (ZMod.map_smul Ψ)
  have : Module.Free (ZMod L) H := Module.Free.of_equiv ΨL.symm
  have : Module.Finite (ZMod L) H := Module.Finite.equiv ΨL.symm
  obtain ⟨G, hG⟩ : ∃ G, G = LinearMap.toMatrix' (ΨL.conj f) := ⟨_, rfl⟩
  have hGv : ∀ v, G *ᵥ v = Ψ (f (Ψ.symm v)) := fun v => by
    rw [← Matrix.toLin'_apply, hG, Matrix.toLin'_toMatrix', LinearEquiv.conj_apply_apply]
    rfl
  have hMG : Mn * G = (q0 : ZMod L) • 1 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hGv, hkey, AddEquiv.apply_symm_apply,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨u, hu⟩ := hq
  have hGM : G * Mn = (q0 : ZMod L) • 1 := by
    have h1 : Mn * (((u⁻¹ : (ZMod L)ˣ) : ZMod L) • G) = 1 := by
      rw [Matrix.mul_smul, hMG, ← hu, smul_smul, Units.inv_mul, one_smul]
    have h2 := (mul_eq_one_comm (a := Mn)).mp h1
    have h3 := congrArg (fun X => (u : ZMod L) • X) h2
    simp only [Matrix.smul_mul, smul_smul, Units.mul_inv, one_smul] at h3
    rw [h3, hu]
  obtain ⟨-, sk, hs⟩ := exists_trace_pow_frob Mn G q0 hGM ⟨u, hu⟩ P0 hP0 c hc hM h0 hfe
  refine ⟨sk, fun k => ⟨?_, (hs k).2.2⟩⟩
  rw [← LinearMap.trace_conj' _ ΨL, conj_pow', ← Matrix.toLin'_toMatrix' (ΨL.conj f), ← hG, ← toLin'_pow',
    Matrix.trace_toLin'_eq, (hs k).2.1]

/-- Transport of `π (Φ (f x)) = q Φ x` and `π (E v) = E (Mn v)` to coordinates: `Mn (Ψ (f x)) = q Ψ x`. -/
theorem coords_key {X G : Type*} [AddCommGroup X] [AddCommGroup G] {P : AddSubgroup G}
    (Φ : X ≃+ P) (E : (Fin s → ZMod L) ≃+ P) (f : X → X) (π : G →+ G) (Mn : Matrix (Fin s) (Fin s) (ZMod L))
    (q : ℕ) (hΦ : ∀ x, π (Φ (f x) : G) = q • (Φ x : G)) (hE : ∀ v, π (E v : G) = (E (Mn *ᵥ v) : G)) (x : X) :
    Mn *ᵥ (Φ.trans E.symm) (f x) = (q : ZMod L) • (Φ.trans E.symm) x := by
  rw [Nat.cast_smul_eq_nsmul]
  apply E.injective
  apply Subtype.ext
  rw [← hE, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, map_nsmul, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, AddSubgroup.coe_nsmul]
  exact hΦ x

end Abstract

section Tate

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable {Ω : Type*} [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable (hk : constField Fq F = ⊥)
variable {l : ℕ} [Fact l.Prime] {k0 : ℕ}
  (hdiv : ∀ y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range, ∃ z, l • z = y) {s : ℕ}
  (b1 : Fin s → (smulHom (Aℓ Ω hk l) (l ^ k0)).range) (hb1 : ∀ i, l • b1 i = 0)

/-- The level-`n` Tate coordinates, as a map into `Pic(X̄)`. -/
noncomputable def tatePic (n : ℕ) : (Fin s → ZMod (l ^ n)) →+ PicBar Ω hk :=
  (AddCommGroup.primaryComponent (PicBar Ω hk) l).subtype.comp
    (((smulHom (Aℓ Ω hk l) (l ^ k0)).range.subtype).comp (tateMap hdiv b1 hb1 n))

theorem tatePic_mem (n : ℕ) (cb : Fin s → ZMod (l ^ n)) :
    tatePic hk hdiv b1 hb1 n cb ∈ PicBar0N Ω hk (l ^ n) := by
  refine ⟨primary_le_PicBar0 hk (Fact.out : l.Prime).ne_zero (tateMap hdiv b1 hb1 n cb : Aℓ Ω hk l).2, ?_⟩
  have h := congrArg (fun y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range => ((y : Aℓ Ω hk l) : PicBar Ω hk))
    (tateMap_smul_eq_zero hdiv b1 hb1 n cb)
  simpa [tatePic] using h

/-- Level-`n` Tate coordinates of `Pic⁰(X̄)[l^n]`. -/
noncomputable def tatePicN (n : ℕ) : (Fin s → ZMod (l ^ n)) →+ PicBar0N Ω hk (l ^ n) :=
  (tatePic hk hdiv b1 hb1 n).codRestrict _ (tatePic_mem hk hdiv b1 hb1 n)

theorem coe_tatePicN (n : ℕ) (cb : Fin s → ZMod (l ^ n)) :
    (tatePicN hk hdiv b1 hb1 n cb : PicBar Ω hk) = tatePic hk hdiv b1 hb1 n cb := rfl

/-- With `A` divisible (`D = A`), the Tate coordinates give `(ℤ/l^n)^s ≅ Pic⁰(X̄)[l^n]`. -/
theorem tatePicN_bijective (hinj : ∀ N, Function.Injective (tateMap hdiv b1 hb1 N))
    (hsurj : ∀ N (x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range), l ^ N • x = 0 → ∃ cb, tateMap hdiv b1 hb1 N cb = x)
    (htop : (smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤) (n : ℕ) :
    Function.Bijective (tatePicN hk hdiv b1 hb1 n) := by
  refine ⟨fun a b hab => hinj n ?_, fun z => ?_⟩
  · have h := congrArg (fun z : PicBar0N Ω hk (l ^ n) => (z : PicBar Ω hk)) hab
    exact Subtype.ext (Subtype.ext h)
  · obtain ⟨-, hzn⟩ : (z : PicBar Ω hk) ∈ PicBar0 Ω hk ∧ l ^ n • (z : PicBar Ω hk) = 0 := z.2
    have hA : (z : PicBar Ω hk) ∈ AddCommGroup.primaryComponent (PicBar Ω hk) l := ⟨n, hzn⟩
    have hy : (⟨z, hA⟩ : Aℓ Ω hk l) ∈ (smulHom (Aℓ Ω hk l) (l ^ k0)).range := htop ▸ AddSubgroup.mem_top _
    obtain ⟨cb, hcb⟩ := hsurj n ⟨⟨z, hA⟩, hy⟩ (Subtype.ext (Subtype.ext (by simpa using hzn)))
    refine ⟨cb, Subtype.ext ?_⟩
    rw [coe_tatePicN]
    simp only [tatePic, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, hcb]

/-- `π` acts on the level-`n` coordinates by `M mod l^n`. -/
theorem tatePic_frob {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (hM : IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M) (n : ℕ) (cb : Fin s → ZMod (l ^ n)) :
    piBar Ω hk (tatePic hk hdiv b1 hb1 n cb) = tatePic hk hdiv b1 hb1 n (M.map (PadicInt.toZModPow n) *ᵥ cb) := by
  have h := congrArg (fun y : (smulHom (Aℓ Ω hk l) (l ^ k0)).range => ((y : Aℓ Ω hk l) : PicBar Ω hk)) (hM n cb)
  exact h

/-- With `A` divisible: an additive `(ℤ/l^n)^s ≃ Pic⁰(X̄)[l^n]` on which `π` acts by `M mod l^n`. -/
theorem exists_tateEquiv (hinj : ∀ N, Function.Injective (tateMap hdiv b1 hb1 N))
    (hsurj : ∀ N (x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range), l ^ N • x = 0 → ∃ cb, tateMap hdiv b1 hb1 N cb = x)
    (htop : (smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤) {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (hM : IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M) (n : ℕ) :
    ∃ E : (Fin s → ZMod (l ^ n)) ≃+ PicBar0N Ω hk (l ^ n), ∀ v,
      piBar Ω hk (E v : PicBar Ω hk) = (E (M.map (PadicInt.toZModPow n) *ᵥ v) : PicBar Ω hk) :=
  ⟨AddEquiv.ofBijective _ (tatePicN_bijective hk hdiv b1 hb1 hinj hsurj htop n),
    fun v => tatePic_frob hk hdiv b1 hb1 hM n v⟩

/-- `exists_tateEquiv` at a level `N = l ^ n`, with the reduced matrix's characteristic polynomial. -/
theorem exists_tateEquivN (hinj : ∀ N, Function.Injective (tateMap hdiv b1 hb1 N))
    (hsurj : ∀ N (x : (smulHom (Aℓ Ω hk l) (l ^ k0)).range), l ^ N • x = 0 → ∃ cb, tateMap hdiv b1 hb1 N cb = x)
    (htop : (smulHom (Aℓ Ω hk l) (l ^ k0)).range = ⊤) {M : Matrix (Fin s) (Fin s) ℤ_[l]}
    (hM : IsTateMat hdiv b1 hb1 (endD (piA Ω hk l) (l ^ k0)) M) (n N : ℕ) (hN : N = l ^ n) (P0 : ℤ[X])
    (hMP : M.charpoly = P0.map (Int.castRingHom ℤ_[l])) :
    ∃ (E : (Fin s → ZMod N) ≃+ PicBar0N Ω hk N) (Mn : Matrix (Fin s) (Fin s) (ZMod N)),
      Mn.charpoly = P0.map (Int.castRingHom (ZMod N)) ∧
      ∀ v, piBar Ω hk (E v : PicBar Ω hk) = (E (Mn *ᵥ v) : PicBar Ω hk) := by
  subst hN
  obtain ⟨E, hE⟩ := exists_tateEquiv hk hdiv b1 hb1 hinj hsurj htop hM n
  refine ⟨E, M.map (PadicInt.toZModPow n), ?_, hE⟩
  rw [Matrix.charpoly_map, hMP, Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

end Tate

section Frob

variable {Fq : Type} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable (hk : constField Fq F = ⊥)

/-- **Core B as an explicit hypothesis** (CB1 + CB2 of `S4_COREB_ROUTE.md`): `A = Pic(X̄)[l^∞]` is `l`-divisible,
and for every CoreA Tate basis (injective at every level) the matrix `M` of the arithmetic Frobenius `π` has
`χ_M = Π (X - ω_i)` with integer coefficients, where `ω` are the zeta roots (`N_m = 1 + q^m - Σ ω_i^m`,
`#ω ≤ 2g`, which pins `ω` down). -/
def CoreBHyp (l : ℕ) [Fact l.Prime] : Prop :=
  (∀ y : Aℓ (AlgebraicClosure F) hk l, ∃ z, l • z = y) ∧
  ∀ (k0 : ℕ) (hdiv : ∀ y : (smulHom (Aℓ (AlgebraicClosure F) hk l) (l ^ k0)).range, ∃ z, l • z = y)
    (b1 : Fin (2 * genusF Fq F) → (smulHom (Aℓ (AlgebraicClosure F) hk l) (l ^ k0)).range)
    (hb1 : ∀ i, l • b1 i = 0) (M : Matrix (Fin (2 * genusF Fq F)) (Fin (2 * genusF Fq F)) ℤ_[l]),
    (∀ N, Function.Injective (tateMap hdiv b1 hb1 N)) →
    IsTateMat hdiv b1 hb1 (endD (piA (AlgebraicClosure F) hk l) (l ^ k0)) M →
    ∀ c : Multiset ℂ, Multiset.card c ≤ 2 * genusF Fq F →
      (∀ m : ℕ, 1 ≤ m → (numPoints Fq F m : ℂ) = 1 + (Fintype.card Fq : ℂ) ^ m - (c.map (· ^ m)).sum) →
      ∃ P0 : ℤ[X], P0.map (Int.castRingHom ℂ) = (c.map fun r => X - Polynomial.C r).prod ∧
        M.charpoly = P0.map (Int.castRingHom ℤ_[l])

/-- **Trace from a Frobenius-equivariant `H ≃ Pic⁰(X̄)[l^n]`** (Core B as a hypothesis): if `π (Φ (f x)) = q Φ x`,
then `Tr(f^m | H) = 1 + q^m - N_m` for every `m ≥ 1`. -/
theorem trace_of_picEquiv (l n : ℕ) [Fact l.Prime] (hn : 0 < n) {N : ℕ} (hN : N = l ^ n)
    (hlq : ¬ l ∣ Fintype.card Fq) (hB : CoreBHyp hk l) {H : Type*} [AddCommGroup H] [Module (ZMod N) H]
    (f : Module.End (ZMod N) H) (Φ : H ≃+ PicBar0N (AlgebraicClosure F) hk N)
    (hΦ : ∀ x, piBar (AlgebraicClosure F) hk (Φ (f x) : PicBar (AlgebraicClosure F) hk) =
      Fintype.card Fq • (Φ x : PicBar (AlgebraicClosure F) hk)) (m : ℕ) (hm : 1 ≤ m) :
    LinearMap.trace (ZMod N) H (f ^ m) =
      (((1 + (Fintype.card Fq : ℤ) ^ m - (numPoints Fq F m : ℤ)) : ℤ) : ZMod N) := by
  have : Fact (1 < N) := ⟨hN ▸ Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
  have hqu : IsUnit ((Fintype.card Fq : ℕ) : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime, hN]
    exact Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hlq))
  obtain ⟨k0, hdiv, b1, hb1, M, hTate, hM, -, -, htopiff, -, -⟩ :=
    tate_module_Pic (Ω := AlgebraicClosure F) hk l hlq
  obtain ⟨c, hcard, -, -, hNm, h0, -, hfe, -⟩ := zeta_RH_FE hk
  obtain ⟨P0, hP0c, hMP⟩ := hB.2 k0 hdiv b1 hb1 M (fun j => (hTate j).1) hM c hcard.le hNm
  have hP0 : P0.Monic := by
    refine Polynomial.monic_of_injective (f := Int.castRingHom ℂ) Int.cast_injective ?_
    rw [hP0c]
    exact monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  obtain ⟨E, Mn, hMn, hE⟩ := exists_tateEquivN hk hdiv b1 hb1 (fun j => (hTate j).1) (fun j => (hTate j).2)
    (htopiff.mpr hB.1) hM n N hN P0 hMP
  obtain ⟨sk, hs⟩ := trace_pow_of_coords (Φ.trans E.symm) f Mn _ hqu
    (coords_key Φ E f (piBar (AlgebraicClosure F) hk) Mn _ hΦ hE) P0 hP0 c hP0c hMn h0 hfe
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [(hs k).1]
  have h := hNm (k + 1) (by omega)
  rw [(hs k).2] at h
  have h' : ((sk k : ℤ) : ℂ) = ((1 + (Fintype.card Fq : ℤ) ^ (k + 1) - (numPoints Fq F (k + 1) : ℤ) : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  have h'' : sk k = 1 + (Fintype.card Fq : ℤ) ^ (k + 1) - (numPoints Fq F (k + 1) : ℤ) := by exact_mod_cast h'
  rw [h'']

variable {p e : ℕ} [Fact p.Prime] [CharP F p] (hq : Fintype.card Fq = p ^ e) (he : 0 < e)
variable {N : ℕ} [NeZero N] (hNf : IsUnit (N : Rfin Fq F)) (hNi : IsUnit (N : Rinf Fq F))
  {ζ : maxUnram (Rfin Fq F) F} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ pi1geo (Rfin Fq F) F (Fintype.card Fq), σ ζ = ζ) {S : Type}
  (D : BdryData (Rfin Fq F) F (Fintype.card Fq) (Rinf Fq F) S)
  (hDB : ∀ Q, D.B Q ↔ IsBdryPrime (Rfin Fq F) F (Rinf Fq F) Q) (hlift : BdryLift (Rfin Fq F) F (Rinf Fq F))
  (hNF : (N : F) ≠ 0)

/-- The geometric Frobenius `F` on `H¹_par(Ū, ℤ/N) = H¹(X̄, ℤ/N)`. -/
noncomputable def frobPar (φ : Pi1 (Rfin Fq F) F) :
    Module.End (ZMod N) (curveH1par (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) D) :=
  (geomFrobH1 (Fintype.card Fq) (triv F (maxUnram (Rfin Fq F) F) N) φ).restrict
    (fun _ hx => geomFrobH1_mem_curveH1par _ D φ hx)

include hq he hNf hNi hζ hζΓ hDB hlift hNF in
set_option maxHeartbeats 1000000 in
/-- **Trace of geometric Frobenius on `H¹(X̄, ℤ/l^n)`** (Core B as a hypothesis; review R4):
`Tr(F^m | H¹_par) = 1 + q^m - N_m` for every `m ≥ 1`. (Instance unification on `H¹_par` is slow, about 14 s.) -/
theorem trace_frobPar (l n : ℕ) [Fact l.Prime] (hn : 0 < n) (hN : N = l ^ n) (hlq : ¬ l ∣ Fintype.card Fq)
    (hB : CoreBHyp hk l) (φ : Pi1 (Rfin Fq F) F) (hφ : IsFrobLift (Rfin Fq F) F (Fintype.card Fq) φ)
    (m : ℕ) (hm : 1 ≤ m) :
    LinearMap.trace (ZMod N) _ (frobPar D φ ^ m) =
      (((1 + (Fintype.card Fq : ℤ) ^ m - (numPoints Fq F m : ℤ)) : ℤ) : ZMod N) :=
  (exists_kummerPicEquiv_frob hk hq he hNf hNi hζ hζΓ D hDB hlift hNF).elim fun Φ hΦ =>
    trace_of_picEquiv hk l n hn hN hlq hB (frobPar D φ) Φ (fun x => hΦ.2 φ hφ x.1 x.2) m hm

end Frob

end RamanujanPetersson.CP4a

end


