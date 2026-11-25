-- Prove2me | Definitions.Def_RPLib_FX_EtP1_17
-- name    : RPLib_FX_EtP1_17
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T09:14:25.458122+00:00
-- url     : https://prove2.me/theorems/46287afb-4a42-597b-ba0a-9ee61c0b10ab
-- title:
--   Étale cohomology of the projective line, library file 17 of 34
-- statement:
--   File 17 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_GmKc`: S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)
--   * `S4.Def_RP_EtCompact_KumForm`: S4-EtCompact, part 56: Kummer arithmetic for the local step (F7e1 of plan v5)
--   * `S4.Def_RP_EtCompact_KumDec`: S4-EtCompact, part 46: every finite-image Galois character is a sum of Kummer characters (F3 of plan v5)
--   * `S4.Def_RP_EtCompact_FixFld`: S4-EtCompact, part 47: elements fixed by the stabiliser of an embedding (F4a of plan v5)
--   * `S4.Def_RP_EtCompact_KDecAt`: S4-EtCompact, part 58: Kummer decomposition of the obstruction at a fibre point (F7e3 of plan v5)
--   * `S4.Def_RP_EtCompact_LFq`: S4-EtCompact, part 57: local factorisation through a point (F7e2 of plan v5)
--   * `S4.Def_RP_EtCompact_Step`: S4-EtCompact, part 59: the local step at a point (F7e4 of plan v5)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_38

/-!
# Étale cohomology of the projective line, library file 17 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_GmKc`: S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)
* `S4.Def_RP_EtCompact_KumForm`: S4-EtCompact, part 56: Kummer arithmetic for the local step (F7e1 of plan v5)
* `S4.Def_RP_EtCompact_KumDec`: S4-EtCompact, part 46: every finite-image Galois character is a sum of Kummer characters (F3 of plan v5)
* `S4.Def_RP_EtCompact_FixFld`: S4-EtCompact, part 47: elements fixed by the stabiliser of an embedding (F4a of plan v5)
* `S4.Def_RP_EtCompact_KDecAt`: S4-EtCompact, part 58: Kummer decomposition of the obstruction at a fibre point (F7e3 of plan v5)
* `S4.Def_RP_EtCompact_LFq`: S4-EtCompact, part 57: local factorisation through a point (F7e2 of plan v5)
* `S4.Def_RP_EtCompact_Step`: S4-EtCompact, part 59: the local step at a point (F7e4 of plan v5)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtCompact_GmKc =====
section

/-!
# S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)

`R = k[X]_X`, `K = k(X)`, `E = K_U = maxUnram R K`, `Γ = π₁(G_m)`, `N = lⁿ` invertible in `k`, `k` algebraically
closed, `γ ^ N = X`.

* `LX.exists_kchar_eq_one`: some `σ₁` has `kchar γ σ₁ = 1` (else `γ ^ l^(n-1) ∈ K` and `X` is an `l`-th power).
* `LX.hom_eq_kchar_smul`: every locally constant homomorphism `c : Γ → V` (`N • V = 0`) is
  `c σ = (kchar γ σ).val • c σ₁`.
* `LX.h1LinEquiv`: `H¹_cont(Γ, M) ≃ M` (trivial action, `N • M = 0`), evaluation at `σ₁`.
* **`Gm.nonempty_h1Equiv`**: `H^1(G_m, Λ) ≃+ Λ` for `lⁿ • Λ = 0`.
-/

set_option autoImplicit false

open Polynomial AlgebraicGeometry

noncomputable section

namespace RamanujanPetersson.EtCompact

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtSheaves.GenBr Kummer EtPi1

section Gen

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)}

end Gen

section Kc

variable {k : Type} [Field k] [IsAlgClosed k]

variable {N : ℕ} [NeZero N] {ζ : maxUnram (LX k) (RatFunc k)} (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))), σ ζ = ζ) {γ : (maxUnram (LX k) (RatFunc k))ˣ}
  (hγ : (γ : maxUnram (LX k) (RatFunc k)) ^ N = algebraMap (RatFunc k) _ RatFunc.X)
  {σ₁ : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k)))} (h1 : kchar hζ γ σ₁ = 1)
include hζΓ hγ h1

/-- `ZMod N`-valued locally constant homomorphisms vanishing at `σ₁` vanish. -/
theorem LX.zmod_hom_eq_zero (c : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) → ZMod N) (hc : IsLocallyConstant c)
    (hadd : ∀ σ τ, c (σ * τ) = c σ + c τ) (hc1 : c σ₁ = 0) : c = 0 := by
  obtain ⟨α, hα, hαc⟩ := exists_kchar_eq hζ hζΓ c hc hadd
  obtain ⟨m, hm⟩ := LX.exists_kchar_eq_nsmul hζ (fun σ => hζΓ σ (Subgroup.mem_top σ)) hγ hα
  have hm0 : (m : ZMod N) = 0 := by
    have h := hm σ₁
    rw [hαc, hc1, h1, nsmul_eq_mul, mul_one] at h
    exact h.symm
  funext σ
  show c σ = 0
  rw [← hαc σ, hm σ, nsmul_eq_mul, hm0, zero_mul]

/-- Finite coefficients killed by `N`. -/
theorem LX.fin_hom_eq_zero {M : Type} [AddCommGroup M] [Finite M] (hM : ∀ x : M, N • x = 0)
    (c : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) → M) (hlc : IsLocallyConstant c)
    (hadd : ∀ g h, c (g * h) = c g + c h) (hc1 : c σ₁ = 0) : c = 0 := by
  have hζC := Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hpow : ∀ (ψ : AddChar M ℂ) (x : M), ψ x ^ N = 1 := fun ψ x => by
    rw [← AddChar.map_nsmul_eq_pow, hM, AddChar.map_zero_eq_one]
  funext g
  refine AddChar.forall_apply_eq_zero.1 fun ψ => ?_
  have h := LX.zmod_hom_eq_zero hζ hζΓ hγ h1 (fun γ => dlog hζC (ψ (c γ)))
    (hlc.comp fun x => dlog hζC (ψ x)) (fun γ δ => by
      rw [hadd, AddChar.map_add_eq_mul, dlog_mul' hζC (hpow ψ _) (hpow ψ _)])
    (by
      have e1 := dlog_epow hζC (0 : ZMod N)
      rw [epow_zero] at e1
      show dlog hζC (ψ (c σ₁)) = 0
      rw [hc1, AddChar.map_zero_eq_one, e1])
  have hg := congrFun h g
  simp only [Pi.zero_apply] at hg
  rw [← epow_dlog hζC (hpow ψ (c g)), hg]
  simp [epow]

/-- Coefficients killed by `N`. -/
theorem LX.tors_hom_eq_zero {V : Type} [AddCommGroup V] (hV : ∀ v : V, N • v = 0)
    (c : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) → V) (hlc : IsLocallyConstant c)
    (hadd : ∀ g h, c (g * h) = c g + c h) (hc1 : c σ₁ = 0) : c = 0 := by
  have hc0 : c 1 = 0 := by
    have h := hadd 1 1
    rw [mul_one] at h
    exact left_eq_add.1 h
  have hcinv : ∀ σ, c σ⁻¹ = -c σ := fun σ => by
    have h := hadd σ⁻¹ σ
    rw [inv_mul_cancel, hc0] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have : CompactSpace (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) :=
    isCompact_iff_compactSpace.1 (by rw [Subgroup.coe_top]; exact isCompact_univ)
  let M : AddSubgroup V :=
    { carrier := Set.range c
      add_mem' := by
        rintro _ _ ⟨σ, rfl⟩ ⟨τ, rfl⟩
        exact ⟨σ * τ, hadd σ τ⟩
      zero_mem' := ⟨1, hc0⟩
      neg_mem' := by
        rintro _ ⟨σ, rfl⟩
        exact ⟨σ⁻¹, hcinv σ⟩ }
  have : Finite M := (hlc.range_finite).to_subtype
  let c' : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) → M := fun σ => ⟨c σ, σ, rfl⟩
  have hlc' : IsLocallyConstant c' := IsLocallyConstant.desc c' Subtype.val hlc Subtype.val_injective
  have h0 := LX.fin_hom_eq_zero hζ hζΓ hγ h1 (M := M) (fun x => Subtype.ext (hV x.1)) c' hlc'
    (fun g h => Subtype.ext (hadd g h)) (Subtype.ext hc1)
  funext σ
  exact congrArg Subtype.val (congrFun h0 σ)

/-- **Every locally constant homomorphism `π₁(G_m) → V` (`N • V = 0`) is `(kchar γ ·) • c σ₁`.** -/
theorem LX.hom_eq_kchar_smul {V : Type} [AddCommGroup V] (hV : ∀ v : V, N • v = 0)
    (c : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) → V) (hlc : IsLocallyConstant c)
    (hadd : ∀ g h, c (g * h) = c g + c h) (σ : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k)))) :
    c σ = (kchar hζ γ σ).val • c σ₁ := by
  have hγr : γ ∈ rad (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) N := fun σ _ => by
    rw [hγ, AlgEquiv.commutes]
  have hd := LX.tors_hom_eq_zero hζ hζΓ hγ h1 hV (fun τ => c τ - (kchar hζ γ τ).val • c σ₁)
    (hlc.sub ((isLocallyConstant_kchar hζ γ).comp fun a => a.val • c σ₁)) (fun g h => by
      simp only [hadd, kchar_mul hζ hζΓ hγr, val_add_nsmul (hV _)]
      abel) (by simp only [h1, val_one_nsmul (hV _), sub_self])
  exact sub_eq_zero.1 (congrFun hd σ)

end Kc

section H1Gen

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N]
  {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 (LX k) (RatFunc k)) M)

/-- Evaluation of a cocycle at `σ₁`. -/
def LX.h1Lin (hρ : ∀ g, ρ g = LinearMap.id) (σ₁ : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k)))) :
    CurveCoh.H1 ρ ⊤ →ₗ[Λ] M :=
  Submodule.liftQ _ ((LinearMap.proj σ₁).comp (CurveCoh.Z1 ρ ⊤).subtype) (fun z hz => by
    obtain ⟨-, m, hm⟩ := (CurveCoh.mem_B1 _ _ _).1 hz
    rw [LinearMap.mem_ker]
    have h := hm σ₁
    rw [hρ, LinearMap.id_apply, sub_self] at h
    exact h)

omit [IsAlgClosed k] in
theorem LX.h1Lin_mk (hρ : ∀ g, ρ g = LinearMap.id) (σ₁ : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))))
    (z : CurveCoh.Z1 ρ ⊤) : LX.h1Lin ρ hρ σ₁ (CurveCoh.H1.mk ρ ⊤ z) = z.1 σ₁ := rfl

/-- **`H¹_cont(π₁(G_m), M) ≃ M`** for the trivial action on `M` with `N • M = 0`. -/
def LX.h1LinEquiv (hρ : ∀ g, ρ g = LinearMap.id) (hM : ∀ v : M, N • v = 0) {ζ : maxUnram (LX k) (RatFunc k)}
    (hζ : IsPrimitiveRoot ζ N) (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))), σ ζ = ζ)
    {γ : (maxUnram (LX k) (RatFunc k))ˣ}
    (hγ : (γ : maxUnram (LX k) (RatFunc k)) ^ N = algebraMap (RatFunc k) _ RatFunc.X)
    {σ₁ : (⊤ : Subgroup (Pi1 (LX k) (RatFunc k)))} (h1 : kchar hζ γ σ₁ = 1) :
    CurveCoh.H1 ρ ⊤ ≃ₗ[Λ] M :=
  have hγr : γ ∈ rad (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))) N := fun σ _ => by
    rw [hγ, AlgEquiv.commutes]
  LinearEquiv.ofBijective (LX.h1Lin ρ hρ σ₁) ⟨(injective_iff_map_eq_zero _).2 fun q hq => by
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ q
    have hz : z.1 σ₁ = 0 := hq
    have hz0 : z = 0 := by
      have hzc := (CurveCoh.mem_Z1 _ _ _).1 z.2
      refine Subtype.ext (funext fun σ => ?_)
      rw [LX.hom_eq_kchar_smul hζ hζΓ hγ h1 hM z.1 hzc.1 (fun g h => by rw [hzc.2, hρ, LinearMap.id_apply]) σ,
        hz, smul_zero]
      rfl
    rw [hz0, map_zero], fun v => by
    refine ⟨CurveCoh.H1.mk ρ ⊤ ⟨fun σ => (kchar hζ γ σ).val • v, (CurveCoh.mem_Z1 _ _ _).2
      ⟨(isLocallyConstant_kchar hζ γ).comp fun a => a.val • v, fun g h => by
        rw [kchar_mul hζ hζΓ hγr, val_add_nsmul (hM v), hρ, LinearMap.id_apply]⟩⟩, ?_⟩
    rw [LX.h1Lin_mk]
    show (kchar hζ γ σ₁).val • v = v
    rw [h1, val_one_nsmul (hM v)]⟩

end H1Gen

section GmH1

variable (k : Type) [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem LX.fibRep_unitSh {Λ : Type} [CommRing Λ] (τ : Pi1 (LX k) (RatFunc k)) :
    EssSurj.fibRep (LX k) (RatFunc k) (unitSh Λ (Spec (CommRingCat.of (LX k)))) isLisse_unitSh τ =
      LinearMap.id := by
  obtain ⟨σ, rfl⟩ := genToPi1_surjective (LX k) (RatFunc k) τ
  rw [EssSurj.fibRep_genToPi1, galRep_unitSh]

end GmH1

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtCompact_KumForm =====
section

/-!
# S4-EtCompact, part 56: Kummer arithmetic for the local step (F7e1 of plan v5)

`ζ` a primitive `d`-th root of unity in a field `Ω`, `σ ∈ Aut_K(Ω)`.

* `dlog_mul_of`, `dlog_pow_of` (on `d`-th roots of unity), `ratio_pow_eq_one`;
* **`root_twist_pow`**: from `t c = v π^n`, `γ^d = c`, `ϖ^d = π`: `(γ t / ϖ^n)^d = v t^(d-1)`;
* **`dlog_twist`**: `dlog(σβ/β) = dlog(σγ/γ) - n dlog(σϖ/ϖ)` for `β = γ t / ϖ^n` with `σ t = t`;
* **`sum_twist`**: on a `d`-torsion group, `∑ (a i - n i b).val • e i = ∑ (a i).val • e i - b.val • ∑ n i • e i`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtCompact.KumForm

open RamanujanPetersson.Kummer

section Dlog

variable {Ω : Type} [Field Ω] {d : ℕ} [NeZero d] {ζ : Ω} (hζ : IsPrimitiveRoot ζ d)

theorem dlog_pow_of {x : Ω} (hx : x ^ d = 1) (n : ℕ) : dlog hζ (x ^ n) = n * dlog hζ x := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul]
    have h0 := dlog_epow hζ (0 : ZMod d)
    rwa [epow, ZMod.val_zero, pow_zero] at h0
  | succ n ih =>
    have hxn : (x ^ n) ^ d = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]
    rw [pow_succ, dlog_mul_of hζ hxn hx, ih, Nat.cast_succ, add_mul, one_mul]

end Dlog

section Twist

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {d : ℕ} [NeZero d] {ζ : Ω} (hζ : IsPrimitiveRoot ζ d)

theorem root_twist_pow {γ t ϖ c v π : Ω} (n : ℕ) (hπ : π ≠ 0) (hγ : γ ^ d = c) (hϖ : ϖ ^ d = π)
    (hrel : t * c = v * π ^ n) : (γ * t / ϖ ^ n) ^ d = v * t ^ (d - 1) := by
  obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne d)).symm⟩
  have hd1 : d - 1 = e := by omega
  rw [hd1, div_pow, mul_pow, hγ, ← pow_mul, mul_comm n d, pow_mul, hϖ, div_eq_iff (pow_ne_zero _ hπ), he]
  linear_combination t ^ e * hrel

theorem dlog_twist (σ : Ω ≃ₐ[K] Ω) {γ t ϖ : Ω} (n : ℕ) (hγ : γ ≠ 0) (ht : t ≠ 0) (hϖ : ϖ ≠ 0) (hσt : σ t = t)
    (hβd : σ ((γ * t / ϖ ^ n) ^ d) = (γ * t / ϖ ^ n) ^ d)
    (hϖd : σ (ϖ ^ d) = ϖ ^ d) :
    dlog hζ (σ (γ * t / ϖ ^ n) / (γ * t / ϖ ^ n)) = dlog hζ (σ γ / γ) - n * dlog hζ (σ ϖ / ϖ) := by
  have hβ : γ * t / ϖ ^ n ≠ 0 := div_ne_zero (mul_ne_zero hγ ht) (pow_ne_zero _ hϖ)
  have hσϖ : σ ϖ ≠ 0 := (map_ne_zero σ).2 hϖ
  have h1 := ratio_pow_eq_one σ hβ hβd
  have h2 := ratio_pow_eq_one σ hϖ hϖd
  have h2n : ((σ ϖ / ϖ) ^ n) ^ d = 1 := by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]
  have key : σ γ / γ = (σ (γ * t / ϖ ^ n) / (γ * t / ϖ ^ n)) * (σ ϖ / ϖ) ^ n := by
    rw [map_div₀, map_mul, map_pow, hσt, div_pow]
    field_simp
    try ring
  rw [key, dlog_mul_of hζ h1 h2n, dlog_pow_of hζ h2]
  ring

end Twist

section Sum

variable {M : Type*} [AddCommGroup M] {d : ℕ} [NeZero d]

theorem val_nsmul_eq (hd : ∀ v : M, d • v = 0) (z : ZMod d) (v : M) :
    z.val • v = (letI := AddCommGroup.zmodModule hd; z • v) := by
  let _ := AddCommGroup.zmodModule hd
  rw [← Nat.cast_smul_eq_nsmul (ZMod d), ZMod.natCast_zmod_val]

theorem sum_twist (hd : ∀ v : M, d • v = 0) {k : ℕ} (a : Fin k → ZMod d) (n : Fin k → ℕ) (b : ZMod d)
    (e : Fin k → M) :
    ∑ i, (a i - n i * b).val • e i = ∑ i, (a i).val • e i - b.val • ∑ i, n i • e i := by
  let _ := AddCommGroup.zmodModule hd
  simp only [val_nsmul_eq hd]
  have hn : ∀ i, n i • e i = (n i : ZMod d) • e i := fun i => (Nat.cast_smul_eq_nsmul (ZMod d) (n i) (e i)).symm
  simp only [hn, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, mul_comm b]

end Sum

end RamanujanPetersson.EtCompact.KumForm

end

end

-- ===== S4.Def_RP_EtCompact_KumDec =====
section

/-!
# S4-EtCompact, part 46: every finite-image Galois character is a sum of Kummer characters (F3 of plan v5)

Setting of `Def_RP_Kummer_Gal`: fields `K ⊆ E`, a subgroup `Γ ≤ Aut_K(E)`, a primitive `N`-th root of unity `ζ` fixed
by `Γ`, and `E` containing all `N`-th roots of its nonzero elements.

* `kchar_level`: level change, `kchar_d(α) σ = kchar_N(β) σ mod d` when `β ^ (N / d) = α`;
* `exists_kchar_lift`: every locally constant additive `c : Γ → ZMod d` (`d ∣ N`) is `kchar_N(β) mod d`;
* **`exists_kdec`**: every locally constant additive `χ : Γ → Λ` with finite image (`N • Λ = 0`) is
  `σ ↦ ∑ i, (kchar_N (β i) σ).val • e i` for finitely many radicals `β i` (structure theorem for the finite group
  `χ(Γ)`, then `exists_kchar_lift` on each cyclic factor).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.EtCompact.KumDec

open RamanujanPetersson.Kummer

noncomputable section

variable {K E : Type} [Field K] [Field E] [Algebra K E] {Γ : Subgroup (E ≃ₐ[K] E)}

/-- Level change for Kummer characters: if `β ^ (N / d) = α` then `kchar_d α = kchar_N β mod d`. -/
theorem kchar_level {N d : ℕ} [NeZero N] [NeZero d] {ζ : E} (hζ : IsPrimitiveRoot ζ N)
    (hζd : IsPrimitiveRoot (ζ ^ (N / d)) d) {α β : Eˣ} (hα : α ∈ rad Γ d) (hβ : β ∈ rad Γ N)
    (hβα : β ^ (N / d) = α) (σ : Γ) :
    kchar hζd α σ = (((kchar hζ β σ).val : ℕ) : ZMod d) := by
  rw [kchar_eq_iff hζd hα, ← hβα, Units.val_pow_eq_pow_val, map_pow, kchar_spec hζ hβ σ, mul_pow]
  congr 1
  unfold epow
  rw [ZMod.val_natCast, pow_mod_N hζd, ← pow_mul, ← pow_mul, mul_comm]

/-- Every locally constant additive character `Γ → ZMod d` (`d ∣ N`) is a Kummer character of level `N`, mod `d`. -/
theorem exists_kchar_lift {N d : ℕ} [NeZero N] [NeZero d] (hdN : d ∣ N) {ζ : E} (hζ : IsPrimitiveRoot ζ N)
    (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ) (hroot : ∀ x : E, x ≠ 0 → ∃ y : E, y ^ N = x) (c : Γ → ZMod d)
    (hc : IsLocallyConstant c) (hhom : ∀ σ τ : Γ, c (σ * τ) = c σ + c τ) :
    ∃ β ∈ rad Γ N, ∀ σ : Γ, c σ = (((kchar hζ β σ).val : ℕ) : ZMod d) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have hd0 : d ≠ 0 := NeZero.ne d
  have hq0 : N / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdN)
    (Nat.pos_of_ne_zero hd0)).ne'
  have hζd : IsPrimitiveRoot (ζ ^ (N / d)) d := by
    have h := hζ.pow_of_dvd hq0 (Nat.div_dvd_of_dvd hdN)
    rwa [Nat.div_div_self hdN hN0] at h
  have hζdΓ : ∀ σ ∈ Γ, σ (ζ ^ (N / d)) = ζ ^ (N / d) := fun σ hσ => by rw [map_pow, hζΓ σ hσ]
  obtain ⟨α, hα, hαc⟩ := exists_kchar_eq hζd hζdΓ c hc hhom
  obtain ⟨y, hy⟩ := hroot (α : E) α.ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0] at hy
    exact α.ne_zero hy.symm
  obtain ⟨β, hβα⟩ : ∃ β : Eˣ, β ^ (N / d) = α := by
    refine ⟨(Units.mk0 y hy0) ^ d, Units.ext ?_⟩
    rw [← pow_mul, Units.val_pow_eq_pow_val, Units.val_mk0, Nat.mul_div_cancel' hdN, hy]
  have hβ : β ∈ rad Γ N := by
    intro σ hσ
    have e : (β : E) ^ N = (α : E) ^ d := by
      rw [← hβα, Units.val_pow_eq_pow_val, ← pow_mul, Nat.div_mul_cancel hdN]
    rw [e]
    exact hα σ hσ
  refine ⟨β, hβ, fun σ => ?_⟩
  rw [← hαc σ]
  exact kchar_level hζ hζd hα hβ hβα σ

/-- **F3 (KumDec)**: a locally constant additive character with finite image into an `N`-torsion group is a finite
sum of Kummer characters of level `N` times fixed elements. -/
theorem exists_kdec {Λ : Type*} [AddCommGroup Λ] {N : ℕ} [NeZero N] {ζ : E} (hζ : IsPrimitiveRoot ζ N)
    (hζΓ : ∀ σ ∈ Γ, σ ζ = ζ) (hroot : ∀ x : E, x ≠ 0 → ∃ y : E, y ^ N = x)
    (hΛ : ∀ x : Λ, N • x = 0) (χ : Γ → Λ) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ)
    (hχc : IsLocallyConstant χ) (hfin : (Set.range χ).Finite) :
    ∃ (ι : Type) (_ : Fintype ι) (β : ι → Eˣ) (e : ι → Λ), (∀ i, β i ∈ rad Γ N) ∧
      ∀ σ, χ σ = ∑ i, (kchar hζ (β i) σ).val • e i := by
  classical
  have h1 : χ 1 = 0 := by
    have h := hχ 1 1
    rw [mul_one] at h
    exact (add_eq_left.mp h.symm)
  let F : AddSubgroup Λ :=
    { carrier := Set.range χ
      add_mem' := by
        rintro _ _ ⟨σ, rfl⟩ ⟨τ, rfl⟩
        exact ⟨σ * τ, hχ σ τ⟩
      zero_mem' := ⟨1, h1⟩
      neg_mem' := by
        rintro _ ⟨σ, rfl⟩
        refine ⟨σ⁻¹, ?_⟩
        have h := hχ σ⁻¹ σ
        rw [inv_mul_cancel, h1] at h
        exact eq_neg_of_add_eq_zero_left h.symm }
  have : Finite F := hfin.to_subtype
  have mem : ∀ σ, χ σ ∈ F := fun σ => Set.mem_range_self σ
  obtain ⟨ι, hι, p, hp, ex, ⟨φ⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite F
  have hdne : ∀ i, NeZero (p i ^ ex i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let ofi : ∀ i, ZMod (p i ^ ex i) →+ DirectSum ι (fun i => ZMod (p i ^ ex i)) := fun i => DirectSum.of (fun i => ZMod (p i ^ ex i)) i
  let g : ι → Λ := fun i => F.subtype (φ.symm (ofi i 1))
  have hof : ∀ i (n : ℕ), n • ofi i 1 = ofi i (n : ZMod (p i ^ ex i)) := fun i n => by
    rw [← map_nsmul, nsmul_eq_mul, mul_one]
  have hdN : ∀ i, p i ^ ex i ∣ N := by
    intro i
    have e1 : φ.symm (N • ofi i 1) = 0 := by
      apply Subtype.ext
      rw [map_nsmul]
      exact hΛ _
    rw [map_eq_zero_iff φ.symm φ.symm.injective, hof] at e1
    have e2 : ((N : ℕ) : ZMod (p i ^ ex i)) = 0 :=
      DirectSum.of_injective (β := fun i => ZMod (p i ^ ex i)) i (e1.trans (map_zero _).symm)
    exact (ZMod.natCast_eq_zero_iff N _).mp e2
  let c : ∀ i, Γ → ZMod (p i ^ ex i) := fun i σ =>
    (fun l : Λ => if h : l ∈ F then φ ⟨l, h⟩ i else 0) (χ σ)
  have hcv : ∀ i σ, c i σ = φ ⟨χ σ, mem σ⟩ i := fun i σ => dif_pos (mem σ)
  have key : ∀ i, ∃ β ∈ rad Γ N, ∀ σ : Γ, c i σ = (((kchar hζ β σ).val : ℕ) : ZMod (p i ^ ex i)) := by
    intro i
    have := hdne i
    refine exists_kchar_lift (hdN i) hζ hζΓ hroot (c i) (hχc.comp (fun l : Λ => if h : l ∈ F then φ ⟨l, h⟩ i else 0)) (fun σ τ => ?_)
    rw [hcv, hcv, hcv]
    have e : (⟨χ (σ * τ), mem _⟩ : F) = ⟨χ σ, mem σ⟩ + ⟨χ τ, mem τ⟩ := Subtype.ext (hχ σ τ)
    rw [e, map_add, DirectSum.add_apply]
  choose β hβ hβc using key
  refine ⟨ι, hι, β, g, hβ, fun σ => ?_⟩
  have e0 : χ σ = F.subtype (φ.symm (φ ⟨χ σ, mem σ⟩)) := by
    rw [AddEquiv.symm_apply_apply]
    rfl
  rw [e0, ← DirectSum.sum_univ_of (φ ⟨χ σ, mem σ⟩), map_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← hcv i σ, hβc i σ]
  show F.subtype (φ.symm (ofi i _)) = _
  rw [← hof, map_nsmul, map_nsmul]

end

end RamanujanPetersson.EtCompact.KumDec


end

-- ===== S4.Def_RP_EtCompact_FixFld =====
section

/-!
# S4-EtCompact, part 47: elements fixed by the stabiliser of an embedding (F4a of plan v5)

`A` a domain with fraction field `K`, `Ω/K` Galois, `B` an `A`-algebra and `φ : B →ₐ[A] Ω`.

* **`exists_mul_eq_of_fixed`**: if `x ∈ Ω` is fixed by every `σ ∈ Gal(Ω/K)` with `σ ∘ φ = φ`, then `x * s = φ c` for
  some `c ∈ B` and `0 ≠ s ∈ A` (the fixed field of the stabiliser is `K(φ B) = K[φ B]`, by infinite Galois theory
  and algebraicity);
* `algebraMap_ne_zero`: `s ≠ 0` in `A` stays nonzero in `Ω`;
* `exists_pow_eq_of_fixed`: a unit `β` whose `N`-th power is so fixed becomes, after multiplying by some `0 ≠ s ∈ A`,
  an `N`-th root of an element of `φ B`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.EtCompact.FixFld

variable {A K Ω B : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field Ω] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [CommRing B] [Algebra A B]

include K in
theorem algebraMap_ne_zero {s : A} (hs : s ≠ 0) : algebraMap A Ω s ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply A K Ω]
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective A K)).2 hs)

variable (K) in
/-- The elements `x` with `x * s = φ c` (`0 ≠ s ∈ A`, `c ∈ B`) form a `K`-subalgebra containing `φ B`. -/
theorem mem_of_mem_adjoin (φ : B →ₐ[A] Ω) {x : Ω} (hx : x ∈ Algebra.adjoin K (Set.range φ)) :
    ∃ c : B, ∃ s : A, s ≠ 0 ∧ x * algebraMap A Ω s = φ c := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, 1, one_ne_zero, by rw [map_one, mul_one]⟩
  | algebraMap r =>
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) r
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    refine ⟨algebraMap A B a, s, hs0, ?_⟩
    rw [φ.commutes, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      div_mul_cancel₀ _ (algebraMap_ne_zero (K := K) hs0)]
  | add x y _ _ hx hy =>
    obtain ⟨c₁, s₁, hs₁, h₁⟩ := hx
    obtain ⟨c₂, s₂, hs₂, h₂⟩ := hy
    refine ⟨c₁ * algebraMap A B s₂ + c₂ * algebraMap A B s₁, s₁ * s₂, mul_ne_zero hs₁ hs₂, ?_⟩
    simp only [map_add, map_mul, φ.commutes, ← h₁, ← h₂]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨c₁, s₁, hs₁, h₁⟩ := hx
    obtain ⟨c₂, s₂, hs₂, h₂⟩ := hy
    refine ⟨c₁ * c₂, s₁ * s₂, mul_ne_zero hs₁ hs₂, ?_⟩
    simp only [map_mul, ← h₁, ← h₂]
    ring

/-- **Fixed elements of the stabiliser of `φ`** lie in `K[φ B]`: `x * s = φ c`. -/
theorem exists_mul_eq_of_fixed [IsGalois K Ω] (φ : B →ₐ[A] Ω) (x : Ω)
    (hx : ∀ σ : Ω ≃ₐ[K] Ω, (∀ c, σ (φ c) = φ c) → σ x = x) :
    ∃ c : B, ∃ s : A, s ≠ 0 ∧ x * algebraMap A Ω s = φ c := by
  let L : IntermediateField K Ω := IntermediateField.adjoin K (Set.range φ)
  have hxL : x ∈ L := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L]
    intro σ
    refine hx σ.1 (fun c => ?_)
    exact (IntermediateField.mem_fixingSubgroup_iff L σ.1).1 σ.2 (φ c)
      (IntermediateField.subset_adjoin K _ ⟨c, rfl⟩)
  have hS : ∀ y ∈ Set.range φ, IsAlgebraic K y := fun y _ => Algebra.IsAlgebraic.isAlgebraic y
  have hxA : x ∈ Algebra.adjoin K (Set.range φ) := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic hS]
    exact hxL
  exact mem_of_mem_adjoin K φ hxA

/-- A unit whose `N`-th power is fixed by the stabiliser of `φ` becomes, after multiplying by some `0 ≠ s ∈ A`,
an `N`-th root of some `φ c`. -/
theorem exists_pow_eq_of_fixed [IsGalois K Ω] (φ : B →ₐ[A] Ω) (n : ℕ) (β : Ω)
    (hβ : ∀ σ : Ω ≃ₐ[K] Ω, (∀ c, σ (φ c) = φ c) → σ (β ^ (n + 1)) = β ^ (n + 1)) :
    ∃ c : B, ∃ s : A, s ≠ 0 ∧ (β * algebraMap A Ω s) ^ (n + 1) = φ c := by
  obtain ⟨c, s, hs, h⟩ := exists_mul_eq_of_fixed (K := K) φ _ hβ
  refine ⟨c * algebraMap A B (s ^ n), s, hs, ?_⟩
  rw [map_mul, φ.commutes, ← h, mul_pow, pow_succ (algebraMap A Ω s), map_pow]
  ring

end RamanujanPetersson.EtCompact.FixFld


end

-- ===== S4.Def_RP_EtCompact_KDecAt =====
section

/-!
# S4-EtCompact, part 58: Kummer decomposition of the obstruction at a fibre point (F7e3 of plan v5)

`stab a`: the stabiliser of a fibre point. **`exists_dec`**: for `q ∈ Q(g^* Spec B)` with germ `p m` at `a₀`, the
obstruction of `m` on `stab a₀` is `∑ i, (dlog(σ γ_i / γ_i)).val • e_i` with `γ_i ≠ 0`, `γ_i ^ d = φ_{a₀}(c_i)`,
`c_i ∈ B` (`KumDec.exists_kdec` on the stabiliser, then `FixFld.exists_pow_eq_of_fixed` with `n = d - 1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.KDecAt

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.LT

variable {A : Type} [CommRing A] [IsDomain A]

/-- The stabiliser of a fibre point. -/
def stab {W : (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A))).Etale}
    (a : (geomPtAt (x0 A)).point.fiber.obj W) : Subgroup (Gal (x0 A)) where
  carrier := {σ | (galAct (x0 A) σ).app W a = a}
  mul_mem' {σ τ} hσ hτ := by
    have h1 : (galAct (x0 A) σ).app W a = a := hσ
    have h2 : (galAct (x0 A) τ).app W a = a := hτ
    show (galAct (x0 A) (σ * τ)).app W a = a
    rw [galAct_mul, h2, h1]
  one_mem' := galAct_one (x0 A) W a
  inv_mem' {σ} hσ := by
    have h : (galAct (x0 A) σ).app W a = a := hσ
    show (galAct (x0 A) σ⁻¹).app W a = a
    conv_lhs => rw [← h]
    rw [← galAct_mul, inv_mul_cancel, galAct_one]

variable {Λ : Type} [CommRing Λ]
  {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} {ι : Ns ⟶ I} {p : I ⟶ Q}

/-- **Kummer decomposition of the obstruction at `a₀`.** -/
theorem exists_dec (hex : ∀ y, (((geomPtAt (x0 A)).stalkF Λ).map p).hom y = 0 →
      ∃ x, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom x = y)
    (hι : Function.Injective (((geomPtAt (x0 A)).stalkF Λ).map ι).hom)
    (hN' : ∀ (σ : Gal (x0 A)) (n : stalk Λ Ns (x0 A)),
      galRep Λ I (x0 A) σ ((((geomPtAt (x0 A)).stalkF Λ).map ι).hom n) = (((geomPtAt (x0 A)).stalkF Λ).map ι).hom n)
    {d : ℕ} [NeZero d] (hdA : IsUnit (d : A)) {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    (hζG : ∀ σ : Gal (x0 A), σ ζ = ζ) (hd : ∀ v : stalk Λ Ns (x0 A), d • v = 0)
    {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) (a₀ : Fib A B) (m : stalk Λ I (x0 A))
    (hm : (((geomPtAt (x0 A)).stalkF Λ).map p).hom m =
      ((geomPtAt (x0 A)).point.toPresheafFiber _ a₀ Q.obj).hom q) :
    ∃ (k : ℕ) (γ : Fin k → SeparableClosure (κ0 A)) (c : Fin k → B) (e : Fin k → stalk Λ Ns (x0 A)),
      (∀ i, γ i ≠ 0) ∧ (∀ i, γ i ^ d = phiB A a₀ (c i)) ∧
      ∀ σ : Gal (x0 A), (galAct (x0 A) σ).app _ a₀ = a₀ →
        Obs.obs (galRep Λ I (x0 A)) (((geomPtAt (x0 A)).stalkF Λ).map ι).hom m σ =
          ∑ i, (dlog hζ (σ (γ i) / γ i)).val • e i := by
  have : NeZero ((d : ℕ) : SeparableClosure (κ0 A)) := ⟨by
    rw [← map_natCast (algebraMap A (SeparableClosure (κ0 A)))]
    exact (hdA.map _).ne_zero⟩
  have hΓ : ∀ σ ∈ stab a₀, ∃ n, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom n = galRep Λ I (x0 A) σ m - m :=
    fun σ hσ => adm hex q a₀ m hm σ hσ
  obtain ⟨H, hHo, hH⟩ := exists_open_fix Λ I (x0 A) m
  let χ : stab a₀ → stalk Λ Ns (x0 A) :=
    fun σ => Obs.obs (galRep Λ I (x0 A)) (((geomPtAt (x0 A)).stalkF Λ).map ι).hom m σ
  have hχ : ∀ σ τ : stab a₀, χ (σ * τ) = χ σ + χ τ := fun σ τ => Obs.obs_mul hι hN' (hΓ σ σ.2) (hΓ τ τ.2)
  have hχc : IsLocallyConstant χ := Obs.isLocallyConstant_obs hι hN' (stab a₀) hΓ hHo hH
  have hfin : (Set.range χ).Finite := Obs.finite_range_obs hι hN' (stab a₀) hΓ hHo hH
  obtain ⟨κ, _, β, e, hβ, hdec⟩ := KumDec.exists_kdec hζ (fun σ _ => hζG σ)
    (fun x _ => IsSepClosed.exists_pow_nat_eq x d) hd χ hχ hχc hfin
  have hfix : ∀ j, ∃ c : B, ∃ s : A, s ≠ 0 ∧
      ((β j : SeparableClosure (κ0 A)) * algebraMap A _ s) ^ (d - 1 + 1) = phiB A a₀ c := by
    intro j
    refine FixFld.exists_pow_eq_of_fixed (K := κ0 A) (phiB A a₀) (d - 1) (β j) fun σ hσ => ?_
    have : @Mono Scheme _ (specEt A B).left (Spec (CommRingCat.of B)) (𝟙 (specEt A B).left) :=
      IsIso.mono_of_iso (𝟙 (specEt A B).left)
    have hσΓ : σ ∈ stab a₀ := FibPt.galAct_eq_of_phi (x0 A) (gen A) (specEt A B) (𝟙 _) σ a₀ hσ
    rw [Nat.sub_add_cancel NeZero.one_le]
    exact hβ j σ hσΓ
  choose c s hs hcs using hfix
  have hne : ∀ j, algebraMap A (SeparableClosure (κ0 A)) (s j) ≠ 0 :=
    fun j h => hs j (Chart.alg_injective (h.trans (map_zero _).symm))
  let eq := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun i => (β (eq.symm i) : _) * algebraMap A _ (s (eq.symm i)), fun i => c (eq.symm i),
    fun i => e (eq.symm i), fun i => mul_ne_zero (β _).ne_zero (hne _), fun i => ?_, fun σ hσ => ?_⟩
  · have := hcs (eq.symm i)
    rwa [Nat.sub_add_cancel NeZero.one_le] at this
  · refine (hdec (⟨σ, hσ⟩ : stab a₀)).trans ?_
    rw [← Equiv.sum_comp eq.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hσs : σ (algebraMap A (SeparableClosure (κ0 A)) (s (eq.symm i))) =
        algebraMap A (SeparableClosure (κ0 A)) (s (eq.symm i)) := by
      rw [IsScalarTower.algebraMap_apply A (κ0 A) (SeparableClosure (κ0 A)), AlgEquiv.commutes]
    have hk : kchar hζ (β (eq.symm i)) (⟨σ, hσ⟩ : stab a₀) =
        dlog hζ (σ ((β (eq.symm i) : SeparableClosure (κ0 A)) * algebraMap A _ (s (eq.symm i))) /
          ((β (eq.symm i) : SeparableClosure (κ0 A)) * algebraMap A _ (s (eq.symm i)))) := by
      rw [map_mul, hσs, mul_div_mul_right _ _ (hne _)]
      rfl
    rw [hk]

end RamanujanPetersson.EtCompact.KDecAt

end

end

-- ===== S4.Def_RP_EtCompact_LFq =====
section

/-!
# S4-EtCompact, part 57: local factorisation through a point (F7e2 of plan v5)

`B` étale over a noetherian domain `A`, `φ : B →ₐ[A] Ω` into a field, `P₀ ⊇ ker φ` a prime of `B` over `(π)`.
**`exists_lf`**: for `φ c ≠ 0` there are `v, s ∉ P₀` and `n` with `φ s * φ c = φ v * π^n`
(`KumEt.exists_mul_eq_unit_mul_pow` on the domain `B ⧸ ker φ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtCompact.LFq

variable {A B Ω : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
  [Field Ω] [Algebra A Ω]

/-- **Local factorisation after `φ`.** -/
theorem exists_lf (φ : B →ₐ[A] Ω) (P₀ : Ideal B) [P₀.IsPrime] (hker : RingHom.ker φ ≤ P₀) (π : A)
    (hP₀ : P₀.comap (algebraMap A B) = Ideal.span {π}) (hπ : algebraMap A Ω π ≠ 0) {c : B} (hc : φ c ≠ 0) :
    ∃ (n : ℕ) (v s : B), v ∉ P₀ ∧ s ∉ P₀ ∧ φ s * φ c = φ v * algebraMap A Ω π ^ n := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hJ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmk : RingHom.ker (Ideal.Quotient.mk (RingHom.ker φ)) ≤ P₀ := by rw [Ideal.mk_ker]; exact hker
  have hw : (P₀.map (Ideal.Quotient.mk (RingHom.ker φ))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hmk
  have hcm : (P₀.map (Ideal.Quotient.mk (RingHom.ker φ))).comap (Ideal.Quotient.mk (RingHom.ker φ)) = P₀ := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 hmk
  have hwA : (P₀.map (Ideal.Quotient.mk (RingHom.ker φ))).comap (algebraMap A (B ⧸ RingHom.ker φ)) =
      Ideal.span {π} := by
    rw [IsScalarTower.algebraMap_eq A B (B ⧸ RingHom.ker φ), ← Ideal.comap_comap, Ideal.Quotient.algebraMap_eq,
      hcm, hP₀]
  have hmem : ∀ z : B, Ideal.Quotient.mk (RingHom.ker φ) z = 0 ↔ φ z = 0 := fun z => by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact RingHom.mem_ker
  have hπ' : algebraMap A (B ⧸ RingHom.ker φ) π ≠ 0 := by
    rw [← Ideal.Quotient.mk_algebraMap]
    intro h
    rw [hmem, AlgHom.commutes] at h
    exact hπ h
  have hc' : Ideal.Quotient.mk (RingHom.ker φ) c ≠ 0 := fun h => hc ((hmem c).1 h)
  obtain ⟨n, v', s', hv, hs, heq⟩ := KumEt.exists_mul_eq_unit_mul_pow π _ hwA hπ' hc'
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v'
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
  refine ⟨n, v, s, fun h => hv (Ideal.mem_map_of_mem _ h), fun h => hs (Ideal.mem_map_of_mem _ h), ?_⟩
  rw [← Ideal.Quotient.mk_algebraMap, ← map_mul, ← map_pow, ← map_mul, Ideal.Quotient.eq, RingHom.mem_ker,
    map_sub, sub_eq_zero, map_mul, map_mul, map_pow, AlgHom.commutes] at heq
  exact heq

end RamanujanPetersson.EtCompact.LFq

end

end

-- ===== S4.Def_RP_EtCompact_Step =====
section

/-!
# S4-EtCompact, part 59: the local step at a point (F7e4 of plan v5)

`A` a noetherian integrally closed domain, `g = gen A`, `ι : Ns ⟶ I`, `p : I ⟶ Q` on `Spec κ(η)` exact on stalks,
`c : g_* Q ⟶ C` epi killing `g_* p`, `b : Λ ⟶ C`.

* `eq_of_bot`: over a one-point `g^* Spec B`, two primes of `B` over `(0)` agree;
* **`exists_kill`**: the Kummer condition at one fibre point for elements `u i ∉ P₀` lifts `q` to `I` on an étale
  neighbourhood of `P₀`;
* **`gen_good`**: the generic point lies in `Good b`;
* **`exists_step`**: at `x = (π)`, a global `a : Λ ⟶ g_* Q` with `x ∈ Good (b - a ≫ c)` and `D(π) ⊆ Good (a ≫ c)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.Step

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.LT

variable {A : Type} [CommRing A] [IsDomain A]

/-- Over a one-point `g^* Spec B`, two primes of `B` over `(0)` agree. -/
theorem eq_of_bot {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    [Subsingleton ((etPull (gen A)).obj (specEt A B)).left] (P₁ P₂ : PrimeSpectrum B)
    (h₁ : P₁.asIdeal.comap (algebraMap A B) = ⊥) (h₂ : P₂.asIdeal.comap (algebraMap A B) = ⊥) : P₁ = P₂ := by
  have hP : ∀ P : PrimeSpectrum B, P.asIdeal.comap (algebraMap A B) = ⊥ →
      ∃ z : ((etPull (gen A)).obj (specEt A B)).left, pullback.fst (specEt A B).hom (gen A) z = P := by
    intro P hP
    have h : (specEt A B).hom P = gen A (x0 A) := by
      refine Eq.trans ?_ (Scheme.fromSpecResidueField_apply _ _).symm
      exact PrimeSpectrum.ext hP
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (specEt A B).hom) (g := gen A) P (x0 A) h
    exact ⟨z, hz⟩
  obtain ⟨z₁, rfl⟩ := hP P₁ h₁
  obtain ⟨z₂, rfl⟩ := hP P₂ h₂
  rw [Subsingleton.elim (α := ((etPull (gen A)).obj (specEt A B)).left) z₁ z₂]

variable {Λ : Type} [CommRing Λ]
  {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} {ι : Ns ⟶ I} {p : I ⟶ Q}

/-- **Killing `q` near `P₀`.** -/
theorem exists_kill (hex : ∀ y, (((geomPtAt (x0 A)).stalkF Λ).map p).hom y = 0 →
      ∃ x, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom x = y)
    (hι : Function.Injective (((geomPtAt (x0 A)).stalkF Λ).map ι).hom)
    (hN' : ∀ (σ : Gal (x0 A)) (n : stalk Λ Ns (x0 A)),
      galRep Λ I (x0 A) σ ((((geomPtAt (x0 A)).stalkF Λ).map ι).hom n) = (((geomPtAt (x0 A)).stalkF Λ).map ι).hom n)
    {d : ℕ} [NeZero d] (hdA : IsUnit (d : A)) {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    (hζG : ∀ σ : Gal (x0 A), σ ζ = ζ)
    {B : Type} [CommRing B] [Algebra A B] [Algebra.Etale A B]
    [Subsingleton ((etPull (gen A)).obj (specEt A B)).left] (P₀ : PrimeSpectrum B)
    (q : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B)))) {k : ℕ} (u : Fin k → B)
    (e : Fin k → stalk Λ Ns (x0 A)) (hu : ∀ i, u i ∉ P₀.asIdeal) (a₀ : Fib A B)
    (h₀ : KCe.KCAt A ι p hζ q u e a₀) :
    ∃ (V' : (Spec (CommRingCat.of A)).Etale) (G : V' ⟶ specEt A B) (w : V'.left), G.left w = P₀ ∧
      ∃ f : I.obj.obj (op ((etPull (gen A)).obj V')),
        (p.hom.app _).hom f = (Q.obj.map ((etPull (gen A)).map G).op).hom q := by
  have hkce := KCe.kc_of_one hex hι hN' hζ hζG q u e a₀ h₀
  have hh : (∏ i, u i) ∉ P₀.asIdeal := Submonoid.prod_mem P₀.asIdeal.primeCompl fun i _ => hu i
  let B' := Localization.Away (∏ i, u i)
  have hunit : ∀ i, IsUnit (algebraMap B B' (u i)) := fun i =>
    isUnit_of_dvd_unit (map_dvd (algebraMap B B') (Finset.dvd_prod_of_mem u (Finset.mem_univ i)))
      (IsLocalization.Away.algebraMap_isUnit (∏ i, u i))
  have hkc : KC A ι p hζ B' ((Q.obj.map ((etPull (gen A)).map
      (specEtMap (IsScalarTower.toAlgHom A B B'))).op).hom q) (fun i => (hunit i).unit) e :=
    KCe.kce_map hζ (IsScalarTower.toAlgHom A B B') q u e hkce
  obtain ⟨V', F, hF, f, hf⟩ := LT.exists_lift hex hdA hζ hζG k B' _ _ e hkc
  have hr := PrimeSpectrum.localization_away_comap_range B' (∏ i, u i)
  obtain ⟨c₀, hc₀⟩ : P₀ ∈ Set.range (PrimeSpectrum.comap (algebraMap B B')) := by
    rw [hr]
    exact hh
  obtain ⟨v', hv'⟩ := hF c₀
  refine ⟨V', F ≫ specEtMap (IsScalarTower.toAlgHom A B B'), v', ?_, f, ?_⟩
  · show (specEtMap (IsScalarTower.toAlgHom A B B')).left (F.left v') = P₀
    rw [hv']
    exact hc₀
  · rw [hf, Functor.map_comp, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

variable [IsIntegrallyClosed A] [IsNoetherianRing A]

end RamanujanPetersson.EtCompact.Step

end

end


