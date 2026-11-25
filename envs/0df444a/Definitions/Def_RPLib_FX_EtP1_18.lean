-- Prove2me | Definitions.Def_RPLib_FX_EtP1_18
-- name    : RPLib_FX_EtP1_18
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T09:23:19.136803+00:00
-- url     : https://prove2.me/theorems/ed6a8f55-f966-5b1b-ac71-f1976df9fbfb
-- title:
--   Étale cohomology of the projective line, library file 18 of 34
-- statement:
--   File 18 of 34 of the étale cohomology library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtCompact_GmKc`: S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)
--   * `S4.Def_RP_EtCompact_Step`: S4-EtCompact, part 59: the local step at a point (F7e4 of plan v5)
--   * `S4.Def_RP_EtCompact_StepX`: S4-EtCompact, part 60: the step at a closed point `(π)` (F7e4 of plan v5)
--   * `S4.Def_RP_EtCompact_LerayG2`: S4-EtCompact, part 41: the Leray step for `g_*` without `R²g_* = 0` (CC4, degrees 1-3)
--
--   **Formalization note.** One file of a library formalizing the étale cohomology of the projective line $\mathbf P^1_k = \operatorname{Proj} k[X_0, X_1]$ over an algebraically closed field $k$ with coefficients in sheaves of $\Lambda$-modules on the small étale site ($H^n = \operatorname{Ext}^n(\Lambda, -)$): $H^1(\mathbf P^1, \Lambda) = 0$, $H^2(\mathbf P^1, \Lambda) \cong \Lambda$ and $H^{n+3}(\mathbf P^1, F) = 0$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §1 (cohomology of curves) and Chapter III, §2 (Kummer theory); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Arcata », Chapter IV (cohomology of curves, Tsen's theorem)

import Mathlib
import Definitions.Def_RPLib_FX_EtP1_17

/-!
# Étale cohomology of the projective line, library file 18 of 34

Declarations of the formalization of the étale cohomology of the projective line over an algebraically
closed field (H¹ = 0, H² ≅ Λ, vanishing in degrees ≥ 3), re-hosted declaration by declaration from the
library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtCompact_GmKc`: S4-EtCompact: `H^1(G_m, Λ) ≃ Λ` (O8c, files M4c + M4e)
* `S4.Def_RP_EtCompact_Step`: S4-EtCompact, part 59: the local step at a point (F7e4 of plan v5)
* `S4.Def_RP_EtCompact_StepX`: S4-EtCompact, part 60: the step at a closed point `(π)` (F7e4 of plan v5)
* `S4.Def_RP_EtCompact_LerayG2`: S4-EtCompact, part 41: the Leray step for `g_*` without `R²g_* = 0` (CC4, degrees 1-3)
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

end Kc

section H1Gen

variable {k : Type} [Field k] [IsAlgClosed k] {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N]
  {M : Type} [AddCommGroup M] [Module Λ M] (ρ : Representation Λ (Pi1 (LX k) (RatFunc k)) M)

end H1Gen

section GmH1

variable (k : Type) [Field k] [IsAlgClosed k]

/-- **`H^1(G_m, Λ) ≃ Λ`** (`k` algebraically closed, `lⁿ • Λ = 0`, `l` invertible in `k`). -/
theorem Gm.nonempty_h1Equiv {Λ : Type} [CommRing Λ] {l n : ℕ} [Fact l.Prime] (hn : 0 < n) (hl : (l : k) ≠ 0)
    (hΛ : ((l ^ n : ℕ) : Λ) = 0) : Nonempty (H Λ (unitSh Λ (Gm k)) 1 ≃+ Λ) := by
  have hlp : l.Prime := Fact.out
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ hlp.ne_zero⟩
  have hN : ((l ^ n : ℕ) : k) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hl
  obtain ⟨ζ0, hζ0⟩ := exists_primitiveRoot_of_ne (k := k) hN
  have hinj : Function.Injective ((algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k))).comp
      (algebraMap k (RatFunc k))) :=
    (algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k))).injective.comp (algebraMap k (RatFunc k)).injective
  have hζ := hζ0.map_of_injective hinj
  have hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 (LX k) (RatFunc k))),
      σ (((algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k))).comp (algebraMap k (RatFunc k))) ζ0) =
        ((algebraMap (RatFunc k) (maxUnram (LX k) (RatFunc k))).comp (algebraMap k (RatFunc k))) ζ0 :=
    fun σ _ => AlgEquiv.commutes σ _
  obtain ⟨γ0, hγ0⟩ := LX.exists_root_X k hN
  have hγ00 : γ0 ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne _)] at hγ0
    exact (_root_.map_ne_zero _).2 RatFunc.X_ne_zero hγ0.symm
  have hγ : ((Units.mk0 γ0 hγ00 : (maxUnram (LX k) (RatFunc k))ˣ) : maxUnram (LX k) (RatFunc k)) ^ (l ^ n) =
      algebraMap (RatFunc k) _ RatFunc.X := hγ0
  obtain ⟨σ₁, h1⟩ := LX.exists_kchar_eq_one hn hζ hζΓ hγ
  have hM : ∀ v : stalk Λ (unitSh Λ (Spec (CommRingCat.of (LX k)))) (genPt (LX k)), (l ^ n) • v = 0 := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]
  exact ⟨(h1Equiv (LX k) (RatFunc k) (isLisse_unitSh (Λ := Λ) (X := Spec (CommRingCat.of (LX k))))).trans
    ((LX.h1LinEquiv _ (LX.fibRep_unitSh k) hM hζ hζΓ hγ h1).toAddEquiv.trans
      (constStalkIso Λ (geomPtAt (genPt (LX k))) (ModuleCat.of Λ Λ)).toLinearEquiv.toAddEquiv)⟩

end GmH1

end RamanujanPetersson.EtCompact

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

variable {Λ : Type} [CommRing Λ]
  {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} {ι : Ns ⟶ I} {p : I ⟶ Q}

variable [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- **The generic point is good** for every `b`. -/
theorem gen_good (hex : ∀ y, (((geomPtAt (x0 A)).stalkF Λ).map p).hom y = 0 →
      ∃ x, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom x = y)
    (hN : ∀ (σ : Gal (x0 A)) (v : stalk Λ Ns (x0 A)), galRep Λ Ns (x0 A) σ v = v)
    [Mono ι] [Epi p]
    {d : ℕ} [NeZero d] (hdA : IsUnit (d : A)) {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    (hζG : ∀ σ : Gal (x0 A), σ ζ = ζ) (hd : ∀ v : stalk Λ Ns (x0 A), d • v = 0)
    {C : EtSh Λ (Spec (CommRingCat.of A))} (c : (push (gen A) Λ).obj Q ⟶ C) [Epi c]
    (hc : (push (gen A) Λ).map p ≫ c = 0) (b : unitSh Λ (Spec (CommRingCat.of A)) ⟶ C)
    (x : Spec (CommRingCat.of A)) (hx : x.asIdeal = ⊥) : x ∈ Supp.Good A b := by
  have hι : Function.Injective (((geomPtAt (x0 A)).stalkF Λ).map ι).hom :=
    (ModuleCat.mono_iff_injective _).1 ((mono_iff_stalk Λ ι).1 inferInstance (x0 A))
  have hN' : ∀ (σ : Gal (x0 A)) (n : stalk Λ Ns (x0 A)), galRep Λ I (x0 A) σ
      ((((geomPtAt (x0 A)).stalkF Λ).map ι).hom n) = (((geomPtAt (x0 A)).stalkF Λ).map ι).hom n := by
    intro σ n
    have h1 := LinearMap.congr_fun (galRep_natural Λ ι (x0 A) σ) n
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, hN]
  obtain ⟨B, _, _, _, P₀, hP₀, hsub, ⟨a₀⟩, hker, s, hs⟩ := Chart.exists_chart_sc A c b x
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B))),
      (c.hom.app (op (specEt A B))).hom s₀ = Supp.sc b (specEt A B) := ⟨s, hs⟩
  have hep : Epi (((geomPtAt (x0 A)).stalkF Λ).map p) := (epi_iff_stalk Λ p).1 inferInstance (x0 A)
  obtain ⟨m, hm⟩ := (ModuleCat.epi_iff_surjective _).1 hep
    (((geomPtAt (x0 A)).point.toPresheafFiber _ a₀ Q.obj).hom s₀)
  obtain ⟨k, γ, c', e, hγ0, hγd, hobs⟩ := KDecAt.exists_dec hex hι hN' hdA hζ hζG hd s₀ a₀ m hm
  have hP₀b : P₀.asIdeal.comap (algebraMap A B) = ⊥ := (congrArg PrimeSpectrum.asIdeal hP₀).trans hx
  have hkb : (RingHom.ker (phiB A a₀)).comap (algebraMap A B) = ⊥ := by
    ext z
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, Ideal.mem_bot]
    exact ⟨fun h => Chart.alg_injective (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
  have hPk := congrArg PrimeSpectrum.asIdeal (eq_of_bot P₀ ⟨_, RingHom.ker_isPrime (phiB A a₀)⟩ hP₀b hkb)
  have hu : ∀ i, c' i ∉ P₀.asIdeal := fun i h => by
    rw [hPk] at h
    exact hγ0 i ((pow_eq_zero_iff (NeZero.ne d)).1 ((hγd i).trans (RingHom.mem_ker.1 h)))
  obtain ⟨V', G, w, hw, f, hf⟩ := exists_kill hex hι hN' hdA hζ hζG P₀ s₀ c' e hu a₀ ⟨m, hm, γ, hγd, hobs⟩
  refine ⟨V', w, (congrArg (fun φ => φ w) (MorphismProperty.Over.w G)).symm.trans
    ((congrArg (fun z => (specEt A B).hom z) hw).trans hP₀), ?_⟩
  rw [← Supp.sc_map b G, ← hs₀]
  have h2 := congrArg (fun ψ => ψ.hom s₀) (c.hom.naturality G.op)
  simp only [ModuleCat.hom_comp] at h2
  refine h2.symm.trans ?_
  show (c.hom.app (op V')).hom ((Q.obj.map ((etPull (gen A)).map G).op).hom s₀) = 0
  rw [← hf]
  refine (congrArg (fun ψ => (ψ.hom.app (op V')).hom f) hc).trans ?_
  simp
  rfl

end RamanujanPetersson.EtCompact.Step

end

end

-- ===== S4.Def_RP_EtCompact_StepX =====
section

/-!
# S4-EtCompact, part 60: the step at a closed point `(π)` (F7e4 of plan v5)

**`exists_step`**: for `c : g_* Q ⟶ C` epi killing `g_* p`, `b : Λ ⟶ C` and `x = (π)`, a global
`a : Λ ⟶ g_* Q` with `x ∈ Good (b - a ≫ c)` and `D(π) ⊆ Good (a ≫ c)`. Chart at `x` (`Chart.exists_chart_sc`),
Kummer decomposition at a fibre point (`KDecAt.exists_dec`), local factorisation (`LFq.exists_lf`), the global
Kummer section (`GlobQ.exists_globQ`) with `r = ∑ n i • e i`, and `Step.exists_kill` for `s - a`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtCompact.Step

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact.GenFrac RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.LT

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] {Λ : Type} [CommRing Λ]
  {Ns I Q : EtSh Λ (Spec ((Spec (CommRingCat.of A)).residueField (GenBr.genPt A)))} {ι : Ns ⟶ I} {p : I ⟶ Q}

/-- **The step at `x = (π)`.** -/
theorem exists_step (hex : ∀ y, (((geomPtAt (x0 A)).stalkF Λ).map p).hom y = 0 →
      ∃ x, (((geomPtAt (x0 A)).stalkF Λ).map ι).hom x = y)
    (hN : ∀ (σ : Gal (x0 A)) (v : stalk Λ Ns (x0 A)), galRep Λ Ns (x0 A) σ v = v)
    [Injective I] [Mono ι] [Epi p] (hιp : ι ≫ p = 0)
    {d : ℕ} [NeZero d] (hdA : IsUnit (d : A)) {ζ : SeparableClosure (κ0 A)} (hζ : IsPrimitiveRoot ζ d)
    (hζG : ∀ σ : Gal (x0 A), σ ζ = ζ) (hd : ∀ v : stalk Λ Ns (x0 A), d • v = 0)
    {C : EtSh Λ (Spec (CommRingCat.of A))} (c : (push (gen A) Λ).obj Q ⟶ C) [Epi c]
    (hc : (push (gen A) Λ).map p ≫ c = 0) (b : unitSh Λ (Spec (CommRingCat.of A)) ⟶ C)
    (x : Spec (CommRingCat.of A)) (π : A) (hπ : π ≠ 0) (hx : x.asIdeal = Ideal.span {π}) :
    ∃ a : unitSh Λ (Spec (CommRingCat.of A)) ⟶ (push (gen A) Λ).obj Q,
      x ∈ Supp.Good A (b - a ≫ c) ∧ ∀ y : Spec (CommRingCat.of A), π ∉ y.asIdeal → y ∈ Supp.Good A (a ≫ c) := by
  have hι : Function.Injective (((geomPtAt (x0 A)).stalkF Λ).map ι).hom :=
    (ModuleCat.mono_iff_injective _).1 ((mono_iff_stalk Λ ι).1 inferInstance (x0 A))
  have hN' : ∀ (σ : Gal (x0 A)) (n : stalk Λ Ns (x0 A)), galRep Λ I (x0 A) σ
      ((((geomPtAt (x0 A)).stalkF Λ).map ι).hom n) = (((geomPtAt (x0 A)).stalkF Λ).map ι).hom n := by
    intro σ n
    have h1 := LinearMap.congr_fun (galRep_natural Λ ι (x0 A) σ) n
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, hN]
  -- the chart and the lift `m`
  obtain ⟨B, _, _, _, P₀, hP₀, hsub, ⟨a₀⟩, hker, s, hs⟩ := Chart.exists_chart_sc A c b x
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B))),
      (c.hom.app (op (specEt A B))).hom s₀ = Supp.sc b (specEt A B) := ⟨s, hs⟩
  have hep : Epi (((geomPtAt (x0 A)).stalkF Λ).map p) := (epi_iff_stalk Λ p).1 inferInstance (x0 A)
  obtain ⟨m, hm⟩ := (ModuleCat.epi_iff_surjective _).1 hep
    (((geomPtAt (x0 A)).point.toPresheafFiber _ a₀ Q.obj).hom s₀)
  obtain ⟨k, γ, c', e, hγ0, hγd, hobs⟩ := KDecAt.exists_dec hex hι hN' hdA hζ hζG hd s₀ a₀ m hm
  -- local factorisation at `P₀`
  have hP₀π : P₀.asIdeal.comap (algebraMap A B) = Ideal.span {π} := (congrArg PrimeSpectrum.asIdeal hP₀).trans hx
  have halg : algebraMap A (SeparableClosure (κ0 A)) π ≠ 0 :=
    fun h => hπ (Chart.alg_injective (h.trans (map_zero _).symm))
  have hφc : ∀ i, phiB A a₀ (c' i) ≠ 0 :=
    fun i h => hγ0 i ((pow_eq_zero_iff (NeZero.ne d)).1 ((hγd i).trans h))
  have hlf : ∀ i, ∃ (n : ℕ) (v s' : B), v ∉ P₀.asIdeal ∧ s' ∉ P₀.asIdeal ∧
      phiB A a₀ s' * phiB A a₀ (c' i) = phiB A a₀ v * algebraMap A (SeparableClosure (κ0 A)) π ^ n :=
    fun i => LFq.exists_lf (phiB A a₀) P₀.asIdeal (hker a₀) π hP₀π halg (hφc i)
  choose n v s' hv hs' hrel using hlf
  -- the global Kummer section
  obtain ⟨ϖ, mx, ax, hϖ, hmx, hgerm, hgood⟩ :=
    GlobQ.exists_globQ ι p hex hN hιp hdA hζ hζG hd π hπ (∑ i, n i • e i)
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : Q.obj.obj (op ((etPull (gen A)).obj (specEt A B))),
      t₀ = Supp.sc ax (specEt A B) := ⟨_, rfl⟩
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne d)] at hϖ
    exact halg hϖ.symm
  have hs'0 : ∀ i, phiB A a₀ (s' i) ≠ 0 := fun i h => hs' i (hker a₀ (RingHom.mem_ker.2 h))
  have hσt : ∀ σ : Gal (x0 A), (galAct (x0 A) σ).app _ a₀ = a₀ → ∀ z : B, σ (phiB A a₀ z) = phiB A a₀ z :=
    fun σ hσ z => (FibPt.phi_galAct_apply (x0 A) (gen A) (specEt A B) (𝟙 _) σ a₀ z).symm.trans
      (congrArg (fun a => phiB A a z) hσ)
  have hβ : ∀ i, (γ i * phiB A a₀ (s' i) / ϖ ^ n i) ^ d = phiB A a₀ (v i * s' i ^ (d - 1)) := fun i => by
    rw [map_mul, map_pow]
    exact KumForm.root_twist_pow (n i) halg (hγd i) hϖ (hrel i)
  -- the Kummer condition for `s₀ - t₀` at `a₀`
  have h₀ : KCe.KCAt A ι p hζ (s₀ - t₀) (fun i => v i * s' i ^ (d - 1)) e a₀ := by
    refine ⟨m - mx, ?_, fun i => γ i * phiB A a₀ (s' i) / ϖ ^ n i, hβ, fun σ hσ => ?_⟩
    · rw [map_sub, map_sub, hm, ht₀, hgerm]
      rfl
    · have hadm := adm hex s₀ a₀ m hm σ hσ
      have hadmx : ∃ n', (((geomPtAt (x0 A)).stalkF Λ).map ι).hom n' = galRep Λ I (x0 A) σ mx - mx :=
        ⟨_, (hmx σ).symm⟩
      have hϖd : σ (ϖ ^ d) = ϖ ^ d := by
        rw [hϖ, IsScalarTower.algebraMap_apply A (κ0 A) (SeparableClosure (κ0 A)), AlgEquiv.commutes]
      have htw : ∀ i, dlog hζ (σ (γ i * phiB A a₀ (s' i) / ϖ ^ n i) / (γ i * phiB A a₀ (s' i) / ϖ ^ n i)) =
          dlog hζ (σ (γ i) / γ i) - (n i : ZMod d) * dlog hζ (σ ϖ / ϖ) := fun i =>
        KumForm.dlog_twist hζ σ (n i) (hγ0 i) (hs'0 i) hϖ0 (hσt σ hσ _)
          (by rw [hβ i, hσt σ hσ]) hϖd
      rw [KCe.obs_sub hι hadm hadmx, hobs σ hσ, Obs.obs_eq_of hι (hmx σ).symm]
      simp only [htw]
      exact (KumForm.sum_twist hd (fun i => dlog hζ (σ (γ i) / γ i)) n _ e).symm
  have hu : ∀ i, v i * s' i ^ (d - 1) ∉ P₀.asIdeal := fun i =>
    P₀.asIdeal.primeCompl.mul_mem (hv i) (P₀.asIdeal.primeCompl.pow_mem (hs' i) _)
  obtain ⟨V', G, w, hw, f, hf⟩ := exists_kill hex hι hN' hdA hζ hζG P₀ (s₀ - t₀) _ e hu a₀ h₀
  refine ⟨ax, ⟨V', w, (congrArg (fun φ => φ w) (MorphismProperty.Over.w G)).symm.trans
    ((congrArg (fun z => (specEt A B).hom z) hw).trans hP₀), ?_⟩, fun y hy => hgood c hc y hy⟩
  have h1 : Supp.sc (b - ax ≫ c) (specEt A B) = (c.hom.app (op (specEt A B))).hom (s₀ - t₀) := by
    rw [Supp.sc_sub, Supp.sc_comp, ← hs₀, ← ht₀]
    exact (LinearMap.map_sub (c.hom.app (op (specEt A B))).hom s₀ t₀).symm
  rw [← Supp.sc_map (b - ax ≫ c) G, h1]
  have h2 := congrArg (fun ψ => ψ.hom (s₀ - t₀)) (c.hom.naturality G.op)
  simp only [ModuleCat.hom_comp] at h2
  refine h2.symm.trans ?_
  show (c.hom.app (op V')).hom ((Q.obj.map ((etPull (gen A)).map G).op).hom (s₀ - t₀)) = 0
  rw [← hf]
  refine (congrArg (fun ψ => (ψ.hom.app (op V')).hom f) hc).trans ?_
  simp
  rfl

end RamanujanPetersson.EtCompact.Step

end

end

-- ===== S4.Def_RP_EtCompact_LerayG2 =====
section

/-!
# S4-EtCompact, part 41: the Leray step for `g_*` without `R²g_* = 0` (CC4, degrees 1-3)

Generic (`LerayG`, `adj : L ⊣ R`, `eAB : L A ≅ B`):
* **`H_push_one_eq_zero`**: `Ext¹(A, R F) = 0` when `Ext¹(B, F) = 0` (the edge `H¹(X, g_*F) ↪ H¹(Y, F)`);
* **`H_push_two_eq_zero'`**: `Ext²(A, R N) = 0` when `Ext²(B, -) = 0` and every `A`-section of `R¹R N` lifts to
  `R (I/N)` (no `R²R = 0` needed);
* **`H_push_three_eq_zero`**: `Ext³(A, R N) = 0` when moreover `Ext¹(A, R¹R N) = 0` and the sections of
  `R¹R (I/N)` lift.
Specialised to `pull g ⊣ push g` (étale cohomology `H Λ`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtCompact

namespace LerayG

open Abelian

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [EnoughInjectives D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.PreservesZeroMorphisms]
  [L.PreservesMonomorphisms] {A : C} {B : D} (eAB : L.obj A ≅ B) [HasExt.{w} C] [HasExt.{w} D]

include adj eAB in
/-- **`Ext¹(A, R F) = 0`** when `Ext¹(B, F) = 0`. -/
theorem H_push_one_eq_zero (F : D) (h1 : ∀ e : Ext.{w} B F 1, e = 0) (e : Ext.{w} A (R.obj F) 1) :
    e = 0 := by
  have : Injective (presA R F).X₂ := injective_push adj (Injective.under F)
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ (presA_shortExact adj F) e
    (Ext.eq_zero_of_injective _) (show 0 + 1 = 1 from rfl)
  obtain ⟨a, ha⟩ := lift_push adj eAB (cokernel.π (Injective.ι F))
    (lift_of_ext_one B (injPres_shortExact F) h1) (Ext.homEquiv₀ x₃ ≫ Abelian.image.ι (pushπ R F))
  have ha' : a ≫ Abelian.factorThruImage (pushπ R F) = Ext.homEquiv₀ x₃ := by
    rw [← cancel_mono (Abelian.image.ι (pushπ R F)), Category.assoc, Abelian.image.fac]
    exact ha
  have hx : x₃ = (Ext.mk₀ a).comp (Ext.mk₀ (Abelian.factorThruImage (pushπ R F))) (zero_add 0) := by
    rw [Ext.mk₀_comp_mk₀, ha', Ext.mk₀_homEquiv₀_apply]
  have hc : (Ext.mk₀ (Abelian.factorThruImage (pushπ R F))).comp (presA_shortExact adj F).extClass
      (zero_add 1) = 0 := (presA_shortExact adj F).comp_extClass
  rw [hx, Ext.comp_assoc_of_second_deg_zero, hc, Ext.comp_zero]

include adj eAB in
/-- **`Ext²(A, R N) = 0`** when `Ext²(B, -) = 0` and every `A`-section of `R¹R N` lifts to `R (I/N)`. -/
theorem H_push_two_eq_zero' (hη : ∀ (M : D) (e : Ext.{w} B M 2), e = 0) (N : D)
    (hs : ∀ b : A ⟶ R1 R N, ∃ a : A ⟶ R.obj (Qt N), a ≫ cokernel.π (pushπ R N) = b)
    (e : Ext.{w} A (R.obj N) 2) : e = 0 := by
  have : Injective (presA R N).X₂ := injective_push adj (Injective.under N)
  obtain ⟨x₃, rfl⟩ := Ext.covariant_sequence_exact₁ _ (presA_shortExact adj N) e
    (Ext.eq_zero_of_injective _) (show 1 + 1 = 2 from rfl)
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ (presB_shortExact R N) x₃
    (H_push_one_eq_zero adj eAB (Qt N) (H_Qt_one_eq_zero hη N) _) (show 0 + 1 = 1 from rfl)
  obtain ⟨a, ha⟩ := hs (Ext.homEquiv₀ y)
  have hy : y = (Ext.mk₀ a).comp (Ext.mk₀ (cokernel.π (pushπ R N))) (zero_add 0) := by
    rw [Ext.mk₀_comp_mk₀, ha, Ext.mk₀_homEquiv₀_apply]
  have hc : (Ext.mk₀ (cokernel.π (pushπ R N))).comp (presB_shortExact R N).extClass (zero_add 1) = 0 :=
    (presB_shortExact R N).comp_extClass
  rw [hy, Ext.comp_assoc_of_second_deg_zero, hc, Ext.comp_zero, Ext.zero_comp]

end LerayG

open RamanujanPetersson.EtSheaves

universe u

variable {X Y : Scheme.{u}} {g : Y ⟶ X} {Λ : Type u} [CommRing Λ]

/-- **`H²(X, g_*N) = 0`** when `H²(Y, -) = 0` and every global section of `R¹g_* N` lifts to `g_*(I/N)`. -/
theorem H_push_two_eq_zero' (hη : ∀ (M : EtSh Λ Y) (e : H Λ M 2), e = 0) (N : EtSh Λ Y)
    (hs : ∀ b : unitSh Λ X ⟶ R1 g Λ N,
      ∃ a : unitSh Λ X ⟶ (push g Λ).obj (Qt Λ N), a ≫ cokernel.π (LerayG.pushπ (push g Λ) N) = b)
    (e : H Λ ((push g Λ).obj N) 2) : e = 0 := by
  have := LerayG.pzm (pullAdj g Λ)
  exact LerayG.H_push_two_eq_zero' (pullAdj g Λ) (pullConst Λ g (ModuleCat.of Λ Λ)) hη N hs e

end RamanujanPetersson.EtCompact

end

end


