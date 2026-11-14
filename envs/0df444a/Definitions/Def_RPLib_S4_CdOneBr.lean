-- Prove2me | Definitions.Def_RPLib_S4_CdOneBr
-- name    : RPLib_S4_CdOneBr
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T05:02:54.463832+00:00
-- url     : https://prove2.me/theorems/fa5e46af-b42a-43a9-a283-84bf3ffad712
-- title:
--   $\mathrm{Br}(L/K) = 0$ for a finite Galois $p$-extension $L$ of a $C_1$ field $K$
-- statement:
--   For $K$ a $C_1$ field (strong form `RamanujanPetersson.Tsen.IsC1`: polynomials in $n$ variables of total degree $< n$ without constant term have a nonzero zero) and $L/K$ finite Galois with $\mathrm{Gal}(L/K)$ a $p$-group, every multiplicative 2-cocycle $\mathrm{Gal}(L/K)^2 \to L^\times$ is a coboundary (`br_eq_zero`, Mathlib's `groupCohomology.IsMulCocycle₂` / `IsMulCoboundary₂`). Proof by induction on $[L:K]$: a central subgroup $N$ of order $p$; the cyclic step for $L/L^N$ (norm surjectivity of finite extensions of $C_1$ fields); Hilbert 90 for $N$ (`h1_subgroup`); degree-2 inflation-restriction; descent to $\mathrm{Gal}(L^N/K)$ (`isCoboundary₂_descend`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Galois cohomology layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, Graduate Texts in Mathematics 67, Springer 1979, doi:10.1007/978-1-4757-5673-9, Chapter X, Section 7; J.-P. Serre, Galois Cohomology, Springer 1997, doi:10.1007/978-3-642-59141-9, Chapter II, Section 3; S. Lang, On quasi algebraic closure, Ann. of Math. (2) 55 (1952), 373-390, doi:10.2307/1969785

import Mathlib
import Definitions.Def_RPLib_S4_CdOneCoh
import Definitions.Def_RPLib_S4_Tsen

/-!
# S4-PD (3a), part 2: `Br(L/K) = 0` for a Galois `p`-extension of a C1 field

`br_eq_zero`: if `K` is C1 and `L/K` is finite Galois with `Gal(L/K)` a `p`-group, every multiplicative 2-cocycle
`Gal(L/K)² → Lˣ` is a coboundary. Induction on `[L : K]`: a central subgroup `N` of order `p`, the cyclic case
for `L / L^N` (norm surjectivity from C1), Hilbert 90 on `N`, inflation-restriction, and descent to `Gal(L^N/K)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe v

namespace RamanujanPetersson.CdOne

open groupCohomology IntermediateField RamanujanPetersson.Tsen

section Mul

variable {G M : Type*} [Monoid G] [CommGroup M] [MulDistribMulAction G M]

/-- `Additive M` with the action induced by the multiplicative action of `G` on `M`. -/
abbrev addAct : DistribMulAction G (Additive M) where
  smul g a := Additive.ofMul (g • a.toMul)
  one_smul a := by show Additive.ofMul ((1 : G) • a.toMul) = a; rw [one_smul]; rfl
  mul_smul g h a := by
    show Additive.ofMul ((g * h) • a.toMul) = Additive.ofMul (g • (h • a.toMul)); rw [mul_smul]
  smul_zero g := by show Additive.ofMul (g • (1 : M)) = Additive.ofMul 1; rw [smul_one]
  smul_add g a b := by
    show Additive.ofMul (g • (a.toMul * b.toMul)) = Additive.ofMul (g • a.toMul * g • b.toMul)
    rw [smul_mul']

attribute [local instance] addAct

theorem isCocycle₂_ofMul {f : G × G → M} (hf : IsMulCocycle₂ f) :
    IsCocycle₂ (fun q => Additive.ofMul (f q)) := fun g h j => hf g h j

theorem isMulCoboundary₂_of_ofMul {f : G × G → M} (h : IsCoboundary₂ (fun q => Additive.ofMul (f q))) :
    IsMulCoboundary₂ f := by
  obtain ⟨x, hx⟩ := h
  exact ⟨fun g => (x g).toMul, fun g h => hx g h⟩

end Mul

attribute [local instance] addAct

section Galois

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- `Gal(L / L^N) ≃* N`. -/
noncomputable def galFixedEquiv (N : Subgroup Gal(L/K)) : Gal(L/fixedField N) ≃* N :=
  (fixingSubgroupEquiv (fixedField N)).symm.trans (MulEquiv.subgroupCongr (fixingSubgroup_fixedField N))

theorem galFixedEquiv_apply (N : Subgroup Gal(L/K)) (τ : Gal(L/fixedField N)) (y : L) :
    ((galFixedEquiv N τ : N) : Gal(L/K)) y = τ y := rfl

/-- Hilbert 90 for a subgroup `N` acting on `Lˣ` (through `Gal(L / L^N)`). -/
theorem h1_subgroup (N : Subgroup Gal(L/K)) (φ : N → Additive Lˣ) (hφ : IsCocycle₁ φ) : IsCoboundary₁ φ := by
  set e := galFixedEquiv N
  have hact : ∀ (τ : Gal(L/fixedField N)) (u : Lˣ), ((e τ : N) : Gal(L/K)) • u = τ • u :=
    fun τ u => Units.ext rfl
  have hφ' : IsMulCocycle₁ (fun τ : Gal(L/fixedField N) => (φ (e τ)).toMul) := by
    intro τ τ'
    show (φ (e (τ * τ'))).toMul = τ • (φ (e τ')).toMul * (φ (e τ)).toMul
    rw [map_mul, hφ (e τ) (e τ'), ← hact]
    rfl
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hφ'
  refine ⟨Additive.ofMul β, fun n => ?_⟩
  obtain ⟨τ, rfl⟩ := e.surjective n
  have := hβ τ
  rw [← hact] at this
  exact congrArg Additive.ofMul this

/-- A `z`-fixed element is a "norm" `∏_{t < ord z} z^t(y)` when the norm to `L^⟨z⟩` is surjective. -/
theorem exists_prod_pow_eq [IsGalois K L] (z : Gal(L/K))
    (hsurj : Function.Surjective (Algebra.norm (fixedField (Subgroup.zpowers z)) : L → _)) (x : L)
    (hx : z x = x) : ∃ y : L, ∏ t ∈ Finset.range (orderOf z), (z ^ t) y = x := by
  classical
  set N := Subgroup.zpowers z
  have hxN : x ∈ fixedField N := by
    rw [mem_fixedField_iff]
    intro g hg
    have hst : N ≤ MulAction.stabilizer Gal(L/K) x :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hx)
    exact MulAction.mem_stabilizer_iff.mp (hst hg)
  obtain ⟨y, hy⟩ := hsurj ⟨x, hxN⟩
  refine ⟨y, ?_⟩
  have h1 := Algebra.norm_eq_prod_automorphisms (fixedField N) y
  rw [hy] at h1
  change x = ∏ σ : Gal(L/fixedField N), σ y at h1
  rw [h1]
  have hfin : IsOfFinOrder z := isOfFinOrder_of_finite z
  calc ∏ t ∈ Finset.range (orderOf z), (z ^ t) y = ∏ i : Fin (orderOf z), (z ^ (i : ℕ)) y :=
        (Fin.prod_univ_eq_prod_range (fun t => (z ^ t) y) _).symm
    _ = ∏ n : N, (n : Gal(L/K)) y :=
        Fintype.prod_equiv (finEquivZPowers hfin) _ _ (fun i => by rw [finEquivZPowers_apply])
    _ = ∏ σ : Gal(L/fixedField N), σ y := by
        convert (Fintype.prod_equiv (galFixedEquiv N) (fun τ : Gal(L/fixedField N) => τ y) (fun n : N => (n : Gal(L/K)) y)
          (fun τ => rfl)).symm

/-- The cyclic step: the restriction of a cocycle to `⟨z⟩` is a coboundary. -/
theorem isCoboundary₂_zpowers [IsGalois K L] (z : Gal(L/K))
    (hsurj : Function.Surjective (Algebra.norm (fixedField (Subgroup.zpowers z)) : L → _))
    {f : Gal(L/K) × Gal(L/K) → Lˣ} (hf : IsMulCocycle₂ f) :
    IsCoboundary₂ (fun q : Subgroup.zpowers z × Subgroup.zpowers z =>
      Additive.ofMul (f ((q.1 : Gal(L/K)), (q.2 : Gal(L/K))))) := by
  set N := Subgroup.zpowers z
  set σ : N := ⟨z, Subgroup.mem_zpowers z⟩
  have hfin : IsOfFinOrder z := isOfFinOrder_of_finite z
  have hord : orderOf σ = orderOf z := Subgroup.orderOf_mk z _
  have hσ : ∀ g : N, ∃ i : ℕ, σ ^ i = g := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := Submonoid.mem_powers_iff _ _ |>.mp (hfin.mem_powers_iff_mem_zpowers.mpr hg)
    exact ⟨k, Subtype.ext (by simpa [σ] using hk)⟩
  have hfc : IsCocycle₂ (fun q : N × N => Additive.ofMul (f ((q.1 : Gal(L/K)), (q.2 : Gal(L/K))))) :=
    fun g h j => hf g h j
  refine isCoboundary₂_of_cyclic hσ hfc (fun a ha => ?_)
  have hza : z ((a.toMul : Lˣ) : L) = ((a.toMul : Lˣ) : L) :=
    congrArg (fun u : Additive Lˣ => ((u.toMul : Lˣ) : L)) ha
  obtain ⟨y, hy⟩ := exists_prod_pow_eq z hsurj _ hza
  have hy0 : y ≠ 0 := by
    rintro rfl
    refine (a.toMul).ne_zero ?_
    rw [← hy]
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hfin.orderOf_pos) (map_zero _)
  refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  rw [toMul_sum, Units.coe_prod, hord, ← hy]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- Descent: a cocycle inflated from `Gal(L/K) ⧸ N` with values in `(Lˣ)^N` is a coboundary when
`Br(L^N / K) = 0`. -/
theorem isCoboundary₂_descend [IsGalois K L] (N : Subgroup Gal(L/K)) [N.Normal]
    {F : Gal(L/K) × Gal(L/K) → Additive Lˣ} (hF : IsCocycle₂ F)
    (hinv : ∀ g h : Gal(L/K), ∀ n ∈ N, F (g * n, h) = F (g, h) ∧ F (g, h * n) = F (g, h) ∧
      n • F (g, h) = F (g, h))
    (hE : ∀ fb : Gal(fixedField N/K) × Gal(fixedField N/K) → (fixedField N)ˣ, IsMulCocycle₂ fb →
      IsMulCoboundary₂ fb) :
    IsCoboundary₂ F := by
  set E := fixedField N
  set res := AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E
  have hres : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective L
  set lift := Function.surjInv hres
  have hlift : ∀ σ, res (lift σ) = σ := Function.surjInv_eq hres
  have hker : ∀ g g', res g = res g' → g⁻¹ * g' ∈ N := by
    intro g g' h
    have : g⁻¹ * g' ∈ res.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [IntermediateField.restrictNormalHom_ker, fixingSubgroup_fixedField] at this
    exact this
  have hFres : ∀ g g' h h', res g = res g' → res h = res h' → F (g, h) = F (g', h') := by
    intro g g' h h' hg hh
    rw [show g' = g * (g⁻¹ * g') by group, show h' = h * (h⁻¹ * h') by group,
      (hinv g _ _ (hker g g' hg)).1, (hinv g h _ (hker h h' hh)).2.1]
  have hval : ∀ g h, (((F (g, h)).toMul : Lˣ) : L) ∈ E := by
    intro g h
    rw [mem_fixedField_iff]
    intro n hn
    exact congrArg (fun u : Additive Lˣ => ((u.toMul : Lˣ) : L)) (hinv g h n hn).2.2
  let fb : Gal(E/K) × Gal(E/K) → Eˣ := fun q =>
    Units.mk0 ⟨(((F (lift q.1, lift q.2)).toMul : Lˣ) : L), hval _ _⟩
      (fun h0 => (F (lift q.1, lift q.2)).toMul.ne_zero (congrArg Subtype.val h0))
  have hact : ∀ (σ : Gal(E/K)) (e : E), ((σ e : E) : L) = (lift σ) (e : L) := by
    intro σ e
    conv_lhs => rw [← hlift σ]
    exact AlgEquiv.restrictNormalHom_apply E (lift σ) e
  have hfb : IsMulCocycle₂ fb := by
    intro σ τ ρ
    have e1 : F (lift (σ * τ), lift ρ) = F (lift σ * lift τ, lift ρ) :=
      hFres _ _ _ _ (by rw [map_mul, hlift, hlift, hlift]) rfl
    have e2 : F (lift σ, lift (τ * ρ)) = F (lift σ, lift τ * lift ρ) :=
      hFres _ _ _ _ rfl (by rw [map_mul, hlift, hlift, hlift])
    have key := congrArg (fun u : Additive Lˣ => ((u.toMul : Lˣ) : L)) (hF (lift σ) (lift τ) (lift ρ))
    apply Units.ext; apply Subtype.ext
    show (((F (lift (σ * τ), lift ρ)).toMul : Lˣ) : L) * (((F (lift σ, lift τ)).toMul : Lˣ) : L) =
      ((σ ((fb (τ, ρ) : Eˣ) : E) : E) : L) * (((F (lift σ, lift (τ * ρ))).toMul : Lˣ) : L)
    rw [hact, e1, e2]
    exact key
  obtain ⟨x, hx⟩ := hE fb hfb
  set ιu : Eˣ →* Lˣ := Units.map (algebraMap E L).toMonoidHom
  have hιu : ∀ (g : Gal(L/K)) (u : Eˣ), ιu ((res g : Gal(E/K)) • u : Eˣ) = g • ιu u := fun g u =>
    Units.ext (AlgEquiv.restrictNormalHom_apply E g (u : E))
  have hιf : ∀ σ τ, ιu (fb (σ, τ)) = (F (lift σ, lift τ)).toMul := fun _ _ => Units.ext rfl
  refine ⟨fun g => Additive.ofMul (ιu (x (res g))), fun g h => ?_⟩
  have := congrArg ιu (hx (res g) (res h))
  rw [map_mul, map_div, hιu, hιf, ← map_mul res g h,
    hFres (lift (res g)) g (lift (res h)) h (hlift _) (hlift _)] at this
  exact congrArg Additive.ofMul this

end Galois

/-- **`Br(L/K) = 0`** for a finite Galois `p`-extension `L` of a C1 field `K`: every multiplicative
2-cocycle `Gal(L/K)² → Lˣ` is a coboundary. -/
theorem br_eq_zero_aux {K : Type*} [Field K] (hK : IsC1 K) (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ∀ (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
      Module.finrank K L ≤ n → IsPGroup p Gal(L/K) →
      ∀ f : Gal(L/K) × Gal(L/K) → Lˣ, IsMulCocycle₂ f → IsMulCoboundary₂ f := by
  induction n with
  | zero =>
    intro L _ _ _ _ hn
    have := Module.finrank_pos (R := K) (M := L)
    omega
  | succ n ih =>
    intro L _ _ _ _ hn hG f hf
    by_cases htriv : Subsingleton Gal(L/K)
    · refine ⟨fun _ => f (1, 1), fun g h => ?_⟩
      rw [Subsingleton.elim g 1, Subsingleton.elim h 1]
      simp
    rw [not_subsingleton_iff_nontrivial] at htriv
    -- a central element of order `p`
    have := hG.center_nontrivial
    have hc : p ∣ Nat.card (Subgroup.center Gal(L/K)) :=
      ((hG.to_subgroup _).card_eq_or_dvd).resolve_left Finite.one_lt_card.ne'
    obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' p hc
    set z : Gal(L/K) := (z0 : Gal(L/K))
    have hzc : z ∈ Subgroup.center Gal(L/K) := z0.2
    have hzp : orderOf z = p := by rw [Subgroup.orderOf_coe]; exact hz0
    set N := Subgroup.zpowers z
    have hNn : N.Normal := ⟨fun m hm g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
      have hcomm : Commute g z := Subgroup.mem_center_iff.mp hzc g
      rw [(hcomm.zpow_right k).eq, mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers z k⟩
    set E := fixedField N
    have hE1 : IsC1 E := IsC1.of_finite hK
    have hsurj : Function.Surjective (Algebra.norm E : L → E) := IsC1.norm_surjective hE1
    -- degrees
    have hdeg : Module.finrank K E < Module.finrank K L := by
      have h1 := Module.finrank_mul_finrank K E L
      have h2 : Module.finrank E L = p := by
        rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hzp]
      have h3 := Module.finrank_pos (R := K) (M := E)
      have h4 := hp.out.two_le
      rw [h2] at h1
      nlinarith
    have hGE : IsPGroup p Gal(E/K) :=
      hG.of_surjective (AlgEquiv.restrictNormalHom E) (AlgEquiv.restrictNormalHom_surjective L)
    -- the three steps
    have hNf := isCoboundary₂_zpowers z hsurj hf
    obtain ⟨b, hbc, hbinv⟩ := exists_inflated N (isCocycle₂_ofMul hf) (h1_subgroup N) hNf
    apply isMulCoboundary₂_of_ofMul
    apply isCoboundary₂_of_sub b
    exact isCoboundary₂_descend N hbc hbinv (fun fb hfb => ih E (by omega) hGE fb hfb)

theorem br_eq_zero {K : Type*} [Field K] (hK : IsC1 K) (p : ℕ) [Fact p.Prime] (L : Type v) [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (hG : IsPGroup p Gal(L/K))
    (f : Gal(L/K) × Gal(L/K) → Lˣ) (hf : IsMulCocycle₂ f) : IsMulCoboundary₂ f :=
  br_eq_zero_aux hK p _ L le_rfl hG f hf

end RamanujanPetersson.CdOne


