-- Prove2me | Definitions.Def_RPLib_S4_CDPack25
-- name    : RPLib_S4_CDPack25
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:24:03.509831+00:00
-- url     : https://prove2.me/theorems/4344275e-4b5d-4a9a-a15a-1e93fe20c606
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 25 of 71
-- statement:
--   Part 25 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacSymB_Noeth`: S4-JacSymB, file C: finiteness of `X^g` and `Sym^g X`; points of `A^g`
--   * `Def_RP_JacSymB_SymLoc`: S4-JacSymB, file F4: `Sym^g` commutes with localization at a norm (L12)
--   * `Def_RP_JacLaw_Span`: S4-JacLaw, file O1: `Sym^g(B)` is spanned by norms (polarization over an infinite field)
--   * `Def_RP_JacSymB_GenPoly`: S4-JacSymB, file H2b: the generic polynomial `E(w) = ∏_l (1 - w_l X)` (L12, valuative criterion)
--   * `Def_RP_JacLaw_Crit`: S4-JacLaw, file O2: the morphism criterion for maps into `Sym^n`
--   * `Def_RP_JacLaw_Add`: S4-JacLaw, file O7: addition `Sym^d × Sym^e → Sym^(d+e)`
--   * `Def_RP_JacComplete_PicK`: The Jacobian (unit S4-JacComplete), part `PicK`: divisor classes over an arbitrary constant field
--   * `Def_RP_JacSymB_GenInt`: S4-JacSymB, file H2d: integrality of `X^g(B)` over the coefficients of `E(w)` (L12, valuative criterion)
--   * `Def_RP_IntersectA_GI`: S4-IntersectA, file GI: integral varieties over an algebraically closed field are geometrically integral
--   * `Def_RP_IntersectA_Prod`: S4-IntersectA, file Prod: products of integral varieties over an algebraically closed field
--   * `Def_RP_IsogDegA_AlgMax`: S4-IsogDegA, file AlgMax: `k`-points of the fibre = primes over the maximal ideal (G1)
--   * `Def_RP_IsogDegA_SpecFib`: S4-IsogDegA, file SpecFib: scheme fibres as primes over a prime (G2, part 1)
--   * `Def_RP_JacFrob_TanP`: S4-JacFrob, part TanP: `q`-th roots in `Sym^g` (generic)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack20
import Definitions.Def_RPLib_S4_CDPack17

/-!
# Curve-duality library package, part 25 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacSymB_Noeth`: S4-JacSymB, file C: finiteness of `X^g` and `Sym^g X`; points of `A^g`
* `Def_RP_JacSymB_SymLoc`: S4-JacSymB, file F4: `Sym^g` commutes with localization at a norm (L12)
* `Def_RP_JacLaw_Span`: S4-JacLaw, file O1: `Sym^g(B)` is spanned by norms (polarization over an infinite field)
* `Def_RP_JacSymB_GenPoly`: S4-JacSymB, file H2b: the generic polynomial `E(w) = ∏_l (1 - w_l X)` (L12, valuative criterion)
* `Def_RP_JacLaw_Crit`: S4-JacLaw, file O2: the morphism criterion for maps into `Sym^n`
* `Def_RP_JacLaw_Add`: S4-JacLaw, file O7: addition `Sym^d × Sym^e → Sym^(d+e)`
* `Def_RP_JacComplete_PicK`: The Jacobian (unit S4-JacComplete), part `PicK`: divisor classes over an arbitrary constant field
* `Def_RP_JacSymB_GenInt`: S4-JacSymB, file H2d: integrality of `X^g(B)` over the coefficients of `E(w)` (L12, valuative criterion)
* `Def_RP_IntersectA_GI`: S4-IntersectA, file GI: integral varieties over an algebraically closed field are geometrically integral
* `Def_RP_IntersectA_Prod`: S4-IntersectA, file Prod: products of integral varieties over an algebraically closed field
* `Def_RP_IsogDegA_AlgMax`: S4-IsogDegA, file AlgMax: `k`-points of the fibre = primes over the maximal ideal (G1)
* `Def_RP_IsogDegA_SpecFib`: S4-IsogDegA, file SpecFib: scheme fibres as primes over a prime (G2, part 1)
* `Def_RP_JacFrob_TanP`: S4-JacFrob, part TanP: `q`-th roots in `Sym^g` (generic)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacSymB_Noeth =====
section

/-!
# S4-JacSymB, file C: finiteness of `X^g` and `Sym^g X`; points of `A^g`

`X^g` and `Sym^g X` are of finite type over `k` (Artin-Tate for the invariants), `X^g` is a finite `Sym^g X`-module,
`Sym^g X` is Noetherian, `symMap` is functorial, and the kernel of a `k`-point of a ring `≃ₐ` a polynomial ring in `g`
variables is generated by `g` elements.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section Comp

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {B'' : Type*} [CommRing B''] [Algebra k B''] {g : ℕ}

theorem xMap_comp (f : B →ₐ[k] B') (f' : B' →ₐ[k] B'') :
    xMap (g := g) (f'.comp f) = (xMap f').comp (xMap f) := by
  apply PiTensorProduct.algHom_ext
  intro i
  change (xMap (f'.comp f)).comp (inc i) = ((xMap f').comp (xMap f)).comp (inc i)
  rw [xMap_inc, AlgHom.comp_assoc, xMap_inc, ← AlgHom.comp_assoc, ← AlgHom.comp_assoc, xMap_inc]

theorem symMap_comp (f : B →ₐ[k] B') (f' : B' →ₐ[k] B'') :
    symMap (g := g) (f'.comp f) = (symMap f').comp (symMap f) := by
  ext x
  change xMap (f'.comp f) (x : XPow k B g) = xMap f' (xMap f x)
  rw [xMap_comp]
  rfl

theorem finiteType_xPow [Algebra.FiniteType k B] : Algebra.FiniteType k (XPow k B g) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k B).FG)
  refine ⟨⟨Finset.univ.biUnion (fun i : Fin g => s.image (inc i)), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r b =>
    refine Subalgebra.smul_mem _ ?_ r
    rw [← prod_inc]
    refine prod_mem fun i _ => ?_
    have hb : b i ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
    have h1 : inc i (b i) ∈ (Algebra.adjoin k (s : Set B)).map (inc i) := Subalgebra.mem_map.2 ⟨b i, hb, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine Algebra.adjoin_mono ?_ h1
    rintro y ⟨z, hz, rfl⟩
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, Finset.mem_image.2 ⟨z, hz, rfl⟩⟩
  | add x y hx hy => exact add_mem hx hy

end Comp

section Noeth

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] [Algebra.FiniteType k B] {g : ℕ}

instance : Algebra.FiniteType k (XPow k B g) := finiteType_xPow

instance : Algebra.FiniteType (SymRing k B g) (XPow k B g) :=
  Algebra.FiniteType.of_restrictScalars_finiteType (R := k) (S := SymRing k B g) (A := XPow k B g)

instance moduleFinite_symRing : Module.Finite (SymRing k B g) (XPow k B g) := Algebra.IsIntegral.finite

instance finiteType_symRing : Algebra.FiniteType k (SymRing k B g) :=
  ⟨fg_of_fg_of_fg (A := k) (B := SymRing k B g) (C := XPow k B g) Algebra.FiniteType.out
    Module.Finite.fg_top Subtype.val_injective⟩

instance isNoetherianRing_symRing : IsNoetherianRing (SymRing k B g) :=
  Algebra.FiniteType.isNoetherianRing k _

instance isNoetherianRing_xPow : IsNoetherianRing (XPow k B g) :=
  Algebra.FiniteType.isNoetherianRing k _

end Noeth

section Point

variable {k : Type*} [Field k] {g : ℕ}

/-- The kernel of a `k`-point of a ring isomorphic to `k[X_1, ..., X_g]` is generated by `g` elements. -/
theorem ker_eq_span_of_equiv {R : Type*} [CommRing R] [Algebra k R] (e : R ≃ₐ[k] MvPolynomial (Fin g) k)
    (ψ : R →ₐ[k] k) :
    RingHom.ker ψ = Ideal.span (Set.range fun j : Fin g =>
      e.symm (MvPolynomial.X j) - algebraMap k R (ψ (e.symm (MvPolynomial.X j)))) := by
  set I := Ideal.span (Set.range fun j : Fin g =>
      e.symm (MvPolynomial.X j) - algebraMap k R (ψ (e.symm (MvPolynomial.X j))))
  have hq : (Ideal.Quotient.mkₐ k I).comp (e.symm : MvPolynomial (Fin g) k →ₐ[k] R) =
      ((Algebra.ofId k (R ⧸ I)).comp ψ).comp (e.symm : MvPolynomial (Fin g) k →ₐ[k] R) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply]
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hq' : ∀ r : R, Ideal.Quotient.mk I r = algebraMap k (R ⧸ I) (ψ r) := fun r => by
    have h := DFunLike.congr_fun hq (e r)
    have he : (e.symm : MvPolynomial (Fin g) k →ₐ[k] R) (e r) = r := e.symm_apply_apply r
    simp only [AlgHom.comp_apply, he, Ideal.Quotient.mkₐ_eq_mk, Algebra.ofId_apply] at h
    exact h
  apply le_antisymm
  · intro r hr
    rw [← Ideal.Quotient.eq_zero_iff_mem, hq', (RingHom.mem_ker).1 hr, map_zero]
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp [RingHom.mem_ker]

end Point

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymB_SymLoc =====
section

/-!
# S4-JacSymB, file F4: `Sym^g` commutes with localization at a norm (L12)

If `B → B'` is injective and `B' = B[1/w]`, then `Sym^g B' = (Sym^g B)[1/N w]` with `N w = ∏_l w_l` (over a field `k`).
So the chart maps `Spec Sym^g B_A' → Spec Sym^g B_A` are open immersions.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section SymLoc

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {g : ℕ}

theorem xMap_id : xMap (g := g) (AlgHom.id k B) = AlgHom.id k (XPow k B g) := by
  apply PiTensorProduct.algHom_ext
  intro i
  change (xMap (AlgHom.id k B)).comp (inc i) = (AlgHom.id k _).comp (inc i)
  rw [xMap_inc]
  rfl

theorem symMap_id : symMap (g := g) (AlgHom.id k B) = AlgHom.id k (SymRing k B g) := by
  ext x
  change xMap (AlgHom.id k B) (x : XPow k B g) = x
  rw [xMap_id]
  rfl

theorem secMap_xMap (f : B →ₐ[k] B') (s : B' →ₗ[k] B) (hs : ∀ b, s (f b) = b) (x : XPow k B g) :
    secMap s (xMap f x) = x := by
  change ((secMap s).comp (xMap f).toLinearMap) x = (LinearMap.id : XPow k B g →ₗ[k] XPow k B g) x
  congr 1
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro b
  simp [secMap, PiTensorProduct.map_tprod, hs]

theorem xMap_injective (f : B →ₐ[k] B') (hf : Function.Injective f) : Function.Injective (xMap (g := g) f) := by
  obtain ⟨s, hs⟩ := f.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (by exact hf))
  have hs' : ∀ b, s (f b) = b := fun b => by simpa using LinearMap.congr_fun hs b
  intro x y hxy
  rw [← secMap_xMap f s hs' x, hxy, secMap_xMap f s hs' y]

theorem symMap_injective (f : B →ₐ[k] B') (hf : Function.Injective f) : Function.Injective (symMap (g := g) f) :=
  fun x y hxy => Subtype.ext (xMap_injective f hf (by
    have := congrArg (fun z : SymRing k B' g => (z : XPow k B' g)) hxy
    simpa only [symMap_coe] using this))

variable (k) in
/-- The norm `N w = ∏_l w_l`, an `S_g`-invariant. -/
noncomputable def normS (w : B) : SymRing k B g :=
  ⟨∏ l, inc l w, (mem_symRing _).mpr fun σ => by
    rw [perm_smul_def, map_prod]
    exact Fintype.prod_equiv σ _ _ fun l => AlgHom.congr_fun (permHom_comp_inc σ l) w⟩

theorem normS_coe (w : B) : (normS k (g := g) w : XPow k B g) = ∏ l, inc l w := rfl

theorem normS_mul (a b : B) : normS k (g := g) (a * b) = normS k a * normS k b := by
  apply Subtype.ext
  simp only [normS_coe, MulMemClass.coe_mul, map_mul, Finset.prod_mul_distrib]

theorem normS_one : normS k (g := g) (1 : B) = 1 := by
  apply Subtype.ext
  simp only [normS_coe, map_one, Finset.prod_const_one, OneMemClass.coe_one]

theorem xMap_prod_inc (f : B →ₐ[k] B') (w : B) : xMap (g := g) f (∏ l, inc l w) = ∏ l, inc l (f w) := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun l _ => AlgHom.congr_fun (xMap_inc f l) w

theorem symMap_normS (f : B →ₐ[k] B') (w : B) : symMap (g := g) f (normS k w) = normS k (f w) := by
  apply Subtype.ext
  rw [symMap_coe, normS_coe, normS_coe, xMap_prod_inc]

/-- `X'^g = X^g[1/N w]` on elements. -/
theorem exists_xMap_eq (f : B →ₐ[k] B') (w : B) (hs : ∀ b' : B', ∃ (n : ℕ) (b : B), f b = f w ^ n * b')
    (t : XPow k B' g) : ∃ (n : ℕ) (u : XPow k B g), xMap f u = (∏ l, inc l (f w)) ^ n * t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r b' =>
    choose n b hb using fun l => hs (b' l)
    refine ⟨∑ l, n l, r • PiTensorProduct.tprod k (fun l => w ^ (∑ l, n l - n l) * b l), ?_⟩
    rw [map_smul, xMap_tprod, mul_smul_comm, ← prod_inc, ← prod_inc, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← map_pow, ← map_mul, map_mul f, map_pow f, hb l, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l))]
  | add t1 t2 h1 h2 =>
    obtain ⟨n1, u1, hu1⟩ := h1
    obtain ⟨n2, u2, hu2⟩ := h2
    refine ⟨n1 + n2, (∏ l, inc l w) ^ n2 * u1 + (∏ l, inc l w) ^ n1 * u2, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, hu1, hu2, xMap_prod_inc]
    ring

/-- `Sym^g B' = (Sym^g B)[1/N w]` when `B' = B[1/w]` (`B → B'` injective). -/
theorem isLocalization_symMap (f : B →ₐ[k] B') (hf : Function.Injective f) (w : B) (hu : IsUnit (f w))
    (hs : ∀ b' : B', ∃ (n : ℕ) (b : B), f b = f w ^ n * b') :
    letI := (symMap (g := g) f).toRingHom.toAlgebra
    IsLocalization.Away (normS k (g := g) w) (SymRing k B' g) := by
  letI := (symMap (g := g) f).toRingHom.toAlgebra
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · change IsUnit (symMap f (normS k w))
    rw [symMap_normS]
    obtain ⟨v, hv⟩ := hu
    refine ⟨⟨normS k (f w), normS k (↑v⁻¹ : B'), ?_, ?_⟩, rfl⟩
    · rw [← normS_mul, ← hv, Units.mul_inv, normS_one]
    · rw [← normS_mul, ← hv, Units.inv_mul, normS_one]
  · intro s
    obtain ⟨n, u, hu'⟩ := exists_xMap_eq f w hs (s : XPow k B' g)
    have h1 : (∏ l, inc l (f w)) ^ n * (s : XPow k B' g) =
        ((normS k (g := g) (f w) ^ n * s : SymRing k B' g) : XPow k B' g) := by
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, normS_coe]
    have hinv : u ∈ SymRing k B g := by
      rw [mem_symRing]
      intro σ
      apply xMap_injective f hf
      rw [xMap_smul, hu', h1, smul_symRing]
    refine ⟨n, ⟨u, hinv⟩, ?_⟩
    change s * symMap f (normS k w) ^ n = symMap f ⟨u, hinv⟩
    apply Subtype.ext
    rw [symMap_normS, symMap_coe]
    change _ = xMap f u
    rw [hu', h1, mul_comm]
  · intro a b hab
    exact ⟨0, by rw [pow_zero, one_mul, one_mul]; exact symMap_injective f hf hab⟩

end SymLoc

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacLaw_Span =====
section

/-!
# S4-JacLaw, file O1: `Sym^g(B)` is spanned by norms (polarization over an infinite field)

For an infinite field `k` and any commutative `k`-algebra `B`, the symmetric tensors
`SymRing k B g ⊆ ⨂^g B` are the `k`-span of the norms `N(w) = ∏_l w_l = w ⊗ ... ⊗ w`.
Proof: a functional `ℓ` killing every `w ⊗ ... ⊗ w` gives, for `w = Σ_j x_j b_j`, a polynomial identity in
the `x_j`; over an infinite field all its coefficients vanish, i.e. `ℓ` kills every orbit sum of basis
tensors; a symmetric tensor is a combination of orbit sums.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym

section Span

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {g : ℕ}

theorem normS_coe_eq_tprod (w : B) :
    (normS k (g := g) w : XPow k B g) = PiTensorProduct.tprod k (fun _ : Fin g => w) := by
  have h : (fun _ : Fin g => w) = ∏ i, Pi.mulSingle i w :=
    (Finset.univ_prod_mulSingle (fun _ : Fin g => w)).symm
  rw [normS_coe, h, PiTensorProduct.tprod_prod]
  rfl

theorem sum_single_apply {ι : Type*} [DecidableEq ι] (f : Fin g → ι) (a : ι) :
    (∑ i, Finsupp.single (f i) 1 : ι →₀ ℕ) a = Multiset.count a (Finset.univ.val.map f) := by
  rw [Finsupp.finsetSum_apply, Multiset.count_map]
  simp only [Finsupp.single_apply, Finset.sum_boole, Nat.cast_id]
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun i _ => eq_comm)

theorem mset_eq_of_sum_single_eq {ι : Type*} [DecidableEq ι] (f h : Fin g → ι)
    (hfh : (∑ i, Finsupp.single (f i) 1 : ι →₀ ℕ) = ∑ i, Finsupp.single (h i) 1) : mset f = mset h := by
  apply Sym.coe_injective
  rw [mset_coe, mset_coe]
  ext a
  rw [← sum_single_apply, ← sum_single_apply, hfh]

theorem repr_permHom {ι : Type*} (b : Module.Basis ι k B) (σ : Equiv.Perm (Fin g)) (x : XPow k B g)
    (p : Fin g → ι) :
    (Basis.piTensorProduct (fun _ : Fin g => b)).repr (permHom σ x) p =
      (Basis.piTensorProduct (fun _ : Fin g => b)).repr x (p ∘ σ) := by
  classical
  set bT := Basis.piTensorProduct (fun _ : Fin g => b)
  have key : (Finsupp.lapply p).comp (bT.repr.toLinearMap.comp (permHom σ).toLinearMap) =
      (Finsupp.lapply (p ∘ σ)).comp bT.repr.toLinearMap := by
    refine bT.ext fun q => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, Finsupp.lapply_apply]
    have hq : permHom σ (bT q) = bT (q ∘ σ.symm) := by
      simp only [bT, Basis.piTensorProduct_apply, permHom_tprod, Function.comp_apply]
    rw [hq, Module.Basis.repr_self, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
    have hiff : q ∘ σ.symm = p ↔ q = p ∘ σ := by
      constructor
      · rintro rfl; funext i; simp
      · rintro rfl; funext i; simp
    simp only [hiff]
  exact LinearMap.congr_fun key x

/-- Polarization: a permutation-invariant tensor is a combination of `w ⊗ ... ⊗ w`. -/
theorem mem_span_tprod_of_fixed [Infinite k] (t : XPow k B g)
    (ht : ∀ σ : Equiv.Perm (Fin g), permHom σ t = t) :
    t ∈ Submodule.span k (Set.range fun w : B => PiTensorProduct.tprod k (fun _ : Fin g => w)) := by
  classical
  set W := Submodule.span k (Set.range fun w : B => PiTensorProduct.tprod k (fun _ : Fin g => w))
  by_contra hnot
  obtain ⟨ℓ, hℓt, hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hℓW : ∀ w : B, ℓ (PiTensorProduct.tprod k (fun _ : Fin g => w)) = 0 := by
    intro w
    have h1 : ℓ (PiTensorProduct.tprod k (fun _ : Fin g => w)) ∈ W.map ℓ :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨w, rfl⟩)
    rwa [hW, Submodule.mem_bot] at h1
  set b := Module.Basis.ofVectorSpace k B
  set bT := Basis.piTensorProduct (fun _ : Fin g => b)
  set c := bT.repr t
  set J := c.support.biUnion (fun f => Finset.univ.image f)
  set F := Fintype.piFinset (fun _ : Fin g => J)
  have hsF : c.support ⊆ F := by
    intro f hf
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_image_of_mem f (Finset.mem_univ i)⟩
  set κ : (Fin g → Module.Basis.ofVectorSpaceIndex k B) → (Module.Basis.ofVectorSpaceIndex k B →₀ ℕ) :=
    fun f => ∑ i, Finsupp.single (f i) 1
  set P : MvPolynomial (Module.Basis.ofVectorSpaceIndex k B) k :=
    ∑ f ∈ F, MvPolynomial.C (ℓ (bT f)) * ∏ i, MvPolynomial.X (f i)
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero]
    have hw := hℓW (∑ j ∈ J, x j • b j)
    rw [MultilinearMap.map_sum_finset (PiTensorProduct.tprod k) (fun _ j => x j • b j)
      (fun _ : Fin g => J)] at hw
    simp only [MultilinearMap.map_smul_univ, map_sum, map_smul, smul_eq_mul] at hw
    rw [← hw]
    simp only [P, map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [mul_comm]
    simp only [bT, Basis.piTensorProduct_apply]
  have hcoeff : ∀ f0, ∑ f ∈ F.filter (fun f => κ f = κ f0), ℓ (bT f) = 0 := by
    intro f0
    have h0 := congrArg (MvPolynomial.coeff (κ f0)) hP
    rw [MvPolynomial.coeff_zero] at h0
    rw [← h0, Finset.sum_filter]
    simp only [P, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hm : (∏ i, MvPolynomial.X (f i) : MvPolynomial (Module.Basis.ofVectorSpaceIndex k B) k) =
        MvPolynomial.monomial (κ f) 1 := (MvPolynomial.monomial_sum_one _ _).symm
    rw [hm, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial]
  have hinv : ∀ f f0, κ f = κ f0 → c f = c f0 := by
    intro f f0 hff
    obtain ⟨σ, hσ⟩ := exists_perm_of_mset_eq f0 f (mset_eq_of_sum_single_eq f0 f hff.symm)
    rw [hσ]
    show bT.repr t (f0 ∘ σ) = bT.repr t f0
    rw [← repr_permHom, ht]
  apply hℓt
  have ht' : ℓ t = ∑ f ∈ F, c f * ℓ (bT f) := by
    conv_lhs => rw [← bT.linearCombination_repr t]
    rw [Finsupp.linearCombination_apply, map_finsuppSum]
    simp only [map_smul, smul_eq_mul]
    rw [Finsupp.sum]
    exact Finset.sum_subset hsF fun f _ hf => by
      rw [Finsupp.notMem_support_iff.mp hf, zero_mul]
  rw [ht', ← Finset.sum_fiberwise_of_maps_to (g := κ) (t := F.image κ)
    (fun f hf => Finset.mem_image_of_mem κ hf)]
  refine Finset.sum_eq_zero fun e he => ?_
  obtain ⟨f0, -, rfl⟩ := Finset.mem_image.mp he
  rw [Finset.sum_congr rfl fun f hf => by rw [hinv f f0 (Finset.mem_filter.mp hf).2], ← Finset.mul_sum,
    hcoeff f0, mul_zero]

/-- **O1**: over an infinite field, `Sym^g(B)` is the `k`-span of the norms `N(w)`. -/
theorem span_normS [Infinite k] : Submodule.span k (Set.range (normS k (B := B) (g := g))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx := mem_span_tprod_of_fixed (x : XPow k B g) (fun σ => (mem_symRing _).mp x.2 σ)
  have hrange : (Set.range fun w : B => PiTensorProduct.tprod k (fun _ : Fin g => w)) =
      (SymRing k B g).val.toLinearMap '' Set.range (normS k (B := B) (g := g)) := by
    rw [← Set.range_comp]
    ext y
    simp only [Set.mem_range, Function.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.coe_val,
      normS_coe_eq_tprod]
  rw [hrange, Submodule.span_image] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  rwa [← hyx']

end Span

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacSymB_GenPoly =====
section

/-!
# S4-JacSymB, file H2b: the generic polynomial `E(w) = ∏_l (1 - w_l X)` (L12, valuative criterion)

For `w ∈ B`, `E(w) = ∏_l (1 - inc_l(w) X) ∈ X^g(B)[X]` has symmetric coefficients, so it comes from
`genPoly w ∈ Sym^g(B)[X]`. Facts: naturality in `B`; `E(w)(t) = N(1 - t w)`; the Taylor identity
`N(1 - t a) · E(b) = E(a)(X + t)` when `(1 - t a) b = a`; and `reflect g E(w) = ∏_l (X - w_l)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section GenPoly

open Polynomial

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {g : ℕ}

/-- `E(w) = ∏_l (1 - w_l X)` over `X^g(B)`. -/
noncomputable def genE (w : B) : (XPow k B g)[X] := ∏ l, (1 - C (inc l w) * X)

theorem map_permHom_genE (σ : Equiv.Perm (Fin g)) (w : B) :
    (genE (k := k) (g := g) w).map (permHom σ).toRingHom = genE w := by
  have h : ∀ l : Fin g, (permHom σ) (inc (k := k) l w) = inc (σ l) w := fun l => by
    rw [← AlgHom.comp_apply, permHom_comp_inc]
  simp only [genE, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_X,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h]
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

theorem genE_coeff_mem (w : B) (j : ℕ) : (genE (k := k) (g := g) w).coeff j ∈ SymRing k B g := by
  rw [mem_symRing]
  intro σ
  rw [perm_smul_def]
  have := congrArg (fun p => p.coeff j) (map_permHom_genE (k := k) σ w)
  simp only [coeff_map] at this
  exact this

theorem genE_mem_lifts (w : B) : genE (k := k) (g := g) w ∈ lifts (SymRing k B g).val.toRingHom := by
  rw [lifts_iff_coeff_lifts]
  intro j
  exact ⟨⟨_, genE_coeff_mem w j⟩, rfl⟩

/-- `E(w)` with coefficients in `Sym^g(B)`. -/
noncomputable def genPoly (w : B) : (SymRing k B g)[X] :=
  Classical.choose ((mem_lifts _).mp (genE_mem_lifts (k := k) (g := g) w))

theorem map_genPoly (w : B) : (genPoly (k := k) (g := g) w).map (SymRing k B g).val.toRingHom = genE w :=
  Classical.choose_spec ((mem_lifts _).mp (genE_mem_lifts (k := k) (g := g) w))

theorem map_val_injective : Function.Injective (Polynomial.map (SymRing k B g).val.toRingHom) :=
  Polynomial.map_injective _ fun _ _ h => Subtype.ext h

theorem coeff_genPoly (w : B) (j : ℕ) :
    ((genPoly (k := k) (g := g) w).coeff j : XPow k B g) = (genE w).coeff j := by
  rw [← map_genPoly w, coeff_map]
  rfl

theorem symMap_genPoly {B' : Type*} [CommRing B'] [Algebra k B'] (f : B →ₐ[k] B') (w : B) :
    (genPoly (k := k) (g := g) w).map (symMap f).toRingHom = genPoly (f w) := by
  apply map_val_injective
  rw [Polynomial.map_map, map_genPoly]
  have e : (SymRing k B' g).val.toRingHom.comp (symMap (g := g) f).toRingHom =
      (xMap f).toRingHom.comp (SymRing k B g).val.toRingHom := RingHom.ext fun _ => rfl
  rw [e, ← Polynomial.map_map, map_genPoly]
  simp only [genE, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_X]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← AlgHom.comp_apply, xMap_inc, AlgHom.comp_apply]

theorem genPoly_eval (w : B) (t : k) :
    (genPoly (k := k) (g := g) w).eval (algebraMap k _ t) = normS k (1 - algebraMap k B t * w) := by
  apply Subtype.val_injective
  have h1 : ((genPoly (k := k) (g := g) w).eval (algebraMap k (SymRing k B g) t)).1 =
      (genE w).eval (algebraMap k (XPow k B g) t) := by
    rw [← map_genPoly w, eval_map]
    exact (eval₂_hom (SymRing k B g).val.toRingHom (algebraMap k (SymRing k B g) t)).symm
  rw [h1, normS_coe, genE, eval_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, map_sub, map_one, map_mul, AlgHom.commutes]
  ring

/-- The Taylor identity: if `(1 - t a) b = a` then `N(1 - t a) · E(b) = E(a)(X + t)`. -/
theorem genPoly_taylor (a b : B) (t : k) (h : (1 - algebraMap k B t * a) * b = a) :
    C (normS k (g := g) (1 - algebraMap k B t * a)) * genPoly b =
      taylor (algebraMap k (SymRing k B g) t) (genPoly a) := by
  apply map_val_injective
  rw [Polynomial.map_mul, map_C, map_genPoly, map_taylor, map_genPoly]
  change C (∏ l, inc l (1 - algebraMap k B t * a)) * genE b = taylor (algebraMap k (XPow k B g) t) (genE a)
  rw [genE, genE, taylor_apply, prod_comp, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  have hz : (1 - algebraMap k (XPow k B g) t * inc l a) * inc l b = inc l a := by
    have := congrArg (inc (k := k) (g := g) l) h
    simpa only [map_mul, map_sub, map_one, AlgHom.commutes] using this
  have hz' : (1 - C (algebraMap k (XPow k B g) t) * C (inc l a)) * C (inc l b) = C (inc l a) := by
    simpa only [map_mul, map_sub, map_one] using congrArg C hz
  simp only [map_sub, map_one, map_mul, AlgHom.commutes, sub_comp, one_comp, mul_comp, C_comp, X_comp]
  linear_combination (-X) * hz'

theorem reflect_prod_one_sub {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (f : ι → R) :
    reflect s.card (∏ i ∈ s, (1 - C (f i) * X)) = ∏ i ∈ s, (X - C (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reflect_one]
  | insert a s ha ih =>
    have hdeg : (∏ i ∈ s, (1 - C (f i) * X)).natDegree ≤ s.card := by
      refine (natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => (?_ : (1 - C (f i) * X).natDegree ≤ 1)).trans (by simp)
      compute_degree!
    have h1 : reflect 1 (1 - C (f a) * X) = X - C (f a) := by
      rw [reflect_sub, reflect_one, show (C (f a) * X : R[X]) = C (f a) * X ^ 1 by rw [pow_one],
        reflect_C_mul_X_pow, revAt_le (le_refl 1)]
      simp
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      show s.card + 1 = 1 + s.card from add_comm _ _, reflect_mul _ _ (by compute_degree!) hdeg, ih, h1]

theorem reflect_genE (w : B) : reflect g (genE (k := k) (g := g) w) = ∏ l : Fin g, (X - C (inc l w)) := by
  have := reflect_prod_one_sub (Finset.univ : Finset (Fin g)) (fun l => (inc l w : XPow k B g))
  rwa [Finset.card_univ, Fintype.card_fin] at this

end GenPoly

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacLaw_Crit =====
section

/-!
# S4-JacLaw, file O2: the morphism criterion for maps into `Sym^n`

`R` reduced of finite type over an algebraically closed field `k`. A map `μ` from the `k`-points of `R` to the
`k`-points of `Sym^n(B)` comes from a (unique) `k`-algebra map `Sym^n(B) → R` as soon as the pullback of every
norm `N(w)` is a function in `R`. Reason: `R` embeds into functions on its `k`-points (Nullstellensatz), and the
norms span `Sym^n(B)` (file O1). Also: values of `N(w)` and of the generic polynomial `E(w)` at a point `symPt a`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym Polynomial

section Crit

variable {k : Type*} [Field k] {R : Type*} [CommRing R] [Algebra k R]

/-- Evaluation of `R` at its `k`-points. -/
noncomputable def evPts : R →ₐ[k] ((R →ₐ[k] k) → k) := AlgHom.pi (fun x => x)

theorem evPts_apply (r : R) (x : R →ₐ[k] k) : evPts (k := k) r x = x r := rfl

/-- Nullstellensatz for reduced rings: a function vanishing at all `k`-points is zero. -/
theorem evPts_injective [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R] :
    Function.Injective (evPts (k := k) (R := R)) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
  have hj : (⊥ : Ideal R).jacobson = ⊥ := IsJacobsonRing.out' ⊥ Ideal.isRadical_bot
  have hc' : c ∈ (⊥ : Ideal R).jacobson := by
    refine Ideal.mem_sInf.2 ?_
    rintro m ⟨-, hm⟩
    have := hm
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) m
    rw [← hφ, RingHom.mem_ker]
    exact congr_fun hc φ
  rw [hj] at hc'
  exact (Submodule.mem_bot _).1 hc'

variable {S : Type*} [CommRing S] [Algebra k S]

/-- Maps into `R` are determined by their compositions with the `k`-points of `R`. -/
theorem algHom_ext_pts [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R] {φ ψ : S →ₐ[k] R}
    (h : ∀ x : R →ₐ[k] k, x.comp φ = x.comp ψ) : φ = ψ := by
  ext s
  apply evPts_injective (k := k)
  funext x
  exact AlgHom.congr_fun (h x) s

/-- Pullback of functions along a map of `k`-points. -/
noncomputable def pullPts (μ : (R →ₐ[k] k) → (S →ₐ[k] k)) : S →ₐ[k] ((R →ₐ[k] k) → k) := AlgHom.pi μ

theorem pullPts_apply (μ : (R →ₐ[k] k) → (S →ₐ[k] k)) (s : S) (x : R →ₐ[k] k) : pullPts μ s x = μ x s := rfl

variable {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}

theorem range_pullPts_le [IsAlgClosed k] (μ : (R →ₐ[k] k) → (SymRing k B n →ₐ[k] k))
    (hμ : ∀ w : B, ∃ r : R, ∀ x, x r = μ x (normS k w)) (s : SymRing k B n) :
    pullPts μ s ∈ (evPts (k := k) (R := R)).range := by
  let T : Submodule k (SymRing k B n) :=
    (Subalgebra.toSubmodule (evPts (k := k) (R := R)).range).comap (pullPts μ).toLinearMap
  have hT : Submodule.span k (Set.range (normS k (B := B) (g := n))) ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨r, hr⟩ := hμ w
    exact ⟨r, funext hr⟩
  have hs : s ∈ T := hT (by rw [span_normS]; trivial)
  exact hs

/-- **O2, morphism criterion**: the `k`-algebra map `Sym^n(B) → R` inducing `μ` on `k`-points. -/
noncomputable def liftPts [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R]
    (μ : (R →ₐ[k] k) → (SymRing k B n →ₐ[k] k)) (hμ : ∀ w : B, ∃ r : R, ∀ x, x r = μ x (normS k w)) :
    SymRing k B n →ₐ[k] R :=
  (AlgEquiv.ofInjective (evPts (k := k) (R := R)) evPts_injective).symm.toAlgHom.comp
    ((pullPts μ).codRestrict _ (range_pullPts_le μ hμ))

theorem evPts_liftPts [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R]
    (μ : (R →ₐ[k] k) → (SymRing k B n →ₐ[k] k)) (hμ : ∀ w : B, ∃ r : R, ∀ x, x r = μ x (normS k w))
    (s : SymRing k B n) : evPts (k := k) (liftPts μ hμ s) = pullPts μ s := by
  rw [← AlgEquiv.ofInjective_apply (evPts (k := k) (R := R)) evPts_injective]
  simp only [liftPts, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  rfl

theorem comp_liftPts [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R]
    (μ : (R →ₐ[k] k) → (SymRing k B n →ₐ[k] k)) (hμ : ∀ w : B, ∃ r : R, ∀ x, x r = μ x (normS k w))
    (x : R →ₐ[k] k) : x.comp (liftPts μ hμ) = μ x := by
  ext s
  exact congr_fun (evPts_liftPts μ hμ s) x

/-- Uniqueness in the morphism criterion. -/
theorem eq_liftPts [IsAlgClosed k] [IsReduced R] [Algebra.FiniteType k R]
    (μ : (R →ₐ[k] k) → (SymRing k B n →ₐ[k] k)) (hμ : ∀ w : B, ∃ r : R, ∀ x, x r = μ x (normS k w))
    (φ : SymRing k B n →ₐ[k] R) (hφ : ∀ x, x.comp φ = μ x) : φ = liftPts μ hμ :=
  algHom_ext_pts fun x => by rw [hφ, comp_liftPts]

/-- The norm `N(w)` at the point `a_1 + ... + a_n`. -/
theorem symPt_normS (a : Fin n → (B →ₐ[k] k)) (w : B) : symPt a (normS k w) = ∏ l, a l w := by
  rw [symPt_apply, normS_coe, map_prod]
  exact Finset.prod_congr rfl fun l _ => AlgHom.congr_fun (ptOf_inc a l) w

/-- The generic polynomial `E(w)` at the point `a_1 + ... + a_n`. -/
theorem map_symPt_genPoly (a : Fin n → (B →ₐ[k] k)) (w : B) :
    (genPoly (k := k) (g := n) w).map (symPt a).toRingHom = ∏ l, (1 - C (a l w) * X) := by
  have h : (symPt a).toRingHom = (ptOf a).toRingHom.comp (SymRing k B n).val.toRingHom := rfl
  rw [h, ← Polynomial.map_map, map_genPoly, genE, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_X]
  congr 3
  exact AlgHom.congr_fun (ptOf_inc a l) w

end Crit

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_Add =====
section

/-!
# S4-JacLaw, file O7: addition `Sym^d × Sym^e → Sym^(d+e)`

`addMap : Sym^(d+e)(B) →ₐ Sym^d(B) ⊗ Sym^e(B)` is the `k`-algebra map of the morphism `(A, A') ↦ A + A'`,
built by the morphism criterion `liftPts` (the norm `N(w)` pulls back to `N(w) ⊗ N(w)`). The tensor
product is a f.g. domain (`isDomain_tensor`), so `k`-points determine maps into it. Points: for tuples
`a`, `b` lifting the two factors of a point `x`, `x ∘ addMap = symPt (Fin.append a b)` (`comp_addMap_eq`);
`addMap` is symmetric (`comm_addMap`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym

section Ext

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}

/-- `k`-points of `Sym^n` are determined by their values on the norms `N(w)` (`k` infinite). -/
theorem symPt_ext [Infinite k] {φ ψ : SymRing k B n →ₐ[k] k}
    (h : ∀ w : B, φ (normS k w) = ψ (normS k w)) : φ = ψ := by
  have := LinearMap.ext_on_range (span_normS (k := k) (B := B) (g := n))
    (f := φ.toLinearMap) (g := ψ.toLinearMap) h
  exact AlgHom.ext fun s => LinearMap.congr_fun this s

/-- The norm at the point `a + b`. -/
theorem symPt_append {d e : ℕ} (a : Fin d → (B →ₐ[k] k)) (b : Fin e → (B →ₐ[k] k)) (w : B) :
    symPt (Fin.append a b) (normS k w) = symPt a (normS k w) * symPt b (normS k w) := by
  rw [symPt_normS, symPt_normS, symPt_normS, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

end Ext

section Tensor

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B] {d e : ℕ}

instance isDomain_symTensor : IsDomain (SymRing k B d ⊗[k] SymRing k B e) :=
  isDomain_tensor (k := k) (B := SymRing k B d) (A := SymRing k B e)

instance finiteType_symTensor : Algebra.FiniteType k (SymRing k B d ⊗[k] SymRing k B e) :=
  Algebra.FiniteType.trans (S := SymRing k B d) inferInstance inferInstance

/-- The first factor of a `k`-point of `Sym^d ⊗ Sym^e`. -/
noncomputable def ptL (x : SymRing k B d ⊗[k] SymRing k B e →ₐ[k] k) : SymRing k B d →ₐ[k] k :=
  x.comp Algebra.TensorProduct.includeLeft

/-- The second factor of a `k`-point of `Sym^d ⊗ Sym^e`. -/
noncomputable def ptR (x : SymRing k B d ⊗[k] SymRing k B e →ₐ[k] k) : SymRing k B e →ₐ[k] k :=
  x.comp Algebra.TensorProduct.includeRight

theorem apply_tmul (x : SymRing k B d ⊗[k] SymRing k B e →ₐ[k] k) (a : SymRing k B d)
    (b : SymRing k B e) : x (a ⊗ₜ b) = ptL x a * ptR x b := by
  rw [ptL, ptR, AlgHom.comp_apply, AlgHom.comp_apply, ← map_mul, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The point `A + A'` of `Sym^(d+e)` over a point `(A, A')`. -/
noncomputable def addPt (x : SymRing k B d ⊗[k] SymRing k B e →ₐ[k] k) : SymRing k B (d + e) →ₐ[k] k :=
  symPt (Fin.append (liftTuple (ptL x)) (liftTuple (ptR x)))

theorem addPt_normS (x : SymRing k B d ⊗[k] SymRing k B e →ₐ[k] k) (w : B) :
    addPt x (normS k w) = x (normS k w ⊗ₜ normS k w) := by
  rw [addPt, symPt_append, apply_tmul, symPt_liftTuple, symPt_liftTuple]

variable (k B d e) in
/-- **O7.** The addition map `Sym^d × Sym^e → Sym^(d+e)` on coordinate rings. -/
noncomputable def addMap : SymRing k B (d + e) →ₐ[k] SymRing k B d ⊗[k] SymRing k B e :=
  liftPts (k := k) (R := SymRing k B d ⊗[k] SymRing k B e) (B := B) (n := d + e) addPt
    fun w => ⟨normS k w ⊗ₜ normS k w, fun x => (addPt_normS x w).symm⟩

theorem comp_addMap (x : SymRing k B d ⊗[k] SymRing k B e →ₐ[k] k) : x.comp (addMap k B d e) = addPt x :=
  comp_liftPts (k := k) (R := SymRing k B d ⊗[k] SymRing k B e) (B := B) (n := d + e) _ _ x

/-- Points of `addMap` for any lifts `a`, `b` of the two factors. -/
theorem comp_addMap_eq (x : SymRing k B d ⊗[k] SymRing k B e →ₐ[k] k) (a : Fin d → (B →ₐ[k] k))
    (b : Fin e → (B →ₐ[k] k)) (ha : symPt a = ptL x) (hb : symPt b = ptR x) :
    x.comp (addMap k B d e) = symPt (Fin.append a b) := by
  rw [comp_addMap]
  refine symPt_ext fun w => ?_
  rw [addPt, symPt_append, symPt_append, symPt_liftTuple, symPt_liftTuple, ha, hb]

/-- The `k`-point `(y, z)` of `Sym^d ⊗ Sym^e`. -/
noncomputable def pairPt (y : SymRing k B d →ₐ[k] k) (z : SymRing k B e →ₐ[k] k) :
    SymRing k B d ⊗[k] SymRing k B e →ₐ[k] k :=
  Algebra.TensorProduct.lift y z fun _ _ => Commute.all _ _

theorem ptL_pairPt (y : SymRing k B d →ₐ[k] k) (z : SymRing k B e →ₐ[k] k) : ptL (pairPt y z) = y := by
  ext a
  simp [ptL, pairPt]

theorem ptR_pairPt (y : SymRing k B d →ₐ[k] k) (z : SymRing k B e →ₐ[k] k) : ptR (pairPt y z) = z := by
  ext a
  simp [ptR, pairPt]

theorem pairPt_ptL_ptR (x : SymRing k B d ⊗[k] SymRing k B e →ₐ[k] k) : pairPt (ptL x) (ptR x) = x :=
  Algebra.TensorProduct.ext' fun a b => by rw [apply_tmul, apply_tmul, ptL_pairPt, ptR_pairPt]

theorem pairPt_comp_addMap (a : Fin d → (B →ₐ[k] k)) (b : Fin e → (B →ₐ[k] k)) :
    (pairPt (symPt a) (symPt b)).comp (addMap k B d e) = symPt (Fin.append a b) :=
  comp_addMap_eq _ a b (ptL_pairPt _ _).symm (ptR_pairPt _ _).symm

theorem ptL_comm (x : SymRing k B d ⊗[k] SymRing k B d →ₐ[k] k) :
    ptL (x.comp (Algebra.TensorProduct.comm k (SymRing k B d) (SymRing k B d)).toAlgHom) = ptR x := by
  ext a
  simp [ptL, ptR]

theorem ptR_comm (x : SymRing k B d ⊗[k] SymRing k B d →ₐ[k] k) :
    ptR (x.comp (Algebra.TensorProduct.comm k (SymRing k B d) (SymRing k B d)).toAlgHom) = ptL x := by
  ext a
  simp [ptL, ptR]

/-- `A + A' = A' + A`. -/
theorem comm_addMap :
    (Algebra.TensorProduct.comm k (SymRing k B d) (SymRing k B d)).toAlgHom.comp (addMap k B d d) =
      addMap k B d d := by
  refine algHom_ext_pts (k := k) (R := SymRing k B d ⊗[k] SymRing k B d) fun x => ?_
  rw [← AlgHom.comp_assoc, comp_addMap, comp_addMap]
  refine symPt_ext fun w => ?_
  rw [addPt, addPt, symPt_append, symPt_append, symPt_liftTuple, symPt_liftTuple, symPt_liftTuple,
    symPt_liftTuple, ptL_comm, ptR_comm, mul_comm]

end Tensor

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacComplete_PicK =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicK`: divisor classes over an arbitrary constant field

For a function field `F / K(x)` over an arbitrary field `K` (S4-JacRRFam's Fintype-free divisors):
* `PrincK K F`: the principal divisors; `PicK K F = Divisor ⧸ PrincK`; `clsK`; `degPicK`; `Pic0K K F := ker degPicK`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.JacComplete

section PicK

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem divK_one : (PlacesK.div (1 : F) : Places.Divisor K F) = 0 :=
  (PlacesK.div_eq_zero_iff (K := K) (F := F) one_ne_zero).2 (one_mem _)

variable {F} in
theorem divK_inv {f : F} (hf : f ≠ 0) : (PlacesK.div f⁻¹ : Places.Divisor K F) = -PlacesK.div f := by
  rw [← one_div, PlacesK.div_div one_ne_zero hf, divK_one, zero_sub]

/-- The principal divisors of `F / K`. -/
noncomputable def PrincK : AddSubgroup (Places.Divisor K F) where
  carrier := {D | ∃ f : F, f ≠ 0 ∧ (PlacesK.div f : Places.Divisor K F) = D}
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, mul_ne_zero hf hg, PlacesK.div_mul hf hg⟩
  zero_mem' := ⟨1, one_ne_zero, divK_one K F⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨f⁻¹, inv_ne_zero hf, divK_inv K hf⟩

theorem mem_PrincK {D : Places.Divisor K F} :
    D ∈ PrincK K F ↔ ∃ f : F, f ≠ 0 ∧ (PlacesK.div f : Places.Divisor K F) = D := Iff.rfl

theorem div_mem_PrincK {f : F} (hf : f ≠ 0) : (PlacesK.div f : Places.Divisor K F) ∈ PrincK K F :=
  ⟨f, hf, rfl⟩

/-- The divisor class group of `F / K`. -/
noncomputable abbrev PicK : Type _ := Places.Divisor K F ⧸ PrincK K F

/-- The class of a divisor. -/
noncomputable abbrev clsK (D : Places.Divisor K F) : PicK K F := QuotientAddGroup.mk D

theorem clsK_eq_iff {D E : Places.Divisor K F} : clsK K F D = clsK K F E ↔ -D + E ∈ PrincK K F :=
  QuotientAddGroup.eq

/-- The degree as an additive map. -/
noncomputable def degHomK : Places.Divisor K F →+ ℤ where
  toFun := Places.Divisor.deg
  map_zero' := Finsupp.sum_zero_index
  map_add' := PlacesK.Divisor.deg_add

@[simp] theorem degHomK_apply (D : Places.Divisor K F) : degHomK K F D = D.deg := rfl

/-- The degree of a divisor class. -/
noncomputable def degPicK : PicK K F →+ ℤ :=
  QuotientAddGroup.lift (PrincK K F) (degHomK K F) (by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := hx
    simpa using PlacesK.deg_div hf)

theorem degPicK_clsK (D : Places.Divisor K F) : degPicK K F (clsK K F D) = D.deg := rfl

/-- **`Pic⁰(F / K)`**: the divisor classes of degree `0`. -/
noncomputable def Pic0K : AddSubgroup (PicK K F) := (degPicK K F).ker

theorem mem_Pic0K {x : PicK K F} : x ∈ Pic0K K F ↔ degPicK K F x = 0 := AddMonoidHom.mem_ker

theorem clsK_mem_Pic0K {D : Places.Divisor K F} (h : D.deg = 0) : clsK K F D ∈ Pic0K K F :=
  (mem_Pic0K K F).2 h

end PicK

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacSymB_GenInt =====
section

/-!
# S4-JacSymB, file H2d: integrality of `X^g(B)` over the coefficients of `E(w)` (L12, valuative criterion)

If every `b ∈ B` is integral over `k[w]`, then every element of `X^g(B)` is a root of a monic polynomial whose
coefficients are polynomials (over `k`) in the coefficients of `E(w)`: the `w_l` are roots of
`reflect g E(w) = ∏ (X - w_l)`, the `b_l` are integral over `k[w_l]`, and the `b_l` generate `X^g(B)`.
`mem_range_of_monic`: such an element is sent into `O` by any ring map to `Frac O` that sends `k` and the coefficients
into the valuation ring `O`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacSym

section GenInt

open Polynomial

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {g : ℕ}

theorem exists_monic_genE (w : B)
    (hint : ∀ b : B, ∃ p : (Polynomial k)[X], p.Monic ∧ p.eval₂ (Polynomial.aeval w).toRingHom b = 0)
    (t : XPow k B g) :
    ∃ p : (MvPolynomial ℕ k)[X], p.Monic ∧
      p.eval₂ (MvPolynomial.aeval fun j => (genE (k := k) (g := g) w).coeff j).toRingHom t = 0 := by
  classical
  set β : MvPolynomial ℕ k →ₐ[k] XPow k B g := MvPolynomial.aeval fun j => (genE (k := k) (g := g) w).coeff j
    with hβ
  rcases subsingleton_or_nontrivial (XPow k B g) with hT | hT
  · exact ⟨X, monic_X, Subsingleton.elim _ _⟩
  let _ : Algebra (MvPolynomial ℕ k) (XPow k B g) := β.toRingHom.toAlgebra
  set IC := integralClosure (MvPolynomial ℕ k) (XPow k B g) with hIC
  have hA : ∀ l : Fin g, inc l w ∈ IC := by
    intro l
    have hR : (∏ m : Fin g, (X - C (inc (k := k) m w))) ∈ lifts β.toRingHom := by
      rw [lifts_iff_coeff_lifts]
      intro i
      rw [← reflect_genE, coeff_reflect]
      exact ⟨MvPolynomial.X _, MvPolynomial.aeval_X _ _⟩
    obtain ⟨q, hq, -, hqm⟩ :=
      lifts_and_degree_eq_and_monic hR (monic_prod_of_monic _ _ fun m _ => monic_X_sub_C _)
    rw [mem_integralClosure_iff]
    refine ⟨q, hqm, ?_⟩
    change q.eval₂ β.toRingHom (inc l w) = 0
    rw [← eval_map, hq, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  have hk : ∀ c : k, algebraMap k (XPow k B g) c ∈ IC := fun c => by
    have : algebraMap k (XPow k B g) c = algebraMap (MvPolynomial ℕ k) (XPow k B g) (MvPolynomial.C c) :=
      (MvPolynomial.aeval_C _ c).symm
    rw [this]
    exact IC.algebraMap_mem _
  have hB : ∀ (l : Fin g) (b : B), inc l b ∈ IC := by
    intro l b
    obtain ⟨p, hpm, hp⟩ := hint b
    let φ : Polynomial k →+* IC :=
      Polynomial.eval₂RingHom ((algebraMap (MvPolynomial ℕ k) IC).comp MvPolynomial.C) ⟨inc l w, hA l⟩
    have hφ : (algebraMap IC (XPow k B g)).comp φ = (inc l).toRingHom.comp (Polynomial.aeval w).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro c
        rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]
        change β (MvPolynomial.C c) = inc l (Polynomial.aeval w (Polynomial.C c))
        rw [MvPolynomial.aeval_C, Polynomial.aeval_C, AlgHom.commutes]
      · rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, eval₂_X]
        change inc l w = inc l (Polynomial.aeval w Polynomial.X)
        rw [Polynomial.aeval_X]
    have hint' : IsIntegral IC (inc (k := k) (g := g) l b) := by
      refine ⟨p.map φ, hpm.map φ, ?_⟩
      rw [eval₂_map, hφ]
      exact (hom_eval₂ p (Polynomial.aeval (R := k) w).toRingHom (inc (k := k) (g := g) l).toRingHom b).symm.trans (by rw [hp, map_zero])
    have hmem : inc (k := k) (g := g) l b ∈ integralClosure IC (XPow k B g) := hint'
    rw [integralClosure_idem, Algebra.mem_bot] at hmem
    obtain ⟨y, hy⟩ := hmem
    rw [← hy]
    exact y.2
  have hC : ∀ t : XPow k B g, t ∈ IC := by
    intro t
    induction t using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [← prod_inc, Algebra.smul_def]
      exact IC.mul_mem (hk r) (prod_mem fun l _ => hB l (f l))
    | add x y hx hy => exact IC.add_mem hx hy
  obtain ⟨p, hpm, hp⟩ := (mem_integralClosure_iff _ _).mp (hC t)
  exact ⟨p, hpm, hp⟩

/-- The valuation step: an element satisfying a monic equation over `k[e_j]` maps into `O` when `k` and the `e_j` do. -/
theorem mem_range_of_monic {O K S : Type*} [CommRing S] [Algebra k S] [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] (μ : k →+* O) (Φ : S →+* K)
    (hμ : ∀ c, algebraMap O K (μ c) = Φ (algebraMap k S c)) (e : ℕ → S) (o : ℕ → O)
    (ho : ∀ j, algebraMap O K (o j) = Φ (e j)) (s : S)
    (hs : ∃ p : (MvPolynomial ℕ k)[X], p.Monic ∧ p.eval₂ (MvPolynomial.aeval e).toRingHom s = 0) :
    ∃ y : O, algebraMap O K y = Φ s := by
  obtain ⟨p, hpm, hp⟩ := hs
  let ψ : MvPolynomial ℕ k →+* O := MvPolynomial.eval₂Hom μ o
  have hψ : (algebraMap O K).comp ψ = Φ.comp (MvPolynomial.aeval e).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, hμ]
      change Φ (algebraMap k S c) = Φ (MvPolynomial.aeval e (MvPolynomial.C c))
      rw [MvPolynomial.aeval_C]
    · intro j
      rw [RingHom.comp_apply, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, ho]
      change Φ (e j) = Φ (MvPolynomial.aeval e (MvPolynomial.X j))
      rw [MvPolynomial.aeval_X]
  have hint : IsIntegral O (Φ s) := by
    refine ⟨p.map ψ, hpm.map ψ, ?_⟩
    rw [eval₂_map, hψ]
    exact (hom_eval₂ p (MvPolynomial.aeval e).toRingHom Φ s).symm.trans (by rw [hp, map_zero])
  have hv : (ValuationRing.valuation O K).Integers O :=
    { hom_inj := IsFractionRing.injective O K
      map_le_one := fun r => (Valuation.mem_integer_iff _ _).mp ((ValuationRing.mem_integer_iff O K _).mpr ⟨r, rfl⟩)
      exists_of_le_one := fun r hr => (ValuationRing.mem_integer_iff O K r).mp ((Valuation.mem_integer_iff _ _).mpr hr) }
  exact (ValuationRing.mem_integer_iff O K _).mp (hv.mem_of_integral hint)

end GenInt

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_IntersectA_GI =====
section

/-!
# S4-IntersectA, file GI: integral varieties over an algebraically closed field are geometrically integral

`geometricallyIntegral_of_isAlgClosed`: `X` integral and locally of finite type over `Spec k`, `k`
algebraically closed. Over a field `K ⊇ k`, the base change is covered by the opens
`Spec (B ⊗[k] K)` (charts `Spec B` of `X`), domains by `isDomain_tensor`; these opens are irreducible
and pairwise meet (the projection is surjective and `X` is irreducible), so the base change is integral.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace RamanujanPetersson.IntersectA

theorem irreducibleSpace_of_cover {Y : Type*} [TopologicalSpace Y] [Nonempty Y] {ι : Type*}
    (V : ι → Set Y) (hVo : ∀ i, IsOpen (V i)) (hV : ∀ i, IsPreirreducible (V i))
    (hcov : ∀ y, ∃ i, y ∈ V i) (hmeet : ∀ i j, (V i ∩ V j).Nonempty) : IrreducibleSpace Y := by
  refine { isPreirreducible_univ := ?_, toNonempty := ‹_› }
  rintro u v hu hv ⟨x, -, hx⟩ ⟨y, -, hy⟩
  obtain ⟨i, hxi⟩ := hcov x
  obtain ⟨j, hyj⟩ := hcov y
  obtain ⟨z, hzi, hzu, hzj⟩ := hV i u (V j) hu (hVo j) ⟨x, hxi, hx⟩ (hmeet i j)
  obtain ⟨w, -, ⟨hwu, -⟩, hwv⟩ :=
    hV j (u ∩ V i) v (hu.inter (hVo i)) hv ⟨z, hzj, hzu, hzi⟩ ⟨y, hyj, hy⟩
  exact ⟨w, trivial, hwu, hwv⟩

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsIntegral X] [LocallyOfFiniteType f]

include f in
/-- A nonempty affine chart of `X`, base changed to a field `K`, is integral. -/
theorem isIntegral_chart {K : Type u} [Field K] [Algebra k K] {Y : Scheme.{u}} {fst : Y ⟶ X}
    {snd : Y ⟶ Spec (.of K)} (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    {B : CommRingCat.{u}} (v : Spec B ⟶ X) (hv : IsOpenImmersion v) (hB : Nonempty (Spec B)) :
    IsIntegral (pullback fst v) := by
  haveI := hv
  haveI := hB
  haveI : IsIntegral (Spec B) := isIntegral_of_isOpenImmersion v
  haveI : IsDomain B := (affine_isIntegral_iff B).mp inferInstance
  set φ : CommRingCat.of k ⟶ B := Spec.preimage (v ≫ f)
  have hφ : Spec.map φ = v ≫ f := Spec.map_preimage _
  letI : Algebra k B := φ.hom.toAlgebra
  haveI : Algebra.FiniteType k B := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  haveI : IsDomain (B ⊗[k] K) := JacSym.isDomain_tensor
  have hT := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k B K)
  have hP := (IsPullback.of_hasPullback fst v).flip.paste_vert h
  rw [← hφ] at hP
  let e := hP.isoIsPullback _ _ hT
  obtain ⟨t⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of (B ⊗[k] K))))
  haveI : Nonempty (pullback fst v : Scheme.{u}) := ⟨e.inv t⟩
  exact isIntegral_of_isOpenImmersion e.hom

theorem geometricallyIntegral_of_isAlgClosed : GeometricallyIntegral f := by
  rw [geometricallyIntegral_iff, geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  haveI : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  haveI hfst : Surjective fst :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) h.flip inferInstance
  have key : ∀ i, Nonempty (X.affineCover.X i) → IsIntegral (pullback fst (X.affineCover.f i)) :=
    fun i hi => isIntegral_chart f h (X.affineCover.f i) (X.affineCover.map_prop i) hi
  have hc : ∀ x, Nonempty (X.affineCover.X (X.affineCover.idx x)) := fun x =>
    ⟨(X.affineCover.covers x).choose⟩
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  obtain ⟨y0, hy0⟩ := fst.surjective x0
  haveI : Nonempty Y := ⟨y0⟩
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨irreducibleSpace_of_cover
    (fun x => Set.range (pullback.fst fst (X.affineCover.f (X.affineCover.idx x))))
    (fun x => (pullback.fst fst _).isOpenEmbedding.isOpen_range)
    (fun x => ?_) (fun y => ?_) (fun x x' => ?_), ?_⟩
  · haveI := key _ (hc x)
    simpa [Set.image_univ] using ((IrreducibleSpace.isIrreducible_univ _).image _
      (pullback.fst fst (X.affineCover.f (X.affineCover.idx x))).continuous.continuousOn).isPreirreducible
  · obtain ⟨z, hz⟩ := X.affineCover.covers (fst y)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback y z hz.symm
    exact ⟨fst y, w, hw⟩
  · obtain ⟨x1, ⟨z, hz⟩, ⟨z', hz'⟩⟩ := nonempty_preirreducible_inter
      (X.affineCover.f (X.affineCover.idx x)).isOpenEmbedding.isOpen_range
      (X.affineCover.f (X.affineCover.idx x')).isOpenEmbedding.isOpen_range
      ⟨_, (X.affineCover.covers x)⟩ ⟨_, (X.affineCover.covers x')⟩
    obtain ⟨y, rfl⟩ := fst.surjective x1
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback y z hz.symm
    obtain ⟨w', hw', -⟩ := Scheme.Pullback.exists_preimage_pullback y z' hz'.symm
    exact ⟨y, ⟨w, hw⟩, ⟨w', hw'⟩⟩
  · haveI : ∀ i, IsReduced ((X.affineCover.pullback₁ fst).X i) := fun i => by
      change IsReduced (pullback fst (X.affineCover.f i))
      by_cases hi : Nonempty (X.affineCover.X i)
      · haveI := key i hi
        infer_instance
      · haveI : IsEmpty (pullback fst (X.affineCover.f i) : Scheme.{u}) :=
          ⟨fun w => hi ⟨pullback.snd fst (X.affineCover.f i) w⟩⟩
        haveI : ∀ w : (pullback fst (X.affineCover.f i) : Scheme.{u}),
            _root_.IsReduced ((pullback fst (X.affineCover.f i)).presheaf.stalk w) :=
          fun w => isEmptyElim w
        exact isReduced_of_isReduced_stalk _
    exact IsReduced.of_openCover (𝒰 := X.affineCover.pullback₁ fst)

end RamanujanPetersson.IntersectA

end

-- ===== S4.Def_RP_IntersectA_Prod =====
section

/-!
# S4-IntersectA, file Prod: products of integral varieties over an algebraically closed field

Mathlib's `IsIntegral (pullback f g)` instance asks for `UniversallyOpen g`, which this Mathlib cannot
supply. We redo the chart argument of file GI with the field `K` replaced by a `k`-domain `C`
(`isIntegral_of_isPullback_domain`), then cover `S` by affine charts `Spec C`:
`isIntegral_pullback f g` for `X` integral, locally of finite type over `Spec k` and `S` integral.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace RamanujanPetersson.IntersectA

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsIntegral X] [LocallyOfFiniteType f]

include f in
/-- A nonempty affine chart of `X`, base changed to a `k`-domain `C`, is integral. -/
theorem isIntegral_chart_domain {C : Type u} [CommRing C] [IsDomain C] [Algebra k C] {Y : Scheme.{u}}
    {fst : Y ⟶ X} {snd : Y ⟶ Spec (.of C)}
    (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap k C))))
    {B : CommRingCat.{u}} (v : Spec B ⟶ X) (hv : IsOpenImmersion v) (hB : Nonempty (Spec B)) :
    IsIntegral (pullback fst v) := by
  have := hv
  have := hB
  have : IsIntegral (Spec B) := isIntegral_of_isOpenImmersion v
  have : IsDomain B := (affine_isIntegral_iff B).mp inferInstance
  set φ : CommRingCat.of k ⟶ B := Spec.preimage (v ≫ f)
  have hφ : Spec.map φ = v ≫ f := Spec.map_preimage _
  letI : Algebra k B := φ.hom.toAlgebra
  have : Algebra.FiniteType k B := by
    have : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  have : IsDomain (B ⊗[k] C) := JacSym.isDomain_tensor
  have hT := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k B C)
  have hP := (IsPullback.of_hasPullback fst v).flip.paste_vert h
  rw [← hφ] at hP
  let e := hP.isoIsPullback _ _ hT
  obtain ⟨t⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of (B ⊗[k] C))))
  have : Nonempty (pullback fst v : Scheme.{u}) := ⟨e.inv t⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- The base change of `X` to a `k`-domain `C` is integral. -/
theorem isIntegral_of_isPullback_domain {C : Type u} [CommRing C] [IsDomain C] [Algebra k C]
    {Y : Scheme.{u}} {fst : Y ⟶ X} {snd : Y ⟶ Spec (.of C)}
    (h : IsPullback fst snd f (Spec.map (CommRingCat.ofHom (algebraMap k C)))) : IsIntegral Y := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k C))) :=
    ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  have hfst : Surjective fst :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) h.flip inferInstance
  have key : ∀ i, Nonempty (X.affineCover.X i) → IsIntegral (pullback fst (X.affineCover.f i)) :=
    fun i hi => isIntegral_chart_domain f h (X.affineCover.f i) (X.affineCover.map_prop i) hi
  have hc : ∀ x, Nonempty (X.affineCover.X (X.affineCover.idx x)) := fun x =>
    ⟨(X.affineCover.covers x).choose⟩
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  obtain ⟨y0, hy0⟩ := fst.surjective x0
  have : Nonempty Y := ⟨y0⟩
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨irreducibleSpace_of_cover
    (fun x => Set.range (pullback.fst fst (X.affineCover.f (X.affineCover.idx x))))
    (fun x => (pullback.fst fst _).isOpenEmbedding.isOpen_range)
    (fun x => ?_) (fun y => ?_) (fun x x' => ?_), ?_⟩
  · have := key _ (hc x)
    simpa [Set.image_univ] using ((IrreducibleSpace.isIrreducible_univ _).image _
      (pullback.fst fst (X.affineCover.f (X.affineCover.idx x))).continuous.continuousOn).isPreirreducible
  · obtain ⟨z, hz⟩ := X.affineCover.covers (fst y)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback y z hz.symm
    exact ⟨fst y, w, hw⟩
  · obtain ⟨x1, ⟨z, hz⟩, ⟨z', hz'⟩⟩ := nonempty_preirreducible_inter
      (X.affineCover.f (X.affineCover.idx x)).isOpenEmbedding.isOpen_range
      (X.affineCover.f (X.affineCover.idx x')).isOpenEmbedding.isOpen_range
      ⟨_, (X.affineCover.covers x)⟩ ⟨_, (X.affineCover.covers x')⟩
    obtain ⟨y, rfl⟩ := fst.surjective x1
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback y z hz.symm
    obtain ⟨w', hw', -⟩ := Scheme.Pullback.exists_preimage_pullback y z' hz'.symm
    exact ⟨y, ⟨w, hw⟩, ⟨w', hw'⟩⟩
  · have : ∀ i, IsReduced ((X.affineCover.pullback₁ fst).X i) := fun i => by
      change IsReduced (pullback fst (X.affineCover.f i))
      by_cases hi : Nonempty (X.affineCover.X i)
      · have := key i hi
        infer_instance
      · have : IsEmpty (pullback fst (X.affineCover.f i) : Scheme.{u}) :=
          ⟨fun w => hi ⟨pullback.snd fst (X.affineCover.f i) w⟩⟩
        have : ∀ w : (pullback fst (X.affineCover.f i) : Scheme.{u}),
            _root_.IsReduced ((pullback fst (X.affineCover.f i)).presheaf.stalk w) :=
          fun w => isEmptyElim w
        exact isReduced_of_isReduced_stalk _
    exact IsReduced.of_openCover (𝒰 := X.affineCover.pullback₁ fst)

/-- A nonempty affine chart `Spec B` of an integral `S` gives an integral open `X ×ₖ Spec B`. -/
theorem isIntegral_chart_prod {S : Scheme.{u}} (g : S ⟶ Spec (.of k)) [IsIntegral S]
    {B : CommRingCat.{u}} (v : Spec B ⟶ S) (hv : IsOpenImmersion v) (hB : Nonempty (Spec B)) :
    IsIntegral (pullback (pullback.snd f g) v) := by
  have := hv
  have := hB
  have : IsIntegral (Spec B) := isIntegral_of_isOpenImmersion v
  have : IsDomain B := (affine_isIntegral_iff B).mp inferInstance
  set φ : CommRingCat.of k ⟶ B := Spec.preimage (v ≫ g)
  have hφ : Spec.map φ = v ≫ g := Spec.map_preimage _
  letI : Algebra k B := φ.hom.toAlgebra
  have hP := ((IsPullback.of_hasPullback (pullback.snd f g) v).flip.paste_vert
    (IsPullback.of_hasPullback f g).flip).flip
  rw [← hφ] at hP
  exact isIntegral_of_isPullback_domain f (C := B) hP

/-- `X ×ₖ S` is integral for `X` integral and locally of finite type over `k`, and `S` integral. -/
theorem isIntegral_pullback {S : Scheme.{u}} (g : S ⟶ Spec (.of k)) [IsIntegral S] :
    IsIntegral (pullback f g) := by
  have key : ∀ j, Nonempty (S.affineCover.X j) →
      IsIntegral (pullback (pullback.snd f g) (S.affineCover.f j)) :=
    fun j hj => isIntegral_chart_prod f g (S.affineCover.f j) (S.affineCover.map_prop j) hj
  have hc : ∀ y, Nonempty (S.affineCover.X (S.affineCover.idx y)) := fun y =>
    ⟨(S.affineCover.covers y).choose⟩
  obtain ⟨x0⟩ := (inferInstance : Nonempty X)
  obtain ⟨y0⟩ := (inferInstance : Nonempty S)
  obtain ⟨w0, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x0 y0
    (Subsingleton.elim _ _)
  have : Nonempty (pullback f g : Scheme.{u}) := ⟨w0⟩
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨irreducibleSpace_of_cover
    (fun y => Set.range (pullback.fst (pullback.snd f g) (S.affineCover.f (S.affineCover.idx y))))
    (fun y => (pullback.fst (pullback.snd f g) _).isOpenEmbedding.isOpen_range)
    (fun y => ?_) (fun w => ?_) (fun y y' => ?_), ?_⟩
  · have := key _ (hc y)
    simpa [Set.image_univ] using ((IrreducibleSpace.isIrreducible_univ _).image _
      (pullback.fst (pullback.snd f g)
        (S.affineCover.f (S.affineCover.idx y))).continuous.continuousOn).isPreirreducible
  · obtain ⟨z, hz⟩ := S.affineCover.covers (pullback.snd f g w)
    obtain ⟨w', hw', -⟩ := Scheme.Pullback.exists_preimage_pullback w z hz.symm
    exact ⟨pullback.snd f g w, w', hw'⟩
  · obtain ⟨y1, ⟨z, hz⟩, ⟨z', hz'⟩⟩ := nonempty_preirreducible_inter
      (S.affineCover.f (S.affineCover.idx y)).isOpenEmbedding.isOpen_range
      (S.affineCover.f (S.affineCover.idx y')).isOpenEmbedding.isOpen_range
      ⟨_, (S.affineCover.covers y)⟩ ⟨_, (S.affineCover.covers y')⟩
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x0 y1
      (Subsingleton.elim _ _)
    obtain ⟨u1, hu1, -⟩ := Scheme.Pullback.exists_preimage_pullback w z (hw.trans hz.symm)
    obtain ⟨u2, hu2, -⟩ := Scheme.Pullback.exists_preimage_pullback w z' (hw.trans hz'.symm)
    exact ⟨w, ⟨u1, hu1⟩, ⟨u2, hu2⟩⟩
  · have : ∀ j, IsReduced ((S.affineCover.pullback₁ (pullback.snd f g)).X j) := fun j => by
      change IsReduced (pullback (pullback.snd f g) (S.affineCover.f j))
      by_cases hj : Nonempty (S.affineCover.X j)
      · have := key j hj
        infer_instance
      · have : IsEmpty (pullback (pullback.snd f g) (S.affineCover.f j) : Scheme.{u}) :=
          ⟨fun w => hj ⟨pullback.snd (pullback.snd f g) (S.affineCover.f j) w⟩⟩
        have : ∀ w : (pullback (pullback.snd f g) (S.affineCover.f j) : Scheme.{u}),
            _root_.IsReduced ((pullback (pullback.snd f g) (S.affineCover.f j)).presheaf.stalk w) :=
          fun w => isEmptyElim w
        exact isReduced_of_isReduced_stalk _
    exact IsReduced.of_openCover (𝒰 := S.affineCover.pullback₁ (pullback.snd f g))

end RamanujanPetersson.IntersectA

end

-- ===== S4.Def_RP_IsogDegA_AlgMax =====
section

/-!
# S4-IsogDegA, file AlgMax: `k`-points of the fibre = primes over the maximal ideal (G1)

For `k` algebraically closed and `B` integral over `R`, the `k`-points of `Spec B` over
`χ : R →ₐ[k] k` correspond to the primes of `B` over `ker χ` (`ψ ↦ ker ψ`). With the
Nullstellensatz (every maximal ideal of a finite type `k`-algebra is some `ker χ`), the generic
fibre count of Fib4 becomes a count of primes over maximal ideals.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Polynomial

namespace RamanujanPetersson.IsogDegA

section AlgMax

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {R : Type*} (B : Type*) [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]

/-- The primes of `B` lying over the ideal `p` of `R`. -/
abbrev primesOver' (p : Ideal R) : Type _ :=
  {P : Ideal B // P.IsPrime ∧ P.comap (algebraMap R B) = p}

variable {B}

/-- `ψ ↦ ker ψ`. -/
def kerMap (χ : R →ₐ[k] k) (ψ : fiber k B χ) : primesOver' B (RingHom.ker χ) :=
  ⟨RingHom.ker ψ.1, RingHom.ker_isPrime _, by
    ext r
    simp [RingHom.mem_ker, fiber_apply_algebraMap]⟩

omit [IsAlgClosed k] in
theorem kerMap_injective (χ : R →ₐ[k] k) : Function.Injective (kerMap χ (B := B)) := by
  intro ψ₁ ψ₂ h
  have hk : RingHom.ker ψ₁.1 = RingHom.ker ψ₂.1 := congrArg Subtype.val h
  refine Subtype.ext (AlgHom.ext fun b ↦ ?_)
  have hb : b - algebraMap k B (ψ₁.1 b) ∈ RingHom.ker ψ₂.1 := hk ▸ (by simp [RingHom.mem_ker])
  simp only [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] at hb
  exact hb.symm

theorem kerMap_surjective [Algebra.IsIntegral R B] (χ : R →ₐ[k] k) :
    Function.Surjective (kerMap χ (B := B)) := by
  rintro ⟨P, hP, hPc⟩
  have hmax : (RingHom.ker χ).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective χ fun c ↦ ⟨algebraMap k R c, by simp⟩
  haveI hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P (hPc ▸ hmax)
  have hR : ∀ r : R, Ideal.Quotient.mk P (algebraMap R B r) = algebraMap k (B ⧸ P) (χ r) := by
    intro r
    have hmem : r - algebraMap k R (χ r) ∈ P.comap (algebraMap R B) := by
      rw [hPc, RingHom.mem_ker, map_sub, AlgHom.commutes]; simp
    rw [Ideal.mem_comap, map_sub, ← IsScalarTower.algebraMap_apply] at hmem
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
    exact hmem
  have hintk : Algebra.IsIntegral k (B ⧸ P) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) b
    refine ⟨p.map (χ : R →+* k), hpm.map _, ?_⟩
    rw [eval₂_map]
    have hc : (algebraMap k (B ⧸ P)).comp (χ : R →+* k) =
        (Ideal.Quotient.mk P).comp (algebraMap R B) := by
      ext r; exact (hR r).symm
    rw [hc, ← hom_eval₂, hp, map_zero]
  have hbij : Function.Bijective (algebraMap k (B ⧸ P)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] B ⧸ P := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ P)) hbij
  let ψ : B →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k P)
  have hψ : ∀ b : B, e (ψ b) = Ideal.Quotient.mk P b := fun b ↦ by simp [ψ]
  refine ⟨⟨ψ, AlgHom.ext fun r ↦ e.injective ?_⟩, Subtype.ext (Ideal.ext fun b ↦ ?_)⟩
  · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    rw [hψ, hR]
    rfl
  · change b ∈ RingHom.ker ψ ↔ b ∈ P
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← hψ, map_eq_zero_iff e e.injective]

/-- **G1.** `k`-points of the fibre over `χ` = primes over `ker χ`. -/
noncomputable def fiberEquiv [Algebra.IsIntegral R B] (χ : R →ₐ[k] k) :
    fiber k B χ ≃ primesOver' B (RingHom.ker χ) :=
  Equiv.ofBijective (kerMap χ) ⟨kerMap_injective χ, kerMap_surjective χ⟩

/-- Nullstellensatz: every maximal ideal of a finite type `k`-algebra is a kernel `ker χ`. -/
theorem exists_algHom_ker_eq [Algebra.FiniteType k R] (m : Ideal R) (hm : m.IsMaximal) :
    ∃ χ : R →ₐ[k] k, RingHom.ker χ = m := by
  letI := Ideal.Quotient.field m
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  have hbij : Function.Bijective (algebraMap k (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] R ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), Ideal.ext fun r ↦ ?_⟩
  change e.symm (Ideal.Quotient.mk m r) = 0 ↔ r ∈ m
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

end AlgMax

section Headline

variable {R B K L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Module.Finite R B]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]
  (k : Type*) [Field k] [IsAlgClosed k] [Algebra k R] [Algebra k B] [IsScalarTower k R B]

variable (K L) in
/-- **O1 in prime form.** For `a ≠ 0` suitable, over every maximal ideal `m ∌ a` of `R` there
are exactly `Field.finSepDegree K L` primes of `B`. -/
theorem exists_card_primesOver_eq_finSepDegree [Algebra.FiniteType k R] :
    ∃ a : R, a ≠ 0 ∧ ∀ m : Ideal R, m.IsMaximal → a ∉ m →
      Finite (primesOver' B m) ∧ Nat.card (primesOver' B m) = Field.finSepDegree K L := by
  obtain ⟨a, ha, h⟩ := exists_card_fiber_eq_finSepDegree (R := R) (B := B) (K := K) (L := L) (k := k)
  refine ⟨a, ha, fun m hm ham ↦ ?_⟩
  obtain ⟨χ, rfl⟩ := exists_algHom_ker_eq (k := k) m hm
  obtain ⟨hfin, hcard⟩ := h χ fun h0 ↦ ham (RingHom.mem_ker.2 h0)
  exact ⟨Finite.of_equiv _ (fiberEquiv χ), (Nat.card_congr (fiberEquiv χ)).symm.trans hcard⟩

end Headline

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_IsogDegA_SpecFib =====
section

/-!
# S4-IsogDegA, file SpecFib: scheme fibres as primes over a prime (G2, part 1)

For `f : X ⟶ Y`, an affine open `V ⊆ Y` with `f ⁻¹ᵁ V` affine and `y ∈ V`, the scheme fibre
`f ⁻¹' {y}` is in bijection with the primes of `Γ(X, f ⁻¹ᵁ V)` lying over the prime of `y`.
Also the O1 count restated for `K = L` (an endomorphism's function field), where the two algebra
structures `R → K` must be passed by hand.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace RamanujanPetersson.IsogDegA

section SpecFib

variable {X Y : Scheme.{u}}

theorem primeIdealOf_injective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective hU.primeIdealOf := fun x y h ↦ by
  have := congrArg hU.fromSpec h
  rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
  exact Subtype.ext this

theorem primeIdealOf_surjective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective hU.primeIdealOf := fun p ↦ by
  let q : Spec Γ(X, U) := p
  refine ⟨hU.isoSpec.inv q, ?_⟩
  change hU.isoSpec.hom (hU.isoSpec.inv q) = q
  rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
  rfl

variable (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
  [Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V)] (halg : algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = (f.app V).hom)
  (y : Y) (hy : y ∈ V)

include halg in
theorem comap_primeIdealOf_eq (x : X) (hx : f x = y) (hxV : x ∈ f ⁻¹ᵁ V) :
    ((hU.primeIdealOf ⟨x, hxV⟩).asIdeal).comap (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) =
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
  subst hx
  rw [halg, ← Scheme.Hom.appLE_eq_app]
  exact congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE V hV (f ⁻¹ᵁ V) hU le_rfl hxV)

omit [Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V)] in
include hy in
theorem mem_preimage_of_eq (x : X) (hx : f x = y) : x ∈ f ⁻¹ᵁ V :=
  show f x ∈ V from hx ▸ hy

/-- Points of the fibre ↦ primes over the prime of `y`. -/
noncomputable def fiberPrimes (x : f ⁻¹' {y}) :
    primesOver' Γ(X, f ⁻¹ᵁ V) (hV.primeIdealOf ⟨y, hy⟩).asIdeal :=
  ⟨(hU.primeIdealOf ⟨x.1, mem_preimage_of_eq f y hy x.1 x.2⟩).asIdeal,
    (hU.primeIdealOf _).isPrime,
    comap_primeIdealOf_eq f hV hU halg y hy x.1 x.2 _⟩

include halg in
theorem fiberPrimes_bijective : Function.Bijective (fiberPrimes f hV hU halg y hy) := by
  constructor
  · intro x₁ x₂ h
    have h' := primeIdealOf_injective hU (PrimeSpectrum.ext (congrArg Subtype.val h))
    exact Subtype.ext (by simpa using h')
  · rintro ⟨P, hP, hc⟩
    obtain ⟨⟨x, hxV⟩, hx⟩ := primeIdealOf_surjective hU ⟨P, hP⟩
    have h1 := IsAffineOpen.comap_primeIdealOf_appLE V hV (f ⁻¹ᵁ V) hU le_rfl hxV
    rw [Scheme.Hom.appLE_eq_app, ← halg, hx] at h1
    have h2 : hV.primeIdealOf ⟨f x, hxV⟩ = hV.primeIdealOf ⟨y, hy⟩ :=
      PrimeSpectrum.ext ((congrArg PrimeSpectrum.asIdeal h1).symm.trans hc)
    have hfx : f x = y := congrArg Subtype.val (primeIdealOf_injective hV h2)
    refine ⟨⟨x, hfx⟩, Subtype.ext ?_⟩
    change (hU.primeIdealOf ⟨x, _⟩).asIdeal = P
    rw [hx]

/-- **Fibre = primes over.** -/
noncomputable def fiberPrimesEquiv :
    (f ⁻¹' {y}) ≃ primesOver' Γ(X, f ⁻¹ᵁ V) (hV.primeIdealOf ⟨y, hy⟩).asIdeal :=
  Equiv.ofBijective _ (fiberPrimes_bijective f hV hU halg y hy)

end SpecFib

section SelfField

variable {R B K : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B] [Algebra R B]
  [Module.Finite R B] [Field K] [iRK : Algebra R K] [IsFractionRing R K] [iBK : Algebra B K]
  [IsFractionRing B K]

/-- O1 (prime form) when both fraction fields are the same field `K`, with `K → K` given by
`hKK` (e.g. `φ^*` on `K(A)`); the compatibility is `hKK ∘ (R → K) = (B → K) ∘ (R → B)`. -/
theorem card_primesOver_self (hKK : Algebra K K)
    (h : ∀ r : R, @algebraMap K K _ _ hKK (algebraMap R K r) = algebraMap B K (algebraMap R B r))
    (k : Type*) [Field k] [IsAlgClosed k] [Algebra k R] [Algebra.FiniteType k R] :
    ∃ a : R, a ≠ 0 ∧ ∀ m : Ideal R, m.IsMaximal → a ∉ m →
      Finite (primesOver' B m) ∧ Nat.card (primesOver' B m) = @Field.finSepDegree K K _ _ hKK := by
  let kB : Algebra k B := ((algebraMap R B).comp (algebraMap k R)).toAlgebra
  have tk : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' rfl
  let iRL : Algebra R K := ((algebraMap B K).comp (algebraMap R B)).toAlgebra
  have t1 : @IsScalarTower R K K iRK.toSMul hKK.toSMul iRL.toSMul :=
    @IsScalarTower.of_algebraMap_eq R K K _ _ _ iRK hKK iRL fun r ↦ (h r).symm
  have t2 : @IsScalarTower R B K _ iBK.toSMul iRL.toSMul :=
    @IsScalarTower.of_algebraMap_eq R B K _ _ _ _ iBK iRL fun _ ↦ rfl
  exact @exists_card_primesOver_eq_finSepDegree R B K K _ _ _ _ _ _ _ _ iRK _ iBK _ hKK iRL t1 t2
    k _ _ _ _ tk _

end SelfField

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_JacFrob_TanP =====
section

/-!
# S4-JacFrob, part TanP: `q`-th roots in `Sym^g` (generic)

`k` algebraically closed of characteristic `p`, `q = p^n`.
* `xMap_pow_root`: if every `f b` is a `q`-th power, so is every `xMap f x` (`k` perfect, Frobenius additive);
* `symMap_pow_root`: if moreover `X'^g` is a domain, every `symMap f x` is the `q`-th power of an invariant
  (`(σ • u)^q = u^q` forces `σ • u = u`);
* `snd_pow_char`: in `K[ε]`, `(x^q).snd = 0`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacFrob

open RamanujanPetersson.JacSym

section PowRoot

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [Algebra k B]
  {B' : Type*} [CommRing B'] [Algebra k B'] {g : ℕ}
variable (p n : ℕ) [Fact p.Prime] [CharP k p]

theorem xMap_pow_root [IsDomain (XPow k B' g)] (f : B →ₐ[k] B') (hf : ∀ b, ∃ c, f b = c ^ p ^ n)
    (x : XPow k B g) : ∃ u, xMap f x = u ^ p ^ n := by
  have : CharP (XPow k B' g) p := charP_of_injective_algebraMap (algebraMap k (XPow k B' g)).injective p
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r b =>
    choose c hc using fun i => hf (b i)
    obtain ⟨r', hr'⟩ := IsAlgClosed.exists_pow_nat_eq r (pow_pos (Fact.out : p.Prime).pos n)
    refine ⟨r' • ∏ i, inc i (c i), ?_⟩
    rw [smul_pow, hr', ← Finset.prod_pow, map_smul, xMap_tprod, ← prod_inc]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hc i, map_pow]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, hu, hv, add_pow_char_pow]⟩

theorem symMap_pow_root [IsDomain (XPow k B' g)] (f : B →ₐ[k] B') (hf : ∀ b, ∃ c, f b = c ^ p ^ n)
    (x : SymRing k B g) : ∃ y : SymRing k B' g, symMap f x = y ^ p ^ n := by
  have : CharP (XPow k B' g) p := charP_of_injective_algebraMap (algebraMap k (XPow k B' g)).injective p
  obtain ⟨u, hu⟩ := xMap_pow_root p n f hf (x : XPow k B g)
  have hinj : ∀ v w : XPow k B' g, v ^ p ^ n = w ^ p ^ n → v = w := fun v w h => by
    have h0 : (v - w) ^ p ^ n = 0 := by rw [sub_pow_char_pow, h, sub_self]
    exact sub_eq_zero.1 (IsNilpotent.eq_zero ⟨_, h0⟩)
  refine ⟨⟨u, (mem_symRing u).2 fun σ => hinj _ _ ?_⟩, Subtype.ext ?_⟩
  · rw [perm_smul_def, ← map_pow, ← hu, ← perm_smul_def, ← xMap_smul, smul_symRing]
  · rw [symMap_coe, SubmonoidClass.coe_pow]
    exact hu

end PowRoot

theorem snd_pow_char {K : Type*} [Field K] (p : ℕ) [CharP K p] (n : ℕ) (hn : n ≠ 0) (x : DualNumber K) :
    (x ^ p ^ n).snd = 0 := by
  rw [TrivSqZeroExt.snd_pow, nsmul_eq_mul, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn, zero_mul]

end RamanujanPetersson.JacFrob

end


