-- Prove2me | Definitions.Def_RPLib_F2_018
-- name    : RPLib_F2_018
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-19T10:01:59.198752+00:00
-- url     : https://prove2.me/theorems/bad51aa9-6285-48f8-a4ac-1be90bf44e2a
-- title:
--   Ramanujan-Petersson curve library, flat edition, file 018 of 70
-- statement:
--   File 018 of 70 of the flat curve library: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_JacDivisors_C`: S4-JacDivisors C (O2 and helpers for Serre's hard direction)
--   * `S4.Def_RP_JacDivisors_D`: S4-JacDivisors D (O3a and O4: Serre's hard direction)
--   * `S4.Def_RP_JacDivisors_E`: S4-JacDivisors E (O6: localizations of regular local rings)
--   * `S4.Def_RP_JacDivisors_F`: S4-JacDivisors F (O8: finite free resolutions)
--   * `S4.Def_RP_JacDivisors_G`: S4-JacDivisors G (O9: Auslander-Buchsbaum, regular local rings are UFDs)
--   * `S4.Def_RP_JacDivisors_S`: S4-JacDivisors S (O10, scheme part, and the smooth form of Weil's extension theorem)
--   * `S4.Def_RP_IntersectB_Prime`: S4-IntersectB, file Prime: prime divisors as locally principal ideal sheaves (O6)
--   * `S4.Def_RP_IntersectB_Form`: S4-IntersectB, file Form: intersection numbers of prime-divisor products (O7, part 1)
--   * `S4.Def_RP_IntersectB_Form2`: S4-IntersectB, file Form2: the intersection form on all divisors (O7, part 2; L33)
--   * `S4.Def_RP_IntersectB_Pen3`: S4-IntersectB, O9 part 3: the Weil bridge for the pencil of a rational function
--   * `S4.Def_RP_IntersectB_Pen1`: S4-IntersectB, O9 part 1: fibres of the pencil family over the affine line
--   * `S4.Def_RP_ThetaCube_Pull`: S4-ThetaCube, T7a: the ideal sheaf of a pulled-back effective divisor
--   * `S4.Def_RP_IntersectB_Pen2`: S4-IntersectB, O9 part 2: flatness of the pencil family at fibre points
--   * `S4.Def_RP_IntersectB_Pen4`: S4-IntersectB, O9 part 4: the pencil function `f / (f - 1)` and its fibres over `0` and `1`
--   * `S4.Def_RP_IntersectB_Fam1`: S4-IntersectB, file Fam1: flat neighbourhoods of finite fibres (O8, part 1)
--   * `S4.Def_RP_IntersectB_Pen5`: S4-IntersectB, file Pen5: the two fibres of the pencil have the same length (L34, B4)
--   * `S4.Def_RP_IntersectB_Pen6`: S4-IntersectB, file Pen6: transport along isomorphisms (L34, B4)
--   * `S4.Def_RP_IntersectB_Pen7`: S4-IntersectB, file Pen7: generic translates of a small configuration do not meet (L34, B4)
--   * `S4.Def_RP_IntersectB_Pen8`: S4-IntersectB, file Pen8: the pencil for generic translates (L34, B4)
--   * `S4.Def_RP_IntersectB_Pen9`: S4-IntersectB, file Pen9: the intersection form respects linear equivalence (L34, B4)
--   * `S4.Def_RP_IntersectC_Rank`: S4-IntersectC, file Rank: ranks multiply in a finite flat tower over a field (L35 core)
--   * `S4.Def_RP_IntersectC_Len`: S4-IntersectC, file Len: length under a finite flat endomorphism (L35, O2)
--   * `S4.Def_RP_IsogDegA_QF`: S4-IsogDegA, file QF: a dominant endomorphism of a proper group variety is finite (O3)
--   * `S4.Def_RP_IsogDegA_Trdeg`: S4-IsogDegA, file Trdeg: `K(A)` is finite over `φ^* K(A)` (O3 without the hypothesis)
--   * `S4.Def_RP_IsogDegA_Mult`: S4-IsogDegA, file Mult: the degree is multiplicative (O4)
--   * `S4.Def_RP_IsogDegA_AlgMax`: S4-IsogDegA, file AlgMax: `k`-points of the fibre = primes over the maximal ideal (G1)
--   * `S4.Def_RP_IsogDegA_SpecFib`: S4-IsogDegA, file SpecFib: scheme fibres as primes over a prime (G2, part 1)
--   * `S4.Def_RP_IsogDegA_Count`: S4-IsogDegA, file Count: a closed fibre of the right size (G2, part 2)
--   * `S4.Def_RP_IsogDegA`: S4-IsogDegA: isogeny degree of an abelian variety (lemmas L24-L26 of S4_COREB_ROUTE.md §3)
--   * `S4.Def_RP_IntersectC_Flat`: S4-IntersectC, file Flat: dominant endomorphisms are flat (L35, O3)
--   * `S4.Def_RP_IntersectC_Deg`: S4-IntersectC, file Deg: the rank of a dominant endomorphism is its degree (L35, O4)
--   * `S4.Def_RP_IntersectC_Proj`: S4-IntersectC, file Proj: pulling divisors back along a dominant endomorphism (L35, O5)
--   * `S4.Def_RP_IsogDegB_Unram`: S4-IsogDegB, algebra part (lemma L27 of S4_COREB_ROUTE.md §3)
--   * `S4.Def_RP_IsogDegB_Der`: S4-IsogDegB, tangent vectors from the cotangent space (lemma L27 of S4_COREB_ROUTE.md §3)
--   * `S4.Def_RP_IsogDegB_TanA`: S4-IsogDegB, the tangent space at the identity (lemma L27 of S4_COREB_ROUTE.md §3)
--   * `S4.Def_RP_IsogDegB_TanB`: S4-IsogDegB, differentials on stalks and tangent vectors from stalk maps (L27 of S4_COREB_ROUTE.md §3)
--   * `S4.Def_RP_IsogDegB_TanC`: S4-IsogDegB, the group law on tangent vectors is addition (L27 of S4_COREB_ROUTE.md §3)
--   * `S4.Def_RP_IsogDegB_DerT`: S4-IsogDegB, tangent vectors over a `k`-tower (L27 of S4_COREB_ROUTE.md §3)
--   * `S4.Def_RP_IsogDegB_Sep`: S4-IsogDegB, file Sep: an injective differential makes `φ` unramified at the identity
--   * `S4.Def_RP_IsogDegB_SepFF`: S4-IsogDegB, file SepFF: an injective differential makes the isogeny separable (Sep-4b)
--   * `S4.Def_RP_IsogDegB_DomA`: S4-IsogDegB, file DomA: locally quasi-finite endomorphisms are dominant (O4, part 1)
--   * `S4.Def_RP_IsogDegB_DomB`: S4-IsogDegB, file DomB: finite kernel ⇔ dominant ⇔ deg ≠ 0 (O4, part 2)
--   * `S4.Def_RP_IntersectC_NonDom`: S4-IntersectC, file NonDom: the projection formula (L35, O6)
--   * `S4.Def_RP_JacComplete_Ext`: The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)
--   * `S4.Def_RP_ThetaSquare_Def`: Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)
--   * `S4.Def_RP_ThetaSquare_Ne`: Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`
--   * `S4.Def_RP_ThetaSquare_Stab`: Unit S4-ThetaSquare, file Stab: the stabiliser of `W_{g-1}` is trivial (divisor form, Riemann-Roch only)
--   * `S4.Def_RP_IntersectC_Pit`: S4-IntersectC, file Pit: Krull's height theorem on a scheme (L36, O8)
--   * `S4.Def_RP_IntersectC_Pit2`: S4-IntersectC, file Pit2: Krull at translated intersections; many `k`-points (L36, O8)
--   * `S4.Def_RP_IntersectC_Pos`: S4-IntersectC, file Pos: positivity of the self-intersection (L36, O9)
--
--   **Formalization note.** One file of the flat edition of a library formalizing Poincaré duality for constant coefficients on an affine curve over a finite field and the Lefschetz trace formula for its Frobenius. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later files and solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves) and Chapter VI, §13 (the Lefschetz trace formula); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité » and « Rapport sur la formule des traces »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_F2_017

/-!
# Ramanujan-Petersson curve library (flat edition), file 018 of 70

Declarations of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field and of the Lefschetz trace formula for its Frobenius, re-hosted declaration by declaration from
the library modules below. Each module contributes the declarations assigned to this file, copied verbatim with
the module's own `namespace` / `open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_JacDivisors_C`: S4-JacDivisors C (O2 and helpers for Serre's hard direction)
* `S4.Def_RP_JacDivisors_D`: S4-JacDivisors D (O3a and O4: Serre's hard direction)
* `S4.Def_RP_JacDivisors_E`: S4-JacDivisors E (O6: localizations of regular local rings)
* `S4.Def_RP_JacDivisors_F`: S4-JacDivisors F (O8: finite free resolutions)
* `S4.Def_RP_JacDivisors_G`: S4-JacDivisors G (O9: Auslander-Buchsbaum, regular local rings are UFDs)
* `S4.Def_RP_JacDivisors_S`: S4-JacDivisors S (O10, scheme part, and the smooth form of Weil's extension theorem)
* `S4.Def_RP_IntersectB_Prime`: S4-IntersectB, file Prime: prime divisors as locally principal ideal sheaves (O6)
* `S4.Def_RP_IntersectB_Form`: S4-IntersectB, file Form: intersection numbers of prime-divisor products (O7, part 1)
* `S4.Def_RP_IntersectB_Form2`: S4-IntersectB, file Form2: the intersection form on all divisors (O7, part 2; L33)
* `S4.Def_RP_IntersectB_Pen3`: S4-IntersectB, O9 part 3: the Weil bridge for the pencil of a rational function
* `S4.Def_RP_IntersectB_Pen1`: S4-IntersectB, O9 part 1: fibres of the pencil family over the affine line
* `S4.Def_RP_ThetaCube_Pull`: S4-ThetaCube, T7a: the ideal sheaf of a pulled-back effective divisor
* `S4.Def_RP_IntersectB_Pen2`: S4-IntersectB, O9 part 2: flatness of the pencil family at fibre points
* `S4.Def_RP_IntersectB_Pen4`: S4-IntersectB, O9 part 4: the pencil function `f / (f - 1)` and its fibres over `0` and `1`
* `S4.Def_RP_IntersectB_Fam1`: S4-IntersectB, file Fam1: flat neighbourhoods of finite fibres (O8, part 1)
* `S4.Def_RP_IntersectB_Pen5`: S4-IntersectB, file Pen5: the two fibres of the pencil have the same length (L34, B4)
* `S4.Def_RP_IntersectB_Pen6`: S4-IntersectB, file Pen6: transport along isomorphisms (L34, B4)
* `S4.Def_RP_IntersectB_Pen7`: S4-IntersectB, file Pen7: generic translates of a small configuration do not meet (L34, B4)
* `S4.Def_RP_IntersectB_Pen8`: S4-IntersectB, file Pen8: the pencil for generic translates (L34, B4)
* `S4.Def_RP_IntersectB_Pen9`: S4-IntersectB, file Pen9: the intersection form respects linear equivalence (L34, B4)
* `S4.Def_RP_IntersectC_Rank`: S4-IntersectC, file Rank: ranks multiply in a finite flat tower over a field (L35 core)
* `S4.Def_RP_IntersectC_Len`: S4-IntersectC, file Len: length under a finite flat endomorphism (L35, O2)
* `S4.Def_RP_IsogDegA_QF`: S4-IsogDegA, file QF: a dominant endomorphism of a proper group variety is finite (O3)
* `S4.Def_RP_IsogDegA_Trdeg`: S4-IsogDegA, file Trdeg: `K(A)` is finite over `φ^* K(A)` (O3 without the hypothesis)
* `S4.Def_RP_IsogDegA_Mult`: S4-IsogDegA, file Mult: the degree is multiplicative (O4)
* `S4.Def_RP_IsogDegA_AlgMax`: S4-IsogDegA, file AlgMax: `k`-points of the fibre = primes over the maximal ideal (G1)
* `S4.Def_RP_IsogDegA_SpecFib`: S4-IsogDegA, file SpecFib: scheme fibres as primes over a prime (G2, part 1)
* `S4.Def_RP_IsogDegA_Count`: S4-IsogDegA, file Count: a closed fibre of the right size (G2, part 2)
* `S4.Def_RP_IsogDegA`: S4-IsogDegA: isogeny degree of an abelian variety (lemmas L24-L26 of S4_COREB_ROUTE.md §3)
* `S4.Def_RP_IntersectC_Flat`: S4-IntersectC, file Flat: dominant endomorphisms are flat (L35, O3)
* `S4.Def_RP_IntersectC_Deg`: S4-IntersectC, file Deg: the rank of a dominant endomorphism is its degree (L35, O4)
* `S4.Def_RP_IntersectC_Proj`: S4-IntersectC, file Proj: pulling divisors back along a dominant endomorphism (L35, O5)
* `S4.Def_RP_IsogDegB_Unram`: S4-IsogDegB, algebra part (lemma L27 of S4_COREB_ROUTE.md §3)
* `S4.Def_RP_IsogDegB_Der`: S4-IsogDegB, tangent vectors from the cotangent space (lemma L27 of S4_COREB_ROUTE.md §3)
* `S4.Def_RP_IsogDegB_TanA`: S4-IsogDegB, the tangent space at the identity (lemma L27 of S4_COREB_ROUTE.md §3)
* `S4.Def_RP_IsogDegB_TanB`: S4-IsogDegB, differentials on stalks and tangent vectors from stalk maps (L27 of S4_COREB_ROUTE.md §3)
* `S4.Def_RP_IsogDegB_TanC`: S4-IsogDegB, the group law on tangent vectors is addition (L27 of S4_COREB_ROUTE.md §3)
* `S4.Def_RP_IsogDegB_DerT`: S4-IsogDegB, tangent vectors over a `k`-tower (L27 of S4_COREB_ROUTE.md §3)
* `S4.Def_RP_IsogDegB_Sep`: S4-IsogDegB, file Sep: an injective differential makes `φ` unramified at the identity
* `S4.Def_RP_IsogDegB_SepFF`: S4-IsogDegB, file SepFF: an injective differential makes the isogeny separable (Sep-4b)
* `S4.Def_RP_IsogDegB_DomA`: S4-IsogDegB, file DomA: locally quasi-finite endomorphisms are dominant (O4, part 1)
* `S4.Def_RP_IsogDegB_DomB`: S4-IsogDegB, file DomB: finite kernel ⇔ dominant ⇔ deg ≠ 0 (O4, part 2)
* `S4.Def_RP_IntersectC_NonDom`: S4-IntersectC, file NonDom: the projection formula (L35, O6)
* `S4.Def_RP_JacComplete_Ext`: The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)
* `S4.Def_RP_ThetaSquare_Def`: Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)
* `S4.Def_RP_ThetaSquare_Ne`: Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`
* `S4.Def_RP_ThetaSquare_Stab`: Unit S4-ThetaSquare, file Stab: the stabiliser of `W_{g-1}` is trivial (divisor form, Riemann-Roch only)
* `S4.Def_RP_IntersectC_Pit`: S4-IntersectC, file Pit: Krull's height theorem on a scheme (L36, O8)
* `S4.Def_RP_IntersectC_Pit2`: S4-IntersectC, file Pit2: Krull at translated intersections; many `k`-points (L36, O8)
* `S4.Def_RP_IntersectC_Pos`: S4-IntersectC, file Pos: positivity of the self-intersection (L36, O9)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacDivisors_C =====
section

/-!
# S4-JacDivisors C (O2 and helpers for Serre's hard direction)
* `coeff_mem_maximalIdeal_of_minimal`: relations among a minimal generating set have all
  coefficients in `m`.
* `free_of_depth_zero` (O2): if `s ≠ 0` kills `m`, every finite module of finite projective dimension
  is free; `maximalIdeal_eq_bot_of_depth_zero`: then `pd k < ∞` forces `m = 0`.
* `exists_nonZeroDivisor_not_mem_sq`: prime avoidance over the associated primes and `m²`.
* `spanFinrank_maximalIdeal_le_quotient_add_one`: lifting generators from `R ⧸ (x)`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal

universe u

variable {R : Type u} [CommRing R]

/-- O2: over a local ring of depth zero, finite modules of finite projective dimension are free. -/
theorem free_of_depth_zero [IsLocalRing R] [IsNoetherianRing R] {s : R} (hs : s ≠ 0)
    (hsm : ∀ y ∈ maximalIdeal R, s * y = 0) : ∀ (n : ℕ) (M : ModuleCat.{u} R), Module.Finite R M →
      HasProjectiveDimensionLT M (n + 1) → Module.Free R M := by
  intro n
  induction n with
  | zero =>
    intro M _ hM
    have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
    have : Module.Projective R M := (IsProjective.iff_projective (R := R) M).mpr this
    exact Module.free_of_flat_of_isLocalRing
  | succ n ih =>
    intro M _ hM
    classical
    obtain ⟨t, hcard, ht⟩ :=
      (Module.Finite.fg_top (R := R) (M := M)).exists_span_finset_card_eq_spanFinrank
    let f : (t →₀ R) →ₗ[R] M := Finsupp.linearCombination R (Subtype.val : t → M)
    have surj : Function.Surjective f := by
      rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
      simpa using ht
    have hmin : ∀ t' : Finset M, Submodule.span R (t' : Set M) = ⊤ → t.card ≤ t'.card := by
      intro t' ht'
      rw [hcard, ← ht']
      simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := R) t'.finite_toSet
    have hS := LinearMap.shortExact_shortComplexKer surj
    have : Projective (ModuleCat.of R (t →₀ R)) :=
      ModuleCat.projective_of_free Finsupp.basisSingleOne
    have hK := (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hM
    have hKf : Module.Free R (LinearMap.ker f) := ih _ inferInstance hK
    have hsK : ∀ k : LinearMap.ker f, s • k = 0 := by
      intro k
      refine Subtype.ext (Finsupp.ext fun i => ?_)
      simp [hsm _ (coeff_mem_maximalIdeal_of_minimal t ht hmin _ (LinearMap.mem_ker.mp k.2) i)]
    have hK0 : Subsingleton (LinearMap.ker f) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      let b := Module.Free.chooseBasis R (LinearMap.ker f)
      obtain ⟨i⟩ := b.index_nonempty
      apply hs
      simpa using congr_arg (fun v => b.repr v i) (hsK (b i))
    have inj : Function.Injective f := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr
      fun c hc => congr_arg Subtype.val (Subsingleton.elim (⟨c, hc⟩ : LinearMap.ker f) 0))
    exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨inj, surj⟩)

/-- Depth zero and `pd k < ∞` force `m = 0`. -/
theorem maximalIdeal_eq_bot_of_depth_zero [IsLocalRing R] [IsNoetherianRing R] {s : R}
    (hs : s ≠ 0) (hsm : ∀ y ∈ maximalIdeal R, s * y = 0) (n : ℕ)
    (hk : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) n) :
    maximalIdeal R = ⊥ := by
  have hk' : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1) :=
    hasProjectiveDimensionLT_of_ge _ n (n + 1) (by omega)
  have : Module.Free R (R ⧸ maximalIdeal R) := free_of_depth_zero hs hsm n _ inferInstance hk'
  let b := Module.Free.chooseBasis R (R ⧸ maximalIdeal R)
  obtain ⟨i⟩ := b.index_nonempty
  rw [eq_bot_iff]
  intro y hy
  have h0 : y • b i = 0 := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hy,
      zero_mul]
  have := congr_arg (fun v => b.repr v i) h0
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, map_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  exact (Submodule.mem_bot R).mpr this

theorem mem_maximalIdeal_iff_quotient [IsLocalRing R] {x : R} [IsLocalRing (R ⧸ span {x})]
    (y : R) : y ∈ maximalIdeal R ↔ Ideal.Quotient.mk (span {x}) y ∈ maximalIdeal (R ⧸ span {x}) := by
  have h := IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective
    (Ideal.Quotient.mk (span {x})) Ideal.Quotient.mk_surjective (K := maximalIdeal (R ⧸ span {x})))
  rw [← h, Ideal.mem_comap]

/-- Lifting generators: `μ(m) ≤ μ(m / x) + 1`. -/
theorem spanFinrank_maximalIdeal_le_quotient_add_one [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 := by
  classical
  obtain ⟨t, hcard, ht⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (Ideal.fg_of_isNoetherianRing (maximalIdeal (R ⧸ span {x})))
  let g := Function.surjInv (Ideal.Quotient.mk_surjective (I := span {x}))
  have hg : ∀ s, Ideal.Quotient.mk (span {x}) (g s) = s := Function.surjInv_eq _
  let T : Finset R := insert x (t.image g)
  have hT : span (T : Set R) = maximalIdeal R := by
    apply le_antisymm
    · rw [span_le]
      intro y hy
      simp only [T, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
        Finset.mem_coe] at hy
      rcases hy with rfl | ⟨s, hs, rfl⟩
      · exact hx
      · rw [SetLike.mem_coe, mem_maximalIdeal_iff_quotient (x := x), hg, ← ht]
        exact subset_span hs
    · intro y hy
      have h1 : Ideal.Quotient.mk (span {x}) y ∈
          (span ((t.image g : Finset R) : Set R)).map (Ideal.Quotient.mk (span {x})) := by
        rw [Ideal.map_span, Finset.coe_image, ← Set.image_comp]
        have : (Ideal.Quotient.mk (span {x}) ∘ g) = id := funext hg
        rw [this, Set.image_id]
        change _ ∈ Submodule.span (R ⧸ span {x}) (t : Set (R ⧸ span {x}))
        rw [ht]
        exact (mem_maximalIdeal_iff_quotient (x := x) y).mp hy
      obtain ⟨z, hz, hzy⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
      have hyz : y - z ∈ span {x} := Ideal.Quotient.eq.mp hzy.symm
      have hTx : span (T : Set R) = span {x} ⊔ span ((t.image g : Finset R) : Set R) := by
        simp only [T, Finset.coe_insert]
        exact Submodule.span_insert _ _
      rw [hTx]
      exact Submodule.mem_sup.mpr ⟨y - z, hyz, z, hz, by ring⟩
  calc (maximalIdeal R).spanFinrank = (span (T : Set R)).spanFinrank := by rw [hT]
    _ ≤ (T : Set R).ncard := Submodule.spanFinrank_span_le_ncard_of_finite T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ (t.image g).card + 1 := Finset.card_insert_le _ _
    _ ≤ t.card + 1 := by have := Finset.card_image_le (s := t) (f := g); omega
    _ = _ := by rw [hcard]

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_D =====
section

/-!
# S4-JacDivisors D (O3a and O4: Serre's hard direction)
* `hasPDLT_quotSMulTop` (O3a): `pd_{R/x} (M / x M) ≤ pd_R M` for `x` regular on `R` and `M`.
* `hasPDLT_residue_of_quotSMulTop`: for `x ∈ m \ m²`, the residue field of `R ⧸ (x)` is a retract
  of `m / x m`, so it inherits finite projective dimension.
* `isRegularLocalRing_of_hasPDLT` (O4): a Noetherian local ring whose residue field has finite
  projective dimension is regular.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal
open scoped Pointwise

universe u

variable {R : Type u} [CommRing R]

theorem isSMulRegular_pi {x : R} (hx : IsSMulRegular R x) (k : ℕ) :
    IsSMulRegular (Fin k → R) x := fun _ _ h => funext fun i => hx (congr_fun h i)

theorem isSMulRegular_submodule {M : Type u} [AddCommGroup M] [Module R M] {x : R}
    (hx : IsSMulRegular M x) (N : Submodule R M) : IsSMulRegular N x :=
  fun _ _ h => Subtype.ext (hx (congrArg Subtype.val h))

theorem isSMulRegular_of_mem_nonZeroDivisors {x : R} (hx : x ∈ nonZeroDivisors R) :
    IsSMulRegular R x := fun a b h => by
  have h' : (a - b) * x = 0 := by
    simp only [smul_eq_mul] at h
    rw [sub_mul, mul_comm a, mul_comm b, h, sub_self]
  exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hx).mp h')

/-- O3a: `pd_{R/x} (M / x M) ≤ pd_R M` for `x` regular on `R` and on `M`. -/
theorem hasPDLT_quotSMulTop [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hxR : IsSMulRegular R x) : ∀ (n : ℕ) (M : ModuleCat.{u} R), Module.Finite R M →
      IsSMulRegular M x → HasProjectiveDimensionLT M (n + 1) →
        HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro M _ _ hM
    have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    have : Projective (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x M)) :=
      ModuleCat.projective_of_free (Module.Free.chooseBasis (R ⧸ span {x}) (QuotSMulTop x M))
    infer_instance
  | succ n ih =>
    intro M _ hxM hM
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have : Projective (ModuleCat.of R (Fin k → R)) :=
      ModuleCat.projective_of_free (Pi.basisFun R (Fin k))
    have hK := (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hM
    have hxK : IsSMulRegular (LinearMap.ker f) x :=
      isSMulRegular_submodule (isSMulRegular_pi hxR k) _
    have hK' := ih (ModuleCat.of R (LinearMap.ker f)) inferInstance hxK hK
    have hsurj : Function.Surjective (algebraMap R (R ⧸ span {x})) := Ideal.Quotient.mk_surjective
    have hex : Function.Exact (QuotSMulTop.map x (LinearMap.ker f).subtype) (QuotSMulTop.map x f) :=
      QuotSMulTop.map_exact x (LinearMap.exact_subtype_ker_map f) hf
    have hinj : Function.Injective (QuotSMulTop.map x (LinearMap.ker f).subtype) := by
      rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
      rw [Submodule.mkQ_apply, QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero] at hq
      obtain ⟨p, -, hp⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hq
      have hfp : f p = 0 := hxM (by
        change x • f p = x • 0
        rw [smul_zero, ← map_smul, hp]
        exact a.2)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨⟨p, hfp⟩, trivial, Subtype.ext hp⟩
    let g₁ := (QuotSMulTop.map x (LinearMap.ker f).subtype).extendScalarsOfSurjective hsurj
    let g₂ := (QuotSMulTop.map x f).extendScalarsOfSurjective hsurj
    have hS' : (ShortComplex.moduleCatMk g₁ g₂
        (LinearMap.ext fun q => hex.apply_apply_eq_zero q)).ShortExact :=
      ModuleCat.shortComplex_shortExact _ hex hinj (QuotSMulTop.map_surjective x hf)
    have : Projective (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x (Fin k → R))) :=
      ModuleCat.projective_of_free
        (Module.Free.chooseBasis (R ⧸ span {x}) (QuotSMulTop x (Fin k → R)))
    exact hS'.hasProjectiveDimensionLT_X₃ (n + 1) hK'
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x (Fin k → R)))
        1 (n + 2) (by omega))

/-- For `x ∈ m \ m²`, the residue field of `R ⧸ (x)` is a retract of `m / x m`; hence it
inherits a bound on projective dimension. -/
theorem hasPDLT_residue_of_quotSMulTop [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] (n : ℕ)
    (h : HasProjectiveDimensionLT
      (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x (maximalIdeal R))) n) :
    HasProjectiveDimensionLT (ModuleCat.of (R ⧸ span {x})
      ((R ⧸ span {x}) ⧸ maximalIdeal (R ⧸ span {x}))) n := by
  have hsurj : Function.Surjective (algebraMap R (R ⧸ span {x})) := Ideal.Quotient.mk_surjective
  let v : QuotSMulTop x (maximalIdeal R) := Submodule.Quotient.mk ⟨x, hx⟩
  have hi : maximalIdeal (R ⧸ span {x}) ≤
      LinearMap.ker (LinearMap.toSpanSingleton (R ⧸ span {x}) _ v) := by
    intro s hs
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hr : r ∈ maximalIdeal R := (mem_maximalIdeal_iff_quotient (x := x) r).mpr hs
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      Module.IsTorsionBy.mk_smul (Module.isTorsionBy_quotient_element_smul _ x) r v,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨⟨r, hr⟩, trivial, Subtype.ext (by change x * r = r * x; ring)⟩
  let i := (maximalIdeal (R ⧸ span {x})).liftQ _ hi
  have : (maximalIdeal R).IsMaximal := maximalIdeal.isMaximal R
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have hv : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]; exact hx2
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (R ⧸ maximalIdeal R) (maximalIdeal R).Cotangent,
      φ ((maximalIdeal R).toCotangent ⟨x, hx⟩) ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff _ _).mp hc)
  let φ' := (φ ((maximalIdeal R).toCotangent ⟨x, hx⟩))⁻¹ • φ
  have hφ' : φ' ((maximalIdeal R).toCotangent ⟨x, hx⟩) = 1 := by
    simp [φ', hφ]
  let ψ := (φ'.restrictScalars R) ∘ₗ (maximalIdeal R).toCotangent
  have hψ : x • (⊤ : Submodule R (maximalIdeal R)) ≤ LinearMap.ker ψ := by
    intro a ha
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ha
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hx, zero_mul]
  let ψ' := (x • (⊤ : Submodule R (maximalIdeal R))).liftQ ψ hψ
  have hθ : maximalIdeal R ≤
      LinearMap.ker (Algebra.linearMap R ((R ⧸ span {x}) ⧸ maximalIdeal (R ⧸ span {x}))) := by
    intro r hr
    rw [LinearMap.mem_ker, Algebra.linearMap_apply]
    change Ideal.Quotient.mk _ (Ideal.Quotient.mk (span {x}) r) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_maximalIdeal_iff_quotient (x := x) r).mp hr)
  let θ := (maximalIdeal R).liftQ _ hθ
  let r := (θ ∘ₗ ψ').extendScalarsOfSurjective hsurj
  have hri : r ∘ₗ i = LinearMap.id := by
    apply Submodule.linearMap_qext
    apply LinearMap.ext_ring
    have h1 : i (Submodule.Quotient.mk 1) = v := by
      simp only [i, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
    have h2 : r v = θ (φ' ((maximalIdeal R).toCotangent ⟨x, hx⟩)) := rfl
    have h3 : θ 1 = 1 := by
      change Algebra.linearMap R ((R ⧸ span {x}) ⧸ maximalIdeal (R ⧸ span {x})) 1 = 1
      rw [Algebra.linearMap_apply, map_one]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.id_apply]
    rw [h1, h2, hφ', h3]
    rfl
  let rt : Retract (ModuleCat.of (R ⧸ span {x}) ((R ⧸ span {x}) ⧸ maximalIdeal (R ⧸ span {x})))
      (ModuleCat.of (R ⧸ span {x}) (QuotSMulTop x (maximalIdeal R))) :=
    ⟨ModuleCat.ofHom i, ModuleCat.ofHom r, ModuleCat.hom_ext hri⟩
  exact rt.hasProjectiveDimensionLT n

theorem isRegularLocalRing_of_maximalIdeal_eq_bot [IsLocalRing R] [IsNoetherianRing R]
    (hb : maximalIdeal R = ⊥) : IsRegularLocalRing R := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [hb, Submodule.spanFinrank_bot, Nat.cast_zero]
  exact ringKrullDim_nonneg_of_nontrivial

/-- O4 (Serre, hard direction), by induction on the number of generators of `m`. -/
theorem isRegularLocalRing_of_hasPDLT_aux : ∀ (d : ℕ) (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R], (maximalIdeal R).spanFinrank ≤ d → ∀ n : ℕ,
      HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) n → IsRegularLocalRing R := by
  intro d
  induction d with
  | zero =>
    intro R _ _ _ hd n hn
    exact isRegularLocalRing_of_maximalIdeal_eq_bot ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal R).fg_of_isNoetherianRing).mp (by omega))
  | succ d ih =>
    intro R _ _ _ hd n hn
    by_cases hb : maximalIdeal R = ⊥
    · exact isRegularLocalRing_of_maximalIdeal_eq_bot hb
    by_cases hdis : Disjoint (maximalIdeal R : Set R) (nonZeroDivisors R)
    · exfalso
      obtain ⟨s, hs, hs0⟩ :=
        SetLike.exists_of_lt (Ideal.bot_lt_annihilator_of_disjoint_nonZeroDivisors hdis)
      refine hb (maximalIdeal_eq_bot_of_depth_zero (s := s)
        (fun h0 => hs0 ((Submodule.mem_bot R).mpr h0)) (fun y hy => ?_) n hn)
      exact congrArg Subtype.val ((Module.mem_annihilator.mp hs) ⟨y, hy⟩)
    have hm2 : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2 := fun hle => hb
      (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
        (maximalIdeal R).fg_of_isNoetherianRing (by rwa [pow_two] at hle)
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]))
    obtain ⟨x, hx, hx2, hxnz⟩ := exists_nonZeroDivisor_not_mem_sq hm2 hdis
    have : IsLocalRing (R ⧸ span {x}) := isLocalRing_quotient_span hx
    have hxR : IsSMulRegular R x := isSMulRegular_of_mem_nonZeroDivisors hxnz
    have hSm : (ShortComplex.moduleCatMk (maximalIdeal R).subtype (maximalIdeal R).mkQ
        (LinearMap.exact_subtype_mkQ _).linearMap_comp_eq_zero).ShortExact :=
      ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ _)
        (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    have hP : Projective (ModuleCat.of R R) :=
      ModuleCat.projective_of_free (Module.Basis.singleton Unit R)
    have hn2 : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 2) :=
      hasProjectiveDimensionLT_of_ge _ n (n + 2) (by omega)
    have hmn := (hSm.hasProjectiveDimensionLT_X₃_iff n hP).mp hn2
    have hq := hasPDLT_quotSMulTop hxR n (ModuleCat.of R (maximalIdeal R)) inferInstance
      (isSMulRegular_submodule hxR _) hmn
    have hk := hasPDLT_residue_of_quotSMulTop hx hx2 (n + 1) hq
    have hS1 := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have := ih (R ⧸ span {x}) (by omega) (n + 1) hk
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    have h1 := spanFinrank_maximalIdeal_le_quotient_add_one (R := R) hx
    rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hxnz hx,
      ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ span {x})]
    exact_mod_cast h1

/-- O4 (Serre): a Noetherian local ring whose residue field has finite projective dimension
is regular. -/
theorem isRegularLocalRing_of_hasPDLT [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
    (hn : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) n) :
    IsRegularLocalRing R :=
  isRegularLocalRing_of_hasPDLT_aux _ R le_rfl n hn

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_E =====
section

/-!
# S4-JacDivisors E (O6: localizations of regular local rings)
* `localizedModule_quotient_iso`: `(R ⧸ Q)_Q ≅ R_Q ⧸ m_{R_Q}` as `R_Q`-modules.
* `isRegularLocalRing_localization` (O6): `R` regular local, `Q` prime ⟹ `R_Q` regular local
  (Serre: `pd_R (R ⧸ Q) < ∞` localizes to `pd_{R_Q} k(Q) < ∞`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal

universe u

variable {R : Type u} [CommRing R]

/-- `(R ⧸ Q)_Q ≅ R_Q ⧸ m` as `R_Q`-modules. -/
noncomputable def localizedModule_quotient_iso (Q : Ideal R) [Q.IsPrime] :
    (ModuleCat.of R (R ⧸ Q)).localizedModule Q.primeCompl ≅
      ModuleCat.of (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ maximalIdeal (Localization.AtPrime Q)) :=
  let e1 := Shrink.linearEquiv.{u} (Localization.AtPrime Q)
    (LocalizedModule Q.primeCompl (R ⧸ Q))
  let e2 := (IsLocalizedModule.iso Q.primeCompl
    (Q.toLocalizedQuotient' (Localization.AtPrime Q) Q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime Q)))).extendScalarsOfIsLocalization
        Q.primeCompl (Localization.AtPrime Q)
  let e3 := Submodule.quotEquivOfEq _ _ (by
    rw [Ideal.localized'_eq_map, Localization.AtPrime.map_eq_maximalIdeal])
  (e1.trans (e2.trans e3)).toModuleIso

/-- O6: the localization of a regular local ring at a prime is regular local. -/
theorem isRegularLocalRing_localization [IsRegularLocalRing R] (Q : Ideal R) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  obtain ⟨n, hn⟩ := exists_hasPDLT_of_isRegularLocalRing (ModuleCat.of R (R ⧸ Q))
  have : HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Q)) n :=
    hasProjectiveDimensionLT_of_ge _ n (n + 1) (by omega)
  have h1 := (ModuleCat.of R (R ⧸ Q)).localizedModule_hasProjectiveDimensionLE n Q.primeCompl
  have h2 := hasProjectiveDimensionLT_of_iso (localizedModule_quotient_iso Q) (n + 1)
  exact isRegularLocalRing_of_hasPDLT (n + 1) h2

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_F =====
section

/-!
# S4-JacDivisors F (O8: finite free resolutions)
* `HasFFR A n M`: `M` has a resolution of length `n` by finite free `A`-modules.
* `hasFFR_of_hasPDLT`: over a Noetherian local ring, a finite module of finite projective
  dimension has a finite free resolution.
* `hasFFR_of_isLocalizedModule`: finite free resolutions localize.
* `isStablyFree_of_hasFFR`: a projective module with a finite free resolution is stably free.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal
open scoped TensorProduct

universe u

/-- `HasFFR A n M`: a resolution `0 → F_n → ⋯ → F_0 → M → 0` by finite free modules. -/
def HasFFR (A : Type u) [CommRing A] : ℕ → (M : Type u) → [AddCommGroup M] → [Module A M] → Prop
  | 0 => fun M => Module.Finite A M ∧ Module.Free A M
  | n + 1 => fun M => ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module A F),
      Module.Finite A F ∧ Module.Free A F ∧ ∃ f : F →ₗ[A] M, Function.Surjective f ∧
        HasFFR A n (LinearMap.ker f)

section Basic

variable {A : Type u} [CommRing A]

theorem hasFFR_zero_iff {M : Type u} [AddCommGroup M] [Module A M] :
    HasFFR A 0 M ↔ Module.Finite A M ∧ Module.Free A M := Iff.rfl

theorem hasFFR_succ_iff {n : ℕ} {M : Type u} [AddCommGroup M] [Module A M] :
    HasFFR A (n + 1) M ↔ ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module A F),
      Module.Finite A F ∧ Module.Free A F ∧ ∃ f : F →ₗ[A] M, Function.Surjective f ∧
        HasFFR A n (LinearMap.ker f) := Iff.rfl

theorem HasFFR.finite : ∀ {n : ℕ} {M : Type u} [AddCommGroup M] [Module A M],
    HasFFR A n M → Module.Finite A M
  | 0, _, _, _, h => h.1
  | _ + 1, _, _, _, h => by
    obtain ⟨F, _, _, _, _, f, hf, -⟩ := hasFFR_succ_iff.mp h
    exact Module.Finite.of_surjective f hf

theorem HasFFR.of_equiv : ∀ {n : ℕ} {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N], HasFFR A n M → (M ≃ₗ[A] N) → HasFFR A n N
  | 0, _, _, _, _, _, _, h, e => by
    obtain ⟨_, _⟩ := hasFFR_zero_iff.mp h
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  | _ + 1, _, _, _, _, _, _, h, e => by
    obtain ⟨F, _, _, _, _, f, hf, hK⟩ := hasFFR_succ_iff.mp h
    refine hasFFR_succ_iff.mpr ⟨F, _, _, inferInstance, inferInstance, e.toLinearMap ∘ₗ f,
      e.surjective.comp hf, ?_⟩
    exact HasFFR.of_equiv hK (LinearEquiv.ofEq _ _ (LinearEquiv.ker_comp e f).symm)

end Basic

/-- Over a Noetherian local ring, a finite module with `pd < n + 1` has a free resolution of
length `n` by finite free modules. -/
theorem hasFFR_of_hasPDLT {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∀ (n : ℕ) (M : ModuleCat.{u} R), Module.Finite R M → HasProjectiveDimensionLT M (n + 1) →
      HasFFR R n M := by
  intro n
  induction n with
  | zero =>
    intro M _ hM
    have : Projective M := projective_iff_hasProjectiveDimensionLT_one.mpr hM
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    exact ⟨inferInstance, this⟩
  | succ n ih =>
    intro M _ hM
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS := LinearMap.shortExact_shortComplexKer hf
    have : Projective (ModuleCat.of R (Fin k → R)) :=
      ModuleCat.projective_of_free (Pi.basisFun R (Fin k))
    have hK := (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hM
    exact hasFFR_succ_iff.mpr ⟨Fin k → R, _, _, inferInstance, inferInstance, f, hf,
      ih (ModuleCat.of R (LinearMap.ker f)) inferInstance hK⟩

/-- Finite free resolutions localize. -/
theorem hasFFR_of_isLocalizedModule {R : Type u} [CommRing R] (S : Submonoid R) (A : Type u)
    [CommRing A] [Algebra R A] [IsLocalization S A] :
    ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module R M], HasFFR R n M →
      ∀ (M' : Type u) [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
        (g : M →ₗ[R] M') [IsLocalizedModule S g], HasFFR A n M' := by
  intro n
  induction n with
  | zero =>
    intro M _ _ hM M' _ _ _ _ g _
    obtain ⟨_, _⟩ := hasFFR_zero_iff.mp hM
    exact ⟨Module.Finite.of_isLocalizedModule S g, Module.free_of_isLocalizedModule S g⟩
  | succ n ih =>
    intro M _ _ hM M' _ _ _ _ g _
    obtain ⟨F, _, _, _, _, f, hf, hK⟩ := hasFFR_succ_iff.mp hM
    let gF : F →ₗ[R] A ⊗[R] F := TensorProduct.mk R A F 1
    have : IsLocalizedModule S gF :=
      (isLocalizedModule_iff_isBaseChange S A gF).mpr (TensorProduct.isBaseChange R F A)
    let f' : A ⊗[R] F →ₗ[A] M' :=
      (IsLocalizedModule.map S gF g f).extendScalarsOfIsLocalization S A
    have hf' : Function.Surjective f' := IsLocalizedModule.map_surjective S gF g f hf
    let e : (LinearMap.ker f).localized' A S gF ≃ₗ[A] LinearMap.ker f' :=
      LinearEquiv.ofEq _ _ (LinearMap.localized'_ker_eq_ker_localizedMap A S gF g f)
    let h : LinearMap.ker f →ₗ[R] LinearMap.ker f' :=
      (e.restrictScalars R).toLinearMap ∘ₗ (LinearMap.ker f).toLocalized' A S gF
    have : IsLocalizedModule S h := IsLocalizedModule.of_linearEquiv S _ _
    exact hasFFR_succ_iff.mpr ⟨A ⊗[R] F, _, _, Module.Finite.of_isLocalizedModule S gF,
      Module.free_of_isLocalizedModule S gF, f', hf',
      ih (LinearMap.ker f) hK (LinearMap.ker f') h⟩

/-- A projective module with a finite free resolution is stably free. -/
theorem isStablyFree_of_hasFFR {A : Type u} [CommRing A] :
    ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module A M] [Module.Projective A M],
      HasFFR A n M → Module.IsStablyFree A M := by
  intro n
  induction n with
  | zero =>
    intro M _ _ _ hM
    obtain ⟨_, _⟩ := hasFFR_zero_iff.mp hM
    infer_instance
  | succ n ih =>
    intro M _ _ _ hM
    obtain ⟨F, _, _, _, _, f, hf, hK⟩ := hasFFR_succ_iff.mp hM
    obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
    have hfs (m : M) : f (s m) = m := LinearMap.congr_fun hs m
    let K := LinearMap.ker f
    let r : F →ₗ[A] K := (LinearMap.id - s ∘ₗ f).codRestrict K (fun y =>
      LinearMap.mem_ker.mpr (by simp [hfs]))
    have hr : r ∘ₗ K.subtype = LinearMap.id := by
      ext k
      simp [r, LinearMap.mem_ker.mp k.2]
    have : Module.Projective A K := Module.Projective.of_split K.subtype r hr
    have : Module.IsStablyFree A K := ih K hK
    have : Module.Finite A K := hK.finite
    obtain ⟨N, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod A K
    let φ : M × K →ₗ[A] F := LinearMap.coprod s K.subtype
    have hφ : Function.Bijective φ := by
      refine ⟨(injective_iff_map_eq_zero φ).mpr fun ⟨m, k⟩ h => ?_, fun y => ⟨(f y, r y), ?_⟩⟩
      · have h' : s m + (k : F) = 0 := h
        have hm : m = 0 := by
          have := congrArg f h'
          rwa [map_add, hfs, LinearMap.mem_ker.mp k.2, add_zero, map_zero] at this
        subst hm
        have hk : (k : F) = 0 := by simpa using h'
        exact Prod.ext rfl (Subtype.ext hk)
      · simp [φ, r]
    let e : (M × K) ≃ₗ[A] F := LinearEquiv.ofBijective φ hφ
    have : Module.Free A (M × (K × N)) := Module.Free.of_equiv
      ((e.symm.prodCongr (LinearEquiv.refl A N)).trans (LinearEquiv.prodAssoc A M K N))
    exact Module.IsStablyFree.of_free_prod A M (K × N)

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_G =====
section

/-!
# S4-JacDivisors G (O9: Auslander-Buchsbaum, regular local rings are UFDs)
* `invertible_of_forall_isMaximal`: a nonzero ideal of a domain that is principal near every
  maximal ideal is an invertible module.
* `exists_dvd_of_ufd_localization`: a height-one prime `p` is principal near `Q` when `R_Q` is a UFD.
* `uniqueFactorizationMonoid_of_isRegularLocalRing` (O9).
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open CategoryTheory IsLocalRing Ideal

universe u

/-- A (nonzero) ideal of a domain that is "principal near every maximal ideal" is invertible. -/
theorem invertible_of_forall_isMaximal {A : Type u} [CommRing A] [IsDomain A] (P : Ideal A)
    (hP : ∀ M : Ideal A, M.IsMaximal → ∃ a ∈ P, a ≠ 0 ∧ ∃ s ∉ M, ∀ y ∈ P, a ∣ s * y) :
    Module.Invertible A P := by
  have hinj : Function.Injective (algebraMap A (FractionRing A)) :=
    IsFractionRing.injective A (FractionRing A)
  have hIJ : Submodule.map (Algebra.linearMap A (FractionRing A)) P *
      (1 / Submodule.map (Algebra.linearMap A (FractionRing A)) P) = 1 := by
    refine le_antisymm Submodule.mul_one_div_le_one ?_
    let L : Ideal A := Submodule.comap (Algebra.linearMap A (FractionRing A))
      (Submodule.map (Algebra.linearMap A (FractionRing A)) P *
        (1 / Submodule.map (Algebra.linearMap A (FractionRing A)) P))
    have hL : L = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hLM⟩ := Ideal.exists_le_maximal L hne
      obtain ⟨a, ha, ha0, s, hs, hdiv⟩ := hP M hM
      refine hs (hLM ?_)
      have ha0' : algebraMap A (FractionRing A) a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
      have hmem : algebraMap A (FractionRing A) s / algebraMap A (FractionRing A) a ∈
          1 / Submodule.map (Algebra.linearMap A (FractionRing A)) P := by
        rw [Submodule.mem_div_iff_forall_mul_mem]
        intro y hy
        obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
        obtain ⟨c, hc⟩ := hdiv p hp
        rw [Submodule.mem_one]
        refine ⟨c, ?_⟩
        rw [Algebra.linearMap_apply, div_mul_eq_mul_div, eq_div_iff ha0', ← map_mul, ← map_mul,
          hc, mul_comm]
      show Algebra.linearMap A (FractionRing A) s ∈
        Submodule.map (Algebra.linearMap A (FractionRing A)) P *
          (1 / Submodule.map (Algebra.linearMap A (FractionRing A)) P)
      rw [Algebra.linearMap_apply]
      have : algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a *
          (algebraMap A (FractionRing A) s / algebraMap A (FractionRing A) a) := by
        field_simp
      rw [this]
      exact Submodule.mul_mem_mul (Submodule.mem_map_of_mem ha) hmem
    intro z hz
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hz
    have : r ∈ L := hL ▸ Submodule.mem_top
    exact this
  let u := (IsUnit.of_mul_eq_one _ hIJ).unit
  have h1 : Module.Invertible A (u : Submodule A (FractionRing A)) := inferInstance
  have h2 : Module.Invertible A (Submodule.map (Algebra.linearMap A (FractionRing A)) P) := h1
  exact Module.Invertible.congr
    (Submodule.equivMapOfInjective (Algebra.linearMap A (FractionRing A)) hinj P).symm

/-- If `R_Q` is a UFD, a height-one prime `p` of `R` is principal near `Q`. -/
theorem exists_dvd_of_ufd_localization {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (Q : Ideal R) [Q.IsPrime]
    [IsDomain (Localization.AtPrime Q)] [UniqueFactorizationMonoid (Localization.AtPrime Q)] :
    ∃ a ∈ p, a ≠ 0 ∧ ∃ s ∉ Q, ∀ y ∈ p, a ∣ s * y := by
  by_cases hpQ : p ≤ Q
  swap
  · obtain ⟨t, htp, htQ⟩ := SetLike.not_le_iff_exists.mp hpQ
    exact ⟨t, htp, fun h => htQ (h ▸ Q.zero_mem), t, htQ, fun y _ => dvd_mul_right t y⟩
  have hd : Disjoint (Q.primeCompl : Set R) p :=
    Set.disjoint_left.mpr fun t ht htp => ht (hpQ htp)
  have hQp : (p.map (algebraMap R (Localization.AtPrime Q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl _ p ‹_› hd
  have hh : (p.map (algebraMap R (Localization.AtPrime Q))).height = 1 := by
    rw [← IsLocalization.height_under Q.primeCompl,
      IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl _ ‹p.IsPrime› hd, hp]
  obtain ⟨g, hg⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh
  have hg0 : g ∈ p.map (algebraMap R (Localization.AtPrime Q)) :=
    hg ▸ Submodule.mem_span_singleton_self g
  obtain ⟨⟨a, t⟩, hat⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl _).mp hg0
  have hspan : p.map (algebraMap R (Localization.AtPrime Q)) =
      Ideal.span {algebraMap R (Localization.AtPrime Q) a} := by
    rw [hg, ← hat]
    exact (Ideal.span_singleton_mul_right_unit (IsLocalization.map_units _ t) g).symm
  have ha0 : (a : R) ≠ 0 := by
    intro h0
    refine Ideal.ne_bot_of_height_eq_one hh ?_
    rw [hspan, h0, map_zero, Ideal.span_singleton_eq_bot]
  have hloc : ∀ y ∈ p, ∃ t' ∈ Q.primeCompl, (a : R) ∣ t' * y := by
    intro y hy
    have hy' : algebraMap R (Localization.AtPrime Q) y ∈
        Ideal.span {algebraMap R (Localization.AtPrime Q) a} :=
      hspan ▸ Ideal.mem_map_of_mem _ hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hy'
    obtain ⟨⟨r, t'⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl c
    have he : algebraMap R (Localization.AtPrime Q) (r * a) =
        algebraMap R (Localization.AtPrime Q) (t' * y) := by
      rw [map_mul, map_mul, ← hc, ← mul_assoc, IsLocalization.mk'_spec']
    have := IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors he
    exact ⟨t', t'.2, r, by rw [← this, mul_comm]⟩
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian p : p.FG)
  choose! t' ht' hdvd using hloc
  have hGp : ∀ g ∈ G, g ∈ p := fun g hg => hG ▸ Submodule.subset_span hg
  refine ⟨a, a.2, ha0, ∏ g ∈ G, t' g, ?_, fun y hy => ?_⟩
  · exact Q.primeCompl.prod_mem fun g hg => ht' g (hGp g hg)
  rw [← hG] at hy
  refine Submodule.span_induction (fun g hg => ?_) ?_ (fun u v _ _ hu hv => ?_)
    (fun c u _ hu => ?_) hy
  · obtain ⟨w, hw⟩ := Finset.dvd_prod_of_mem t' hg
    rw [hw, mul_comm (t' g) w, mul_assoc]
    exact Dvd.dvd.mul_left (hdvd g (hGp g hg)) w
  · simp
  · rw [mul_add]
    exact dvd_add hu hv
  · rw [smul_eq_mul, mul_left_comm]
    exact Dvd.dvd.mul_left hu c

variable {R : Type u} [CommRing R]

/-- O9 core: for `x ∈ m \ m²` and a height-one prime `p ∌ x`, `p R_x` is principal, provided every
`R_Q` with `Q ≠ m` is a UFD. -/
theorem isPrincipal_map_away [IsRegularLocalRing R] {x : R} (hx0 : x ≠ 0)
    (hxm : x ∈ maximalIdeal R) (p : Ideal R) [p.IsPrime] (hp : p.height = 1)
    (hQ : ∀ (Q : Ideal R) [Q.IsPrime], x ∉ Q →
      UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    (p.map (algebraMap R (Localization.Away x))).IsPrincipal := by
  have : IsDomain (Localization.Away x) := IsLocalization.Away.isDomain _ hx0
  have hinjA := IsLocalization.injective (Localization.Away x)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  have hInv : Module.Invertible (Localization.Away x)
      (p.map (algebraMap R (Localization.Away x))) := by
    refine invertible_of_forall_isMaximal _ fun M hM => ?_
    have hxQ : x ∉ M.comap (algebraMap R (Localization.Away x)) := fun h =>
      hM.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit x))
    have := hQ _ hxQ
    obtain ⟨a, ha, ha0, s, hs, hdiv⟩ :=
      exists_dvd_of_ufd_localization p hp (M.comap (algebraMap R (Localization.Away x)))
    refine ⟨algebraMap R _ a, Ideal.mem_map_of_mem _ ha, (map_ne_zero_iff _ hinjA).mpr ha0,
      algebraMap R _ s, hs, fun y hy => ?_⟩
    refine Submodule.span_induction (fun g hg => ?_) ?_ (fun u v _ _ hu hv => ?_)
      (fun c u _ hu => ?_) hy
    · obtain ⟨h, hh, rfl⟩ := hg
      rw [← map_mul]
      exact map_dvd _ (hdiv h hh)
    · simp
    · rw [mul_add]
      exact dvd_add hu hv
    · rw [smul_eq_mul, mul_left_comm]
      exact Dvd.dvd.mul_left hu c
  obtain ⟨n, hn⟩ := exists_hasPDLT_of_isRegularLocalRing (ModuleCat.of R p)
  have hn' : HasProjectiveDimensionLT (ModuleCat.of R p) (n + 1) :=
    hasProjectiveDimensionLT_of_ge _ n (n + 1) (by omega)
  have h1 : HasFFR R n p := hasFFR_of_hasPDLT n (ModuleCat.of R p) inferInstance hn'
  have h2 := hasFFR_of_isLocalizedModule (Submonoid.powers x) (Localization.Away x) n p h1 _
    (p.toLocalized' (Localization.Away x) (Submonoid.powers x)
      (Algebra.linearMap R (Localization.Away x)))
  have h3 : HasFFR (Localization.Away x) n (p.map (algebraMap R (Localization.Away x))) :=
    h2.of_equiv (LinearEquiv.ofEq _ _
      (Ideal.localized'_eq_map (Localization.Away x) (Submonoid.powers x) p))
  have : Module.IsStablyFree (Localization.Away x)
      (p.map (algebraMap R (Localization.Away x))) := isStablyFree_of_hasFFR n _ h3
  have := Module.free_of_isStablyFree_of_invertible (Localization.Away x)
    (p.map (algebraMap R (Localization.Away x)))
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.mp this
  refine ⟨⟨(e.symm 1 : Localization.Away x), le_antisymm (fun y hy => ?_)
    ((Submodule.span_singleton_le_iff_mem _ _).mpr (e.symm 1).2)⟩⟩
  rw [Submodule.mem_span_singleton]
  refine ⟨e ⟨y, hy⟩, ?_⟩
  have he : e.symm (e ⟨y, hy⟩) = e ⟨y, hy⟩ • e.symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [e.symm_apply_apply] at he
  exact (congrArg Subtype.val he).symm

theorem uniqueFactorizationMonoid_aux : ∀ (k : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
    ringKrullDim R = k → UniqueFactorizationMonoid R := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro R _ _ hk
  rw [UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one]
  intro p _ hp1
  have hk0 : (maximalIdeal R).spanFinrank ≠ 0 := by
    intro h0
    have h1 := Ideal.height_le_ringKrullDim_of_isPrime (I := p)
    rw [hp1, ← IsRegularLocalRing.spanFinrank_maximalIdeal, h0] at h1
    exact absurd h1 (by decide)
  obtain ⟨x, hxm, hx2⟩ := exists_mem_maximalIdeal_not_mem_sq hk0
  have hx0 : x ≠ 0 := fun h => hx2 (h ▸ Ideal.zero_mem _)
  have hxp : Prime x := (Ideal.span_singleton_prime hx0).mp (isPrime_span_of_not_mem_sq hxm hx2)
  by_cases hxP : x ∈ p
  · exact ⟨x, p.eq_span_singleton_of_height_eq_one hp1 hxP hxp⟩
  refine p.isPrincipal_of_isPrincipal_localizationAway_of_prime hxp hxP
    (isPrincipal_map_away hx0 hxm p hp1 fun Q _ hxQ => ?_)
  have hQm : Q ≠ maximalIdeal R := fun h => hxQ (h ▸ hxm)
  have hlt : Q.height < ringKrullDim R := lt_of_le_of_ne Ideal.height_le_ringKrullDim_of_isPrime
    fun h => hQm (Ideal.height_eq_ringKrullDim_iff.mp h)
  have := isRegularLocalRing_localization Q
  obtain ⟨k', hk'⟩ := exists_nat_ringKrullDim_eq (R := Localization.AtPrime Q)
  have hkk : k' < k := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q), hk', hk] at hlt
    exact_mod_cast hlt
  exact ih k' hkk _ hk'

/-- O9 (Auslander-Buchsbaum): a regular local ring is a UFD. -/
theorem uniqueFactorizationMonoid_of_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : UniqueFactorizationMonoid R := by
  obtain ⟨k, hk⟩ := exists_nat_ringKrullDim_eq (R := R)
  exact uniqueFactorizationMonoid_aux k R hk

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_JacDivisors_S =====
section

/-!
# S4-JacDivisors S (O10, scheme part, and the smooth form of Weil's extension theorem)
* `isRegularLocalRing_stalk_of_smooth`: the local rings of a smooth `k`-scheme are regular
  (standard smooth charts are étale over a polynomial ring, file R).
* `uniqueFactorizationMonoid_stalk_of_smooth`: they are factorial (file G, Auslander-Buchsbaum).
* `domain_eq_top_of_smooth`, `domain_eq_top_of_smooth_of_isProper` (Milne I.3.2): for `k`
  algebraically closed, `V` smooth over `k` with `V` and `V ×_k V` integral, every rational map
  from `V` to a separated group `G` over `k` (locally of finite type, valuative existence, e.g.
  proper) is defined everywhere.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacDivisors

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj CartesianMonoidalCategory

universe u

/-- The stalks of `X` at points of an affine open with regular ring of sections are regular. -/
theorem isRegularLocalRing_stalk_of_isAffineOpen {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)
    [IsRegularRing Γ(X, V)] (y : V) : IsRegularLocalRing (X.presheaf.stalk y) := by
  have := hV.isLocalization_stalk y
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv
    (hV.primeIdealOf y).asIdeal.primeCompl (Localization.AtPrime (hV.primeIdealOf y).asIdeal)
    (X.presheaf.stalk y)).toRingEquiv

/-- The local rings of a smooth scheme over a field are regular local rings. -/
theorem isRegularLocalRing_stalk_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hxV, e, hs⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, g, -, het⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hs
  have hUtop : U = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    have hfx : f x ∈ U := e hxV
    rwa [Subsingleton.elim y (f x)]
  subst hUtop
  have : IsRegularRing Γ(Spec (.of k), ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm
  let := g.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) Γ(Spec (.of k), ⊤)) Γ(X, V) := het
  have : IsRegularRing Γ(X, V) :=
    isRegularRing_of_etale (A := MvPolynomial (Fin n) Γ(Spec (.of k), ⊤))
  exact isRegularLocalRing_stalk_of_isAffineOpen hV ⟨x, hxV⟩

/-- The local rings of a smooth scheme over a field are factorial. -/
theorem uniqueFactorizationMonoid_stalk_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  haveI := isRegularLocalRing_stalk_of_smooth f x
  uniqueFactorizationMonoid_of_isRegularLocalRing _

section
variable {k : Type u} [Field k] {V G : Over (Spec (.of k))}

instance smooth_tensor_hom [Smooth V.hom] : Smooth (V ⊗ V).hom :=
  show Smooth (pullback.fst V.hom V.hom ≫ V.hom) from inferInstance

variable [GrpObj G]

/-- **Weil's extension theorem** (Milne I.3.2), smooth form: a rational map from a smooth
`k`-variety `V` (with `V ×_k V` integral) to a separated group `G` satisfying valuative
existence is defined everywhere. -/
theorem domain_eq_top_of_smooth [IsAlgClosed k] [Smooth V.hom] [LocallyOfFiniteType G.hom]
    [IsSeparated G.hom] [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (hY : ValuativeCriterion.Existence G.hom)
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    f.toRationalMap.domain = ⊤ := by
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian V.hom
  have : IsLocallyNoetherian (V ⊗ V).left := LocallyOfFiniteType.isLocallyNoetherian (V ⊗ V).hom
  have : ∀ v : V.left, UniqueFactorizationMonoid (V.left.presheaf.stalk v) :=
    uniqueFactorizationMonoid_stalk_of_smooth V.hom
  have : ∀ p : (V ⊗ V).left, UniqueFactorizationMonoid ((V ⊗ V).left.presheaf.stalk p) :=
    uniqueFactorizationMonoid_stalk_of_smooth (V ⊗ V).hom
  exact domain_eq_top hY f hf

/-- **Weil's extension theorem** (Milne I.3.2) for a proper group `G` and smooth `V`. -/
theorem domain_eq_top_of_smooth_of_isProper [IsAlgClosed k] [Smooth V.hom] [IsProper G.hom]
    [IsIntegral V.left] [IsIntegral (V ⊗ V).left]
    (f : V.left.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι ≫ V.hom) :
    f.toRationalMap.domain = ⊤ := by
  have h : UniversallyClosed G.hom := inferInstance
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact domain_eq_top_of_smooth h.1 f hf

end

end RamanujanPetersson.JacDivisors


end

-- ===== S4.Def_RP_IntersectB_Prime =====
section

/-!
# S4-IntersectB, file Prime: prime divisors as locally principal ideal sheaves (O6)

* `primeI z`: the vanishing ideal sheaf of `closure {z}`; `coe_support_primeI`.
* `ideal_primeI_fromSpec`, `ideal_primeI_of_notMem`: on an affine chart `V` the ideal is the prime
  `y` with `z = fromSpec y`, and `⊤` when `z ∉ V`.
* `support_primeI_ne_top`: the support is a proper closed set when `z` has codimension one.
* `isLocPrin_primeI`: on an integral locally Noetherian scheme with factorial stalks, a
  codimension-one point gives a locally principal ideal sheaf; `isLocPrin_primeI_of_smooth`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology Order

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.JacDivisors

variable {X : Scheme.{u}}

/-- The ideal sheaf of the closure of a point (a prime divisor when `z` has codimension one). -/
noncomputable def primeI (z : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {z}, isClosed_closure⟩

lemma coe_support_primeI (z : X) : ((primeI z).support : Set X) = closure {z} := by
  simp [primeI]

lemma ideal_primeI (z : X) (V : X.affineOpens) :
    (primeI z).ideal V = PrimeSpectrum.vanishingIdeal (V.2.fromSpec ⁻¹' closure {z}) := by
  rw [primeI, Scheme.IdealSheafData.vanishingIdeal_ideal]
  rfl

lemma ideal_primeI_fromSpec {V : X.Opens} (hV : IsAffineOpen V) (y : Spec Γ(X, V)) :
    (primeI (hV.fromSpec y)).ideal ⟨V, hV⟩ = y.asIdeal := by
  ext r
  rw [ideal_primeI, PrimeSpectrum.mem_vanishingIdeal]
  constructor
  · intro h
    exact h y (subset_closure (Set.mem_singleton _))
  · intro hr x hx
    have hx' : hV.fromSpec y ⤳ hV.fromSpec x := specializes_iff_mem_closure.mpr hx
    exact (fromSpec_specializes_iff hV y x).mp hx' hr

lemma ideal_primeI_of_notMem {z : X} (V : X.affineOpens) (hz : z ∉ (V : X.Opens)) :
    (primeI z).ideal V = ⊤ := by
  rw [Ideal.eq_top_iff_one, ideal_primeI, PrimeSpectrum.mem_vanishingIdeal]
  intro w hw
  have hw' : z ⤳ V.2.fromSpec w := specializes_iff_mem_closure.mpr hw
  exact absurd (hw'.mem_open (V : X.Opens).isOpen (fromSpec_mem V.2 w)) hz

/-- A codimension-one point is not dense. -/
lemma support_primeI_ne_top {z : X} (hz : coheight z = 1) : (primeI z).support ≠ ⊤ := by
  intro h
  have h1 : ¬ IsMax z := fun hmax => by
    rw [Order.coheight_eq_zero.mpr hmax] at hz; exact zero_ne_one hz
  obtain ⟨η, hη⟩ := not_isMax_iff.mp h1
  have hmem : η ∈ ((primeI z).support : Set X) := by rw [h]; exact Set.mem_univ _
  rw [coe_support_primeI] at hmem
  exact hη.not_ge (show η ≤ z from specializes_iff_mem_closure.mpr hmem)

/-- The UFD hypothesis at a closed point of a chart, transported to `R_m`. -/
lemma ufd_localization {V : X.Opens} (hV : IsAffineOpen V) (m : Ideal Γ(X, V)) [m.IsPrime]
    (hufd : UniqueFactorizationMonoid (X.presheaf.stalk (hV.fromSpec ⟨m, ‹_›⟩)))
    [IsDomain (X.presheaf.stalk (hV.fromSpec ⟨m, ‹_›⟩))] [IsDomain (Localization.AtPrime m)] :
    UniqueFactorizationMonoid (Localization.AtPrime m) := by
  let mm : PrimeSpectrum Γ(X, V) := ⟨m, ‹_›⟩
  let _ : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec mm)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hV.fromSpec mm, fromSpec_mem hV mm⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec mm)) m :=
    hV.isLocalization_stalk' mm (fromSpec_mem hV mm)
  exact (IsLocalization.algEquiv m.primeCompl (X.presheaf.stalk (hV.fromSpec mm))
    (Localization.AtPrime m)).toRingEquiv.toMulEquiv.uniqueFactorizationMonoid hufd

/-- **O6**: a codimension-one point with factorial local rings is locally principal. -/
theorem isLocPrin_primeI [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) {z : X}
    (hz : coheight z = 1) : IsLocPrin (primeI z) := by
  intro V m hm
  by_cases hzV : z ∈ (V : X.Opens)
  · obtain ⟨y, rfl⟩ := exists_fromSpec_eq V.2 hzV
    rw [ideal_primeI_fromSpec V.2 y]
    have : Nonempty (V : X.Opens) := ⟨⟨_, hzV⟩⟩
    have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
    have : y.asIdeal.IsPrime := y.isPrime
    have : m.IsPrime := hm.isPrime
    have hy : y.asIdeal.height = 1 := by rw [← coheight_fromSpec V.2 y]; exact hz
    have : UniqueFactorizationMonoid (Localization.AtPrime m) :=
      ufd_localization V.2 m (hufd _)
    obtain ⟨a, ha, -, s, hs, hdvd⟩ := exists_dvd_of_ufd_localization y.asIdeal hy m
    exact ⟨a, ha, s, hs, fun w hw => Ideal.mem_span_singleton.mpr (hdvd w hw)⟩
  · rw [ideal_primeI_of_notMem V hzV]
    refine ⟨1, Submodule.mem_top, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h),
      fun w _ => ?_⟩
    rw [Ideal.span_singleton_one]; exact Submodule.mem_top

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Form =====
section

/-!
# S4-IntersectB, file Form: intersection numbers of prime-divisor products (O7, part 1)

* `support_finite_of_compact`: a cycle on a quasi-compact scheme has finite support.
* `support_mul_ne_top`, `support_prod_mul_ne_top`: proper supports stay proper under products.
* `inumZ`: `inum` extended by `0`; `inumZ_perm` (B1), `inumZ_cons_top`, `inumZ_mul` (B3),
  `inumZ_pow_mul`, `inumZ_prod_mul`: `(∏ P_z^{f z}) · J · E = Σ f z (P_z · E) + (J · E)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Top

variable {X : Scheme.{u}}

/-- A cycle on a quasi-compact scheme has finite support. -/
lemma support_finite_of_compact [CompactSpace X] (D : AlgebraicCycle X ℤ) :
    (Function.support D).Finite := by
  choose t ht hfin using fun x => D.supportLocallyFiniteWithinDomain' x (Set.mem_univ x)
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover t (fun x _ => ht x)
  refine (s.finite_toSet.biUnion fun x _ => hfin x).subset fun z hz => ?_
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ z))
  exact Set.mem_biUnion hx ⟨hzx, hz⟩

/-- In an irreducible space two proper closed supports do not cover. -/
lemma support_mul_ne_top [IrreducibleSpace X] {I J : X.IdealSheafData}
    (hI : I.support ≠ ⊤) (hJ : J.support ≠ ⊤) : (I * J).support ≠ ⊤ := by
  rw [Scheme.IdealSheafData.support_mul]
  intro h
  have hu : (I.support : Set X) ∪ J.support = Set.univ := by
    rw [← TopologicalSpace.Closeds.coe_sup, h, TopologicalSpace.Closeds.coe_top]
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp
      (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
      _ _ I.support.isClosed J.support.isClosed hu.ge with h2 | h2
  · exact hI (SetLike.coe_injective ((Set.univ_subset_iff.mp h2).trans
      TopologicalSpace.Closeds.coe_top.symm))
  · exact hJ (SetLike.coe_injective ((Set.univ_subset_iff.mp h2).trans
      TopologicalSpace.Closeds.coe_top.symm))

lemma support_pow_mul_ne_top [IrreducibleSpace X] {P J : X.IdealSheafData}
    (hP : P.support ≠ ⊤) (hJ : J.support ≠ ⊤) (m : ℕ) : (P ^ m * J).support ≠ ⊤ := by
  induction m with
  | zero => simpa using hJ
  | succ m ih => rw [pow_succ, _root_.mul_right_comm]; exact support_mul_ne_top ih hP

lemma support_prod_mul_ne_top [IrreducibleSpace X] (P : X → X.IdealSheafData) (f : X → ℕ)
    (s : Finset X) (hP : ∀ z ∈ s, (P z).support ≠ ⊤) {J : X.IdealSheafData}
    (hJ : J.support ≠ ⊤) : ((∏ z ∈ s, P z ^ f z) * J).support ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hJ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, _root_.mul_assoc]
    exact support_pow_mul_ne_top (hP a (Finset.mem_insert_self _ _))
      (ih fun z hz => hP z (Finset.mem_insert_of_mem hz)) (f a)

end Top

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

open Classical in
/-- `inum` extended by `0` to configurations with a dense slot. -/
noncomputable def inumZ (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) : ℤ :=
  if h : ∀ i, (D i).support ≠ ⊤ then (inum A g hdim D h : ℤ) else 0

lemma inumZ_of (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (h : ∀ i, (D i).support ≠ ⊤) :
    inumZ A g hdim D = inum A g hdim D h := by
  rw [inumZ, dif_pos h]

lemma inumZ_of_not (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (h : ¬ ∀ i, (D i).support ≠ ⊤) :
    inumZ A g hdim D = 0 := by
  rw [inumZ, dif_neg h]

/-- B1 for `inumZ`. -/
lemma inumZ_perm (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (σ : Equiv.Perm (Fin g)) :
    inumZ A g hdim (fun i => D (σ i)) = inumZ A g hdim D := by
  by_cases h : ∀ i, (D i).support ≠ ⊤
  · rw [inumZ_of A g hdim D h, inumZ_of A g hdim _ (fun i => h (σ i)), inum_perm]
  · rw [inumZ_of_not A g hdim D h, inumZ_of_not A g hdim]
    exact fun h' => h fun i => by simpa using h' (σ.symm i)

lemma len_top : len A (⊤ : A.left.IdealSheafData) = 0 := by
  obtain ⟨V, -⟩ := exists_affine_mem A ∅
  letI := (algV A V).hom.toAlgebra
  obtain ⟨-, e⟩ := len_eq_finrank A ⊤ V (by simp) (by simp)
  rw [e]
  have : Subsingleton (Γ(A.left, V) ⧸ (⊤ : A.left.IdealSheafData).ideal V) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton

lemma inumZ_cons_top (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    (E : Fin n → A.left.IdealSheafData) :
    inumZ A (n + 1) hdim (Fin.cons ⊤ E : Fin (n + 1) → A.left.IdealSheafData) = 0 := by
  by_cases h : ∀ i, ((Fin.cons ⊤ E : Fin (n + 1) → A.left.IdealSheafData) i).support ≠ ⊤
  · rw [inumZ_of A _ hdim _ h]
    have := isIntegral_Pw A (n + 1)
    have := isProper_Pw A (n + 1)
    obtain ⟨U, hU, hne, hc⟩ := inum_spec A (n + 1) hdim _ h
    obtain ⟨c, hcU⟩ := exists_pt_mem (Pw A (n + 1)) U hU.isLocallyClosed hne
    rw [← (hc c hcU).2, Zid_cons, Scheme.IdealSheafData.comap_top, top_sup_eq, len_top]
    rfl
  · exact inumZ_of_not A _ hdim _ h

lemma cons_support_ne_top {n : ℕ} {X : A.left.IdealSheafData} {E : Fin n → A.left.IdealSheafData}
    (hX : X.support ≠ ⊤) (hE : ∀ j, (E j).support ≠ ⊤) :
    ∀ i, ((Fin.cons X E : Fin (n + 1) → A.left.IdealSheafData) i).support ≠ ⊤ :=
  fun i => Fin.cases (by simpa using hX) (fun j => by simpa using hE j) i

lemma inumZ_cons_of_not (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    {E : Fin n → A.left.IdealSheafData} (hE : ¬ ∀ j, (E j).support ≠ ⊤)
    (X : A.left.IdealSheafData) :
    inumZ A (n + 1) hdim (Fin.cons X E : Fin (n + 1) → A.left.IdealSheafData) = 0 := by
  refine inumZ_of_not A _ hdim _ fun h => hE fun j => ?_
  simpa using h j.succ

/-- B3 for `inumZ`. -/
lemma inumZ_mul (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    {I I' : A.left.IdealSheafData} (E : Fin n → A.left.IdealSheafData)
    (hI : I.support ≠ ⊤) (hI' : I'.support ≠ ⊤) (hloc : IsLocPrin I') :
    inumZ A (n + 1) hdim (Fin.cons (I * I') E : Fin (n + 1) → A.left.IdealSheafData) =
      inumZ A (n + 1) hdim (Fin.cons I E : Fin (n + 1) → A.left.IdealSheafData) +
        inumZ A (n + 1) hdim (Fin.cons I' E : Fin (n + 1) → A.left.IdealSheafData) := by
  by_cases hE : ∀ j, (E j).support ≠ ⊤
  · rw [inumZ_of A _ hdim _ (cons_support_ne_top A (support_mul_ne_top hI hI') hE),
      inumZ_of A _ hdim _ (cons_support_ne_top A hI hE),
      inumZ_of A _ hdim _ (cons_support_ne_top A hI' hE), inum_mul A n hdim I I' E _ _ _ hloc]
    push_cast; rfl
  · rw [inumZ_cons_of_not A n hdim hE, inumZ_cons_of_not A n hdim hE,
      inumZ_cons_of_not A n hdim hE, add_zero]

lemma inumZ_pow_mul (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    {P J : A.left.IdealSheafData} (E : Fin n → A.left.IdealSheafData)
    (hP : P.support ≠ ⊤) (hJ : J.support ≠ ⊤) (hloc : IsLocPrin P) (m : ℕ) :
    inumZ A (n + 1) hdim (Fin.cons (P ^ m * J) E : Fin (n + 1) → A.left.IdealSheafData) =
      m * inumZ A (n + 1) hdim (Fin.cons P E : Fin (n + 1) → A.left.IdealSheafData) +
        inumZ A (n + 1) hdim (Fin.cons J E : Fin (n + 1) → A.left.IdealSheafData) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, _root_.mul_right_comm,
      inumZ_mul A n hdim E (support_pow_mul_ne_top hP hJ m) hP hloc, ih]
    push_cast; ring

/-- Expansion of a product of locally principal factors in slot `0`. -/
lemma inumZ_prod_mul (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    (P : A.left → A.left.IdealSheafData) (f : A.left → ℕ) (E : Fin n → A.left.IdealSheafData)
    (s : Finset A.left) (hP : ∀ z ∈ s, (P z).support ≠ ⊤) (hloc : ∀ z ∈ s, IsLocPrin (P z))
    {J : A.left.IdealSheafData} (hJ : J.support ≠ ⊤) :
    inumZ A (n + 1) hdim
        (Fin.cons ((∏ z ∈ s, P z ^ f z) * J) E : Fin (n + 1) → A.left.IdealSheafData) =
      ∑ z ∈ s, (f z : ℤ) *
          inumZ A (n + 1) hdim (Fin.cons (P z) E : Fin (n + 1) → A.left.IdealSheafData) +
        inumZ A (n + 1) hdim (Fin.cons J E : Fin (n + 1) → A.left.IdealSheafData) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ z ∈ s, (P z).support ≠ ⊤ := fun z hz => hP z (Finset.mem_insert_of_mem hz)
    rw [Finset.prod_insert ha, _root_.mul_assoc,
      inumZ_pow_mul A n hdim E (hP a (Finset.mem_insert_self _ _))
        (support_prod_mul_ne_top P f s hs hJ) (hloc a (Finset.mem_insert_self _ _)),
      ih hs fun z hz => hloc z (Finset.mem_insert_of_mem hz), Finset.sum_insert ha]
    ring

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Form2 =====
section

/-!
# S4-IntersectB, file Form2: the intersection form on all divisors (O7, part 2; L33)

* `multi_expand`: a slot-wise expansion rule expands all `n` slots at once.
* `effI D = ∏ᶠ z, P_z ^ (D z)⁺`; `inumZ_update_effI`: expansion of an effective Weil divisor in
  any slot.
* `iform D = Σ_z (∏ D_i(z_i)) · (P_{z_1} ⋯ P_{z_n})`: additive in each slot (`iform_update_add`),
  symmetric (`iform_perm`), and equal to `inumZ (effI ∘ D)` on effective Weil divisors
  (`iform_eq_inumZ`).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.JacDivisors

section Comb

variable {α β : Type*}

lemma support_prod_subset {n : ℕ} (w : Fin n → α → ℤ) (G : (Fin n → α) → ℤ) :
    Function.support (fun z : Fin n → α => (∏ i, w i (z i)) * G z) ⊆
      Set.pi Set.univ fun i => Function.support (w i) := by
  intro z hz i _
  exact Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul hz) i (Finset.mem_univ i)

lemma finite_support_prod {n : ℕ} (w : Fin n → α → ℤ) (hw : ∀ i, (Function.support (w i)).Finite)
    (G : (Fin n → α) → ℤ) :
    (Function.support (fun z : Fin n → α => (∏ i, w i (z i)) * G z)).Finite :=
  (Set.Finite.pi hw).subset (support_prod_subset w G)

/-- Slot-wise expansion rules expand all slots. -/
theorem multi_expand (p : α → β) : ∀ (n : ℕ) (F : (Fin n → β) → ℤ) (e : Fin n → β)
    (w : Fin n → α → ℤ), (∀ i, (Function.support (w i)).Finite) →
    (∀ (Q : Fin n → β) (i : Fin n),
      F (Function.update Q i (e i)) = ∑ᶠ a, w i a * F (Function.update Q i (p a))) →
    F e = ∑ᶠ z : Fin n → α, (∏ i, w i (z i)) * F (fun i => p (z i))
  | 0, F, e, w, _, _ => by
    rw [finsum_unique]
    obtain rfl : e = fun i => p ((default : Fin 0 → α) i) := funext fun i => i.elim0
    simp
  | n + 1, F, e, w, hw, h => by
    have h0 := h e 0
    rw [Function.update_eq_self] at h0
    rw [h0]
    have hIH : ∀ a, F (Function.update e 0 (p a)) = ∑ᶠ z' : Fin n → α,
        (∏ j, w j.succ (z' j)) * F (Fin.cons (p a) fun j => p (z' j)) := by
      intro a
      have he : Function.update e 0 (p a) = Fin.cons (p a) (Fin.tail e) := by
        rw [← Fin.update_cons_zero (e 0) (Fin.tail e) (p a), Fin.cons_self_tail]
      rw [he]
      refine multi_expand p n (fun Q => F (Fin.cons (p a) Q)) (Fin.tail e) (fun j => w j.succ)
        (fun j => hw j.succ) fun Q j => ?_
      simp only [Fin.cons_update]
      exact h _ j.succ
    simp_rw [hIH]
    have hfin := finite_support_prod w hw (fun z => F fun i => p (z i))
    rw [← finsum_comp_equiv (Fin.consEquiv fun _ => α)] at *
    rw [finsum_curry _ (by
      refine (hfin.preimage (Fin.consEquiv fun _ => α).injective.injOn).subset fun x hx => ?_
      exact hx)]
    refine finsum_congr fun a => ?_
    rw [mul_finsum]
    refine finsum_congr fun z' => ?_
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [_root_.mul_assoc]
    congr 3
    funext i
    refine Fin.cases rfl (fun j => rfl) i

lemma update_swap {n : ℕ} (P : Fin (n + 1) → β) (i : Fin (n + 1)) (Y : β) :
    (fun j => Function.update P i Y (Equiv.swap 0 i j)) =
      (Fin.cons Y fun j => P (Equiv.swap 0 i j.succ) : Fin (n + 1) → β) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · rw [Fin.cons_succ, Function.update_of_ne]
    rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
    exact Fin.succ_ne_zero j

lemma prod_update_apply {n : ℕ} (D : Fin n → α → ℤ) (i : Fin n) (Y : α → ℤ) (z : Fin n → α) :
    ∏ j, Function.update D i Y j (z j) = Y (z i) * ∏ j ∈ Finset.univ.erase i, D j (z j) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

end Comb

section Eff

variable {X : Scheme.{u}}

/-- The effective ideal sheaf `∏ P_z ^ (D z)⁺` of a cycle. -/
noncomputable def effI (D : AlgebraicCycle X ℤ) : X.IdealSheafData :=
  ∏ᶠ z, primeI z ^ (D z).toNat

lemma effI_eq_prod (D : AlgebraicCycle X ℤ) (s : Finset X) (hs : Function.support D ⊆ s) :
    effI D = ∏ z ∈ s, primeI z ^ (D z).toNat := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun z hz => hs fun h => hz ?_
  simp [h]

end Eff

section Iform

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- Expansion of an effective Weil divisor in slot `0`. -/
theorem inumZ_cons_effI (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ)) (D : AlgebraicCycle A.left ℤ)
    (hW : D ∈ weilDivisors A.left) (hD : ∀ z, 0 ≤ D z) (E : Fin n → A.left.IdealSheafData) :
    inumZ A (n + 1) hdim (Fin.cons (effI D) E : Fin (n + 1) → A.left.IdealSheafData) =
      ∑ᶠ z, D z *
        inumZ A (n + 1) hdim (Fin.cons (primeI z) E : Fin (n + 1) → A.left.IdealSheafData) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hfin := support_finite_of_compact D
  have hs : Function.support D ⊆ hfin.toFinset := fun z hz => hfin.mem_toFinset.mpr hz
  have h1 : ∀ z ∈ hfin.toFinset, Order.coheight z = 1 := fun z hz =>
    hW z (hfin.mem_toFinset.mp hz)
  have htop : (⊤ : A.left.IdealSheafData).support ≠ ⊤ := by
    intro h
    obtain ⟨x⟩ : Nonempty A.left := inferInstance
    have hx : x ∈ ((⊤ : A.left.IdealSheafData).support : Set A.left) := by
      rw [h]; exact Set.mem_univ _
    simp [Scheme.IdealSheafData.support_top] at hx
  rw [effI_eq_prod D _ hs, ← _root_.mul_one (∏ z ∈ hfin.toFinset, primeI z ^ (D z).toNat),
    Scheme.IdealSheafData.one_eq_top,
    inumZ_prod_mul A n hdim primeI (fun z => (D z).toNat) E _
      (fun z hz => support_primeI_ne_top (h1 z hz)) (fun z hz => isLocPrin_primeI hufd (h1 z hz))
      htop, inumZ_cons_top, add_zero,
    finsum_eq_sum_of_support_subset _ (fun z hz => hs (left_ne_zero_of_mul hz))]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Int.toNat_of_nonneg (hD z)]

/-- Expansion of an effective Weil divisor in any slot. -/
theorem inumZ_update_effI
    (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    (P : Fin (n + 1) → A.left.IdealSheafData) (i : Fin (n + 1)) (D : AlgebraicCycle A.left ℤ)
    (hW : D ∈ weilDivisors A.left) (hD : ∀ z, 0 ≤ D z) :
    inumZ A (n + 1) hdim (Function.update P i (effI D)) =
      ∑ᶠ z, D z * inumZ A (n + 1) hdim (Function.update P i (primeI z)) := by
  rw [← inumZ_perm A _ hdim _ (Equiv.swap 0 i), update_swap,
    inumZ_cons_effI A hufd n hdim D hW hD]
  refine finsum_congr fun z => ?_
  rw [← inumZ_perm A _ hdim (Function.update P i (primeI z)) (Equiv.swap 0 i), update_swap]

/-- **L33**: the intersection form on all cycles, the multilinear extension of `inumZ` on prime
divisors. -/
noncomputable def iform (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ n)
    (D : Fin n → AlgebraicCycle A.left ℤ) : ℤ :=
  ∑ᶠ z : Fin n → A.left, (∏ i, D i (z i)) * inumZ A n hdim (fun i => primeI (z i))

/-- On effective Weil divisors `iform` is the intersection number of the effective ideals. -/
theorem iform_eq_inumZ (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ n) (D : Fin n → AlgebraicCycle A.left ℤ)
    (hW : ∀ i, D i ∈ weilDivisors A.left) (hD : ∀ i z, 0 ≤ D i z) :
    iform A n hdim D = inumZ A n hdim (fun i => effI (D i)) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  refine (multi_expand primeI n (inumZ A n hdim) (fun i => effI (D i)) (fun i z => D i z)
    (fun i => support_finite_of_compact (D i)) fun Q i => ?_).symm
  cases n with
  | zero => exact i.elim0
  | succ m => exact inumZ_update_effI A hufd m hdim Q i (D i) (hW i) (hD i)

/-- **L33**: additivity in each slot. -/
theorem iform_update_add (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ n)
    (D : Fin n → AlgebraicCycle A.left ℤ) (i : Fin n) (D₁ D₂ : AlgebraicCycle A.left ℤ) :
    iform A n hdim (Function.update D i (D₁ + D₂)) =
      iform A n hdim (Function.update D i D₁) + iform A n hdim (Function.update D i D₂) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have e : ∀ z : Fin n → A.left,
      (∏ j, Function.update D i (D₁ + D₂) j (z j)) * inumZ A n hdim (fun j => primeI (z j)) =
        (∏ j, Function.update D i D₁ j (z j)) * inumZ A n hdim (fun j => primeI (z j)) +
          (∏ j, Function.update D i D₂ j (z j)) * inumZ A n hdim (fun j => primeI (z j)) := by
    intro z
    have h : ∀ Y : AlgebraicCycle A.left ℤ, ∏ j, Function.update D i Y j (z j) =
        Y (z i) * ∏ j ∈ Finset.univ.erase i, D j (z j) := fun Y => by
      rw [← prod_update_apply (fun j => ⇑(D j)) i (⇑Y) z]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    rw [h, h, h, Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    ring
  simp only [iform]
  rw [finsum_congr e]
  exact finsum_add_distrib
    (finite_support_prod _ (fun j => support_finite_of_compact (Function.update D i D₁ j)) _)
    (finite_support_prod _ (fun j => support_finite_of_compact (Function.update D i D₂ j)) _)

/-- **L33**: symmetry. -/
theorem iform_perm (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ n)
    (D : Fin n → AlgebraicCycle A.left ℤ) (σ : Equiv.Perm (Fin n)) :
    iform A n hdim (fun i => D (σ i)) = iform A n hdim D := by
  simp only [iform]
  let e : (Fin n → A.left) ≃ (Fin n → A.left) :=
    { toFun := fun z i => z (σ i), invFun := fun z i => z (σ.symm i),
      left_inv := fun z => by funext i; simp, right_inv := fun z => by funext i; simp }
  rw [← finsum_comp_equiv e]
  refine finsum_congr fun z => ?_
  show (∏ i, D (σ i) (z (σ i))) * inumZ A n hdim (fun i => primeI (z (σ i))) = _
  congr 1
  · exact Equiv.prod_comp σ (fun i => D i (z i))
  · exact inumZ_perm A n hdim (fun i => primeI (z i)) σ

end Iform

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Pen3 =====
section

/-!
# S4-IntersectB, O9 part 3: the Weil bridge for the pencil of a rational function

* `ideal_res_span`: a principal component of an ideal sheaf stays principal on a smaller affine.
* `ideal_prod_pow`: components of finite products of powers of ideal sheaves.
* `exists_chart_gens`: finitely many codimension-one prime ideal sheaves are principal on one
  affine chart around any point (factorial local rings).
* `ord_chart_gen`: such a generator has order one along its own prime divisor and order zero at
  the other codimension-one points of the chart.
* `effGen`: near every point, `effI D` is generated by one section whose order at every
  codimension-one point of the chart is the positive part of `D`.
* `exists_bridge`: near every point, the zero and pole ideal sheaves `effI (div f)` and
  `effI (-div f)` are generated by sections `u`, `v` of one affine chart with `u = f * v` in the
  function field.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology Order IsLocalRing

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.JacDivisors

variable {X : Scheme.{u}}

/-- A principal component restricts to a principal component on a smaller affine open. -/
lemma ideal_res_span (I : X.IdealSheafData) {U V : X.affineOpens} (h : U ≤ V) {a : Γ(X, V)}
    (ha : I.ideal V = Ideal.span {a}) :
    I.ideal U = Ideal.span {X.presheaf.map (homOfLE h).op a} := by
  rw [← I.map_ideal h, ha, Ideal.map_span, Set.image_singleton]

lemma ideal_prod_pow (s : Finset X) (P : X → X.IdealSheafData) (n : X → ℕ) (W : X.affineOpens) :
    (∏ z ∈ s, P z ^ n z).ideal W = ∏ z ∈ s, (P z).ideal W ^ n z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top]
    rfl
  | insert z s hz ih =>
    rw [Finset.prod_insert hz, Finset.prod_insert hz, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
      Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, ih]

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The prime ideal sheaves of finitely many codimension-one points are principal on one affine
chart around `x`. -/
lemma exists_chart_gens (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (s : Finset X) (hs : ∀ z ∈ s, coheight z = 1) (x : X) :
    ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧ ∃ a : X → Γ(X, W),
      ∀ z ∈ s, (primeI z).ideal W = Ideal.span {a z} := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨y, rfl⟩ := exists_fromSpec_eq hV hxV
  obtain ⟨m, hm, hym⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
  have key : ∀ z : X, ∃ v t : Γ(X, V), t ∉ m ∧ (z ∈ s → v ∈ (primeI z).ideal ⟨V, hV⟩ ∧
      ∀ w ∈ (primeI z).ideal ⟨V, hV⟩, t * w ∈ Ideal.span {v}) := by
    intro z
    by_cases hz : z ∈ s
    · obtain ⟨v, hv, t, ht, h⟩ := isLocPrin_primeI hufd (hs z hz) ⟨V, hV⟩ m hm
      exact ⟨v, t, ht, fun _ => ⟨hv, h⟩⟩
    · exact ⟨1, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h), fun h => absurd h hz⟩
  choose v t ht hv using key
  have : m.IsPrime := hm.isPrime
  have hT : (∏ z ∈ s, t z) ∉ m := by
    intro h
    obtain ⟨z, -, hz⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact ht z hz
  obtain ⟨W, hW⟩ : ∃ W : X.affineOpens,
      W = X.affineBasicOpen (U := ⟨V, hV⟩) (∏ z ∈ s, t z) := ⟨_, rfl⟩
  have hWV : (W : X.Opens) ≤ V := by rw [hW]; exact X.basicOpen_le _
  have h1 : IsUnit ((X.presheaf.map (homOfLE hWV).op).hom (∏ z ∈ s, t z)) := by
    subst hW; exact X.toRingedSpace.isUnit_res_basicOpen _
  refine ⟨W, ?_, fun z => (X.presheaf.map (homOfLE hWV).op).hom (v z), fun z hz => ?_⟩
  · rw [hW]; exact (fromSpec_mem_basicOpen_iff hV _ y).mpr fun h => hT (hym h)
  · set ρ := (X.presheaf.map (homOfLE hWV).op).hom with hρ
    have hu : IsUnit (ρ (t z)) := by
      have h2 := map_mul ρ (t z) (∏ w ∈ s.erase z, t w)
      rw [Finset.mul_prod_erase s t hz] at h2
      rw [h2] at h1
      exact isUnit_of_mul_isUnit_left h1
    rw [← (primeI z).map_ideal (U := W) (V := ⟨V, hV⟩) hWV]
    apply le_antisymm
    · refine Ideal.map_le_of_le_comap fun w hw => ?_
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((hv z hz).2 w hw)
      refine Ideal.mem_span_singleton'.mpr ⟨↑hu.unit⁻¹ * ρ c, ?_⟩
      have e : ρ c * ρ (v z) = ρ (t z) * ρ w := by rw [← map_mul, ← map_mul, hc]
      rw [mul_assoc, e, ← mul_assoc, hu.val_inv_mul, one_mul]
      exact rfl
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_map_of_mem _ (hv z hz).1))

open Classical in
/-- A chart generator of a codimension-one prime has order one along it and order zero at the
other codimension-one points of the chart. -/
lemma ord_chart_gen {W : X.affineOpens} [Nonempty (W : X.Opens)] {z : X} (hz : coheight z = 1)
    {a : Γ(X, W)} (ha : (primeI z).ideal W = Ideal.span {a}) :
    a ≠ 0 ∧ ∀ w ∈ (W : X.Opens), coheight w = 1 →
      Scheme.ord (X.germToFunctionField W a) w = if w = z then 1 else 0 := by
  by_cases hzW : z ∈ (W : X.Opens)
  · obtain ⟨y, rfl⟩ := exists_fromSpec_eq W.2 hzW
    have hy : y.asIdeal = Ideal.span {a} := (ideal_primeI_fromSpec W.2 y).symm.trans ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      have h1 : ¬ IsMax (W.2.fromSpec y) := fun hmax => by
        rw [Order.coheight_eq_zero.mpr hmax] at hz; exact zero_ne_one hz
      obtain ⟨η, hη⟩ := not_isMax_iff.mp h1
      have hηW : η ∈ (W : X.Opens) :=
        (show η ⤳ W.2.fromSpec y from hη.le).mem_open W.1.isOpen hzW
      obtain ⟨y'', rfl⟩ := exists_fromSpec_eq W.2 hηW
      have hbot : y.asIdeal = ⊥ := by rw [hy]; exact Ideal.span_singleton_eq_bot.mpr rfl
      have : y'' = y := PrimeSpectrum.ext (le_antisymm
        ((fromSpec_specializes_iff W.2 y'' y).mp hη.le) (by rw [hbot]; exact bot_le))
      exact hη.ne (by rw [this])
    refine ⟨ha0, fun w hw hw1 => ?_⟩
    by_cases hwz : w = W.2.fromSpec y
    · subst hwz
      rw [if_pos rfl]
      refine ord_germ_eq_one hw hz ha0 ?_
      rw [maximalIdeal_stalk_fromSpec W.2 y, hy, Ideal.map_span, Set.image_singleton]
    · rw [if_neg hwz]
      obtain ⟨y', rfl⟩ := exists_fromSpec_eq W.2 hw
      refine ord_germ_eq_zero a ((fromSpec_mem_basicOpen_iff W.2 a y').mpr fun hay => ?_)
      have hsp : W.2.fromSpec y ⤳ W.2.fromSpec y' := (fromSpec_specializes_iff W.2 y y').mpr
        (by rw [hy]; exact (Ideal.span_singleton_le_iff_mem _).mpr hay)
      have hle : W.2.fromSpec y' ≤ W.2.fromSpec y := hsp
      have hlt : W.2.fromSpec y' < W.2.fromSpec y :=
        lt_of_le_not_ge hle fun hge => hwz (Specializes.antisymm hsp hge).eq.symm
      have := coheight_strictAnti hlt (by simp [hz])
      rw [hz, hw1] at this
      exact lt_irrefl _ this
  · have htop : Ideal.span {a} = ⊤ := by rw [← ha]; exact ideal_primeI_of_notMem W hzW
    have hunit : IsUnit a := Ideal.span_singleton_eq_top.mp htop
    refine ⟨hunit.ne_zero, fun w hw _ => ?_⟩
    rw [if_neg (fun h : w = z => hzW (h ▸ hw))]
    exact ord_germ_eq_zero a (by rw [X.basicOpen_of_isUnit hunit]; exact hw)

/-- **Local generators of `effI D`** with the expected orders. -/
theorem effGen (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {D : AlgebraicCycle X ℤ} (hD : D ∈ weilDivisors X) (hfin : (Function.support D).Finite)
    (x : X) :
    ∃ W : X.affineOpens, ∃ hxW : x ∈ (W : X.Opens), ∃ u : Γ(X, W), u ≠ 0 ∧
      (effI D).ideal W = Ideal.span {u} ∧ ∀ w ∈ (W : X.Opens), coheight w = 1 →
        Scheme.ord (algebraMap _ X.functionField (X.presheaf.germ W x hxW u)) w = (D w).toNat := by
  classical
  have hs : ∀ z ∈ hfin.toFinset, coheight z = 1 :=
    fun z hz => hD z ((Set.Finite.mem_toFinset hfin).mp hz)
  obtain ⟨W, hxW, a, ha⟩ := exists_chart_gens hufd hfin.toFinset hs x
  have : Nonempty (W : X.Opens) := ⟨⟨x, hxW⟩⟩
  have hA := fun z (hz : z ∈ hfin.toFinset) => ord_chart_gen (hs z hz) (ha z hz)
  refine ⟨W, hxW, ∏ z ∈ hfin.toFinset, a z ^ (D z).toNat, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun z hz => pow_ne_zero _ (hA z hz).1
  · have e : ∀ z ∈ hfin.toFinset, (primeI z).ideal W ^ (D z).toNat =
        Ideal.span {a z ^ (D z).toNat} := fun z hz => by rw [ha z hz, Ideal.span_singleton_pow]
    rw [effI_eq_prod D hfin.toFinset (Set.Finite.coe_toFinset hfin).ge,
      ideal_prod_pow hfin.toFinset primeI (fun z => (D z).toNat) W, Finset.prod_congr rfl e,
      Ideal.prod_span_singleton]
  · intro w hw hw1
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, map_prod]
    have e : ∀ z ∈ hfin.toFinset, X.germToFunctionField W (a z ^ (D z).toNat) =
        X.germToFunctionField W (a z) ^ (((D z).toNat : ℕ) : ℤ) := fun z _ => by
      rw [map_pow, zpow_natCast]
    rw [Finset.prod_congr rfl e, ord_prod_zpow hfin.toFinset _ _
      (fun z hz => germToFunctionField_ne_zero (hA z hz).1) w,
      Finset.sum_congr rfl (fun z hz => congrArg (fun t => (((D z).toNat : ℕ) : ℤ) * t)
        ((hA z hz).2 w hw hw1))]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · have : D w = 0 := by simpa using h
      simp [this]

/-- **Weil bridge**: near every point the zero and pole ideal sheaves of `f` are generated by
sections `u`, `v` of one affine chart with `u = f * v` in the function field. -/
theorem exists_bridge (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {f : X.functionField} (hf : f ≠ 0) (hfin : (Function.support (div X f)).Finite) (x : X) :
    ∃ W : X.affineOpens, ∃ hxW : x ∈ (W : X.Opens), ∃ u v : Γ(X, W),
      (effI (div X f)).ideal W = Ideal.span {u} ∧ (effI (-div X f)).ideal W = Ideal.span {v} ∧
      algebraMap _ X.functionField (X.presheaf.germ W x hxW u) =
        f * algebraMap _ X.functionField (X.presheaf.germ W x hxW v) := by
  have hD := div_mem_weilDivisors f
  have hfin' : (Function.support (-div X f)).Finite := by
    convert hfin using 1; ext z; simp
  obtain ⟨W1, hx1, u1, hu1, hI1, ho1⟩ := effGen hufd hD hfin x
  obtain ⟨W2, hx2, v2, hv2, hI2, ho2⟩ := effGen hufd (neg_mem hD) hfin' x
  have hgu : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W1 x hx1 u1) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (germ_ne_zero hx1 hu1)
  have hgv : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W2 x hx2 v2) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (germ_ne_zero hx2 hv2)
  have := hufd x
  obtain ⟨e0, he0, he0'⟩ := exists_isUnit_of_ord_eq_zero x
    (div_ne_zero (mul_ne_zero hf hgv) hgu) fun z hzx hz1 => by
      rw [div_eq_mul_inv, Scheme.ord_mul (mul_ne_zero hf hgv) (inv_ne_zero hgu),
        Scheme.ord_mul hf hgv, ord_inv' hgu, ho1 z (hzx.mem_open W1.1.isOpen hx1) hz1,
        ho2 z (hzx.mem_open W2.1.isOpen hx2) hz1]
      have hneg : (-div X f) z = -(div X f z) := by simp
      rw [hneg, show Scheme.ord f z = div X f z from rfl]
      generalize div X f z = n
      omega
  obtain ⟨U, hxU, e, he⟩ := X.presheaf.exists_germ_eq e0
  have hxe : x ∈ X.basicOpen e := (X.mem_basicOpen e x hxU).mpr (by rw [he]; exact he0)
  obtain ⟨r, hr2, hxr⟩ := W1.2.exists_basicOpen_le (V := W2) ⟨x, hx2⟩ hx1
  obtain ⟨r', hr', hxr'⟩ := (X.affineBasicOpen r).2.exists_basicOpen_le ⟨x, hxe⟩ hxr
  obtain ⟨W, hW⟩ : ∃ W : X.affineOpens, W = X.affineBasicOpen r' := ⟨_, rfl⟩
  have hxW : x ∈ (W : X.Opens) := by rw [hW]; exact hxr'
  have hW1 : (W : X.Opens) ≤ W1 := by rw [hW]; exact (X.basicOpen_le r').trans (X.basicOpen_le r)
  have hW2 : (W : X.Opens) ≤ W2 := by rw [hW]; exact (X.basicOpen_le r').trans hr2
  have hWe : (W : X.Opens) ≤ X.basicOpen e := by rw [hW]; exact hr'
  have he' : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le e)).op e) :=
    X.toRingedSpace.isUnit_res_basicOpen e
  have hu : IsUnit (X.presheaf.map (homOfLE hWe).op
      (X.presheaf.map (homOfLE (X.basicOpen_le e)).op e)) :=
    he'.map (ConcreteCategory.hom (X.presheaf.map (homOfLE hWe).op))
  refine ⟨W, hxW,
    X.presheaf.map (homOfLE hWe).op (X.presheaf.map (homOfLE (X.basicOpen_le e)).op e) *
      X.presheaf.map (homOfLE hW1).op u1, X.presheaf.map (homOfLE hW2).op v2, ?_, ?_, ?_⟩
  · rw [Ideal.span_singleton_mul_left_unit hu]
    exact ideal_res_span (U := W) _ hW1 hI1
  · exact ideal_res_span (U := W) _ hW2 hI2
  · simp only [map_mul, TopCat.Presheaf.germ_res_apply]
    rw [he, he0']
    exact div_mul_cancel₀ _ hgu

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Pen1 =====
section

/-!
# S4-IntersectB, O9 part 1: fibres of the pencil family over the affine line

`π : X ⟶ S`, a closed subscheme `C` of `X`, an open `O ⊆ X` and `g ∈ Γ(X, O)`. The graph of `g` on
`C ∩ O` is `gam : C ∩ O ⟶ 𝔸¹_X`; its scheme-theoretic image maps to `𝔸¹_S` by `famL`. For a
section `l` of `S`, `isPullback_fibre` identifies the fibre of `famL` over the `l`-point of `𝔸¹_S`
with a closed subscheme `J ⊇ C` of `X`, given that `g = l` on `J` and that, on an affine cover,
`J` is cut out by `C` and one element `h` with `a (g - l) = h` on `C ∩ O`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace RamanujanPetersson.IntersectB

/-- The affine line over `X`. -/
noncomputable abbrev Ln (X : Scheme.{u}) : Scheme.{u} := 𝔸(PUnit.{u+1}; X)

/-- The projection of the affine line. -/
noncomputable abbrev prL (X : Scheme.{u}) : Ln X ⟶ X := 𝔸(PUnit.{u+1}; X) ↘ X

lemma appLE_congr_hom {X Y : Scheme.{u}} {f f' : X ⟶ Y} (hf : f = f') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = f'.appLE U V (hf ▸ e) := by
  subst hf; rfl

/-- Pulling back an element of an ideal sheaf lands in the pulled back ideal sheaf. -/
lemma appLE_mem_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (U : Y.affineOpens)
    (W : X.affineOpens) (e : W.1 ≤ f ⁻¹ᵁ U.1) {r : Γ(Y, U)} (hr : r ∈ I.ideal U) :
    f.appLE U W e r ∈ (I.comap f).ideal W := by
  have hr' : I.subschemeι.app U r = 0 := by
    rw [← RingHom.mem_ker, ← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
    exact hr
  rw [Scheme.IdealSheafData.comap, Scheme.Hom.ker_apply, RingHom.mem_ker,
    Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom pullback.condition, Scheme.Hom.comp_appLE, CommRingCat.comp_apply, hr',
    map_zero]

lemma comap_self_eq_bot {X : Scheme.{u}} (C : X.IdealSheafData) :
    C.comap C.subschemeι = ⊥ :=
  Scheme.Hom.ker_eq_bot_of_isIso (pullback.fst C.subschemeι C.subschemeι)

section Line
variable {X S : Scheme.{u}} (π : X ⟶ S)

/-- The `l`-point of the affine line over `S`. -/
noncomputable def ptL (l : Γ(S, ⊤)) : S ⟶ Ln S := AffineSpace.homOfVector (𝟙 S) fun _ => l

/-- The `l`-section of the affine line over `X`. -/
noncomputable def secL (l : Γ(S, ⊤)) : X ⟶ Ln X :=
  AffineSpace.homOfVector (𝟙 X) fun _ => π.appTop l

@[reassoc (attr := simp)]
lemma secL_prL (l : Γ(S, ⊤)) : secL π l ≫ prL X = 𝟙 X := AffineSpace.homOfVector_over _ _

@[reassoc (attr := simp)]
lemma ptL_prL (l : Γ(S, ⊤)) : ptL l ≫ prL S = 𝟙 S := AffineSpace.homOfVector_over _ _

lemma isPullback_secL (l : Γ(S, ⊤)) :
    IsPullback (secL π l) π (AffineSpace.map PUnit.{u+1} π) (ptL l) := by
  refine IsPullback.of_right ?_ ?_ (AffineSpace.isPullback_map (n := PUnit.{u+1}) π).flip
  · rw [secL_prL, ptL_prL]
    exact IsPullback.id_horiz π
  · refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro i
      change (AffineSpace.homOfVector (𝟙 X) _).appTop
          ((AffineSpace.map PUnit.{u+1} π).appTop (AffineSpace.coord S i)) =
        π.appTop ((AffineSpace.homOfVector (𝟙 S) _).appTop (AffineSpace.coord S i))
      rw [AffineSpace.map_appTop_coord, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_appTop_coord]

end Line

section Graph
variable {X S : Scheme.{u}} (π : X ⟶ S) (C : X.IdealSheafData) (O : X.Opens)

/-- The open part `C ∩ O` of the closed subscheme `C`. -/
noncomputable abbrev COo : C.subscheme.Opens := C.subschemeι ⁻¹ᵁ O

/-- Its inclusion into `X`. -/
noncomputable def ιCO : (COo C O).toScheme ⟶ X := (COo C O).ι ≫ C.subschemeι

lemma le_ιCO_preimage : (⊤ : (COo C O).toScheme.Opens) ≤ ιCO C O ⁻¹ᵁ O := by
  rintro ⟨x, hx⟩ -
  exact hx

/-- `g` restricted to `C ∩ O`. -/
noncomputable def gCO (g : Γ(X, O)) : Γ((COo C O).toScheme, ⊤) :=
  (ιCO C O).appLE O ⊤ (le_ιCO_preimage C O) g

/-- The graph of `g` on `C ∩ O`, a morphism to the affine line over `X`. -/
noncomputable def gam (g : Γ(X, O)) : (COo C O).toScheme ⟶ Ln X :=
  AffineSpace.homOfVector (ιCO C O) fun _ => gCO C O g

@[reassoc (attr := simp)]
lemma gam_prL (g : Γ(X, O)) : gam C O g ≫ prL X = ιCO C O := AffineSpace.homOfVector_over _ _

/-- The pencil family: the closure of the graph, over the affine line of `S`. -/
noncomputable def famL (g : Γ(X, O)) : (gam C O g).image ⟶ Ln S :=
  (gam C O g).imageι ≫ AffineSpace.map PUnit.{u+1} π

lemma comap_prL_le_ker (g : Γ(X, O)) : C.comap (prL X) ≤ (gam C O g).ker := by
  rw [← Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.le_map_iff_comap_le,
    ← Scheme.IdealSheafData.comap_comp, gam_prL, ιCO, Scheme.IdealSheafData.comap_comp,
    comap_self_eq_bot, ← Scheme.IdealSheafData.le_map_iff_comap_le]
  exact bot_le

/-- The element `a (t - l) - h` of the affine line over `W` vanishes on the graph. -/
lemma mem_ker_gam (g : Γ(X, O)) [QuasiCompact (gam C O g)] (l : Γ(S, ⊤)) (W : X.affineOpens)
    (a h : Γ(X, W))
    (hid : (ιCO C O).app W a * (COo C O).toScheme.presheaf.map (homOfLE le_top).op
      (gCO C O g - (ιCO C O ≫ π).appTop l) = (ιCO C O).app W h) :
    (prL X).app W a * (Ln X).presheaf.map (homOfLE le_top).op
      (AffineSpace.coord X PUnit.unit - (prL X ≫ π).appTop l) - (prL X).app W h ∈
      (gam C O g).ker.ideal ⟨prL X ⁻¹ᵁ W.1, W.2.preimage _⟩ := by
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  have e1 : ∀ r : Γ(X, W), (gam C O g).app (prL X ⁻¹ᵁ W.1) ((prL X).app W r) =
      (ιCO C O).appLE W _ (le_of_eq (by rw [← Scheme.Hom.comp_preimage, gam_prL])) r := by
    intro r
    rw [Scheme.Hom.app_eq_appLE (gam C O g), ← CommRingCat.comp_apply,
      Scheme.Hom.app_eq_appLE (prL X), Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (gam_prL C O g)]
  have hV : (gam C O g) ⁻¹ᵁ (prL X ⁻¹ᵁ W.1) ≤ ιCO C O ⁻¹ᵁ W.1 :=
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, gam_prL])
  have e2 : ∀ x : Γ(Ln X, ⊤), (gam C O g).app (prL X ⁻¹ᵁ W.1)
      ((Ln X).presheaf.map (homOfLE le_top).op x) =
      (COo C O).toScheme.presheaf.map (homOfLE hV).op
        ((COo C O).toScheme.presheaf.map (homOfLE le_top).op ((gam C O g).appTop x)) := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, ← CommRingCat.comp_apply,
      ← Functor.map_comp, CommRingCat.comp_apply]
    rfl
  have e3 : (gam C O g).appTop (AffineSpace.coord X PUnit.unit - (prL X ≫ π).appTop l) =
      gCO C O g - (ιCO C O ≫ π).appTop l := by
    rw [map_sub, gam, AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, ← Category.assoc, AffineSpace.homOfVector_over]
  rw [map_sub, map_mul, e1, e1, e2, e3]
  change (COo C O).toScheme.presheaf.map (homOfLE hV).op ((ιCO C O).app W a) * _ -
    (COo C O).toScheme.presheaf.map (homOfLE hV).op ((ιCO C O).app W h) = 0
  rw [← map_mul, ← map_sub, hid, sub_self, map_zero]

/-- The fibre of the pencil family over the `l`-point of `𝔸¹_S` is the closed subscheme `J`. -/
theorem isPullback_fibre (g : Γ(X, O)) [QuasiCompact (gam C O g)] (l : Γ(S, ⊤))
    (J : X.IdealSheafData) (m : J.subscheme ⟶ (COo C O).toScheme)
    (hm : m ≫ ιCO C O = J.subschemeι)
    (hg : m.appTop (gCO C O g) = (J.subschemeι ≫ π).appTop l)
    (H : ∀ x : X, ∃ W : X.affineOpens, x ∈ W.1 ∧ ∃ a h : Γ(X, W),
      J.ideal W ≤ Ideal.span {h} ⊔ C.ideal W ∧
      (ιCO C O).app W a * (COo C O).toScheme.presheaf.map (homOfLE le_top).op
        (gCO C O g - (ιCO C O ≫ π).appTop l) = (ιCO C O).app W h) :
    IsPullback (m ≫ (gam C O g).toImage) (J.subschemeι ≫ π) (famL π C O g) (ptL l) := by
  have h1 : J.subschemeι ≫ secL π l = (m ≫ (gam C O g).toImage) ≫ (gam C O g).imageι := by
    rw [Category.assoc, Scheme.Hom.toImage_imageι]
    refine AffineSpace.hom_ext ?_ ?_
    · simp only [Category.assoc, secL_prL, gam_prL, hm, Category.comp_id]
    · intro i
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        CommRingCat.comp_apply, secL, gam, AffineSpace.homOfVector_appTop_coord,
        AffineSpace.homOfVector_appTop_coord, hg, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have h2 : (gam C O g).imageι.ker.comap (secL π l) = J.subschemeι.ker := by
    simp only [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
    refine le_antisymm ?_ ?_
    · rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
      conv_rhs => rw [← Scheme.IdealSheafData.ker_subschemeι J]
      rw [Scheme.IdealSheafData.map_ker, h1, Category.assoc, Scheme.Hom.toImage_imageι]
      exact Scheme.Hom.le_ker_comp _ _
    · choose W hxW a h hJ hid using H
      refine Scheme.IdealSheafData.le_of_iSup_eq_top W ?_ fun x => ?_
      · exact top_le_iff.mp fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxW y⟩
      refine (hJ x).trans (sup_le ?_ ?_)
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        have hle : (W x).1 ≤ secL π l ⁻¹ᵁ (prL X ⁻¹ᵁ (W x).1) :=
          le_of_eq (by rw [← Scheme.Hom.comp_preimage, secL_prL] <;> rfl)
        have hE := appLE_mem_comap _ (secL π l) ⟨prL X ⁻¹ᵁ (W x).1, (W x).2.preimage _⟩ (W x) hle
          (mem_ker_gam π C O g l (W x) (a x) (h x) (hid x))
        have eA : ∀ r : Γ(X, (W x).1), (secL π l).appLE _ (W x).1 hle ((prL X).app (W x).1 r) = r := by
          intro r
          rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
            appLE_congr_hom (secL_prL π l)]
          change (X.presheaf.map (homOfLE (le_refl (W x).1)).op) r = r
          first
          | (rw [show (homOfLE (le_refl (W x).1)).op = 𝟙 (Opposite.op (W x).1) from rfl,
              CategoryTheory.Functor.map_id]; rfl)
          | exact congrArg (fun φ => (ConcreteCategory.hom φ) r)
              (X.presheaf.map_id (Opposite.op (W x).1))
        have eM : ∀ y : Γ(Ln X, ⊤), (secL π l).appLE _ (W x).1 hle
            ((Ln X).presheaf.map (homOfLE le_top).op y) =
            X.presheaf.map (homOfLE le_top).op ((secL π l).appTop y) := by
          intro y
          rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
          rfl
        have eT : (secL π l).appTop (AffineSpace.coord X PUnit.unit - (prL X ≫ π).appTop l) = 0 := by
          rw [map_sub, secL, AffineSpace.homOfVector_appTop_coord, ← CommRingCat.comp_apply,
            ← Scheme.Hom.comp_appTop, ← Category.assoc, AffineSpace.homOfVector_over,
            Category.id_comp, sub_self]
        rw [map_sub, map_mul, eA, eA, eM, eT, map_zero, mul_zero, zero_sub] at hE
        exact (neg_mem_iff).mp hE
      · calc C.ideal (W x) ≤ ((C.comap (prL X)).comap (secL π l)).ideal (W x) :=
              le_of_eq (by rw [← Scheme.IdealSheafData.comap_comp, secL_prL,
                Scheme.IdealSheafData.comap_id])
          _ ≤ _ := Scheme.IdealSheafData.le_def.mp
              (Scheme.IdealSheafData.comap_mono (secL π l) (comap_prL_le_ker C O g)) (W x)
  exact (isPullback_of_isClosedImmersion J.subschemeι (gam C O g).imageι
    (m ≫ (gam C O g).toImage) (secL π l) h1 h2).flip.paste_vert (isPullback_secL π l)

end Graph

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_ThetaCube_Pull =====
section

/-!
# S4-ThetaCube, T7a: the ideal sheaf of a pulled-back effective divisor

For `f : C ⟶ Y` between integral locally Noetherian schemes with factorial stalks, `C` quasi-compact and
`f` quasi-compact, and an effective Weil divisor `D` of finite support on `Y` whose support avoids
`f (η_C)`, the ideal sheaf of the pulled-back divisor is the pulled-back ideal sheaf:
`effI (cpull f D) = (effI D).comap f` (`effI_cpull`).
* `gff_res`: the function-field image of a section is unchanged by restriction.
* `exists_span_eq`: two sections with the same orders along the codimension-one points of an open set
  generate the same ideal on an affine neighbourhood of any point.
* `isLocEq_of_chart`, `fpull_gff`: a chart generator of `effI D` is a local equation of `D`, and its pull-back.
* `exists_span_cpull`: near every point of `f⁻¹ U`, `effI (cpull f D)` is generated by the pull-back of a
  chart generator of `effI D` on `U`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.ThetaCube

open AlgebraicGeometry CategoryTheory Order Topology RamanujanPetersson.JacDivisors
  RamanujanPetersson.IntersectB RamanujanPetersson.ThetaSquare

universe u

section Span

variable {X : Scheme.{u}} [IsIntegral X]

lemma gff_res {U V : X.Opens} (h : V ≤ U) [Nonempty V] [Nonempty U] (a : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op a) = X.germToFunctionField U a := by
  obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty V›
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx,
    ← Scheme.algebraMap_germ_eq_germToFunctionField X (h hx), TopCat.Presheaf.germ_res_apply]

variable [IsLocallyNoetherian X]

/-- Two sections with the same orders along the codimension-one points of `W` generate the same
ideal on an affine neighbourhood of any point of `W`. -/
lemma exists_span_eq {W : X.Opens} [Nonempty W] {a b : Γ(X, W)}
    (ha : X.germToFunctionField W a ≠ 0) (hb : X.germToFunctionField W b ≠ 0)
    (hab : ∀ w ∈ W, coheight w = 1 →
      Scheme.ord (X.germToFunctionField W a) w = Scheme.ord (X.germToFunctionField W b) w)
    (x : X) [UniqueFactorizationMonoid (X.presheaf.stalk x)] (hx : x ∈ W) :
    ∃ W' : X.affineOpens, ∃ h : (W' : X.Opens) ≤ W, x ∈ (W' : X.Opens) ∧
      Ideal.span {X.presheaf.map (homOfLE h).op a} = Ideal.span {X.presheaf.map (homOfLE h).op b} := by
  obtain ⟨r, hr, hrA⟩ := exists_isUnit_of_ord_eq_zero x (div_ne_zero ha hb) fun z hz h1 =>
    ord_eq_of_div_eq ha hb (hab z (hz.mem_open W.isOpen hx) h1)
  obtain ⟨V₁, hx₁, s, hs⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V₂, hx₂, t, ht⟩ := X.presheaf.exists_germ_eq (↑hr.unit⁻¹ : X.presheaf.stalk x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((W ⊓ V₁ ⊓ V₂ : X.Opens) : Set X) from ⟨⟨hx, hx₁⟩, hx₂⟩) (W ⊓ V₁ ⊓ V₂).isOpen
  have h0 : V ≤ W := fun y hy => (hVle hy).1.1
  have h1 : V ≤ V₁ := fun y hy => (hVle hy).1.2
  have h2 : V ≤ V₂ := fun y hy => (hVle hy).2
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nonempty V₁ := ⟨⟨x, hx₁⟩⟩
  have : Nonempty V₂ := ⟨⟨x, hx₂⟩⟩
  have es : X.germToFunctionField V (X.presheaf.map (homOfLE h1).op s) = algebraMap _ _ r := by
    rw [gff_res h1 s, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx₁, hs]
  have et : X.germToFunctionField V (X.presheaf.map (homOfLE h2).op t) =
      algebraMap _ _ (↑hr.unit⁻¹ : X.presheaf.stalk x) := by
    rw [gff_res h2 t, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx₂, ht]
  have hu : IsUnit (X.presheaf.map (homOfLE h1).op s) := by
    refine isUnit_iff_exists_inv.mpr ⟨X.presheaf.map (homOfLE h2).op t,
      X.germToFunctionField_injective V ?_⟩
    rw [map_mul, map_one, es, et, ← map_mul, hr.mul_val_inv, map_one]
  have hab' : X.presheaf.map (homOfLE h0).op a =
      X.presheaf.map (homOfLE h1).op s * X.presheaf.map (homOfLE h0).op b := by
    refine X.germToFunctionField_injective V ?_
    rw [map_mul, es, hrA, gff_res h0 a, gff_res h0 b, div_mul_cancel₀ _ hb]
  refine ⟨⟨V, hV⟩, h0, hxV, ?_⟩
  show Ideal.span {X.presheaf.map (homOfLE h0).op a} = Ideal.span {X.presheaf.map (homOfLE h0).op b}
  rw [hab', Ideal.span_singleton_mul_left_unit hu]

/-- A section whose orders on `U` are those of an effective Weil divisor `D` is a local equation of
`D` at every point of `U`. -/
lemma isLocEq_of_chart {D : AlgebraicCycle X ℤ} (hD : D ∈ weilDivisors X) (hD0 : ∀ z, 0 ≤ D z)
    {U : X.Opens} [Nonempty U] {u : Γ(X, U)} (hu : X.germToFunctionField U u ≠ 0)
    (ho : ∀ w ∈ U, coheight w = 1 → Scheme.ord (X.germToFunctionField U u) w = (D w).toNat)
    {y : X} (hy : y ∈ U) : IsLocEq D y (X.germToFunctionField U u) := by
  refine ⟨hu, U, U.isOpen, hy, fun w hw => ?_⟩
  rw [div_apply]
  by_cases h1 : coheight w = 1
  · rw [ho w hw h1, Int.toNat_of_nonneg (hD0 w)]
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one h1]
    by_contra h
    exact h1 (hD w h)

end Span

/-- Restriction commutes with the ring maps of a morphism. -/
lemma map_app_apply {X Y : Scheme.{u}} (g : X ⟶ Y) {U W : Y.Opens} (e : W ≤ U)
    (h : g ⁻¹ᵁ W ≤ g ⁻¹ᵁ U) (s : Γ(Y, U)) :
    X.presheaf.map (homOfLE h).op (g.app U s) = g.app W (Y.presheaf.map (homOfLE e).op s) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, g.naturality]
  rfl

section Pull

variable {C Y : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsIntegral Y] [IsLocallyNoetherian Y]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] (f : C ⟶ Y)

omit [IsLocallyNoetherian C] [IsLocallyNoetherian Y] [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)] in
lemma fpull_gff {U : Y.Opens} {W : C.Opens} (e : W ≤ f ⁻¹ᵁ U) [Nonempty U] [Nonempty W]
    (u : Γ(Y, U)) :
    fpull f (Y.germToFunctionField U u) = C.germToFunctionField W (f.appLE U W e u) := by
  obtain ⟨⟨x, hx⟩⟩ := ‹Nonempty W›
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField Y (show f x ∈ U from e hx), fpull_algebraMap_at,
    Scheme.Hom.germ_stalkMap_apply, ← Scheme.algebraMap_germ_eq_germToFunctionField C hx]
  show _ = algebraMap _ _ (C.presheaf.germ W x hx ((f.app U ≫ C.presheaf.map (homOfLE e).op) u))
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

variable [∀ x : C, UniqueFactorizationMonoid (C.presheaf.stalk x)] [CompactSpace C]

/-- Near every point of `f⁻¹ U`, `effI (cpull f D)` is generated by the pull-back of a chart
generator of `effI D` on `U`. -/
lemma exists_span_cpull {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y) (hD0 : ∀ z, 0 ≤ D z)
    (hA : Avoid f D) {U : Y.Opens} [Nonempty U] {u : Γ(Y, U)} (hu : Y.germToFunctionField U u ≠ 0)
    (ho : ∀ w ∈ U, coheight w = 1 → Scheme.ord (Y.germToFunctionField U u) w = (D w).toNat)
    (x : C) (hx : f x ∈ U) :
    ∃ W : C.affineOpens, ∃ e : (W : C.Opens) ≤ f ⁻¹ᵁ U, x ∈ (W : C.Opens) ∧
      (effI (cpull f D)).ideal W = Ideal.span {f.appLE U W e u} := by
  have hloc := fun y (hy : y ∈ U) => isLocEq_of_chart hD hD0 hu ho hy
  have hE0 : ∀ z, 0 ≤ cpull f D z := fun z => cpull_nonneg f hD hA z fun w _ _ => hD0 w
  have hEW : cpull f D ∈ weilDivisors C := fun z hz => by
    by_contra h1
    exact hz (by rw [cpull_apply f hD hA, Scheme.ord_eq_zero_of_coheight_neq_one h1])
  obtain ⟨W₁, hxW₁, v, hv, hKv, hov⟩ :=
    effGen (fun z => inferInstance) hEW (support_finite_of_compact (cpull f D)) x
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hxW₀, hW₀le⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((W₁.1 ⊓ f ⁻¹ᵁ U : C.Opens) : Set C) from ⟨hxW₁, hx⟩) (W₁.1 ⊓ f ⁻¹ᵁ U).isOpen
  have h1 : W₀ ≤ W₁.1 := fun y hy => (hW₀le hy).1
  have h2 : W₀ ≤ f ⁻¹ᵁ U := fun y hy => (hW₀le hy).2
  have : Nonempty W₀ := ⟨⟨x, hxW₀⟩⟩
  have : Nonempty W₁.1 := ⟨⟨x, hxW₁⟩⟩
  have hga : C.germToFunctionField W₀ (f.appLE U W₀ h2 u) = fpull f (Y.germToFunctionField U u) :=
    (fpull_gff f h2 u).symm
  have hgb : C.germToFunctionField W₀ (C.presheaf.map (homOfLE h1).op v) =
      C.germToFunctionField W₁.1 v := gff_res h1 v
  have hfne : fpull f (Y.germToFunctionField U u) ≠ 0 := by
    obtain ⟨w, hw, hw'⟩ := exists_unit_of_isLocEq f hA (hloc (f x) hx)
    rw [← hw']
    exact fpull_ne_zero f hw
  have hvne : C.germToFunctionField W₁.1 v ≠ 0 := germToFunctionField_ne_zero hv
  obtain ⟨W, hW, hxW, hspan⟩ := exists_span_eq (W := W₀) (a := f.appLE U W₀ h2 u)
    (b := C.presheaf.map (homOfLE h1).op v) (by rw [hga]; exact hfne) (by rw [hgb]; exact hvne)
    (fun w hw hw1 => by
      rw [hga, hgb, ← cpull_eq_of f hD hA (hloc (f w) (h2 hw)),
        ← Scheme.algebraMap_germ_eq_germToFunctionField C hxW₁ v, hov w (h1 hw) hw1,
        Int.toNat_of_nonneg (hE0 w)]) x hxW₀
  have hWW₁ : W ≤ W₁ := Subtype.coe_le_coe.mp (hW.trans h1)
  refine ⟨W, hW.trans h2, hxW, ?_⟩
  rw [ideal_res_span (effI (cpull f D)) hWW₁ hKv]
  have e1 : C.presheaf.map (homOfLE hW).op (f.appLE U W₀ h2 u) = f.appLE U W (hW.trans h2) u := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have e2 : C.presheaf.map (homOfLE hW).op (C.presheaf.map (homOfLE h1).op v) =
      C.presheaf.map (homOfLE (hW.trans h1)).op v := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [← e1, hspan, e2]
  rfl

/-- **T7a**: the ideal sheaf of the pull-back of an effective divisor is the pull-back of its ideal
sheaf. -/
theorem effI_cpull [QuasiCompact f] {D : AlgebraicCycle Y ℤ} (hD : D ∈ weilDivisors Y)
    (hD0 : ∀ z, 0 ≤ D z) (hfin : (Function.support D).Finite) (hA : Avoid f D) :
    effI (cpull f D) = (effI D).comap f := by
  have hufd : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y) := fun y => inferInstance
  choose U hyU u hu hIu hou using fun y : Y => effGen hufd hD hfin y
  have hne : ∀ y, Nonempty ((U y : Y.Opens)) := fun y => ⟨⟨y, hyU y⟩⟩
  have hgu : ∀ y, Y.germToFunctionField (U y) (u y) ≠ 0 := fun y => germToFunctionField_ne_zero (hu y)
  have ho : ∀ y, ∀ w ∈ (U y : Y.Opens), coheight w = 1 →
      Scheme.ord (Y.germToFunctionField (U y) (u y)) w = (D w).toNat := fun y w hw hw1 => by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField Y (hyU y)]
    exact hou y w hw hw1
  apply le_antisymm
  · choose W e hxW hW using fun x : C =>
      exists_span_cpull f hD hD0 hA (hgu (f x)) (ho (f x)) x (hyU (f x))
    refine Scheme.IdealSheafData.le_of_iSup_eq_top W
      (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩) fun x => ?_
    rw [hW x, Ideal.span_le, Set.singleton_subset_iff]
    exact appLE_mem_comap _ f (U (f x)) (W x) (e x) (by rw [hIu]; exact Ideal.subset_span rfl)
  · refine (Scheme.IdealSheafData.map_gc f _ _).mpr ?_
    refine Scheme.IdealSheafData.le_of_iSup_eq_top U
      (eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩) fun y => ?_
    rw [hIu y, Ideal.span_le, Set.singleton_subset_iff]
    show u y ∈ ((effI (cpull f D)).subschemeι ≫ f).ker.ideal (U y)
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    change (effI (cpull f D)).subschemeι.app (f ⁻¹ᵁ (U y : Y.Opens)) (f.app (U y) (u y)) = 0
    refine (effI (cpull f D)).subscheme.IsSheaf.section_ext fun z hz => ?_
    obtain ⟨W, e, hxW, hW⟩ := exists_span_cpull f hD hD0 hA (hgu y) (ho y)
      ((effI (cpull f D)).subschemeι z) hz
    have hmem : f.appLE (U y) W e (u y) ∈ (effI (cpull f D)).ideal W := by
      rw [hW]
      exact Ideal.subset_span rfl
    rw [← (effI (cpull f D)).ker_subschemeι, Scheme.Hom.ker_apply, RingHom.mem_ker] at hmem
    refine ⟨(effI (cpull f D)).subschemeι ⁻¹ᵁ W,
      ((TopologicalSpace.Opens.map (effI (cpull f D)).subschemeι.base).map (homOfLE e)).le, hxW, ?_⟩
    rw [map_zero]
    exact (map_app_apply _ e _ _).trans hmem

end Pull

end RamanujanPetersson.ThetaCube


end

-- ===== S4.Def_RP_IntersectB_Pen2 =====
section

/-!
# S4-IntersectB, O9 part 2: flatness of the pencil family at fibre points

* `flat_of_poly`: a local algebra `B` over `R ≅ K[X]` is flat when `X - l` acts on `B` as a
  non-zero-divisor lying in the maximal ideal.
* `lineEquiv`: `Γ(𝔸¹_S) ≅ Γ(S)[X]` for affine `S`.
* `stalkMap_flat_of_stalk`: flatness of a stalk map from flatness over sections of an affine open.
* `flat_famL`: the pencil family is flat at the image of a point `x` of `C ∩ O` where the germ of
  `g - l` is a non-zero-divisor in the maximal ideal.
* `preimage_subset_range`, `isImmersion_gam`, `isProper_famL`: the remaining inputs of
  `finrank_eq_of_fibres`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace RamanujanPetersson.IntersectB

/-- Flatness over `K[X]` from a non-zero-divisor condition at one point. -/
theorem flat_of_poly {K R B : Type*} [Field K] [CommRing R] [CommRing B] [IsLocalRing B]
    [Algebra R B] (e : K[X] ≃+* R) (l : K)
    (hy : ∀ b : B, algebraMap R B (e (X - C l)) * b = 0 → b = 0)
    (hm : algebraMap R B (e (X - C l)) ∈ IsLocalRing.maximalIdeal B) : Module.Flat R B := by
  have : IsDomain R := MulEquiv.isDomain K[X] e.symm.toMulEquiv
  have : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro b hb
  rw [Submodule.mem_torsion_iff] at hb
  obtain ⟨⟨r, hr⟩, hrb⟩ := hb
  rw [Submodule.mem_bot]
  obtain ⟨p, rfl⟩ := e.surjective r
  have hp : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hr
    exact zero_notMem_nonZeroDivisors hr
  obtain ⟨s, hps, hs⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp l
  set y := algebraMap R B (e (X - C l)) with hy_def
  have hunit : IsUnit (algebraMap R B (e s)) := by
    have hs0 : s.eval l ≠ 0 := fun h => hs (Polynomial.dvd_iff_isRoot.mpr h)
    have h1 : IsUnit (algebraMap R B (e (C (s.eval l)))) :=
      ((Polynomial.isUnit_C.mpr (Ne.isUnit hs0)).map e).map (algebraMap R B)
    obtain ⟨t, ht⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := s) (a := l)
    have hst : s = C (s.eval l) + (X - C l) * t := by rw [← ht]; ring
    have h2 : algebraMap R B (e s) =
        algebraMap R B (e (C (s.eval l))) + y * algebraMap R B (e t) := by
      conv_lhs => rw [hst]
      rw [map_add, map_mul, map_add, map_mul]
    rw [h2]
    by_contra hnu
    have h3 : algebraMap R B (e (C (s.eval l))) + y * algebraMap R B (e t) ∈
        IsLocalRing.maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h4 := sub_mem h3 (Ideal.mul_mem_right (algebraMap R B (e t)) _ hm)
    rw [add_sub_cancel_right] at h4
    exact (IsLocalRing.mem_maximalIdeal _).mp h4 h1
  rw [Submonoid.smul_def, Algebra.smul_def] at hrb
  have hrb2 : algebraMap R B (e p) * b = 0 := hrb
  have hrb' : y ^ (rootMultiplicity l p) * (algebraMap R B (e s) * b) = 0 := by
    rw [hps, map_mul, map_mul, map_pow, map_pow] at hrb2
    rw [← mul_assoc]
    exact hrb2
  have hpow : ∀ n : ℕ, ∀ c : B, y ^ n * c = 0 → c = 0 := by
    intro n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      apply ih
      apply hy
      rw [← mul_assoc, ← pow_succ']
      exact hc
  exact (hunit.mul_right_eq_zero).mp (hpow _ _ hrb')

/-- The ring of functions on the affine line over an affine scheme. -/
noncomputable def lineEquiv (S : Scheme.{u}) [IsAffine S] : Γ(S, ⊤)[X] ≃+* Γ(Ln S, ⊤) :=
  (MvPolynomial.uniqueAlgEquiv Γ(S, ⊤) PUnit.{u+1}).symm.toRingEquiv.trans
    (RingEquiv.ofBijective (MvPolynomial.eval₂Hom ((prL S).appTop).hom (AffineSpace.coord S)) (by
      have h : MvPolynomial.eval₂Hom ((prL S).appTop).hom (AffineSpace.coord S) =
          ((Scheme.ΓSpecIso (.of (MvPolynomial PUnit.{u+1} Γ(S, ⊤)))).inv ≫
            (AffineSpace.isoOfIsAffine PUnit.{u+1} S).hom.appTop).hom := by
        rw [AffineSpace.isoOfIsAffine_hom_appTop, Iso.inv_hom_id_assoc]
        rfl
      haveI : IsIso (AffineSpace.isoOfIsAffine PUnit.{u+1} S).hom.appTop :=
        inferInstanceAs (IsIso ((AffineSpace.isoOfIsAffine PUnit.{u+1} S).hom.app ⊤))
      rw [h]
      exact ConcreteCategory.bijective_of_isIso _))

lemma lineEquiv_apply (S : Scheme.{u}) [IsAffine S] (p : Γ(S, ⊤)[X]) :
    lineEquiv S p = p.eval₂ ((prL S).appTop).hom (AffineSpace.coord S PUnit.unit) := by
  change MvPolynomial.eval₂Hom _ _ ((MvPolynomial.uniqueAlgEquiv _ _).symm p) = _
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_uniqueAlgEquiv_symm]

/-- A stalk map is flat when the stalk is flat over the sections of an affine open below. -/
theorem stalkMap_flat_of_stalk {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : p x ∈ U)
    (h : letI := ((p.stalkMap x).hom.comp (Y.presheaf.germ U (p x) hx).hom).toAlgebra
      Module.Flat Γ(Y, U) (X.presheaf.stalk x)) :
    (p.stalkMap x).hom.Flat := by
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨p x, hx⟩
  have hlt := hU.isLocalization_stalk ⟨p x, hx⟩
  letI : Algebra (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
  letI : Algebra Γ(Y, U) (X.presheaf.stalk x) :=
    ((p.stalkMap x).hom.comp (Y.presheaf.germ U (p x) hx).hom).toAlgebra
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change Module.Flat (Y.presheaf.stalk (p x)) (X.presheaf.stalk x)
  rw [Module.flat_iff_of_isLocalization (Y.presheaf.stalk (p x))
    (hU.primeIdealOf ⟨p x, hx⟩).asIdeal.primeCompl]
  exact h

/-- Points of `p` over a point of the base of a pullback square come from the square. -/
lemma preimage_subset_range {P Z S T : Scheme.{u}} {fst : P ⟶ Z} {snd : P ⟶ S} {p : Z ⟶ T}
    {c : S ⟶ T} (h : IsPullback fst snd p c) (s : S) : p ⁻¹' {c s} ⊆ Set.range fst := by
  intro z hz
  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := c) z s hz
  refine ⟨h.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
  exact hw1

section Graph
variable {X S : Scheme.{u}} (π : X ⟶ S) (C : X.IdealSheafData) (O : X.Opens)

instance isImmersion_gam (g : Γ(X, O)) : IsImmersion (gam C O g) := by
  have : IsImmersion (gam C O g ≫ prL X) := by
    rw [gam_prL, ιCO]
    infer_instance
  exact IsImmersion.of_comp _ (prL X)

instance isProper_famL [IsProper π] (g : Γ(X, O)) : IsProper (famL π C O g) := by
  have : IsProper (AffineSpace.map PUnit.{u+1} π) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (AffineSpace.isPullback_map (n := PUnit.{u+1}) π).flip inferInstance
  unfold famL
  infer_instance

/-- Flatness of the pencil family at the image of `x ∈ C ∩ O`, when the germ of `g - l` at `x`
is a non-zero-divisor in the maximal ideal. -/
theorem flat_famL [IsAffine S] {K : Type u} [Field K] (σ : K ≃+* Γ(S, ⊤)) (g : Γ(X, O))
    [QuasiCompact (gam C O g)] (l : K) (x : (COo C O).toScheme)
    (hy : ∀ b : (COo C O).toScheme.presheaf.stalk x,
      (COo C O).toScheme.presheaf.germ ⊤ x trivial
        (gCO C O g - (ιCO C O ≫ π).appTop (σ l)) * b = 0 → b = 0)
    (hm : (COo C O).toScheme.presheaf.germ ⊤ x trivial
        (gCO C O g - (ιCO C O ≫ π).appTop (σ l)) ∈ IsLocalRing.maximalIdeal _) :
    ((famL π C O g).stalkMap ((gam C O g).toImage x)).hom.Flat := by
  have hq : (gam C O g).toImage ≫ famL π C O g = gam C O g ≫ AffineSpace.map PUnit.{u+1} π := by
    rw [famL, Scheme.Hom.toImage_imageι_assoc]
  let e : K[X] ≃+* Γ(Ln S, ⊤) := (Polynomial.mapEquiv σ).trans (lineEquiv S)
  have he : e (Polynomial.X - Polynomial.C l) =
      AffineSpace.coord S PUnit.unit - (prL S).appTop (σ l) := by
    change lineEquiv S ((Polynomial.X - Polynomial.C l).map (σ : K →+* Γ(S, ⊤))) = _
    rw [lineEquiv_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    rfl
  have hγ : ((gam C O g).toImage ≫ famL π C O g).appTop (e (Polynomial.X - Polynomial.C l)) =
      gCO C O g - (ιCO C O ≫ π).appTop (σ l) := by
    rw [he, map_sub, hq]
    congr 1
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord, gam,
        AffineSpace.homOfVector_appTop_coord]
    · have h2 : (gam C O g ≫ AffineSpace.map PUnit.{u+1} π) ≫ prL S = ιCO C O ≫ π := by
        simp [AffineSpace.map_over]
      rw [← h2, Scheme.Hom.comp_appTop _ (prL S), CommRingCat.comp_apply]
  have hflat : (((gam C O g).toImage ≫ famL π C O g).stalkMap x).hom.Flat := by
    refine stalkMap_flat_of_stalk _ ⊤ (isAffineOpen_top _) x trivial ?_
    letI := ((((gam C O g).toImage ≫ famL π C O g).stalkMap x).hom.comp
      ((Ln S).presheaf.germ ⊤ _ trivial).hom).toAlgebra
    have halg : algebraMap Γ(Ln S, ⊤) _ (e (Polynomial.X - Polynomial.C l)) =
        (COo C O).toScheme.presheaf.germ ⊤ x trivial (gCO C O g - (ιCO C O ≫ π).appTop (σ l)) := by
      change (((gam C O g).toImage ≫ famL π C O g).stalkMap x)
        ((Ln S).presheaf.germ ⊤ _ trivial (e (Polynomial.X - Polynomial.C l))) = _
      exact (Scheme.Hom.germ_stalkMap_apply ((gam C O g).toImage ≫ famL π C O g) ⊤ x trivial
        _).trans (congrArg ((COo C O).toScheme.presheaf.germ ⊤ x trivial) hγ)
    exact flat_of_poly e l (fun b hb => hy b (halg ▸ hb)) (halg ▸ hm)
  rw [Scheme.Hom.stalkMap_comp] at hflat
  have key : (famL π C O g).stalkMap ((gam C O g).toImage x) =
      ((famL π C O g).stalkMap ((gam C O g).toImage x) ≫ (gam C O g).toImage.stalkMap x) ≫
        inv ((gam C O g).toImage.stalkMap x) := by
    simp
  rw [key, CommRingCat.hom_comp]
  exact RingHom.Flat.comp hflat (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))

end Graph

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Pen4 =====
section

/-!
# S4-IntersectB, O9 part 4: the pencil function `f / (f - 1)` and its fibres over `0` and `1`

* `exists_regOpen`: the regular locus of a rational function on an integral scheme, with the
  section it defines there (sheaf gluing).
* `hid_of_res`: an identity of sections on `O ⊓ W` gives the identity on `C ∩ O` used by
  `isPullback_fibre`.
* `appLE_eq_of_local`: a section pulled back along a morphism is computed stalkwise.
* `pencil_chart`: near every point, local equations `u`, `v` of the zeros and poles of `f` with
  `(u - v) (f / (f - 1) - n) = h` for the generator `h` of the fibre over `n ∈ {0, 1}`.
* `isPullback_pencil`: the fibres over `0` and `1` of the graph family of `f / (f - 1)` on `C`
  are the subschemes `effI (div f) ⊔ C` and `effI (-div f) ⊔ C`, provided `C` misses the common
  points of the zero and pole divisors.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology IsLocalRing

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.JacDivisors

lemma isUnit_sub_of_nonunit {R : Type*} [CommRing R] [IsLocalRing R] {a b : R} (ha : ¬IsUnit a)
    (hb : IsUnit b) : IsUnit (a - b) := by
  by_contra h
  have := (maximalIdeal R).sub_mem ((mem_maximalIdeal a).mpr ha) ((mem_maximalIdeal _).mpr h)
  rw [sub_sub_cancel] at this
  exact (mem_maximalIdeal b).mp this hb

lemma pencil_K {K : Type*} [Field K] {f U V H : K} (hf1 : f ≠ 1) (n : K) (huv : U = f * V)
    (hh : H = U - n * (U - V)) : (U - V) * (f / (f - 1) - n) = H := by
  have : f - 1 ≠ 0 := sub_ne_zero.mpr hf1
  rw [hh, huv]
  field_simp

lemma appLE_res {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} (hU : U' ≤ U) {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U') (s : Γ(Y, U)) :
    f.appLE U' V e (Y.presheaf.map (homOfLE hU).op s) =
      f.appLE U V (e.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE hU)).le) s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

lemma res_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (hV : V' ≤ V) (s : Γ(Y, U)) :
    X.presheaf.map (homOfLE hV).op (f.appLE U V e s) = f.appLE U V' (hV.trans e) s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

lemma res_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) {V : X.Opens} (s : Γ(Y, ⊤)) :
    X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (f.appTop s) = f.appLE ⊤ V le_top s := rfl

section Reg

variable {X : Scheme.{u}} [IsIntegral X]

/-- The regular locus `O` of a rational function `r` on an integral scheme, with the section of
`𝒪(O)` that `r` defines. -/
theorem exists_regOpen (r : X.functionField) :
    ∃ O : X.Opens, ∃ g : Γ(X, O), (∀ x (hx : x ∈ O),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ O x hx g) = r) ∧
      ∀ x : X, r ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) → x ∈ O := by
  let ι := {p : Σ U : X.Opens, Γ(X, U) // ∀ x (hx : x ∈ p.1),
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ p.1 x hx p.2) = r}
  let U : ι → X.Opens := fun i => i.1.1
  let sf : ∀ i : ι, Γ(X, U i) := fun i => i.1.2
  have hc : TopCat.Presheaf.IsCompatible X.sheaf.1 U sf := by
    intro i j
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => ?_
    show X.presheaf.germ (U i ⊓ U j) x hx
        (X.presheaf.map (TopologicalSpace.Opens.infLELeft (U i) (U j)).op (sf i)) =
      X.presheaf.germ (U i ⊓ U j) x hx
        (X.presheaf.map (TopologicalSpace.Opens.infLERight (U i) (U j)).op (sf j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      ((i.2 x hx.1).trans (j.2 x hx.2).symm)
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing U sf hc
  refine ⟨iSup U, s, fun x hx => ?_, fun x ⟨y, hy⟩ => ?_⟩
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have e := X.presheaf.germ_res_apply (TopologicalSpace.Opens.leSupr U i) x hi s
    rw [show X.presheaf.map (TopologicalSpace.Opens.leSupr U i).op s = sf i from hs i] at e
    rw [← e]
    exact i.2 x hi
  · obtain ⟨W, hxW, t, rfl⟩ := X.presheaf.exists_germ_eq (x := x) y
    haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
    rw [Scheme.algebraMap_germ_eq_germToFunctionField] at hy
    let i : ι := ⟨⟨W, t⟩, fun x' hx' => by
      haveI : Nonempty W := ⟨⟨x', hx'⟩⟩
      rw [Scheme.algebraMap_germ_eq_germToFunctionField]; exact hy⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hxW⟩

lemma mem_range_generic (r : X.functionField) (x : X) (hx : x = genericPoint X) :
    r ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  subst hx
  obtain ⟨W, hW, t, rfl⟩ := X.presheaf.exists_germ_eq (x := genericPoint X) r
  haveI : Nonempty W := ⟨⟨_, hW⟩⟩
  exact ⟨X.presheaf.germ W _ hW t, Scheme.algebraMap_germ_eq_germToFunctionField X hW t⟩

lemma res_eq_of_germ {U : X.Opens} (x : X) (hx : x ∈ U) {s t : Γ(X, U)}
    (h : algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) =
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx t)) : s = t :=
  germ_injective_of_isIntegral X x hx (IsFractionRing.injective _ _ h)

end Reg

section Hid

variable {X S : Scheme.{u}} (π : X ⟶ S) (C : X.IdealSheafData) (O : X.Opens)

lemma ιCO_preimage_le (W : X.Opens) : ιCO C O ⁻¹ᵁ W ≤ ιCO C O ⁻¹ᵁ (O ⊓ W) := fun y hy =>
  ⟨le_ιCO_preimage C O (show y ∈ (⊤ : (COo C O).toScheme.Opens) from trivial), hy⟩

/-- An identity of sections on `O ⊓ W` gives the identity on `C ∩ O ∩ W` of `isPullback_fibre`. -/
lemma hid_of_res (g : Γ(X, O)) (l : Γ(S, ⊤)) (W : X.Opens) (a h : Γ(X, W))
    (hΓ : X.presheaf.map (homOfLE (inf_le_right : O ⊓ W ≤ W)).op a *
      (X.presheaf.map (homOfLE (inf_le_left : O ⊓ W ≤ O)).op g -
        X.presheaf.map (homOfLE (le_top : O ⊓ W ≤ ⊤)).op (π.appTop l)) =
      X.presheaf.map (homOfLE (inf_le_right : O ⊓ W ≤ W)).op h) :
    (ιCO C O).app W a * (COo C O).toScheme.presheaf.map (homOfLE le_top).op
        (gCO C O g - (ιCO C O ≫ π).appTop l) = (ιCO C O).app W h := by
  have e := congrArg ((ιCO C O).appLE (O ⊓ W) _ (ιCO_preimage_le C O W)) hΓ
  simp only [map_mul, map_sub, appLE_res] at e
  rw [map_sub, gCO, res_appLE, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, res_appTop,
    Scheme.Hom.app_eq_appLE]
  exact e

/-- A section pulled back along `ι` is computed stalkwise: it suffices that near every point of
the image, `a (s - c) = h` with `a` a unit at the point and `h` killed by `ι`. -/
lemma appLE_eq_of_local {Y : Scheme.{u}} (ι : Y ⟶ X) (U : X.Opens) (e : ⊤ ≤ ι ⁻¹ᵁ U)
    (s : Γ(X, U)) (c : Γ(X, ⊤))
    (H : ∀ y : Y, ∃ W : X.Opens, ∃ hW : ι y ∈ W, ∃ a h : Γ(X, W),
      IsUnit (X.presheaf.germ W (ι y) hW a) ∧ ι.app W h = 0 ∧
      X.presheaf.germ W (ι y) hW a * (X.presheaf.germ U (ι y)
        (e (show y ∈ (⊤ : Y.Opens) from trivial)) s - X.presheaf.germ ⊤ (ι y) trivial c) =
        X.presheaf.germ W (ι y) hW h) :
    ι.appLE U ⊤ e s = ι.appTop c := by
  refine TopCat.Presheaf.section_ext Y.sheaf _ _ _ fun y _ => ?_
  obtain ⟨W, hW, a, h, ha, h0, hid⟩ := H y
  have hu : IsUnit (ι.stalkMap y (X.presheaf.germ W (ι y) hW a)) := ha.map _
  have := congrArg (ι.stalkMap y) hid
  simp only [map_mul, map_sub, Scheme.Hom.germ_stalkMap_apply, h0, map_zero] at this hu
  have h2 := sub_eq_zero.mp ((hu.mul_right_eq_zero).mp this)
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  erw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply] at h2
  exact h2

end Hid

section Pencil

variable {X S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (π : X ⟶ S)
  (C : X.IdealSheafData) (O : X.Opens)

lemma mem_support_iff_germ (I : X.IdealSheafData) {W : X.affineOpens} {x : X}
    (hx : x ∈ (W : X.Opens)) {u : Γ(X, W)} (hu : I.ideal W = Ideal.span {u}) :
    x ∈ I.support ↔ ¬IsUnit (X.presheaf.germ W x hx u) := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx, hu, Scheme.zeroLocus_span,
    Scheme.mem_zeroLocus_iff]
  simp [Scheme.mem_basicOpen X u x hx]

/-- Charts of the pencil: local equations `u`, `v` of the zeros and poles of `f`, the generator
`h` of the fibre over `n ∈ {0, 1}`, the identity `(u - v) (f / (f - 1) - n) = h` in `K(X)`, and
`u - v` a unit at points of the fibre when `C` misses the common points of zeros and poles. -/
theorem pencil_chart (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {f : X.functionField} (hf : f ≠ 0) (hf1 : f ≠ 1) (hfin : (Function.support (div X f)).Finite)
    (J : X.IdealSheafData) (n : ℤ)
    (hJ : J = effI (div X f) ⊔ C ∧ n = 0 ∨ J = effI (-div X f) ⊔ C ∧ n = 1) (x : X) :
    ∃ W : X.affineOpens, ∃ hxW : x ∈ (W : X.Opens), ∃ u v h : Γ(X, W),
      J.ideal W = Ideal.span {h} ⊔ C.ideal W ∧
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hxW (u - v)) *
        (f / (f - 1) - n) =
        algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hxW h) ∧
      ((∀ y, y ∈ C.support → y ∈ (effI (div X f)).support → y ∉ (effI (-div X f)).support) →
        x ∈ J.support → IsUnit (X.presheaf.germ W x hxW (u - v))) := by
  obtain ⟨W, hxW, u, v, hu, hv, huv⟩ := exists_bridge hufd hf hfin x
  have hP := mem_support_iff_germ (effI (div X f)) hxW hu
  have hN := mem_support_iff_germ (effI (-div X f)) hxW hv
  rcases hJ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨W, hxW, u, v, u, ?_, ?_, ?_⟩
    · show (effI (div X f)).ideal W ⊔ C.ideal W = _
      rw [hu]
    · simp only [map_sub]
      exact pencil_K hf1 _ huv (by simp)
    · intro hCPN hx
      rw [Scheme.IdealSheafData.support_sup] at hx
      have h1 := hP.mp hx.1
      have h2 : IsUnit (X.presheaf.germ W x hxW v) := not_not.mp (mt hN.mpr (hCPN x hx.2 hx.1))
      rw [map_sub]
      exact isUnit_sub_of_nonunit h1 h2
  · refine ⟨W, hxW, u, v, v, ?_, ?_, ?_⟩
    · show (effI (-div X f)).ideal W ⊔ C.ideal W = _
      rw [hv]
    · simp only [map_sub]
      exact pencil_K hf1 _ huv (by push_cast; ring)
    · intro hCPN hx
      rw [Scheme.IdealSheafData.support_sup] at hx
      have h1 := hN.mp hx.1
      have h2 : IsUnit (X.presheaf.germ W x hxW u) :=
        not_not.mp (mt hP.mpr (fun hp => hCPN x hx.2 hp hx.1))
      rw [map_sub, ← neg_sub]
      exact (isUnit_sub_of_nonunit h1 h2).neg

/-- The chart hypothesis `H` of `isPullback_fibre` for the pencil. -/
theorem pencil_H (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {f : X.functionField} (hf : f ≠ 0) (hf1 : f ≠ 1) (hfin : (Function.support (div X f)).Finite)
    (g : Γ(X, O)) (hO : genericPoint X ∈ O)
    (hg : ∀ x (hx : x ∈ O),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ O x hx g) = f / (f - 1))
    (J : X.IdealSheafData) (n : ℤ)
    (hJ : J = effI (div X f) ⊔ C ∧ n = 0 ∨ J = effI (-div X f) ⊔ C ∧ n = 1)
    (l : Γ(S, ⊤)) (hl : l = n) (x : X) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ ∃ a h : Γ(X, W),
      J.ideal W ≤ Ideal.span {h} ⊔ C.ideal W ∧
      (ιCO C O).app W a * (COo C O).toScheme.presheaf.map (homOfLE le_top).op
        (gCO C O g - (ιCO C O ≫ π).appTop l) = (ιCO C O).app W h := by
  obtain ⟨W, hxW, u, v, h, hJW, hK, -⟩ := pencil_chart C hufd hf hf1 hfin J n hJ x
  refine ⟨W, hxW, u - v, h, hJW.le, hid_of_res π C O g l W _ _ ?_⟩
  have hηW : genericPoint X ∈ (W : X.Opens) :=
    ((genericPoint_spec X).mem_open_set_iff W.1.isOpen).mpr ⟨x, trivial, hxW⟩
  haveI : Nonempty (W : X.Opens) := ⟨⟨x, hxW⟩⟩
  haveI : Nonempty O := ⟨⟨_, hO⟩⟩
  have hg' := hg _ hO
  apply res_eq_of_germ (genericPoint X) (show genericPoint X ∈ O ⊓ (W : X.Opens) from ⟨hO, hηW⟩)
  simp only [map_sub, Scheme.algebraMap_germ_eq_germToFunctionField] at hK hg'
  simp only [hl, map_intCast, map_mul, map_sub, TopCat.Presheaf.germ_res_apply,
    Scheme.algebraMap_germ_eq_germToFunctionField]
  rw [hg']
  exact hK

lemma top_le_preimage (J : X.IdealSheafData) {O : X.Opens} (hJO : (J.support : Set X) ⊆ O) :
    (⊤ : J.subscheme.Opens) ≤ J.subschemeι ⁻¹ᵁ O := fun y _ =>
  show J.subschemeι y ∈ O from hJO (show J.subschemeι y ∈ (J.support : Set X) by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y, rfl⟩)

/-- A subscheme `J ≥ C` supported in `O` maps into `C ∩ O`. -/
noncomputable def mCO (J : X.IdealSheafData) (hCJ : C ≤ J) (hJO : (J.support : Set X) ⊆ O) :
    J.subscheme ⟶ (COo C O).toScheme :=
  IsOpenImmersion.lift (COo C O).ι (Scheme.IdealSheafData.inclusion hCJ) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show C.subschemeι (Scheme.IdealSheafData.inclusion hCJ y) ∈ O
    rw [← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
    exact top_le_preimage J hJO (show y ∈ (⊤ : J.subscheme.Opens) from trivial))

lemma mCO_ιCO (J : X.IdealSheafData) (hCJ : C ≤ J) (hJO : (J.support : Set X) ⊆ O) :
    mCO C O J hCJ hJO ≫ ιCO C O = J.subschemeι := by
  rw [mCO, ιCO, ← Category.assoc, IsOpenImmersion.lift_fac,
    Scheme.IdealSheafData.inclusion_subschemeι]

variable {C O} in
/-- Points of the fibre lie in the regular locus of `f / (f - 1)`. -/
lemma pencil_supp_le (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {f : X.functionField} (hf : f ≠ 0) (hf1 : f ≠ 1) (hfin : (Function.support (div X f)).Finite)
    (hreg : ∀ x : X, f / (f - 1) ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) →
      x ∈ O)
    (hCPN : ∀ y, y ∈ C.support → y ∈ (effI (div X f)).support → y ∉ (effI (-div X f)).support)
    (J : X.IdealSheafData) (n : ℤ)
    (hJ : J = effI (div X f) ⊔ C ∧ n = 0 ∨ J = effI (-div X f) ⊔ C ∧ n = 1) :
    (J.support : Set X) ⊆ O := by
  intro x hx
  obtain ⟨W, hxW, u, v, h, -, hK, hU⟩ := pencil_chart C hufd hf hf1 hfin J n hJ x
  have hu := hU hCPN hx
  apply hreg x
  refine ⟨n + X.presheaf.germ W x hxW h * ↑hu.unit⁻¹, ?_⟩
  have hne : algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ W x hxW (u - v)) ≠ 0 := (hu.map _).ne_zero
  rw [map_add, map_intCast, map_mul, map_units_inv, IsUnit.unit_spec, ← hK, mul_right_comm,
    mul_inv_cancel₀ hne, one_mul]
  ring

theorem pencil_hg (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {f : X.functionField} (hf : f ≠ 0) (hf1 : f ≠ 1) (hfin : (Function.support (div X f)).Finite)
    (g : Γ(X, O))
    (hg : ∀ x (hx : x ∈ O),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ O x hx g) = f / (f - 1))
    (hCPN : ∀ y, y ∈ C.support → y ∈ (effI (div X f)).support → y ∉ (effI (-div X f)).support)
    (J : X.IdealSheafData) (n : ℤ)
    (hJ : J = effI (div X f) ⊔ C ∧ n = 0 ∨ J = effI (-div X f) ⊔ C ∧ n = 1)
    (hCJ : C ≤ J) (hJO : (J.support : Set X) ⊆ O) (l : Γ(S, ⊤)) (hl : l = n) :
    (mCO C O J hCJ hJO).appTop (gCO C O g) = (J.subschemeι ≫ π).appTop l := by
  have e1 : (mCO C O J hCJ hJO).appTop (gCO C O g) =
      J.subschemeι.appLE O ⊤ (top_le_preimage J hJO) g := by
    show (mCO C O J hCJ hJO).app ⊤ (gCO C O g) = _
    rw [← Scheme.Hom.appLE_eq_app, gCO, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (mCO_ιCO C O J hCJ hJO)]
    rfl
  rw [e1, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  refine appLE_eq_of_local _ O _ g _ fun y => ?_
  have hxJ : J.subschemeι y ∈ (J.support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y, rfl⟩
  obtain ⟨W, hxW, u, v, h, hJW, hK, hU⟩ :=
    pencil_chart C hufd hf hf1 hfin J n hJ (J.subschemeι y)
  refine ⟨W, hxW, u - v, h, hU hCPN hxJ, ?_, ?_⟩
  · have hh : h ∈ J.ideal W := hJW ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self h)
    rw [← Scheme.IdealSheafData.ker_subschemeι_app] at hh
    exact hh
  · apply IsFractionRing.injective (X.presheaf.stalk (J.subschemeι y)) X.functionField
    simp only [hl, map_intCast, map_mul, map_sub, hg _ (hJO hxJ)] at hK ⊢
    exact hK

end Pencil

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Fam1 =====
section

/-!
# S4-IntersectB, file Fam1: flat neighbourhoods of finite fibres (O8, part 1)

* `flat_atPrime_of_flat_away`: if `M_b` is flat over `B` then so is `M_𝔮` for every prime `𝔮 ∌ b`.
* `flat_away_of_projective`: `M_b` is flat over `B` when `(M_b)` is projective over `B_b`.
* `flat_semilocal`: for `M` finite over `B` with `M_𝔮` flat over `B` for all `𝔮` over `𝔭`, the
  semilocal ring `M_𝔭` is flat over `B`.
* `exists_flat_basicOpen`: (ring form of the open flat locus) there is `b ∉ 𝔭` such that `M_𝔮` is
  flat over `B` for every prime `𝔮` of `M` not containing `b`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace RamanujanPetersson.IntersectB

section Ring

variable {B M : Type u} [CommRing B] [CommRing M] [Algebra B M]

theorem flat_atPrime_of_flat_away (b : B) (𝔮 : Ideal M) [𝔮.IsPrime]
    (hb : algebraMap B M b ∉ 𝔮)
    (hN : Module.Flat B (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b)))) :
    Module.Flat B (Localization.AtPrime 𝔮) := by
  set S := Algebra.algebraMapSubmonoid M (Submonoid.powers b) with hSdef
  have hS : S ≤ 𝔮.primeCompl := by
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    show _ ∉ 𝔮
    rw [map_pow]
    exact fun h => hb (‹𝔮.IsPrime›.mem_of_pow_mem n h)
  letI : Algebra (Localization S) (Localization.AtPrime 𝔮) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ S 𝔮.primeCompl hS
  have : IsScalarTower M (Localization S) (Localization.AtPrime 𝔮) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ S 𝔮.primeCompl hS
  have : IsLocalization (𝔮.primeCompl.map (algebraMap M (Localization S)))
      (Localization.AtPrime 𝔮) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ S 𝔮.primeCompl hS
  have : Module.Flat (Localization S) (Localization.AtPrime 𝔮) :=
    IsLocalization.flat _ (𝔮.primeCompl.map (algebraMap M (Localization S)))
  have : IsScalarTower B (Localization S) (Localization.AtPrime 𝔮) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply B M (Localization S),
        IsScalarTower.algebraMap_apply B M (Localization.AtPrime 𝔮),
        ← IsScalarTower.algebraMap_apply M (Localization S) (Localization.AtPrime 𝔮)]
  exact Module.Flat.trans B (Localization S) (Localization.AtPrime 𝔮)

theorem flat_away_of_projective (b : B)
    [Module.Projective (Localization.Away b) (LocalizedModule.Away b M)] :
    Module.Flat B (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b))) := by
  have : Module.Flat B (LocalizedModule.Away b M) :=
    (Module.flat_iff_of_isLocalization (Localization.Away b) (Submonoid.powers b) _).mp
      inferInstance
  have : IsLocalizedModule (Submonoid.powers b) (IsScalarTower.toAlgHom B M
      (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b)))).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  exact Module.Flat.of_linearEquiv (IsLocalizedModule.iso (Submonoid.powers b) (IsScalarTower.toAlgHom
    B M (Localization (Algebra.algebraMapSubmonoid M (Submonoid.powers b)))).toLinearMap).symm

theorem flat_semilocal [Module.Finite B M] (𝔭 : Ideal B) [𝔭.IsPrime]
    (h : ∀ (𝔮 : Ideal M) [𝔮.IsPrime], 𝔮.comap (algebraMap B M) = 𝔭 →
      Module.Flat B (Localization.AtPrime 𝔮)) :
    Module.Flat B (Localization (Algebra.algebraMapSubmonoid M 𝔭.primeCompl)) := by
  set Sp := Algebra.algebraMapSubmonoid M 𝔭.primeCompl
  refine Module.flat_of_isLocalized_maximal (Localization Sp) (Localization Sp)
    (fun P _ => Localization.AtPrime P) (fun P _ => Algebra.linearMap _ _) (fun P hP => ?_)
  have hmax : (P.comap (algebraMap (Localization.AtPrime 𝔭) (Localization Sp))).IsMaximal :=
    Ideal.IsMaximal.under (Localization.AtPrime 𝔭) P
  have h𝔮 : (P.comap (algebraMap M (Localization Sp))).comap (algebraMap B M) = 𝔭 := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq B (Localization.AtPrime 𝔭) (Localization Sp),
      ← Ideal.comap_comap, IsLocalRing.eq_maximalIdeal hmax]
    exact Localization.AtPrime.under_maximalIdeal (I := 𝔭)
  have := h _ h𝔮
  exact Module.Flat.of_linearEquiv
    ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization Sp P).restrictScalars
      B).toLinearEquiv.symm

theorem exists_flat_basicOpen [IsNoetherianRing B] [Module.Finite B M] (𝔭 : Ideal B) [𝔭.IsPrime]
    (h : ∀ (𝔮 : Ideal M) [𝔮.IsPrime], 𝔮.comap (algebraMap B M) = 𝔭 →
      Module.Flat B (Localization.AtPrime 𝔮)) :
    ∃ b ∉ 𝔭, ∀ (𝔮 : Ideal M) [𝔮.IsPrime], algebraMap B M b ∉ 𝔮 →
      Module.Flat B (Localization.AtPrime 𝔮) := by
  set Sp := Algebra.algebraMapSubmonoid M 𝔭.primeCompl
  have := Module.finitePresentation_of_finite B M
  have := flat_semilocal 𝔭 h
  have : Module.Flat (Localization.AtPrime 𝔭) (Localization Sp) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime 𝔭) 𝔭.primeCompl _).mpr
      inferInstance
  have : Module.Free (Localization.AtPrime 𝔭) (Localization Sp) :=
    Module.free_of_flat_of_isLocalRing
  have : IsLocalizedModule 𝔭.primeCompl
      (IsScalarTower.toAlgHom B M (Localization Sp)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have hmem : (⟨𝔭, inferInstance⟩ : PrimeSpectrum B) ∈ Module.freeLocus B M :=
    (Module.mem_freeLocus_of_isLocalization _ (Localization.AtPrime 𝔭) (Localization Sp)
      (IsScalarTower.toAlgHom B M (Localization Sp)).toLinearMap).mpr inferInstance
  obtain ⟨_, ⟨b, rfl⟩, hb, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hmem
      Module.isOpen_freeLocus
  have := Module.basicOpen_subset_freeLocus_iff.mp hsub
  exact ⟨b, hb, fun 𝔮 _ h𝔮 => flat_atPrime_of_flat_away b 𝔮 h𝔮 (flat_away_of_projective b)⟩

end Ring

section Scheme

theorem isFinite_restrict_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (hUV : U ≤ V)
    [IsFinite (f ∣_ V)] : IsFinite (f ∣_ U) := by
  have hE : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf]
  have : MorphismProperty.RespectsIso @IsFinite :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) => inferInstance
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U) ≪≫ morphismRestrictEq f hE)).mp inferInstance

theorem finite_app_of_isFinite_restrict {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) [IsFinite (p ∣_ U)] : (p.app U).hom.Finite := by
  have : IsAffine U := hU
  have h := Scheme.Hom.finite_appTop (p ∣_ U)
  change ((p ∣_ U).app ⊤).hom.Finite at h
  rw [morphismRestrict_app'] at h
  rw [Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_congr _ _ (Scheme.Opens.ι_image_top U) (by simp)
    (fun φ => φ.hom.Finite)).mp h

theorem mem_basicOpen_iff_primeIdealOf {Y : Scheme.{u}} {U : Y.Opens} (hU : IsAffineOpen U)
    (y : Y) (hy : y ∈ U) (b : Γ(Y, U)) :
    y ∈ Y.basicOpen b ↔ b ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal := by
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  have := hU.isLocalization_stalk ⟨y, hy⟩
  rw [Scheme.mem_basicOpen Y b y hy]
  exact IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) _ b

theorem stalkMap_flat_iff {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (p ⁻¹ᵁ U)) (x : X) (hx : p x ∈ U) :
    (p.stalkMap x).hom.Flat ↔
      letI := (p.app U).hom.toAlgebra
      Module.Flat Γ(Y, U) (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  letI := (p.app U).hom.toAlgebra
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨p x, hx⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : p ⁻¹ᵁ U)
  have hlt := hU.isLocalization_stalk ⟨p x, hx⟩
  have hlx := hV.isLocalization_stalk ⟨x, hx⟩
  letI : Algebra (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) := (p.stalkMap x).hom.toAlgebra
  letI : Algebra Γ(Y, U) (X.presheaf.stalk x) :=
    ((p.stalkMap x).hom.comp (Y.presheaf.germ U (p x) hx).hom).toAlgebra
  have : IsScalarTower Γ(Y, U) (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(Y, U) Γ(X, p ⁻¹ᵁ U) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun r => Scheme.Hom.germ_stalkMap_apply p U x hx r
  change Module.Flat (Y.presheaf.stalk (p x)) (X.presheaf.stalk x) ↔ _
  rw [Module.flat_iff_of_isLocalization (Y.presheaf.stalk (p x))
    (hU.primeIdealOf ⟨p x, hx⟩).asIdeal.primeCompl]
  let e : Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≃ₐ[Γ(X, p ⁻¹ᵁ U)]
      X.presheaf.stalk x :=
    IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ _
  exact ⟨fun _ => Module.Flat.of_linearEquiv (e.restrictScalars Γ(Y, U)).toLinearEquiv,
    fun _ => Module.Flat.of_linearEquiv (e.restrictScalars Γ(Y, U)).toLinearEquiv.symm⟩

theorem exists_basicOpen_flat_stalk {X Y : Scheme.{u}} (p : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen (p ⁻¹ᵁ U)) (hfin : (p.app U).hom.Finite)
    [IsNoetherianRing Γ(Y, U)] (y : Y) (hy : y ∈ U)
    (hflat : ∀ x, p x = y → (p.stalkMap x).hom.Flat) :
    ∃ b : Γ(Y, U), y ∈ Y.basicOpen b ∧ ∀ x, p x ∈ Y.basicOpen b → (p.stalkMap x).hom.Flat := by
  letI := (p.app U).hom.toAlgebra
  have : Module.Finite Γ(Y, U) Γ(X, p ⁻¹ᵁ U) := hfin
  have hcomap : ∀ x (hx : p x ∈ U), (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap
      (algebraMap Γ(Y, U) Γ(X, p ⁻¹ᵁ U)) = (hU.primeIdealOf ⟨p x, hx⟩).asIdeal := by
    intro x hx
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := p) U hU (p ⁻¹ᵁ U) hV le_rfl hx
    rw [Scheme.Hom.appLE_eq_app] at h
    exact congrArg PrimeSpectrum.asIdeal h
  have hsub : ∀ (q q' : PrimeSpectrum Γ(X, p ⁻¹ᵁ U)), q' = q →
      Module.Flat Γ(Y, U) (Localization.AtPrime q'.asIdeal) →
      Module.Flat Γ(Y, U) (Localization.AtPrime q.asIdeal) := by
    rintro _ _ rfl h; exact h
  have hfib : ∀ (𝔮 : Ideal Γ(X, p ⁻¹ᵁ U)) [𝔮.IsPrime],
      𝔮.comap (algebraMap Γ(Y, U) Γ(X, p ⁻¹ᵁ U)) = (hU.primeIdealOf ⟨y, hy⟩).asIdeal →
      Module.Flat Γ(Y, U) (Localization.AtPrime 𝔮) := by
    intro 𝔮 _ h𝔮
    let q : PrimeSpectrum Γ(X, p ⁻¹ᵁ U) := ⟨𝔮, inferInstance⟩
    have hxV : hV.fromSpec q ∈ p ⁻¹ᵁ U := by
      rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨q, rfl⟩
    have hq : hV.primeIdealOf ⟨hV.fromSpec q, hxV⟩ = q :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨_, hxV⟩)
    have hpx : p (hV.fromSpec q) = y := by
      have h1 := hcomap _ hxV
      rw [hq] at h1
      have h2 : hU.primeIdealOf ⟨p (hV.fromSpec q), hxV⟩ = hU.primeIdealOf ⟨y, hy⟩ :=
        PrimeSpectrum.ext (h1.symm.trans h𝔮)
      have h3 := congrArg hU.fromSpec h2
      rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h3
    exact hsub q _ hq ((stalkMap_flat_iff p U hU hV _ hxV).mp (hflat _ hpx))
  obtain ⟨b, hb, H⟩ := exists_flat_basicOpen (B := Γ(Y, U)) (M := Γ(X, p ⁻¹ᵁ U))
    (hU.primeIdealOf ⟨y, hy⟩).asIdeal hfib
  refine ⟨b, (mem_basicOpen_iff_primeIdealOf hU y hy b).mpr hb, fun x hx => ?_⟩
  have hxU : p x ∈ U := Y.basicOpen_le b hx
  rw [stalkMap_flat_iff p U hU hV x hxU]
  refine H _ fun hmem => (mem_basicOpen_iff_primeIdealOf hU (p x) hxU b).mp hx ?_
  rw [← hcomap x hxU]
  exact hmem

/-- (B') A proper morphism to a locally Noetherian scheme with a finite fibre at `t` whose stalk
maps over `t` are flat is finite over an open neighbourhood `V` of `t`, with flat stalk maps at
every point over `V`. -/
theorem exists_flat_nbhd {Z T : Scheme.{u}} (p : Z ⟶ T) [IsProper p] [IsLocallyNoetherian T]
    (t : T) (hfin : (p ⁻¹' {t}).Finite) (hflat : ∀ z, p z = t → (p.stalkMap z).hom.Flat) :
    ∃ V : T.Opens, t ∈ V ∧ IsFinite (p ∣_ V) ∧ ∀ z, p z ∈ V → (p.stalkMap z).hom.Flat := by
  obtain ⟨V1, htV1, hV1⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton p t hfin
  obtain ⟨U, hU, htU, hUV1⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens htV1
  have hU' : IsAffineOpen U := hU
  have : IsFinite (p ∣_ U) := isFinite_restrict_of_le p hUV1
  have : IsAffine U := hU'
  have hV : IsAffineOpen (p ⁻¹ᵁ U) := isAffine_of_isAffineHom (p ∣_ U)
  have : IsNoetherianRing Γ(T, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU'⟩
  obtain ⟨b, htb, H⟩ := exists_basicOpen_flat_stalk p U hU' hV
    (finite_app_of_isFinite_restrict p U hU') t htU hflat
  exact ⟨T.basicOpen b, htb, isFinite_restrict_of_le p ((T.basicOpen_le b).trans hUV1), H⟩

end Scheme

section Const

theorem flat_restrict_of_stalk {Z T : Scheme.{u}} (p : Z ⟶ T) (V : T.Opens)
    (H : ∀ z, p z ∈ V → (p.stalkMap z).hom.Flat) : Flat (p ∣_ V) :=
  Flat.of_stalkMap _ fun x =>
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap p V x)).mpr (H x.1 x.2)

theorem finrank_pullback_eq_restrict {Z T P S : Scheme.{u}} (p : Z ⟶ T) (V : T.Opens)
    [Flat (p ∣_ V)] [IsFinite (p ∣_ V)] (fst : P ⟶ Z) (snd : P ⟶ S) (c : S ⟶ T)
    (h : IsPullback fst snd p c) (hc : Set.range c ⊆ V) (s : S) :
    ∃ a : V.toScheme, snd.finrank s = (p ∣_ V).finrank a := by
  let c' : S ⟶ V.toScheme := IsOpenImmersion.lift V.ι c (by rw [Scheme.Opens.range_ι]; exact hc)
  have hc' : c' ≫ V.ι = c := IsOpenImmersion.lift_fac _ _ _
  have hr := (isPullback_morphismRestrict p V).flip
  let fst' : P ⟶ (p ⁻¹ᵁ V).toScheme :=
    hr.lift fst (snd ≫ c') (by rw [h.w, Category.assoc, hc'])
  have e1 : fst' ≫ (p ⁻¹ᵁ V).ι = fst := hr.lift_fst _ _ _
  have h' : IsPullback fst' snd (p ∣_ V) c' := by
    refine IsPullback.of_right ?_ (hr.lift_snd _ _ _) hr
    rw [e1, hc']
    exact h
  exact ⟨c' s, Scheme.Hom.finrank_of_isPullback fst' snd (p ∣_ V) c' h' s⟩

theorem finrank_restrict_eq {Z T : Scheme.{u}} [IrreducibleSpace T] [IsLocallyNoetherian T]
    (p : Z ⟶ T) (V : T.Opens) [Flat (p ∣_ V)] [IsFinite (p ∣_ V)] (a b : V.toScheme) :
    (p ∣_ V).finrank a = (p ∣_ V).finrank b := by
  have hV : _root_.IsPreconnected (V : Set T) :=
    ((IrreducibleSpace.isIrreducible_univ (X := T)).isPreirreducible.open_subset V.2
      (Set.subset_univ _)).isPreconnected
  have : _root_.PreconnectedSpace V.toScheme := isPreconnected_iff_preconnectedSpace.mp hV
  exact (Scheme.Hom.isLocallyConstant_finrank (p ∣_ V)).apply_eq_of_preconnectedSpace a b

/-- (C') Fibre ranks of a proper family over an irreducible locally Noetherian base agree at two
points with finite fibres and flat stalk maps, read through any base changes concentrated there. -/
theorem finrank_eq_of_fibres {Z T P0 S0 P1 S1 : Scheme.{u}} (p : Z ⟶ T) [IsProper p]
    [IsLocallyNoetherian T] [IrreducibleSpace T] (t0 t1 : T)
    (hfin0 : (p ⁻¹' {t0}).Finite) (hfin1 : (p ⁻¹' {t1}).Finite)
    (hflat0 : ∀ z, p z = t0 → (p.stalkMap z).hom.Flat)
    (hflat1 : ∀ z, p z = t1 → (p.stalkMap z).hom.Flat)
    (fst0 : P0 ⟶ Z) (snd0 : P0 ⟶ S0) (c0 : S0 ⟶ T) (h0 : IsPullback fst0 snd0 p c0)
    (hc0 : ∀ s, c0 s = t0)
    (fst1 : P1 ⟶ Z) (snd1 : P1 ⟶ S1) (c1 : S1 ⟶ T) (h1 : IsPullback fst1 snd1 p c1)
    (hc1 : ∀ s, c1 s = t1) (s0 : S0) (s1 : S1) :
    snd0.finrank s0 = snd1.finrank s1 := by
  obtain ⟨V0, ht0, hfV0, hV0⟩ := exists_flat_nbhd p t0 hfin0 hflat0
  obtain ⟨V1, ht1, hfV1, hV1⟩ := exists_flat_nbhd p t1 hfin1 hflat1
  have := flat_restrict_of_stalk p V0 hV0
  have := flat_restrict_of_stalk p V1 hV1
  obtain ⟨w, hw0, hw1⟩ := nonempty_preirreducible_inter V0.2 V1.2 ⟨t0, ht0⟩ ⟨t1, ht1⟩
  let W : T.Opens := V0 ⊓ V1
  have hwW : w ∈ W := ⟨hw0, hw1⟩
  have hWr : ∀ (V : T.Opens), W ≤ V → Set.range W.ι ⊆ V := fun V hV => by
    rw [Scheme.Opens.range_ι]; exact hV
  obtain ⟨a0, e0⟩ := finrank_pullback_eq_restrict p V0 fst0 snd0 c0 h0
    (by rintro _ ⟨s, rfl⟩; rw [hc0]; exact ht0) s0
  obtain ⟨a1, e1⟩ := finrank_pullback_eq_restrict p V1 fst1 snd1 c1 h1
    (by rintro _ ⟨s, rfl⟩; rw [hc1]; exact ht1) s1
  have hpb := IsPullback.of_hasPullback p W.ι
  obtain ⟨b0, f0⟩ := finrank_pullback_eq_restrict p V0 _ _ _ hpb (hWr V0 inf_le_left)
    (⟨w, hwW⟩ : W)
  obtain ⟨b1, f1⟩ := finrank_pullback_eq_restrict p V1 _ _ _ hpb (hWr V1 inf_le_right)
    (⟨w, hwW⟩ : W)
  rw [e0, e1, finrank_restrict_eq p V0 a0 b0, finrank_restrict_eq p V1 a1 b1, ← f0, ← f1]

end Const

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Pen5 =====
section

/-!
# S4-IntersectB, file Pen5: the two fibres of the pencil have the same length (L34, B4)

* `mem_of_mul_mem_of_ass`, `nzd_algebraMap`: non-zero-divisors from associated primes and
  under localisation.
* `nzd_germ_subscheme`, `nzd_germ_CO`: a local equation avoiding the associated points of `C`
  is a non-zero-divisor in the stalks of `C` and of `C ∩ O`.
* `pencil_chart2`: charts of the pencil at a point of the fibre with the unit `u - v` and the
  associated-prime condition on the fibre equation.
* `hy_pencil`, `hm_pencil`: the two hypotheses of `flat_famL`.
* `len_pencil`: `len (effI (div f) ⊔ C) = len (effI (-div f) ⊔ C)` for `C` avoiding the common
  points of zeros and poles and with no associated point on them.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology IsLocalRing

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section NZD

/-- An element outside every associated prime of `R ⧸ I` is a non-zero-divisor modulo `I`. -/
lemma mem_of_mul_mem_of_ass {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) {h : R}
    (hh : ∀ p ∈ associatedPrimes R (R ⧸ I), h ∉ p) {r : R} (hr : h * r ∈ I) : r ∈ I := by
  have hreg : IsSMulRegular (R ⧸ I) h := by
    by_contra hc
    have hmem : h ∈ ⋃ p ∈ associatedPrimes R (R ⧸ I), (p : Set R) := by
      rw [biUnion_associatedPrimes_eq_compl_regular R (R ⧸ I)]; exact hc
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hmem
    obtain ⟨p, hp, hhp⟩ := hmem
    exact hh p hp hhp
  have e : h • Ideal.Quotient.mk I r = h • (0 : R ⧸ I) := by
    rw [smul_zero]; exact Ideal.Quotient.eq_zero_iff_mem.2 hr
  exact Ideal.Quotient.eq_zero_iff_mem.1 (hreg e)

/-- The image of a non-zero-divisor in a localisation is a non-zero-divisor. -/
lemma nzd_algebraMap {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] (M : Submonoid R)
    [IsLocalization M T] {t : R} (ht : ∀ r, t * r = 0 → r = 0) :
    ∀ b : T, algebraMap R T t * b = 0 → b = 0 := by
  intro b hb
  obtain ⟨r, s, rfl⟩ := IsLocalization.mk'_surjective M b
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hb
  rw [IsLocalization.mk'_eq_zero_iff]
  obtain ⟨m, hm⟩ := hb
  exact ⟨m, ht _ (by rw [mul_left_comm]; exact hm)⟩

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (C : X.IdealSheafData)

/-- A section avoiding the associated primes of `C` is a non-zero-divisor in the stalks of `C`. -/
lemma nzd_germ_subscheme (W : X.affineOpens) {h : Γ(X, W)}
    (hh : ∀ p ∈ associatedPrimes Γ(X, W) (Γ(X, W) ⧸ C.ideal W), h ∉ p)
    (z : C.subscheme) (hz : z ∈ C.subschemeι ⁻¹ᵁ (W : X.Opens)) :
    ∀ b : C.subscheme.presheaf.stalk z,
      C.subscheme.presheaf.germ _ z hz (C.subschemeι.app W h) * b = 0 → b = 0 := by
  have hV : IsAffineOpen (C.subschemeι ⁻¹ᵁ (W : X.Opens)) := W.2.preimage C.subschemeι
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian W
  let φ := (C.subschemeObjIso W).commRingCatIsoToRingEquiv
  have hφ : ∀ a : Γ(X, W), C.subschemeι.app W a = φ.symm (Ideal.Quotient.mk _ a) := fun a => by
    rw [Scheme.IdealSheafData.subschemeι_app]; rfl
  have ht : ∀ r : Γ(C.subscheme, C.subschemeι ⁻¹ᵁ (W : X.Opens)),
      C.subschemeι.app W h * r = 0 → r = 0 := by
    intro r hr
    obtain ⟨r', hr'⟩ := Ideal.Quotient.mk_surjective (φ r)
    have hr2 : r = φ.symm (Ideal.Quotient.mk _ r') := by rw [hr', RingEquiv.symm_apply_apply]
    rw [hr2, hφ, ← map_mul, ← map_mul, map_eq_zero_iff _ φ.symm.injective,
      Ideal.Quotient.eq_zero_iff_mem] at hr
    rw [hr2, Ideal.Quotient.eq_zero_iff_mem.2 (mem_of_mul_mem_of_ass _ hh hr), map_zero]
  letI := TopCat.Presheaf.algebra_section_stalk C.subscheme.presheaf ⟨z, hz⟩
  have hloc := hV.isLocalization_stalk ⟨z, hz⟩
  exact nzd_algebraMap (hV.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl ht

variable (O : X.Opens)

/-- The same in the stalks of the open part `C ∩ O`. -/
lemma nzd_germ_CO (W : X.affineOpens) {h : Γ(X, W)}
    (hh : ∀ p ∈ associatedPrimes Γ(X, W) (Γ(X, W) ⧸ C.ideal W), h ∉ p)
    (x : (COo C O).toScheme) (hx : x ∈ ιCO C O ⁻¹ᵁ (W : X.Opens)) :
    ∀ b : (COo C O).toScheme.presheaf.stalk x,
      (COo C O).toScheme.presheaf.germ _ x hx ((ιCO C O).app W h) * b = 0 → b = 0 := by
  intro b hb
  have hz : (COo C O).ι x ∈ C.subschemeι ⁻¹ᵁ (W : X.Opens) := hx
  have e1 : (COo C O).toScheme.presheaf.germ _ x hx ((ιCO C O).app W h) =
      (COo C O).ι.stalkMap x (C.subscheme.presheaf.germ _ _ hz (C.subschemeι.app W h)) := by
    rw [Scheme.Hom.germ_stalkMap_apply]; rfl
  let ψ := (asIso ((COo C O).ι.stalkMap x)).commRingCatIsoToRingEquiv
  obtain ⟨b', rfl⟩ : ∃ b', ψ b' = b := ψ.surjective b
  rw [e1] at hb
  have hb' : C.subscheme.presheaf.germ _ _ hz (C.subschemeι.app W h) * b' = 0 := by
    apply ψ.injective
    rw [map_mul, map_zero]
    exact hb
  rw [nzd_germ_subscheme C W hh _ hz b' hb', map_zero]

end NZD

section Chart

variable {X S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (π : X ⟶ S)
  (C : X.IdealSheafData) (O : X.Opens)

/-- Charts of the pencil at a point of the fibre: the identity of `isPullback_fibre` with `a` a
unit at the point and the fibre equation `h` outside the associated primes of `C`. -/
theorem pencil_chart2 (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {f : X.functionField} (hf : f ≠ 0) (hf1 : f ≠ 1) (hfin : (Function.support (div X f)).Finite)
    (g : Γ(X, O)) (hO : genericPoint X ∈ O)
    (hg : ∀ x (hx : x ∈ O),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ O x hx g) = f / (f - 1))
    (hCPN : ∀ y, y ∈ C.support → y ∈ (effI (div X f)).support → y ∉ (effI (-div X f)).support)
    (hAss : ∀ ξ ∈ assSet C, ξ ∉ (effI (div X f)).support ∧ ξ ∉ (effI (-div X f)).support)
    (J : X.IdealSheafData) (n : ℤ)
    (hJ : J = effI (div X f) ⊔ C ∧ n = 0 ∨ J = effI (-div X f) ⊔ C ∧ n = 1)
    (l : Γ(S, ⊤)) (hl : l = n) (x : X) (hx : x ∈ J.support) :
    ∃ W : X.affineOpens, ∃ hxW : x ∈ (W : X.Opens), ∃ a h : Γ(X, W),
      IsUnit (X.presheaf.germ W x hxW a) ∧
      (∀ p ∈ associatedPrimes Γ(X, W) (Γ(X, W) ⧸ C.ideal W), h ∉ p) ∧
      (ιCO C O).app W a * (COo C O).toScheme.presheaf.map (homOfLE le_top).op
        (gCO C O g - (ιCO C O ≫ π).appTop l) = (ιCO C O).app W h := by
  obtain ⟨W, hxW, u, v, hu, hv, huv⟩ := exists_bridge hufd hf hfin x
  have hP := mem_support_iff_germ (effI (div X f)) hxW hu
  have hN := mem_support_iff_germ (effI (-div X f)) hxW hv
  have key : ∀ h : Γ(X, W), algebraMap _ X.functionField (X.presheaf.germ W x hxW (u - v)) *
      (f / (f - 1) - n) = algebraMap _ X.functionField (X.presheaf.germ W x hxW h) →
      (ιCO C O).app W (u - v) * (COo C O).toScheme.presheaf.map (homOfLE le_top).op
        (gCO C O g - (ιCO C O ≫ π).appTop l) = (ιCO C O).app W h := by
    intro h hK
    refine hid_of_res π C O g l W _ _ ?_
    have hηW : genericPoint X ∈ (W : X.Opens) :=
      ((genericPoint_spec X).mem_open_set_iff W.1.isOpen).mpr ⟨x, trivial, hxW⟩
    haveI : Nonempty (W : X.Opens) := ⟨⟨x, hxW⟩⟩
    haveI : Nonempty O := ⟨⟨_, hO⟩⟩
    have hg' := hg _ hO
    apply res_eq_of_germ (genericPoint X) (show genericPoint X ∈ O ⊓ (W : X.Opens) from ⟨hO, hηW⟩)
    simp only [map_sub, Scheme.algebraMap_germ_eq_germToFunctionField] at hK hg'
    simp only [hl, map_intCast, map_mul, map_sub, TopCat.Presheaf.germ_res_apply,
      Scheme.algebraMap_germ_eq_germToFunctionField]
    rw [hg']
    exact hK
  rcases hJ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [Scheme.IdealSheafData.support_sup] at hx
    refine ⟨W, hxW, u - v, u, ?_, ?_, key u ?_⟩
    · rw [map_sub]
      exact isUnit_sub_of_nonunit (hP.mp hx.1) (not_not.mp (mt hN.mpr (hCPN x hx.2 hx.1)))
    · intro p hp hup
      exact not_le_of_ass C _ (fun ξ hξ => (hAss ξ hξ).1) W p hp
        (by rw [hu]; exact (Ideal.span_singleton_le_iff_mem p).2 hup)
    · simp only [map_sub]
      exact pencil_K hf1 _ huv (by simp)
  · rw [Scheme.IdealSheafData.support_sup] at hx
    refine ⟨W, hxW, u - v, v, ?_, ?_, key v ?_⟩
    · have h2 : IsUnit (X.presheaf.germ W x hxW u) :=
        not_not.mp (mt hP.mpr (fun hp => hCPN x hx.2 hp hx.1))
      rw [map_sub, ← neg_sub]
      exact (isUnit_sub_of_nonunit (hN.mp hx.1) h2).neg
    · intro p hp hvp
      exact not_le_of_ass C _ (fun ξ hξ => (hAss ξ hξ).2) W p hp
        (by rw [hv]; exact (Ideal.span_singleton_le_iff_mem p).2 hvp)
    · simp only [map_sub]
      exact pencil_K hf1 _ huv (by push_cast; ring)

/-- `flat_famL`'s non-zero-divisor hypothesis at a point of the fibre. -/
theorem hy_pencil (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {f : X.functionField} (hf : f ≠ 0) (hf1 : f ≠ 1) (hfin : (Function.support (div X f)).Finite)
    (g : Γ(X, O)) (hO : genericPoint X ∈ O)
    (hg : ∀ x (hx : x ∈ O),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ O x hx g) = f / (f - 1))
    (hCPN : ∀ y, y ∈ C.support → y ∈ (effI (div X f)).support → y ∉ (effI (-div X f)).support)
    (hAss : ∀ ξ ∈ assSet C, ξ ∉ (effI (div X f)).support ∧ ξ ∉ (effI (-div X f)).support)
    (J : X.IdealSheafData) (n : ℤ)
    (hJ : J = effI (div X f) ⊔ C ∧ n = 0 ∨ J = effI (-div X f) ⊔ C ∧ n = 1)
    (l : Γ(S, ⊤)) (hl : l = n) (x : (COo C O).toScheme) (hxJ : ιCO C O x ∈ J.support) :
    ∀ b : (COo C O).toScheme.presheaf.stalk x,
      (COo C O).toScheme.presheaf.germ ⊤ x trivial
        (gCO C O g - (ιCO C O ≫ π).appTop l) * b = 0 → b = 0 := by
  obtain ⟨W, hxW, a, h, hu, hh, hid⟩ :=
    pencil_chart2 π C O hufd hf hf1 hfin g hO hg hCPN hAss J n hJ l hl _ hxJ
  intro b hb
  have hx : x ∈ ιCO C O ⁻¹ᵁ (W : X.Opens) := hxW
  have e := congrArg ((COo C O).toScheme.presheaf.germ _ x hx) hid
  rw [map_mul, TopCat.Presheaf.germ_res_apply] at e
  have hua : IsUnit ((COo C O).toScheme.presheaf.germ _ x hx ((ιCO C O).app W a)) := by
    have e2 := Scheme.Hom.germ_stalkMap_apply (ιCO C O) (W : X.Opens) x hx a
    have h3 := hu.map ((ιCO C O).stalkMap x).hom
    rw [e2] at h3
    exact h3
  apply nzd_germ_CO C O W hh x hx b
  rw [← e, mul_assoc, hb, mul_zero]

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- `flat_famL`'s maximal-ideal hypothesis at a point of the fibre. -/
theorem hm_pencil (g : Γ(X, O)) (l : Γ(S, ⊤)) (J : X.IdealSheafData)
    (m : J.subscheme ⟶ (COo C O).toScheme) (hm : m ≫ ιCO C O = J.subschemeι)
    (hg : m.appTop (gCO C O g) = (J.subschemeι ≫ π).appTop l) (y : J.subscheme) :
    (COo C O).toScheme.presheaf.germ ⊤ (m y) trivial
      (gCO C O g - (ιCO C O ≫ π).appTop l) ∈ maximalIdeal _ := by
  have e : (m.stalkMap y).hom ((COo C O).toScheme.presheaf.germ ⊤ (m y) trivial
      (gCO C O g - (ιCO C O ≫ π).appTop l)) = 0 := by
    refine (Scheme.Hom.germ_stalkMap_apply m ⊤ y trivial _).trans ?_
    have h2 : m.app ⊤ ((ιCO C O ≫ π).appTop l) = (J.subschemeι ≫ π).appTop l := by
      rw [← hm]
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Category.assoc]
      rfl
    rw [map_sub, h2, show m.app ⊤ (gCO C O g) = _ from hg]
    exact (congrArg _ (sub_self _)).trans (map_zero _)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h3 := hu.map (m.stalkMap y).hom
  rw [e] at h3
  exact not_isUnit_zero h3

end Chart

section Len

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [IsProper A.hom] [IsIntegral A.left]
  [IsLocallyNoetherian A.left]

lemma finite_subscheme {X : Scheme.{u}} (J : X.IdealSheafData) (h : (J.support : Set X).Finite) :
    Finite J.subscheme := by
  have hi : Function.Injective J.subschemeι := J.subschemeι.isEmbedding.injective
  refine Set.finite_univ_iff.mp (Set.Finite.of_finite_image (h.subset ?_) hi.injOn)
  rintro _ ⟨z, -, rfl⟩
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- **The pencil**: the zeros and the poles of `f` meet `C` in subschemes of the same length,
when `C` misses their common points and has no associated point on them. -/
theorem len_pencil (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    {f : A.left.functionField} (hf : f ≠ 0) (hf1 : f ≠ 1)
    (hfin : (Function.support (div A.left f)).Finite) (C : A.left.IdealSheafData)
    (hCPN : ∀ y, y ∈ C.support → y ∈ (effI (div A.left f)).support →
      y ∉ (effI (-div A.left f)).support)
    (hAss : ∀ ξ ∈ assSet C,
      ξ ∉ (effI (div A.left f)).support ∧ ξ ∉ (effI (-div A.left f)).support)
    (hfin0 : ((effI (div A.left f) ⊔ C).support : Set A.left).Finite)
    (hfin1 : ((effI (-div A.left f) ⊔ C).support : Set A.left).Finite) :
    len A (effI (div A.left f) ⊔ C) = len A (effI (-div A.left f) ⊔ C) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := { }
  have : IsLocallyNoetherian (Ln (Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian (prL (Spec (.of k)))
  obtain ⟨O, g, hg, hreg⟩ := exists_regOpen (f / (f - 1))
  have hO : genericPoint A.left ∈ O := hreg _ (mem_range_generic _ _ rfl)
  have : TopologicalSpace.NoetherianSpace (COo C O).toScheme := 
    (C.subschemeι.isEmbedding.comp (COo C O).ι.isEmbedding).isInducing.noetherianSpace
  let σ : k ≃+* Γ(Spec (.of k), ⊤) := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm
  have hfib : ∀ (J : A.left.IdealSheafData) (n : ℤ),
      (J = effI (div A.left f) ⊔ C ∧ n = 0 ∨ J = effI (-div A.left f) ⊔ C ∧ n = 1) →
      (J.support : Set A.left).Finite →
      ∃ m : J.subscheme ⟶ (COo C O).toScheme,
        IsPullback (m ≫ (gam C O g).toImage) (J.subschemeι ≫ A.hom) (famL A.hom C O g)
          (ptL (σ (n : k))) ∧
        ((famL A.hom C O g) ⁻¹' {ptL (σ (n : k)) (pt0 k)}).Finite ∧
        ∀ z, famL A.hom C O g z = ptL (σ (n : k)) (pt0 k) →
          ((famL A.hom C O g).stalkMap z).hom.Flat := by
    intro J n hJ hJf
    have hl : σ (n : k) = (n : Γ(Spec (.of k), ⊤)) := map_intCast σ n
    have hCJ : C ≤ J := by rcases hJ with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact le_sup_right
    have hJO := pencil_supp_le hufd hf hf1 hfin hreg hCPN J n hJ
    have hgm := pencil_hg A.hom C O hufd hf hf1 hfin g hg hCPN J n hJ hCJ hJO _ hl
    have hpb := isPullback_fibre A.hom C O g _ J _ (mCO_ιCO C O J hCJ hJO) hgm
      (pencil_H A.hom C O hufd hf hf1 hfin g hO hg J n hJ _ hl)
    have : Finite J.subscheme := finite_subscheme J hJf
    refine ⟨mCO C O J hCJ hJO, hpb, (Set.finite_range _).subset (preimage_subset_range hpb _),
      fun z hz => ?_⟩
    obtain ⟨y, rfl⟩ := preimage_subset_range hpb (pt0 k) hz
    have hxJ : ιCO C O (mCO C O J hCJ hJO y) ∈ J.support := by
      rw [← Scheme.Hom.comp_apply, mCO_ιCO]
      show J.subschemeι y ∈ (J.support : Set A.left)
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact flat_famL A.hom C O σ g (n : k) _
      (hy_pencil A.hom C O hufd hf hf1 hfin g hO hg hCPN hAss J n hJ _ hl _ hxJ)
      (hm_pencil A.hom C O g _ J _ (mCO_ιCO C O J hCJ hJO) hgm y)
  obtain ⟨m0, h0, hfin0', hflat0⟩ := hfib _ 0 (Or.inl ⟨rfl, rfl⟩) hfin0
  obtain ⟨m1, h1, hfin1', hflat1⟩ := hfib _ 1 (Or.inr ⟨rfl, rfl⟩) hfin1
  exact finrank_eq_of_fibres (famL A.hom C O g) _ _ hfin0' hfin1' hflat0 hflat1 _ _ _ h0
    (fun s => by rw [Subsingleton.elim (α := Spec (.of k)) s (pt0 k)]) _ _ _ h1
    (fun s => by rw [Subsingleton.elim (α := Spec (.of k)) s (pt0 k)]) (pt0 k) (pt0 k)

end Len

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Pen6 =====
section

/-!
# S4-IntersectB, file Pen6: transport along isomorphisms (L34, B4)

* `flat_isFinite_len`: a closed subscheme with finite support inside an affine open is finite
  and flat over `k`.
* `len_comap_iso`, `len_comap_iso'`: the length is unchanged by pulling back along an
  automorphism over `Spec k`.
* `assSet_comap_iso`: associated points move with an isomorphism.
(Pullback of ideal sheaves preserves `⊔` for every morphism: Mathlib's
`Scheme.IdealSheafData.comap_sup`.)
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Len

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- A closed subscheme with finite support inside an affine open is finite and flat over `k`. -/
theorem flat_isFinite_len [LocallyOfFiniteType A.hom] (J : A.left.IdealSheafData)
    (V : A.left.affineOpens) (hV : (J.support : Set A.left) ⊆ V)
    (hfin : (J.support : Set A.left).Finite) :
    Flat (J.subschemeι ≫ A.hom) ∧ IsFinite (J.subschemeι ≫ A.hom) := by
  letI := (algV A V).hom.toAlgebra
  obtain ⟨hmf, -⟩ := len_eq_finrank A J V hV hfin
  let f : Spec (.of (Γ(A.left, V) ⧸ J.ideal V)) ⟶ J.subscheme := J.subschemeCover.f V
  have hfo : IsOpenImmersion f := J.subschemeCover.map_prop V
  have hf : IsIso f := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨hfo, ⟨fun z => ?_⟩⟩
    have h2 := J.opensRange_subschemeCover_map V
    have hz : z ∈ J.subschemeι ⁻¹ᵁ (V : A.left.Opens) :=
      hV (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩)
    rw [← h2] at hz
    exact hz
  have hcomp : f ≫ J.subschemeι ≫ A.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    have h1 : f ≫ J.subschemeι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal V))) ≫
        V.2.fromSpec :=
      (J.subschemeCover_map_subschemeι V).trans (J.glueDataObjι_ι V)
    rw [← Category.assoc, h1, Category.assoc, ← algV_spec, ← Spec.map_comp]
    rfl
  have hg : J.subschemeι ≫ A.hom = inv f ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    rw [← hcomp, IsIso.inv_hom_id_assoc]
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V)))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]; infer_instance
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V)))) := by
    rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]; exact hmf
  rw [hg]
  exact ⟨inferInstance, inferInstance⟩

/-- (T2) The length is unchanged by pulling back along an automorphism over `Spec k`. -/
theorem len_comap_iso [LocallyOfFiniteType A.hom] (J : A.left.IdealSheafData)
    (V : A.left.affineOpens) (hV : (J.support : Set A.left) ⊆ V)
    (hfin : (J.support : Set A.left).Finite) (e : A.left ⟶ A.left) [IsIso e]
    (he : e ≫ A.hom = A.hom) : len A (J.comap e) = len A J := by
  obtain ⟨h1, h2⟩ := flat_isFinite_len A J V hV hfin
  have hc : (J.comap e).subschemeι ≫ A.hom =
      ((J.comapIso e).hom ≫ pullback.snd e J.subschemeι) ≫ J.subschemeι ≫ A.hom := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst J e]
    simp only [Category.assoc]
    rw [← pullback.condition_assoc, he]
  show Scheme.Hom.finrank _ (pt0 k) = Scheme.Hom.finrank _ (pt0 k)
  rw [hc, Scheme.Hom.finrank_comp_left_of_isIso]

/-- (T2') The same on a group scheme over an algebraically closed field (no chart needed). -/
theorem len_comap_iso' [GrpObj A] [IsAlgClosed k] [LocallyOfFiniteType A.hom]
    [IrreducibleSpace A.left] (J : A.left.IdealSheafData)
    (hfin : (J.support : Set A.left).Finite) (e : A.left ⟶ A.left) [IsIso e]
    (he : e ≫ A.hom = A.hom) : len A (J.comap e) = len A J := by
  obtain ⟨V, hV⟩ := exists_affine_mem A hfin.toFinset
  exact len_comap_iso A J V (fun x hx => hV x (hfin.mem_toFinset.mpr hx)) hfin e he

end Len

section AssIso

/-- (T3) Associated points move with an isomorphism. -/
theorem assSet_comap_iso {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (C : Y.IdealSheafData)
    (e : X ⟶ Y) [IsIso e] (x : X) (hx : x ∈ assSet (C.comap e)) : e x ∈ assSet C := by
  obtain ⟨V, hxV, hA⟩ := hx
  let V' : Y.affineOpens := ⟨e ''ᵁ V, V.2.image_of_isOpenImmersion e⟩
  have hx' : e x ∈ (V' : Y.Opens) := ⟨x, hxV, rfl⟩
  refine ⟨V', hx', ?_⟩
  let φ := (e.appIso V.1).commRingCatIsoToRingEquiv
  letI : Algebra Γ(Y, V') Γ(X, V) := φ.toRingHom.toAlgebra
  haveI : IsNoetherianRing Γ(Y, V') := IsLocallyNoetherian.component_noetherian V'
  haveI : IsLocalization (⊥ : Submonoid Γ(Y, V')) Γ(X, V) := by
    haveI : IsLocalization (⊥ : Submonoid Γ(Y, V')) Γ(Y, V') := IsLocalization.self bot_le
    exact IsLocalization.isLocalization_of_algEquiv ⊥ (AlgEquiv.ofRingEquiv (f := φ) fun _ => rfl)
  have hI : (C.comap e).ideal V = (C.ideal V').map (algebraMap Γ(Y, V') Γ(X, V)) := by
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    exact (Ideal.map_comap_of_equiv φ).symm
  have hP : (V'.2.primeIdealOf ⟨e x, hx'⟩).asIdeal =
      (V.2.primeIdealOf ⟨x, hxV⟩).asIdeal.comap (algebraMap Γ(Y, V') Γ(X, V)) := by
    ext a
    rw [Ideal.mem_comap, ← not_iff_not]
    refine (mem_basicOpen_iff_primeIdealOf V'.2 (e x) hx' a).symm.trans
      (Iff.trans ?_ (mem_basicOpen_iff_primeIdealOf V.2 x hxV _))
    have h1 := Scheme.image_basicOpen e (U := V.1) (algebraMap Γ(Y, V') Γ(X, V) a)
    have h2 : (e.appIso V.1).inv (algebraMap Γ(Y, V') Γ(X, V) a) = a := by
      simp [φ, RingHom.algebraMap_toAlgebra]
    rw [h2] at h1
    rw [← h1]
    exact e.isOpenEmbedding.injective.mem_set_image
  unfold IsAssPt at hA ⊢
  rw [hI] at hA
  rw [hP]
  exact (ass_localization ⊥ (C.ideal V') _).mpr hA

end AssIso

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Pen7 =====
section

/-!
# S4-IntersectB, file Pen7: generic translates of a small configuration do not meet (L34, B4)

* `exists_empty_inter`: one cut more than the height bound empties an intersection.
* `mem_range_famP_iff`: a parameter lies in the image of the family exactly when the translated
  intersection is nonempty.
* `exists_open_empty`: if the slot-`0` support has height `< n`, generic translates of
  `X0, E 0, …, E (n-1)` have empty intersection.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits
  TopologicalSpace

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section EmptyTop

variable {X : Scheme.{u}} [NoetherianSpace X]

/-- One cut more than the height bound empties the intersection. -/
theorem exists_empty_inter {α : Type*} (m : ℕ) (H : ℕ → α → Set X)
    (hHc : ∀ i a, IsClosed (H i a)) (hH : ∀ i (S : Finset X), ∃ a, ∀ t ∈ S, t ∉ H i a)
    (S0 : Finset X) (hS0 : ∀ t ∈ S0, Order.height t + 1 ≤ m) :
    ∃ a : ℕ → α, (⋃ t ∈ S0, closure {t}) ∩ (⋂ i < m, H i (a i)) = ∅ := by
  classical
  cases m with
  | zero =>
    obtain ⟨a0, -⟩ := hH 0 ∅
    refine ⟨fun _ => a0, ?_⟩
    have hS : S0 = ∅ := Finset.eq_empty_of_forall_notMem fun t ht => by
      have h := hS0 t ht
      simp at h
    subst hS
    simp
  | succ m =>
    have hS0' : ∀ t ∈ S0, Order.height t ≤ m := fun t ht => by
      have h := hS0 t ht
      push_cast at h
      exact (WithTop.add_le_add_iff_right ENat.one_ne_top).mp h
    obtain ⟨a, S, hsub, hht⟩ := gp_aux m H hHc hH S0 hS0' m le_rfl
    obtain ⟨b, hb⟩ := hH m S
    refine ⟨Function.update a m b, Set.eq_empty_of_forall_notMem fun x hx => ?_⟩
    obtain ⟨hx0, hx⟩ := hx
    have hx' : x ∈ ⋂ i < m, H i (a i) := Set.mem_iInter₂.2 fun i hi => by
      have := Set.mem_iInter₂.1 hx i (Nat.lt_succ_of_lt hi)
      rwa [Function.update_of_ne (Nat.ne_of_lt hi)] at this
    have hxm : x ∈ H m b := by
      have := Set.mem_iInter₂.1 hx m (Nat.lt_succ_self m)
      rwa [Function.update_self] at this
    have hxS := hsub ⟨hx0, hx'⟩
    simp only [Set.mem_iUnion, exists_prop] at hxS
    obtain ⟨t, ht, hxt⟩ := hxS
    have h0 : Order.height t = 0 := by
      have h1 := hht t ht
      by_contra h
      have h3 : (1 : ℕ∞) + m ≤ Order.height t + m := by
        gcongr
        exact Order.one_le_iff_ne_zero.mpr h
      have h2 := h3.trans h1
      norm_cast at h2
      omega
    rw [(isClosed_singleton_of_height_eq_zero t h0).closure_eq, Set.mem_singleton_iff] at hxt
    exact hb t ht (hxt ▸ hxm)

end EmptyTop

section Empty

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- A parameter lies in the image of the family iff the translated intersection is nonempty. -/
theorem mem_range_famP_iff {g : ℕ} (D : Fin g → A.left.IdealSheafData)
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A g) :
    pt (Pw A g) c ∈ Set.range (famP A D) ↔
      ((Zid A D (fun i => c ≫ proj A g i)).support : Set A.left).Nonempty := by
  have hP := RamanujanPetersson.IntersectA.isPullback_fibre A D c
  rw [← comap_famI, ← Scheme.IdealSheafData.range_subschemeι]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := famP A D) (g := c.left)
      w (pt0 k) hw
    exact ⟨_, hP.isoPullback.inv z, rfl⟩
  · rintro ⟨_, z, rfl⟩
    refine ⟨((((famI A D).comapIso (sec A c).left).hom ≫ pullback.snd _ _) z), ?_⟩
    rw [← Scheme.Hom.comp_apply, hP.w, Scheme.Hom.comp_apply]
    show c.left _ = c.left (pt0 k)
    exact congrArg (fun p : Spec (.of k) => c.left p) (@Subsingleton.elim (Spec (.of k)) _ _ _)

variable [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left]

/-- (G1) If the slot-`0` support has height `< n`, generic translates have empty intersection. -/
theorem exists_open_empty (n : ℕ) (X0 : A.left.IdealSheafData) (E : Fin n → A.left.IdealSheafData)
    (hE : ∀ j, (E j).support ≠ ⊤)
    (h0 : ∀ x ∈ (X0.support : Set A.left), Order.height x + 1 ≤ n) :
    ∃ U : Set (Pw A (n + 1)).left, IsOpen U ∧ U.Nonempty ∧
      ∀ c : 𝟙_ (Over (Spec (.of k))) ⟶ Pw A (n + 1), pt (Pw A (n + 1)) c ∈ U →
        ((Zid A (Fin.cons X0 E : Fin (n + 1) → A.left.IdealSheafData)
          (fun i => c ≫ proj A (n + 1) i)).support : Set A.left) = ∅ := by
  classical
  have := noetherianSpace_left A
  have := isProper_famP A (Fin.cons X0 E : Fin (n + 1) → A.left.IdealSheafData)
  refine ⟨(Set.range (famP A (Fin.cons X0 E : Fin (n + 1) → A.left.IdealSheafData)))ᶜ,
    (Scheme.Hom.isClosedMap _).isClosed_range.isOpen_compl, ?_, fun c hc => ?_⟩
  · let H : ℕ → (𝟙_ (Over (Spec (.of k))) ⟶ A) → Set A.left := fun i a =>
      if h : i < n then (transl A a).left ⁻¹' (E ⟨i, h⟩).support else ∅
    have hHc : ∀ i a, IsClosed (H i a) := by
      intro i a
      by_cases h : i < n
      · simp only [H, dif_pos h]
        exact (E ⟨i, h⟩).support.isClosed.preimage (transl A a).left.continuous
      · simp only [H, dif_neg h]
        exact isClosed_empty
    have hH : ∀ i (S : Finset A.left), ∃ a, ∀ y ∈ S, y ∉ H i a := by
      intro i S
      by_cases h : i < n
      · have hne : ((E ⟨i, h⟩).support : Set A.left) ≠ Set.univ := fun he =>
          hE ⟨i, h⟩ (TopologicalSpace.Closeds.ext (by rw [he]; rfl))
        obtain ⟨a, ha⟩ := exists_good A S _ (E ⟨i, h⟩).support.isClosed hne
        exact ⟨a, fun y hy => by simp only [H, dif_pos h]; exact ha y hy⟩
      · exact ⟨1, fun y _ => by simp only [H, dif_neg h]; exact Set.notMem_empty y⟩
    obtain ⟨S0, hS0m, hS0⟩ := exists_finset_closure (X0.support : Set A.left) X0.support.isClosed
    obtain ⟨a, ha⟩ := exists_empty_inter n H hHc hH S0 (fun t ht => h0 t (hS0m t ht))
    let a' : Fin (n + 1) → (𝟙_ (Over (Spec (.of k))) ⟶ A) := Fin.cons 1 (fun j => a j)
    refine ⟨pt (Pw A (n + 1)) (ptOf A (n + 1) a'), fun hmem => ?_⟩
    obtain ⟨y, hy⟩ := (mem_range_famP_iff A _ _).mp hmem
    have he : (fun i => ptOf A (n + 1) a' ≫ proj A (n + 1) i) = a' :=
      funext (ptOf_proj A (n + 1) a')
    rw [he, coe_support_Zid, Set.mem_iInter] at hy
    refine (Set.eq_empty_iff_forall_notMem.mp ha) y ⟨?_, Set.mem_iInter₂.2 fun i hi => ?_⟩
    · rw [← hS0]
      simpa [a', transl_one] using hy 0
    · simp only [H, dif_pos hi]
      have h := hy (Fin.succ ⟨i, hi⟩)
      simp only [a', Fin.cons_succ, Fin.val_mk] at h
      exact h
  · by_contra hne
    exact hc ((mem_range_famP_iff A _ c).mpr (Set.nonempty_iff_ne_empty.mpr hne))

end Empty

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Pen8 =====
section

/-!
# S4-IntersectB, file Pen8: the pencil for generic translates (L34, B4)

* `mem_support_prod`, `mem_support_effI`: points of the support of a product and of `effI D`.
* `height_add_one_le_of_lt`, `height_effI_inf`: the common points of the zeros and the poles of
  `f` have height `< n` when every point has height `≤ n + 1`.
* `len_pencil_comap`: `len_pencil` transported along an automorphism over `k`.
* `inum_pencil`: `inum (effI (div f), E) = inum (effI (-div f), E)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits
  TopologicalSpace

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Height

variable {X : Scheme.{u}}

lemma mem_support_prod {β : Type*} (s : Finset β) (I : β → X.IdealSheafData) {x : X}
    (hx : x ∈ ((∏ z ∈ s, I z).support : Set X)) : ∃ z ∈ s, x ∈ ((I z).support : Set X) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.support_top] at hx
    simp at hx
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.IdealSheafData.support_mul, Closeds.coe_sup] at hx
    rcases hx with h | h
    · exact ⟨a, Finset.mem_insert_self _ _, h⟩
    · obtain ⟨z, hz, h⟩ := ih h
      exact ⟨z, Finset.mem_insert_of_mem hz, h⟩

lemma mem_support_effI (D : AlgebraicCycle X ℤ) (hfin : (Function.support D).Finite) {x : X}
    (hx : x ∈ ((effI D).support : Set X)) : ∃ z, 0 < D z ∧ x ∈ closure {z} := by
  rw [effI_eq_prod D hfin.toFinset fun z hz => hfin.mem_toFinset.mpr hz] at hx
  obtain ⟨z, -, hz⟩ := mem_support_prod _ _ hx
  by_cases h : (D z).toNat = 0
  · rw [h, pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top] at hz
    simp at hz
  · rw [(primeI z).support_pow _ h, coe_support_primeI] at hz
    exact ⟨z, lt_of_not_ge fun h' => h (Int.toNat_eq_zero.mpr h'), hz⟩

lemma height_add_one_le_of_lt [IrreducibleSpace X] (n : ℕ)
    (hdim : ∀ x : X, Order.height x ≤ (n + 1 : ℕ)) {x y : X} (hxy : x < y)
    (hy : Order.coheight y = 1) : Order.height x + 1 ≤ n := by
  have hyη : y < genericPoint X := by
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (genericPoint_specializes y)) fun h => ?_
    have hmax : IsMax y := fun b _ => (Scheme.le_iff_specializes.mpr (genericPoint_specializes b)).trans h
    rw [Order.coheight_eq_zero.mpr hmax] at hy
    exact zero_ne_one hy
  have h4 : Order.height x + 1 + 1 ≤ (n : ℕ∞) + 1 :=
    calc Order.height x + 1 + 1 ≤ Order.height y + 1 := by
          gcongr; exact Order.height_add_one_le hxy
      _ ≤ Order.height (genericPoint X) := Order.height_add_one_le hyη
      _ ≤ ((n + 1 : ℕ) : ℕ∞) := hdim _
      _ = (n : ℕ∞) + 1 := Nat.cast_succ n
  exact (WithTop.add_le_add_iff_right ENat.one_ne_top).mp h4

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- The common points of the zeros and the poles of `f` have height `< n`. -/
lemma height_effI_inf (n : ℕ) (hdim : ∀ x : X, Order.height x ≤ (n + 1 : ℕ))
    (f : X.functionField) (hfin : (Function.support (div X f)).Finite) (x : X)
    (hx : x ∈ ((effI (div X f) ⊔ effI (-div X f)).support : Set X)) :
    Order.height x + 1 ≤ n := by
  rw [Scheme.IdealSheafData.support_sup, Closeds.coe_inf] at hx
  obtain ⟨z, hz, hxz⟩ := mem_support_effI _ hfin hx.1
  obtain ⟨w, hw, hxw⟩ := mem_support_effI _ (hfin.subset fun a ha => by simpa using ha) hx.2
  rw [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply] at hw
  have hle : ∀ y, x ∈ closure {y} → x ≤ y := fun y h =>
    Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr h)
  have hlt : ∀ y, x ∈ closure {y} → x ≠ y → x < y := fun y h hne =>
    lt_of_le_not_ge (hle y h) fun h' =>
      hne ((Scheme.le_iff_specializes.mp h').antisymm (Scheme.le_iff_specializes.mp (hle y h))).eq
  have h1 : ∀ y, div X f y ≠ 0 → Order.coheight y = 1 := fun y hy => div_mem_weilDivisors f y hy
  by_cases hxz' : x = z
  · subst hxz'
    exact height_add_one_le_of_lt n hdim (hlt w hxw fun h => by subst h; omega) (h1 w (by omega))
  · exact height_add_one_le_of_lt n hdim (hlt z hxz hxz') (h1 z (by omega))

end Height

section Pencil

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left] [IsLocallyNoetherian A.left]

/-- `len_pencil` transported along an automorphism `s` of `A` over `k`. -/
lemma len_pencil_comap (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    {f : A.left.functionField} (hf : f ≠ 0) (hf1 : f ≠ 1)
    (hfin : (Function.support (div A.left f)).Finite) (C : A.left.IdealSheafData)
    (s : A.left ⟶ A.left) [IsIso s] (hs : s ≫ A.hom = A.hom)
    (hemp : (((effI (div A.left f) ⊔ effI (-div A.left f)).comap s ⊔ C).support : Set A.left)
      = ∅)
    (hAss : ∀ ξ ∈ assSet C, s ξ ∉ ((effI (div A.left f)).support : Set A.left) ∧
      s ξ ∉ ((effI (-div A.left f)).support : Set A.left))
    (hfin0 : (((effI (div A.left f)).comap s ⊔ C).support : Set A.left).Finite)
    (hfin1 : (((effI (-div A.left f)).comap s ⊔ C).support : Set A.left).Finite) :
    len A ((effI (div A.left f)).comap s ⊔ C) = len A ((effI (-div A.left f)).comap s ⊔ C) := by
  have hse : ∀ y, s (inv s y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id] <;> rfl
  have hid (Y : A.left.IdealSheafData) : Y.comap s ⊔ C = (Y ⊔ C.comap (inv s)).comap s := by
    rw [Scheme.IdealSheafData.comap_sup, ← Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id,
      Scheme.IdealSheafData.comap_id]
  have hsurj : Function.Surjective s := fun y => ⟨inv s y, hse y⟩
  rw [hid, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage] at hemp hfin0 hfin1
  rw [hid, hid, len_comap_iso' A _ (hfin0.of_preimage hsurj) s hs,
    len_comap_iso' A _ (hfin1.of_preimage hsurj) s hs]
  refine len_pencil A hufd hf hf1 hfin _ (fun y hyC hyP hyN => ?_) (fun ξ hξ => ?_)
    (hfin0.of_preimage hsurj) (hfin1.of_preimage hsurj)
  · refine Set.eq_empty_iff_forall_notMem.mp hemp (inv s y) ?_
    rw [Set.mem_preimage, hse]
    simp only [Scheme.IdealSheafData.support_sup, Closeds.coe_inf, Set.mem_inter_iff]
    exact ⟨⟨hyP, hyN⟩, hyC⟩
  · have h := hAss (inv s ξ) (assSet_comap_iso C (inv s) ξ hξ)
    rwa [hse] at h

/-- **B4** for `inum`: the zeros and the poles of `f` have the same intersection number. -/
theorem inum_pencil (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    {f : A.left.functionField} (hf : f ≠ 0) (hf1 : f ≠ 1) (E : Fin n → A.left.IdealSheafData)
    (h1 : ∀ i, ((Fin.cons (effI (div A.left f)) E : Fin (n + 1) → A.left.IdealSheafData) i).support
      ≠ ⊤)
    (h2 : ∀ i, ((Fin.cons (effI (-div A.left f)) E : Fin (n + 1) → A.left.IdealSheafData) i).support
      ≠ ⊤) :
    inum A (n + 1) hdim (Fin.cons (effI (div A.left f)) E) h1 =
      inum A (n + 1) hdim (Fin.cons (effI (-div A.left f)) E) h2 := by
  have := isIntegral_Pw A (n + 1)
  have := isProper_Pw A (n + 1)
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hfin := support_finite_of_compact (div A.left f)
  have hE : ∀ j, (E j).support ≠ ⊤ := fun j => by simpa only [Fin.cons_succ] using h1 j.succ
  obtain ⟨U1, hU1o, hU1n, hU1⟩ := inum_spec A (n + 1) hdim _ h1
  obtain ⟨U2, hU2o, hU2n, hU2⟩ := inum_spec A (n + 1) hdim _ h2
  obtain ⟨U3, hU3o, hU3n, hU3⟩ := exists_open_empty A n
    (effI (div A.left f) ⊔ effI (-div A.left f)) E hE (height_effI_inf n hdim f hfin)
  have hUo : IsOpen (U1 ∩ U2 ∩ U3) := (hU1o.inter hU2o).inter hU3o
  obtain ⟨cs, hcs⟩ := exists_pt_mem (Pw A (n + 1)) (U1 ∩ U2 ∩ U3) hUo.isLocallyClosed
    (nonempty_preirreducible_inter (hU1o.inter hU2o) hU3o
      (nonempty_preirreducible_inter hU1o hU2o hU1n hU2n) hU3n)
  obtain ⟨C, hC⟩ : ∃ C : A.left.IdealSheafData,
      C = ⨆ j, (E j).comap (transl A (cs ≫ proj A (n + 1) j.succ)).left := ⟨_, rfl⟩
  have hEf := assSet_finite C
  have hPN : ((effI (div A.left f) * effI (-div A.left f)).support : Set A.left) ≠ Set.univ :=
    fun h => support_mul_ne_top (by simpa only [Fin.cons_zero] using h1 0)
      (by simpa only [Fin.cons_zero] using h2 0)
      (SetLike.coe_injective (h.trans Closeds.coe_top.symm))
  choose G hGo hGn hG using fun ξ => exists_open_good A ξ _
    (effI (div A.left f) * effI (-div A.left f)).support.isClosed hPN
  have hO : IsOpen ((slice A cs).left ⁻¹' (U1 ∩ U2 ∩ U3)) :=
    hUo.preimage (slice A cs).left.continuous
  have hOn : pt A (cs ≫ proj A (n + 1) 0) ∈ (slice A cs).left ⁻¹' (U1 ∩ U2 ∩ U3) := by
    show (slice A cs).left (pt A _) ∈ U1 ∩ U2 ∩ U3
    rw [← pt_comp, slice_self]; exact hcs
  obtain ⟨c0, hc0O, hc0G⟩ := exists_pt_mem A _
    (hO.inter (isOpen_biInter_finset fun ξ _ => hGo ξ)).isLocallyClosed
    (nonempty_preirreducible_inter hO (isOpen_biInter_finset fun ξ _ => hGo ξ) ⟨_, hOn⟩
      (nonempty_biInter_finset hEf.toFinset G (fun ξ _ => hGo ξ) fun ξ _ => hGn ξ))
  have hc : pt (Pw A (n + 1)) (c0 ≫ slice A cs) ∈ U1 ∩ U2 ∩ U3 := by rw [pt_comp]; exact hc0O
  have hZ (Y : A.left.IdealSheafData) :
      Zid A (Fin.cons Y E : Fin (n + 1) → A.left.IdealSheafData)
        (fun i => (c0 ≫ slice A cs) ≫ proj A (n + 1) i) = Y.comap (transl A c0).left ⊔ C := by
    rw [Zid_cons, hC, pt_slice_zero]
    simp only [pt_slice_succ]
  have := isIso_translL A c0
  obtain ⟨hfin1, hl1⟩ := hU1 _ hc.1.1
  obtain ⟨hfin2, hl2⟩ := hU2 _ hc.1.2
  have hemp := hU3 _ hc.2
  rw [hZ] at hfin1 hl1 hfin2 hl2 hemp
  rw [← hl1, ← hl2]
  refine len_pencil_comap A hufd hf hf1 hfin C _ (Over.w (transl A c0)) hemp (fun ξ hξ => ?_)
    hfin1 hfin2
  have h := hG ξ c0 (Set.mem_iInter₂.1 hc0G ξ (hEf.mem_toFinset.2 hξ))
  rw [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, Set.mem_union] at h
  exact not_or.mp h

end Pencil

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectB_Pen9 =====
section

/-!
# S4-IntersectB, file Pen9: the intersection form respects linear equivalence (L34, B4)

* `support_effI_ne_top`: `effI D` of a Weil divisor has a proper support.
* `inumZ_cons_effI'`: slot-`0` expansion of `effI D` for any Weil divisor (positive parts).
* `inumZ_pencil`: `inumZ (effI (div f), E) = inumZ (effI (-div f), E)`.
* `iform_cons`: slot-`0` expansion of `iform`.
* `iform_cons_div`, `iform_update_div`: `iform` vanishes with a principal divisor in any slot.
* `iform_linEquiv`, `iform_linEquiv_all`: `iform` is invariant under linear equivalence.
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory Limits
  TopologicalSpace

namespace RamanujanPetersson.IntersectB

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA

section Top

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

lemma support_effI_ne_top (D : AlgebraicCycle X ℤ) (hW : D ∈ weilDivisors X)
    (hfin : (Function.support D).Finite) : (effI D).support ≠ ⊤ := by
  rw [effI_eq_prod D hfin.toFinset fun z hz => hfin.mem_toFinset.mpr hz,
    ← _root_.mul_one (∏ z ∈ hfin.toFinset, primeI z ^ (D z).toNat),
    Scheme.IdealSheafData.one_eq_top]
  refine support_prod_mul_ne_top primeI (fun z => (D z).toNat) _
    (fun z hz => support_primeI_ne_top (hW z (hfin.mem_toFinset.mp hz))) ?_
  intro h
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ((⊤ : X.IdealSheafData).support : Set X) := by
    rw [h]; exact Set.mem_univ _
  simp [Scheme.IdealSheafData.support_top] at hx

end Top

section Iform

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left] [IsLocallyNoetherian A.left]

/-- Slot-`0` expansion of `effI D` for any Weil divisor `D` (only `D⁺` contributes). -/
theorem inumZ_cons_effI' (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ)) (D : AlgebraicCycle A.left ℤ)
    (hW : D ∈ weilDivisors A.left) (E : Fin n → A.left.IdealSheafData) :
    inumZ A (n + 1) hdim (Fin.cons (effI D) E : Fin (n + 1) → A.left.IdealSheafData) =
      ∑ᶠ z, ((D z).toNat : ℤ) *
        inumZ A (n + 1) hdim (Fin.cons (primeI z) E : Fin (n + 1) → A.left.IdealSheafData) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hfin := support_finite_of_compact D
  have hs : Function.support D ⊆ hfin.toFinset := fun z hz => hfin.mem_toFinset.mpr hz
  have h1 : ∀ z ∈ hfin.toFinset, Order.coheight z = 1 := fun z hz =>
    hW z (hfin.mem_toFinset.mp hz)
  have htop : (⊤ : A.left.IdealSheafData).support ≠ ⊤ := by
    intro h
    obtain ⟨x⟩ : Nonempty A.left := inferInstance
    have hx : x ∈ ((⊤ : A.left.IdealSheafData).support : Set A.left) := by
      rw [h]; exact Set.mem_univ _
    simp [Scheme.IdealSheafData.support_top] at hx
  rw [effI_eq_prod D _ hs, ← _root_.mul_one (∏ z ∈ hfin.toFinset, primeI z ^ (D z).toNat),
    Scheme.IdealSheafData.one_eq_top,
    inumZ_prod_mul A n hdim primeI (fun z => (D z).toNat) E _
      (fun z hz => support_primeI_ne_top (h1 z hz)) (fun z hz => isLocPrin_primeI hufd (h1 z hz))
      htop, inumZ_cons_top, add_zero,
    finsum_eq_sum_of_support_subset (fun z => ((D z).toNat : ℤ) *
        inumZ A (n + 1) hdim (Fin.cons (primeI z) E : Fin (n + 1) → A.left.IdealSheafData))
      (fun z hz => hs fun h => left_ne_zero_of_mul hz (by simp [h]))] <;> rfl

/-- **B4** for `inumZ`: zeros and poles of `f` give the same intersection number. -/
theorem inumZ_pencil (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ)) {f : A.left.functionField}
    (hf : f ≠ 0) (E : Fin n → A.left.IdealSheafData) :
    inumZ A (n + 1) hdim (Fin.cons (effI (div A.left f)) E : Fin (n + 1) → A.left.IdealSheafData) =
      inumZ A (n + 1) hdim
        (Fin.cons (effI (-div A.left f)) E : Fin (n + 1) → A.left.IdealSheafData) := by
  by_cases hf1 : f = 1
  · subst hf1
    rw [RamanujanPetersson.JacDivisors.div_one, neg_zero]
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  by_cases hE : ∀ j, (E j).support ≠ ⊤
  · have hW := div_mem_weilDivisors f
    have h1 := cons_support_ne_top A
      (support_effI_ne_top _ hW (support_finite_of_compact _)) hE
    have h2 := cons_support_ne_top A
      (support_effI_ne_top _ (neg_mem hW) (support_finite_of_compact _)) hE
    rw [inumZ_of A _ hdim _ h1, inumZ_of A _ hdim _ h2, inum_pencil A n hdim hufd hf hf1 E h1 h2]
  · rw [inumZ_cons_of_not A n hdim hE, inumZ_cons_of_not A n hdim hE]

/-- Slot-`0` expansion of the intersection form. -/
theorem iform_cons (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ))
    (D : AlgebraicCycle A.left ℤ) (E : Fin n → AlgebraicCycle A.left ℤ) :
    iform A (n + 1) hdim (Fin.cons D E) = ∑ᶠ z' : Fin n → A.left, (∏ j, E j (z' j)) *
      ∑ᶠ a, D a * inumZ A (n + 1) hdim
        (Fin.cons (primeI a) fun j => primeI (z' j) : Fin (n + 1) → A.left.IdealSheafData) := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  let e : (Fin n → A.left) × A.left ≃ (Fin (n + 1) → A.left) :=
    (Equiv.prodComm _ _).trans (Fin.consEquiv fun _ => A.left)
  have hfin := finite_support_prod
    (fun i => ⇑((Fin.cons D E : Fin (n + 1) → AlgebraicCycle A.left ℤ) i))
    (fun i => support_finite_of_compact _) (fun z => inumZ A (n + 1) hdim fun i => primeI (z i))
  simp only [iform]
  rw [← finsum_comp_equiv e,
    finsum_curry _ ((hfin.preimage e.injective.injOn).subset fun x hx => hx)]
  refine finsum_congr fun z' => ?_
  rw [mul_finsum]
  refine finsum_congr fun a => ?_
  show (∏ i, (Fin.cons D E : Fin (n + 1) → AlgebraicCycle A.left ℤ) i
      ((Fin.cons a z' : Fin (n + 1) → A.left) i)) *
    inumZ A (n + 1) hdim (fun i => primeI ((Fin.cons a z' : Fin (n + 1) → A.left) i)) = _
  have hc : (fun i => primeI ((Fin.cons a z' : Fin (n + 1) → A.left) i)) =
      (Fin.cons (primeI a) fun j => primeI (z' j) : Fin (n + 1) → A.left.IdealSheafData) := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  rw [hc]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

/-- `iform` vanishes when slot `0` is a principal divisor. -/
theorem iform_cons_div (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ (n + 1 : ℕ)) {f : A.left.functionField}
    (hf : f ≠ 0) (E : Fin n → AlgebraicCycle A.left ℤ) :
    iform A (n + 1) hdim (Fin.cons (div A.left f) E) = 0 := by
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hW := div_mem_weilDivisors f
  have hfin := support_finite_of_compact (div A.left f)
  have key : ∀ E' : Fin n → A.left.IdealSheafData, ∑ᶠ a, div A.left f a *
      inumZ A (n + 1) hdim (Fin.cons (primeI a) E' : Fin (n + 1) → A.left.IdealSheafData) = 0 := by
    intro E'
    have hP := inumZ_cons_effI' A hufd n hdim _ hW E'
    have hN := inumZ_cons_effI' A hufd n hdim _ (neg_mem hW) E'
    have hsub : ∀ D : AlgebraicCycle A.left ℤ, (Function.support D).Finite →
        (Function.support fun a => ((D a).toNat : ℤ) *
          inumZ A (n + 1) hdim (Fin.cons (primeI a) E' : Fin (n + 1) → A.left.IdealSheafData)).Finite :=
      fun D hD => hD.subset fun a ha =>
        Function.mem_support.mpr fun h => left_ne_zero_of_mul ha (by simp [h])
    have e1 : ∀ a, div A.left f a *
        inumZ A (n + 1) hdim (Fin.cons (primeI a) E' : Fin (n + 1) → A.left.IdealSheafData) =
        ((div A.left f a).toNat : ℤ) *
          inumZ A (n + 1) hdim (Fin.cons (primeI a) E' : Fin (n + 1) → A.left.IdealSheafData) -
        (((-div A.left f) a).toNat : ℤ) *
          inumZ A (n + 1) hdim (Fin.cons (primeI a) E' : Fin (n + 1) → A.left.IdealSheafData) :=
      fun a => by
        rw [← sub_mul, Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply,
          Int.toNat_sub_toNat_neg]
    rw [finsum_congr e1, finsum_sub_distrib (hsub _ hfin) (hsub _ (support_finite_of_compact _)),
      ← hP, ← hN, inumZ_pencil A hufd n hdim hf E', sub_self]
  rw [iform_cons]
  exact finsum_eq_zero_of_forall_eq_zero fun z' => by rw [key, mul_zero]

/-- `iform` vanishes when any slot is a principal divisor. -/
theorem iform_update_div (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    (n : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ n) (D : Fin n → AlgebraicCycle A.left ℤ)
    (i : Fin n) {f : A.left.functionField} (hf : f ≠ 0) :
    iform A n hdim (Function.update D i (div A.left f)) = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    rw [← iform_perm A (m + 1) hdim _ (Equiv.swap 0 i), update_swap]
    exact iform_cons_div A hufd m hdim hf _

end Iform

end RamanujanPetersson.IntersectB


end

-- ===== S4.Def_RP_IntersectC_Rank =====
section

/-!
# S4-IntersectC, file Rank: ranks multiply in a finite flat tower over a field (L35 core)

* `finrank_eq_mul_of_flat`: `R` finite over a field `K`, `M` finite flat over `R` of rank `d` at every prime
  ⇒ `finrank K M = d * finrank K R` (semilocal freeness, `Module.free_of_flat_of_finrank_eq`).
* `finrank_comp_SpecMap`: the scheme form, for `g : W ⟶ Spec R` finite flat of rank `d` everywhere.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits TensorProduct

namespace RamanujanPetersson.IntersectC

/-- Ranks multiply: `finrank K M = d * finrank K R` for `M` finite flat of constant rank `d` over `R`. -/
theorem finrank_eq_mul_of_flat (K R M : Type u) [Field K] [CommRing R] [Algebra K R]
    [Module.Finite K R] [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]
    [Module.Finite R M] [Module.Flat R M] (d : ℕ)
    (hd : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = d) :
    Module.finrank K M = d * Module.finrank K R := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · haveI : Subsingleton M := Module.subsingleton R M
    simp [Module.finrank_zero_of_subsingleton]
  haveI : IsArtinianRing R := IsArtinianRing.of_finite K R
  have : Finite (MaximalSpectrum R) := inferInstance
  have hrk : ∀ P : MaximalSpectrum R, Module.finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M) = d := by
    intro P
    haveI : P.1.IsMaximal := P.2
    letI : Field (R ⧸ P.1) := Ideal.Quotient.field P.1
    calc Module.finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M)
        = Module.finrank P.1.ResidueField
            (P.1.ResidueField ⊗[R ⧸ P.1] ((R ⧸ P.1) ⊗[R] M)) :=
          (Module.finrank_baseChange).symm
      _ = Module.finrank P.1.ResidueField (P.1.ResidueField ⊗[R] M) :=
          (AlgebraTensorModule.cancelBaseChange R (R ⧸ P.1) P.1.ResidueField
            P.1.ResidueField M).finrank_eq
      _ = Module.rankAtStalk M ⟨P.1, P.2.isPrime⟩ := Ideal.finrank_fiber_eq_rankAtStalk P.1
      _ = d := hd _
  haveI : Module.Free R M := Module.free_of_flat_of_finrank_eq R M d hrk
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  have h1 : Module.finrank R M = d := by
    rw [← hd ⟨m, hm.isPrime⟩, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← Module.finrank_mul_finrank K R M, h1, mul_comm]

/-- The scheme form: a finite flat `g : W ⟶ Spec R` of rank `d` everywhere, `R` finite over `K`. -/
theorem finrank_comp_SpecMap {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    [Module.Finite K R] {W : Scheme.{u}} (g : W ⟶ Spec (.of R)) [Flat g] [IsFinite g] (d : ℕ)
    (hd : ∀ x, g.finrank x = d) (s : Spec (.of K)) :
    (g ≫ Spec.map (CommRingCat.ofHom (algebraMap K R))).finrank s = d * Module.finrank K R := by
  haveI : IsAffine W := isAffine_of_isAffineHom g
  let r : CommRingCat.of R ⟶ Γ(W, ⊤) := Spec.preimage (W.isoSpec.inv ≫ g)
  have hr : Spec.map r = W.isoSpec.inv ≫ g := Spec.map_preimage _
  letI : Algebra R Γ(W, ⊤) := r.hom.toAlgebra
  letI : Algebra K Γ(W, ⊤) := (r.hom.comp (algebraMap K R)).toAlgebra
  haveI : IsScalarTower K R Γ(W, ⊤) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hg' : g = W.isoSpec.hom ≫ Spec.map r := by rw [hr, Iso.hom_inv_id_assoc]
  haveI : IsFinite (Spec.map r) := by rw [hr]; infer_instance
  haveI : Flat (Spec.map r) := by rw [hr]; infer_instance
  have hfin : r.hom.Finite := (IsFinite.SpecMap_iff r).mp inferInstance
  have hflat : r.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  haveI : Module.Finite R Γ(W, ⊤) := hfin
  haveI : Module.Flat R Γ(W, ⊤) := hflat
  haveI : Module.Finite K Γ(W, ⊤) := Module.Finite.trans R _
  have hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk Γ(W, ⊤) p = d := by
    intro p
    have h1 := Scheme.Hom.finrank_SpecMap_algebraMap R Γ(W, ⊤) p
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap R Γ(W, ⊤))) = W.isoSpec.inv ≫ g := hr
    rw [h2, Scheme.Hom.finrank_comp_left_of_isIso] at h1
    rw [← h1]
    exact hd _
  have key := finrank_eq_mul_of_flat K R Γ(W, ⊤) d hrank
  have hcomp : g ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) =
      W.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(W, ⊤))) := by
    rw [hg', Category.assoc, ← Spec.map_comp]
    rfl
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap K Γ(W, ⊤)))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]; infer_instance
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K Γ(W, ⊤)))) := by
    rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]; infer_instance
  rw [hcomp, Scheme.Hom.finrank_comp_left_of_isIso]
  refine (Scheme.Hom.finrank_SpecMap_algebraMap K Γ(W, ⊤) s).trans ?_
  rw [Module.rankAtStalk_eq_finrank_of_free, key]
  rfl

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_IntersectC_Len =====
section

/-!
# S4-IntersectC, file Len: length under a finite flat endomorphism (L35, O2)

* `len_comap_flat`: if `φ : A ⟶ A` over `Spec k` is finite flat of constant rank `d`, then
  pulling back a closed subscheme with finite support multiplies its length by `d`.
* `finrank_eq_of_preconnected`: the rank of a finite flat finitely presented morphism to a
  preconnected scheme is constant.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.IntersectB

/-- The rank of a finite flat finitely presented morphism to a preconnected scheme is constant. -/
theorem finrank_eq_of_preconnected {X Y : Scheme.{u}} (φ : X ⟶ Y) [Flat φ] [IsFinite φ]
    [LocallyOfFinitePresentation φ] [PreconnectedSpace Y] (x y : Y) :
    φ.finrank x = φ.finrank y :=
  (Scheme.Hom.isLocallyConstant_finrank φ).apply_eq_of_preconnectedSpace x y

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- (O2) Pulling back along a finite flat endomorphism of constant rank `d` over `Spec k`
multiplies the length of a closed subscheme with finite support by `d`. -/
theorem len_comap_flat [LocallyOfFiniteType A.hom] (J : A.left.IdealSheafData)
    (V : A.left.affineOpens) (hV : (J.support : Set A.left) ⊆ V)
    (hfin : (J.support : Set A.left).Finite) (φ : A.left ⟶ A.left) [Flat φ] [IsFinite φ]
    (he : φ ≫ A.hom = A.hom) (d : ℕ) (hd : ∀ x, φ.finrank x = d) :
    len A (J.comap φ) = d * len A J := by
  letI := (algV A V).hom.toAlgebra
  obtain ⟨hmf, hlen⟩ := len_eq_finrank A J V hV hfin
  let f : Spec (.of (Γ(A.left, V) ⧸ J.ideal V)) ⟶ J.subscheme := J.subschemeCover.f V
  have hfo : IsOpenImmersion f := J.subschemeCover.map_prop V
  have hf : IsIso f := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨hfo, ⟨fun z => ?_⟩⟩
    have h2 := J.opensRange_subschemeCover_map V
    have hz : z ∈ J.subschemeι ⁻¹ᵁ (V : A.left.Opens) :=
      hV (by rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩)
    rw [← h2] at hz
    exact hz
  have hcomp : f ≫ J.subschemeι ≫ A.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    have h1 : f ≫ J.subschemeι = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal V))) ≫
        V.2.fromSpec :=
      (J.subschemeCover_map_subschemeι V).trans (J.glueDataObjι_ι V)
    rw [← Category.assoc, h1, Category.assoc, ← algV_spec, ← Spec.map_comp]
    rfl
  have hg : J.subschemeι ≫ A.hom = inv f ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    rw [← hcomp, IsIso.inv_hom_id_assoc]
  have hpb : IsPullback (pullback.fst φ J.subschemeι) (pullback.snd φ J.subschemeι ≫ inv f) φ
      (f ≫ J.subschemeι) :=
    (IsPullback.of_hasPullback φ J.subschemeι).of_iso (Iso.refl _) (Iso.refl _) (asIso f).symm
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  have hr : ∀ x, ((J.comapIso φ).hom ≫ pullback.snd φ J.subschemeι ≫ inv f).finrank x = d := by
    intro x
    rw [Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb, hd]
  have hc1 : (J.comap φ).subschemeι ≫ A.hom =
      ((J.comapIso φ).hom ≫ pullback.snd φ J.subschemeι) ≫ J.subschemeι ≫ A.hom := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst J φ]
    simp only [Category.assoc]
    rw [← pullback.condition_assoc, he]
  have hc : (J.comap φ).subschemeι ≫ A.hom =
      ((J.comapIso φ).hom ≫ pullback.snd φ J.subschemeι ≫ inv f) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (Γ(A.left, V) ⧸ J.ideal V))) := by
    rw [hc1, hg]
    simp only [Category.assoc]
  show Scheme.Hom.finrank _ (pt0 k) = d * len A J
  rw [hlen, hc]
  exact finrank_comp_SpecMap _ d hr (pt0 k)

/-- (O2b) The rank of a finite flat endomorphism of `A` over `Spec k` (with `A` irreducible and
locally of finite type) is constant. -/
theorem finrank_const [LocallyOfFiniteType A.hom] [IrreducibleSpace A.left]
    (φ : A.left ⟶ A.left) [Flat φ] [IsFinite φ] (x y : A.left) : φ.finrank x = φ.finrank y := by
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  exact finrank_eq_of_preconnected φ x y

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_IsogDegA_QF =====
section

/-!
# S4-IsogDegA, file QF: a dominant endomorphism of a proper group variety is finite (O3)

`Q = {x | φ quasi-finite at x}` is open, translation invariant (`transl_comp_hom`), and contains the
generic point when `K(A)` is finite over `φ^* K(A)`. By the Jacobson property `Q = A`, so `φ` is
locally quasi-finite; it is proper, hence finite (`IsFinite.of_isProper_of_locallyQuasiFinite`),
and surjective (closed dense range).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Topology MonObj

namespace RamanujanPetersson.IsogDegA

theorem quasiFiniteAt_iff_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    f.QuasiFiniteAt x ↔
      (Y.presheaf.stalkSpecializes (specializes_of_eq h) ≫ f.stalkMap x).hom.QuasiFinite := by
  subst h
  simp [Scheme.Hom.QuasiFiniteAt]

theorem quasiFiniteAt_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] (hf : (ffMap f).hom.Finite) :
    f.QuasiFiniteAt (genericPoint X) :=
  (quasiFiniteAt_iff_of_eq f _ _ (map_genericPoint f)).2 (RingHom.QuasiFinite.of_finite hf)

section Abelian

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

theorem isIso_transl_left (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : IsIso (transl A a).left :=
  ⟨⟨(transl A a⁻¹).left, by
    rw [← Over.comp_left, transl_comp_transl, _root_.mul_inv_cancel, transl_one, Over.id_left], by
    rw [← Over.comp_left, transl_comp_transl, _root_.inv_mul_cancel, transl_one, Over.id_left]⟩⟩

variable (φ : A ⟶ A) [IsMonHom φ]

theorem quasiFiniteAt_transl_iff (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) (x : A.left) :
    φ.left.QuasiFiniteAt ((transl A a).left x) ↔ φ.left.QuasiFiniteAt x := by
  have := isIso_transl_left A a
  have := isIso_transl_left A (a ≫ φ)
  have h1 : ((transl A a).left ≫ φ.left).QuasiFiniteAt x ↔
      φ.left.QuasiFiniteAt ((transl A a).left x) :=
    Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
  have h2 : (φ.left ≫ (transl A (a ≫ φ)).left).QuasiFiniteAt x ↔ φ.left.QuasiFiniteAt x :=
    Scheme.Hom.quasiFiniteAt_comp_iff
  rw [← h1, ← Over.comp_left, transl_comp_hom, Over.comp_left, h2]

variable [IsAlgClosed k] [IsProper A.hom]

instance locallyOfFiniteType_left : LocallyOfFiniteType φ.left := by
  have : LocallyOfFiniteType (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance
  exact locallyOfFiniteType_of_comp φ.left A.hom

omit [GrpObj A] [IsMonHom φ] [IsAlgClosed k] in
theorem isProper_left : IsProper φ.left := by
  have : IsProper (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance
  exact IsProper.of_comp φ.left A.hom

/-- One quasi-finite point makes `φ` locally quasi-finite. -/
theorem locallyQuasiFinite_of_quasiFiniteAt (x₀ : A.left) (h₀ : φ.left.QuasiFiniteAt x₀) :
    LocallyQuasiFinite φ.left := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hQ : IsOpen {x | φ.left.QuasiFiniteAt x} := φ.left.isOpen_quasiFiniteAt
  obtain ⟨x₁, hx₁Q, hx₁⟩ := nonempty_inter_closedPoints ⟨x₀, h₀⟩ hQ.isLocallyClosed
  have hcl : ∀ z : A.left, IsClosed {z} → φ.left.QuasiFiniteAt z := fun z hz ↦ by
    obtain ⟨a, rfl⟩ := exists_transl_eq A x₁ z hx₁ hz
    exact (quasiFiniteAt_transl_iff A φ a x₁).2 hx₁Q
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  refine top_le_iff.1 fun x _ ↦ Scheme.Hom.mem_quasiFiniteLocus.2 ?_
  by_contra hx
  obtain ⟨z, hzQ, hz⟩ := nonempty_inter_closedPoints (Z := {x | ¬ φ.left.QuasiFiniteAt x}) ⟨x, hx⟩
    hQ.isClosed_compl.isLocallyClosed
  exact hzQ (hcl z hz)

/-- O3: a dominant endomorphism with `K(A)` finite over `φ^* K(A)` is finite. -/
theorem isFinite_of_isDominant [IsIntegral A.left] [IsDominant φ.left]
    (hfin : (ffMap φ.left).hom.Finite) : IsFinite φ.left := by
  have := isProper_left A φ
  have := locallyQuasiFinite_of_quasiFiniteAt A φ _ (quasiFiniteAt_genericPoint φ.left hfin)
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ.left

omit [GrpObj A] [IsMonHom φ] [IsAlgClosed k] in
/-- A dominant endomorphism is surjective. -/
theorem surjective_of_isDominant [IsDominant φ.left] : Surjective φ.left := by
  have := isProper_left A φ
  exact surjective_of_isDominant_of_isClosed_range φ.left φ.left.isClosedMap.isClosed_range

end Abelian

end RamanujanPetersson.IsogDegA


end

-- ===== S4.Def_RP_IsogDegA_Trdeg =====
section

/-!
# S4-IsogDegA, file Trdeg: `K(A)` is finite over `φ^* K(A)` (O3 without the hypothesis)

Abstractly: if `K ≃ₐ[k] L` and `L` is essentially of finite type over `k`, then in a tower
`k → K → L` the extension `L/K` has transcendence degree `0` (degrees add, `trdeg k L < ℵ₀`),
so it is algebraic and essentially of finite type, hence finite.
For a dominant endomorphism `φ` of `A` over `Spec k`, `φ^*` is a `k`-algebra map
(`Over.w φ`), and `K(A)` is essentially of finite type over `k` (`A` locally of finite type).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Topology

namespace RamanujanPetersson.IsogDegA

/-- In a tower `k → K → L` with `K ≃ₐ[k] L` and `L` essentially of finite type over `k`,
`L` is finite over `K`. -/
theorem finiteDimensional_of_algEquiv {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [hKL : Algebra K L] [IsScalarTower k K L] (e : K ≃ₐ[k] L)
    [Algebra.EssFiniteType k L] : FiniteDimensional K L := by
  have hadd := trdeg_add_eq k K (A := L)
  rw [e.trdeg_eq] at hadd
  have h0 : Algebra.trdeg K L = 0 :=
    Cardinal.eq_of_add_eq_add_left (hadd.trans (add_zero _).symm) (trdeg_lt_aleph0 k L)
  have : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.1 h0
  have : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp k K L
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem appTop_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.appTop ≫ X.presheaf.germ ⊤ x trivial = Y.presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x :=
  (Scheme.Hom.germ_stalkMap f ⊤ x trivial).symm

/-- `f^*` on global sections and on function fields agree. -/
theorem germ_ffMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsDominant f] :
    Y.presheaf.germ ⊤ (genericPoint Y) trivial ≫ ffMap f =
      f.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
  rw [appTop_germ, ffMap, ← Category.assoc]
  congr 1
  exact TopCat.Presheaf.germ_stalkSpecializes _ _ _

section Variety

variable {k : Type u} [Field k] (A : Over (Spec (.of k)))

/-- The structure map `k → Γ(Spec k) → Γ(A) → K(A)`. -/
noncomputable def kMap [IrreducibleSpace A.left] : k →+* A.left.functionField :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appTop ≫
    A.left.presheaf.germ ⊤ (genericPoint A.left) trivial).hom

theorem essFiniteType_kMap [IrreducibleSpace A.left] [LocallyOfFiniteType A.hom] :
    (kMap A).EssFiniteType := by
  rw [kMap, appTop_germ, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.EssFiniteType.comp ?_
    (RingHom.EssFiniteType.comp ?_ (LocallyOfFiniteType.stalkMap A.hom _))
  · exact (RingHom.FiniteType.of_surjective _
      fun x ↦ ⟨(Scheme.ΓSpecIso (.of k)).hom x, by simp⟩).essFiniteType
  · let x : (⊤ : (Spec (.of k)).Opens) := ⟨A.hom (genericPoint A.left), trivial⟩
    letI := TopCat.Presheaf.algebra_section_stalk (Spec (.of k)).presheaf x
    have := (isAffineOpen_top (Spec (.of k))).isLocalization_stalk x
    exact RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _
      ((isAffineOpen_top (Spec (.of k))).primeIdealOf x).asIdeal.primeCompl)

/-- `φ^*` is a `k`-algebra map. -/
theorem ffMap_comp_kMap [IsIntegral A.left] (φ : A ⟶ A) [IsDominant φ.left] :
    (ffMap φ.left).hom.comp (kMap A) = kMap A := by
  rw [kMap, ← CommRingCat.hom_comp, Category.assoc, Category.assoc, germ_ffMap,
    ← Category.assoc A.hom.appTop, ← Scheme.Hom.comp_appTop, Over.w φ]

/-- `K(A)` is finite over `φ^* K(A)`. -/
theorem ffMap_finite [IsIntegral A.left] [LocallyOfFiniteType A.hom] (φ : A ⟶ A)
    [IsDominant φ.left] : (ffMap φ.left).hom.Finite := by
  letI i : Algebra k A.left.functionField := (kMap A).toAlgebra
  haveI hE : Algebra.EssFiniteType k A.left.functionField := essFiniteType_kMap A
  have hT := @IsScalarTower.of_algebraMap_eq' k A.left.functionField A.left.functionField _ _ _
    i (ffAlgebra φ.left) i (ffMap_comp_kMap A φ).symm
  exact @finiteDimensional_of_algEquiv k _ _ _ _ _ i i (ffAlgebra φ.left) hT
    (AlgEquiv.refl) hE

variable [GrpObj A] (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]

/-- O3: a dominant endomorphism of a proper group variety is finite. -/
theorem isFinite_left [IsIntegral A.left] [IsDominant φ.left] : IsFinite φ.left :=
  isFinite_of_isDominant A φ (ffMap_finite A φ)

end Variety

end RamanujanPetersson.IsogDegA


end

-- ===== S4.Def_RP_IsogDegA_Mult =====
section

/-!
# S4-IsogDegA, file Mult: the degree is multiplicative (O4)

If `f ≫ g` is dominant and `g` has discrete fibres, then `f` is dominant: `g` sends both the
generic point `η` and `f η` (a specialization of `η`) to the generic point, and a discrete
fibre has no nontrivial specializations. Together with `degree_comp` (dominant pairs) this gives
`degree (f ≫ g) = degree f * degree g` whenever `g` is locally quasi-finite once dominant, in
particular for every composite of endomorphisms of a proper group variety (O3: dominant ⇒ finite).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Topology

namespace RamanujanPetersson.IsogDegA

/-- A morphism sending the generic point to the generic point is dominant. -/
theorem isDominant_of_map_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] (h : f (genericPoint X) = genericPoint Y) : IsDominant f := by
  rw [isDominant_iff, DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff,
    ← (genericPoint_spec Y).def]
  exact closure_mono (Set.singleton_subset_iff.2 ⟨_, h⟩)

/-- If `f ≫ g` is dominant and `g` is locally quasi-finite, `f` is dominant. -/
theorem isDominant_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace Z] [LocallyQuasiFinite g] [IsDominant (f ≫ g)] :
    IsDominant f := by
  have : IsDominant g := IsDominant.of_comp (f := f) (g := g)
  have h1 := map_genericPoint (f ≫ g)
  have h2 := map_genericPoint g
  apply isDominant_of_map_genericPoint
  refine ((g.isDiscrete_preimage_singleton (genericPoint Z)).eq_of_specializes
    ((genericPoint_spec Y).specializes trivial) h2 ?_).symm
  simpa using h1

/-- Multiplicativity of the degree, including the non-dominant cases. -/
theorem degree_comp_of_lqf {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] (hg : IsDominant g → LocallyQuasiFinite g) :
    degree (f ≫ g) = degree f * degree g := by
  by_cases hfg : IsDominant (f ≫ g)
  · have : IsDominant g := IsDominant.of_comp (f := f) (g := g)
    have := hg this
    have := isDominant_of_comp f g
    exact degree_comp f g
  · rw [degree_of_not_isDominant _ hfg]
    by_cases hgd : IsDominant g
    · have hf : ¬ IsDominant f := fun _ ↦ hfg inferInstance
      rw [degree_of_not_isDominant _ hf, zero_mul]
    · rw [degree_of_not_isDominant _ hgd, mul_zero]

section Variety

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] [IsAlgClosed k]
  [IsProper A.hom] [IsIntegral A.left]

/-- O4: `deg (φ ∘ ψ) = deg ψ * deg φ` for endomorphisms `ψ`, `φ` (`φ` a group hom). -/
theorem degree_comp_left (ψ φ : A ⟶ A) [IsMonHom φ] :
    degree (ψ ≫ φ).left = degree ψ.left * degree φ.left := by
  rw [Over.comp_left]
  refine degree_comp_of_lqf _ _ fun _ ↦ ?_
  have := isFinite_left A φ
  infer_instance

/-- O4 for group homomorphisms (both factors). -/
theorem degree_comp_left' (ψ φ : A ⟶ A) [IsMonHom ψ] [IsMonHom φ] :
    degree (ψ ≫ φ).left = degree φ.left * degree ψ.left := by
  rw [degree_comp_left, mul_comm]

end Variety

end RamanujanPetersson.IsogDegA


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

-- ===== S4.Def_RP_IsogDegA_Count =====
section

/-!
# S4-IsogDegA, file Count: a closed fibre of the right size (G2, part 2)

For a dominant endomorphism `φ` of a proper integral group variety `A` over an algebraically
closed field, some closed point `y` has exactly `[K(A) : φ^* K(A)]_s` points in its fibre.
Proof: an affine open `V` (through the generic point) and `U = φ⁻¹ V` give a finite extension
`Γ(V) → Γ(U)` of domains with fraction field `K(A)` on both sides; O1 (prime form) gives `a ≠ 0`;
a closed point of the nonempty open `D(a)` (Jacobson) has the right number of primes over it,
and those are the fibre points (SpecFib).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Topology

namespace RamanujanPetersson.IsogDegA

/-- `f^*` on sections over `V` and on function fields agree. -/
theorem germ_ffMap_of_mem {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] (V : Y.Opens) (hη : genericPoint Y ∈ V)
    (hη' : genericPoint X ∈ f ⁻¹ᵁ V) :
    Y.presheaf.germ V (genericPoint Y) hη ≫ ffMap f =
      f.app V ≫ X.presheaf.germ (f ⁻¹ᵁ V) (genericPoint X) hη' := by
  rw [ffMap, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes, Scheme.Hom.germ_stalkMap]

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] (φ : A ⟶ A) [IsMonHom φ]
  [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left]

/-- **G2.** Some closed fibre of a dominant endomorphism has `sepdeg` points. -/
theorem exists_closed_card_fiber [IsDominant φ.left] :
    ∃ y : A.left, IsClosed ({y} : Set A.left) ∧ Finite (φ.left ⁻¹' {y}) ∧
      Nat.card (φ.left ⁻¹' {y}) = @Field.finSepDegree _ _ _ _ (ffAlgebra φ.left) := by
  have hfin : IsFinite φ.left := isFinite_left A φ
  obtain ⟨V, hV, hηV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := genericPoint A.left) (U := ⊤) trivial
  have hηU : genericPoint A.left ∈ φ.left ⁻¹ᵁ V := by
    show φ.left (genericPoint A.left) ∈ V
    rw [map_genericPoint]
    exact hηV
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  haveI : Nonempty (φ.left ⁻¹ᵁ V) := ⟨⟨_, hηU⟩⟩
  have hU : IsAffineOpen (φ.left ⁻¹ᵁ V) := hV.preimage φ.left
  letI : Algebra Γ(A.left, V) Γ(A.left, φ.left ⁻¹ᵁ V) := (φ.left.app V).hom.toAlgebra
  haveI : Module.Finite Γ(A.left, V) Γ(A.left, φ.left ⁻¹ᵁ V) := φ.left.finite_app V hV
  haveI := functionField_isFractionRing_of_isAffineOpen A.left V hV
  haveI := functionField_isFractionRing_of_isAffineOpen A.left _ hU
  have e : V ≤ A.hom ⁻¹ᵁ ⊤ := by simp
  letI : Algebra k Γ(A.left, V) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ A.hom.appLE ⊤ V e).hom.toAlgebra
  haveI : Algebra.FiniteType k Γ(A.left, V) := by
    change RingHom.FiniteType ((A.hom.appLE ⊤ V e).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _
      fun x ↦ ⟨(Scheme.ΓSpecIso (.of k)).hom x, by simp⟩)
    exact HasRingHomProperty.appLE @LocallyOfFiniteType (f := A.hom) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ e
  obtain ⟨a, ha, hcount⟩ := card_primesOver_self (R := Γ(A.left, V))
    (B := Γ(A.left, φ.left ⁻¹ᵁ V)) (K := A.left.functionField) (ffAlgebra φ.left)
    (fun r ↦ congrArg (fun g ↦ g.hom r) (germ_ffMap_of_mem φ.left V hηV hηU)) k
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hne : ((A.left.basicOpen a : A.left.Opens) : Set A.left).Nonempty :=
    (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 fun h0 ↦ ha ((basicOpen_eq_bot_iff a).1 h0)
  obtain ⟨y, hyO, hy⟩ := nonempty_inter_closedPoints hne (A.left.basicOpen a).isOpen.isLocallyClosed
  have hyV : y ∈ V := A.left.basicOpen_le a hyO
  have hm := hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hyV⟩ hy
  have ham : a ∉ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := by
    have h1 : hV.primeIdealOf ⟨y, hyV⟩ ∈ hV.fromSpec ⁻¹ᵁ A.left.basicOpen a := by
      show hV.fromSpec (hV.primeIdealOf ⟨y, hyV⟩) ∈ A.left.basicOpen a
      rw [hV.fromSpec_primeIdealOf]
      exact hyO
    rw [hV.fromSpec_preimage_basicOpen] at h1
    exact (PrimeSpectrum.mem_basicOpen _ _).1 h1
  obtain ⟨hF, hC⟩ := hcount _ hm ham
  let eq := fiberPrimesEquiv φ.left hV hU rfl y hyV
  exact ⟨y, hy, Finite.of_equiv _ eq.symm, (Nat.card_congr eq).trans hC⟩

end RamanujanPetersson.IsogDegA


end

-- ===== S4.Def_RP_IsogDegA =====
section

/-!
# S4-IsogDegA: isogeny degree of an abelian variety (lemmas L24-L26 of S4_COREB_ROUTE.md §3)

`A : Over (Spec k)` a proper integral group scheme over an algebraically closed field `k`
(an abelian variety), `φ : A ⟶ A` a homomorphism.
* L24: `degree φ = [K(A) : φ^* K(A)]` if `φ` is dominant, `0` otherwise; it is multiplicative;
  a dominant `φ` is finite and surjective.
* L25: `degree φ = sepdeg * insepdeg`, `insepdeg` a power of the exponential characteristic.
* L26: `sepdeg = #Ker φ (k)`, where `Ker φ (k) = {c : 𝟙_ ⟶ A // c ≫ φ = 1}`; every fibre over a
  closed point has `#Ker φ (k)` points (translations).
-/

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Topology MonObj CartesianMonoidalCategory

namespace RamanujanPetersson.IsogDegA

/-- Over a closed point, the points of a locally quasi-finite morphism's fibre are closed. -/
theorem isClosed_of_mem_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) (x : X) (hx : f x = y) : IsClosed ({x} : Set X) := by
  have hsub : closure ({x} : Set X) ⊆ f ⁻¹' {y} :=
    (hy.preimage f.continuous).closure_subset_iff.2 (by simpa using hx)
  refine closure_subset_iff_isClosed.1 fun z hz ↦ ?_
  exact ((f.isDiscrete_preimage_singleton y).eq_of_specializes
    (specializes_iff_mem_closure.2 hz) hx (hsub hz)).symm

section Variety

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Translation by `a` on the points of `A`. -/
noncomputable def translEquiv (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) : A.left ≃ A.left where
  toFun := (transl A a).left
  invFun := (transl A a⁻¹).left
  left_inv z := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_comp_transl, _root_.mul_inv_cancel, transl_one]
    rfl
  right_inv z := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_comp_transl, _root_.inv_mul_cancel, transl_one]
    rfl

variable (φ : A ⟶ A) [IsMonHom φ]

/-- The `k`-points of the kernel. -/
abbrev kerPts : Type u := {c : 𝟙_ (Over (Spec (.of k))) ⟶ A // c ≫ φ = 1}

variable [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left]

/-- `Ker φ (k)` is the fibre over the origin. -/
noncomputable def kerEquivFiber [IsDominant φ.left] : kerPts A φ ≃ (φ.left ⁻¹' {pt A 1}) := by
  have := isFinite_left A φ
  refine Equiv.ofBijective (fun c ↦ ⟨pt A c.1, by simp [← pt_comp, c.2]⟩) ⟨fun c₁ c₂ h ↦ ?_, ?_⟩
  · exact Subtype.ext (pt_injective A (congrArg Subtype.val h))
  · rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := exists_pt_eq A x (isClosed_of_mem_fiber φ.left _ (isClosed_pt A 1) x hx)
    refine ⟨⟨c, pt_injective A ?_⟩, rfl⟩
    rw [pt_comp]
    exact hx

/-- Translations identify all fibres over closed points. -/
noncomputable def fiberEquivFiber [IsDominant φ.left] (y : A.left) (hy : IsClosed ({y} : Set A.left)) :
    (φ.left ⁻¹' {pt A 1}) ≃ (φ.left ⁻¹' {y}) := by
  have := isFinite_left A φ
  have := surjective_of_isDominant A φ
  have hc := Classical.choose_spec (φ.left.surjective y)
  set x₀ := Classical.choose (φ.left.surjective y)
  have hc₀ := Classical.choose_spec (exists_pt_eq A x₀ (isClosed_of_mem_fiber φ.left y hy x₀ hc))
  set c₀ := Classical.choose (exists_pt_eq A x₀ (isClosed_of_mem_fiber φ.left y hy x₀ hc))
  have hcomm : ∀ z, φ.left (translEquiv A c₀ z) = translEquiv A (c₀ ≫ φ) (φ.left z) := fun z ↦ by
    show φ.left ((transl A c₀).left z) = (transl A (c₀ ≫ φ)).left (φ.left z)
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, transl_comp_hom, Over.comp_left,
      Scheme.Hom.comp_apply]
  have hy' : translEquiv A (c₀ ≫ φ) (pt A 1) = y := by
    change (transl A (c₀ ≫ φ)).left (pt A 1) = y
    rw [transl_pt, _root_.one_mul, pt_comp, hc₀, hc]
  refine Equiv.subtypeEquiv (translEquiv A c₀) fun z ↦ ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff, hcomm, ← hy']
  exact (translEquiv A (c₀ ≫ φ)).injective.eq_iff.symm

/-- **L26.** `#Ker φ (k) = [K(A) : φ^* K(A)]_s`, and every closed fibre has `#Ker φ (k)` points. -/
theorem card_kerPts [IsDominant φ.left] :
    Finite (kerPts A φ) ∧
      Nat.card (kerPts A φ) = @Field.finSepDegree _ _ _ _ (ffAlgebra φ.left) ∧
      ∀ y : A.left, IsClosed ({y} : Set A.left) →
        Nat.card (φ.left ⁻¹' {y}) = Nat.card (kerPts A φ) := by
  obtain ⟨y, hy, hF, hC⟩ := exists_closed_card_fiber A φ
  let e := (kerEquivFiber A φ).trans (fiberEquivFiber A φ y hy)
  exact ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).trans hC, fun y' hy' ↦
    (Nat.card_congr ((kerEquivFiber A φ).trans (fiberEquivFiber A φ y' hy'))).symm⟩

/-- **L24.** For dominant `φ`: `degree φ = [K(A) : φ^* K(A)]`, and `φ` is finite and surjective. -/
theorem isogDeg_L24 [IsDominant φ.left] :
    degree φ.left = @Module.finrank _ _ _ _ (ffAlgebra φ.left).toModule ∧
      IsFinite φ.left ∧ Function.Surjective φ.left := by
  have := surjective_of_isDominant A φ
  exact ⟨degree_of_isDominant _, isFinite_left A φ, φ.left.surjective⟩

omit [GrpObj A] [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom] in
/-- **L24** (convention): a non-dominant `φ` has degree `0`. -/
theorem isogDeg_L24_zero (h : ¬ IsDominant φ.left) : degree φ.left = 0 :=
  degree_of_not_isDominant _ h

end Variety

end RamanujanPetersson.IsogDegA


end

-- ===== S4.Def_RP_IntersectC_Flat =====
section

/-!
# S4-IntersectC, file Flat: dominant endomorphisms are flat (L35, O3)

* `flat_of_isField`: a ring map out of a field is flat.
* `stalkMap_flat_of_conj`: flatness at a point is invariant under conjugation by automorphisms.
* `flat_left`: a dominant endomorphism `φ` of a group variety is flat (homogeneity: flat over the
  generic point, hence over an open set, and the translates of that open set cover `A`).
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.IntersectB

/-- A ring map out of a field is flat. -/
theorem flat_of_isField {R S : CommRingCat.{u}} (f : R ⟶ S) (hR : IsField R) : f.hom.Flat := by
  letI := hR.toField
  letI := f.hom.toAlgebra
  show Module.Flat R S
  infer_instance

/-- Flatness of a stalk map is invariant under conjugation by automorphisms. -/
theorem stalkMap_flat_of_conj {X Y : Scheme.{u}} (t : X ⟶ X) (s : Y ⟶ Y) [IsIso t] [IsIso s]
    (φ : X ⟶ Y) (h : t ≫ φ = φ ≫ s) (z : X) (H : (φ.stalkMap (t z)).hom.Flat) :
    (φ.stalkMap z).hom.Flat := by
  have H2 : ((t ≫ φ).stalkMap z).hom.Flat := by
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.Flat.respectsIso.cancel_right_isIso _ _).mpr H
  rw [h, Scheme.Hom.stalkMap_comp] at H2
  exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).mp H2

section Variety

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- (O3) A dominant endomorphism of a group variety is flat. -/
theorem flat_left (φ : A ⟶ A) [IsMonHom φ] [IsDominant φ.left] : Flat φ.left := by
  obtain ⟨-, hfin, hsurj⟩ := isogDeg_L24 A φ
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hinv : ∀ (a : 𝟙_ (Over (Spec (.of k))) ⟶ A) (z : A.left),
      (φ.left.stalkMap ((transl A a).left z)).hom.Flat → (φ.left.stalkMap z).hom.Flat := by
    intro a z H
    have := isIso_transl_left A a
    have := isIso_transl_left A (a ≫ φ)
    refine stalkMap_flat_of_conj (transl A a).left (transl A (a ≫ φ)).left φ.left ?_ z H
    rw [← Over.comp_left, transl_comp_hom, Over.comp_left]
  have hη : ∀ z, φ.left z = genericPoint A.left → (φ.left.stalkMap z).hom.Flat := by
    intro z hz
    apply flat_of_isField
    apply isField_stalk_of_closure_mem_irreducibleComponents
    rw [hz]
    simp [irreducibleComponents_eq_singleton]
  obtain ⟨V, hηV, -, hV⟩ := exists_flat_nbhd φ.left (genericPoint A.left)
    (φ.left.finite_preimage_singleton _) hη
  let U : Set A.left := ⋃ a, (transl A a).left ⁻¹' (φ.left ⁻¹' V)
  have hUo : IsOpen U := isOpen_iUnion fun a =>
    (V.isOpen.preimage φ.left.continuous).preimage (transl A a).left.continuous
  have hU : ∀ z, z ∈ U := by
    by_contra hne
    push_neg at hne
    obtain ⟨c, hc⟩ := exists_pt_mem A Uᶜ hUo.isClosed_compl.isLocallyClosed hne
    obtain ⟨y, hy⟩ := hsurj (genericPoint A.left)
    obtain ⟨c0, hc0⟩ := exists_pt_mem A (φ.left ⁻¹' V)
      (V.isOpen.preimage φ.left.continuous).isLocallyClosed ⟨y, by simp [hy, hηV]⟩
    apply hc
    refine Set.mem_iUnion.mpr ⟨c⁻¹ * c0, ?_⟩
    show φ.left ((transl A (c⁻¹ * c0)).left (pt A c)) ∈ V
    rw [transl_pt, mul_inv_cancel_left]
    exact hc0
  refine Flat.of_stalkMap _ fun z => ?_
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hU z)
  exact hinv a z (hV _ ha)

end Variety

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_IntersectC_Deg =====
section

/-!
# S4-IntersectC, file Deg: the rank of a dominant endomorphism is its degree (L35, O4)

* `finrank_eq_of_square`: along a commutative square of fraction fields, the degree of the
  fraction field extension equals the rank of the ring extension.
* `finrank_eq_degree`: for a dominant endomorphism `φ` of a group variety, `φ` (finite and flat)
  has rank `degree φ` at every point.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.IntersectB

/-- Along a commutative square `A → B`, `K → L` of fraction fields, `[L : K] = rank_A B`. -/
theorem finrank_eq_of_square {A B K L : Type u} [CommRing A] [CommRing B] [CommRing K]
    [CommRing L] (r : A →+* B) (gA : A →+* K) (gB : B →+* L) (m : K →+* L)
    (hc : m.comp gA = gB.comp r) (hA : @IsFractionRing A _ K _ gA.toAlgebra)
    (hB : @IsFractionRing B _ L _ gB.toAlgebra) :
    @Module.finrank K L _ _ m.toAlgebra.toModule = @Module.finrank A B _ _ r.toAlgebra.toModule := by
  letI := r.toAlgebra
  letI := gA.toAlgebra
  letI := gB.toAlgebra
  letI := m.toAlgebra
  letI : Algebra A L := (gB.comp r).toAlgebra
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hc x).symm
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact IsFractionRing.finrank_eq A K B L

/-- The rank of a finite flat ring map out of a domain is its `finrank`. -/
theorem ringHom_finrank_eq {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] (r : R →+* S)
    (hf : r.Finite) (hfl : r.Flat) (p : PrimeSpectrum R) :
    r.finrank p = @Module.finrank R S _ _ r.toAlgebra.toModule := by
  letI := r.toAlgebra
  haveI : Module.Finite R S := hf
  haveI : Module.Flat R S := hfl
  rw [RingHom.finrank, ← Ideal.finrank_fiber_eq_rankAtStalk, Ideal.finrank_fiber_eq_finrank]

section Variety

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- (O4) A dominant endomorphism of a group variety has rank `degree φ` at every point. -/
theorem finrank_eq_degree (φ : A ⟶ A) [IsMonHom φ] [IsDominant φ.left] (x : A.left) :
    φ.left.finrank x = degree φ.left := by
  obtain ⟨hdeg, hfin, -⟩ := isogDeg_L24 A φ
  have hflat := flat_left A φ
  obtain ⟨V, hV, hηV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens
    (show genericPoint A.left ∈ (⊤ : A.left.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  have hW : IsAffineOpen (φ.left ⁻¹ᵁ V) := hV'.preimage φ.left
  have hηW : genericPoint A.left ∈ φ.left ⁻¹ᵁ V := by
    show φ.left (genericPoint A.left) ∈ V
    rw [map_genericPoint]
    exact hηV
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩
  haveI : Nonempty (φ.left ⁻¹ᵁ V) := ⟨⟨_, hηW⟩⟩
  have H : hW.fromSpec ≫ φ.left = Spec.map (φ.left.app V) ≫ hV'.fromSpec := by
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ.left hV' hW le_rfl]
  have hsq : IsPullback (Spec.map (φ.left.app V)) hW.fromSpec hV'.fromSpec φ.left :=
    IsOpenImmersion.isPullback _ _ _ _ H (by rw [hV'.opensRange_fromSpec, hW.opensRange_fromSpec])
  have hf1 : IsFinite (Spec.map (φ.left.app V)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip hfin
  have hf2 : Flat (Spec.map (φ.left.app V)) :=
    MorphismProperty.of_isPullback (P := @Flat) hsq.flip hflat
  have hrf : (φ.left.app V).hom.Finite := (IsFinite.SpecMap_iff _).mp hf1
  have hrfl : (φ.left.app V).hom.Flat := Flat.SpecMap_iff.mp hf2
  let p : PrimeSpectrum Γ(A.left, V) := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 : φ.left.finrank x = (φ.left.app V).hom.finrank p := by
    rw [finrank_const A φ.left x (hV'.fromSpec p),
      ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq.flip p,
      Scheme.Hom.finrank_SpecMap_eq_finrank hrf hrfl]
  rw [h1, ringHom_finrank_eq _ hrf hrfl p, hdeg]
  have hc := congrArg CommRingCat.Hom.hom (germ_ffMap_of_mem φ.left V hηV hηW)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hc
  exact (finrank_eq_of_square (φ.left.app V).hom (A.left.germToFunctionField V).hom
    (A.left.germToFunctionField (φ.left ⁻¹ᵁ V)).hom (ffMap φ.left).hom hc
    (functionField_isFractionRing_of_isAffineOpen A.left V hV')
    (functionField_isFractionRing_of_isAffineOpen A.left _ hW)).symm

end Variety

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_IntersectC_Proj =====
section

/-!
# S4-IntersectC, file Proj: pulling divisors back along a dominant endomorphism (L35, O5)

* `Zid_comap`: translating the pullbacks `φ^* D_i` by `a_i` is pulling back the translates of
  `D_i` by `a_i φ`.
* `Pmap`: the endomorphism `φ × ⋯ × φ` of `A^n`; `Pmap_proj`, `ptOf_Pmap`.
* `exists_lift`: a dominant endomorphism is surjective on `k`-points.
* `inum_comap_dom`: `((φ^* D_1) ⋯ (φ^* D_g)) = deg φ · (D_1 ⋯ D_g)` for dominant `φ`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.IntersectB

section Pmap

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) (φ : A ⟶ A)

/-- The endomorphism `φ × ⋯ × φ` of `A^n`. -/
noncomputable def Pmap : (n : ℕ) → (Pw A n ⟶ Pw A n)
  | 0 => 𝟙 _
  | n + 1 => lift (fst (Pw A n) A ≫ Pmap n) (snd (Pw A n) A ≫ φ)

theorem Pmap_succ_fst (n : ℕ) :
    Pmap A φ (n + 1) ≫ fst (Pw A n) A = fst (Pw A n) A ≫ Pmap A φ n :=
  lift_fst _ _

theorem Pmap_succ_snd (n : ℕ) : Pmap A φ (n + 1) ≫ snd (Pw A n) A = snd (Pw A n) A ≫ φ :=
  lift_snd _ _

theorem Pmap_proj (n : ℕ) (i : Fin n) : Pmap A φ n ≫ proj A n i = proj A n i ≫ φ := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => rw [proj_last]; exact Pmap_succ_snd A φ n
    | cast j =>
      rw [proj_castSucc]
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ proj A n j) (Pmap_succ_fst A φ n))).trans
        ((Category.assoc _ _ _).trans ((congrArg (fst (Pw A n) A ≫ ·) (ih j)).trans
          (Category.assoc _ _ _).symm))

theorem ptOf_Pmap (n : ℕ) (b : Fin n → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    ptOf A n b ≫ Pmap A φ n = ptOf A n (fun i => b i ≫ φ) := by
  rw [← ptOf_comp_proj A n (ptOf A n b ≫ Pmap A φ n)]
  congr 1
  funext i
  rw [Category.assoc, Pmap_proj, ← Category.assoc, ptOf_proj]

end Pmap

section Variety

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- Translating the pullbacks `φ^* D_i` by `a_i` is pulling back the translates by `a_i φ`. -/
theorem Zid_comap {g : ℕ} (φ : A ⟶ A) [IsMonHom φ] (D : Fin g → A.left.IdealSheafData)
    (a : Fin g → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    Zid A (fun i => (D i).comap φ.left) a = (Zid A D (fun i => a i ≫ φ)).comap φ.left := by
  simp only [Zid]
  rw [(Scheme.IdealSheafData.map_gc φ.left).l_iSup]
  congr 1
  funext i
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, ← Over.comp_left,
    transl_comp_hom, Over.comp_left]

variable [IsAlgClosed k] [IsProper A.hom] [IsIntegral A.left]

/-- A dominant endomorphism is surjective on `k`-points. -/
theorem exists_lift (φ : A ⟶ A) [IsMonHom φ] [IsDominant φ.left]
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ A) : ∃ b, b ≫ φ = c := by
  have := isFinite_left A φ
  obtain ⟨x, hx⟩ := (surjective_of_isDominant A φ).surj (pt A c)
  obtain ⟨b, rfl⟩ := exists_pt_eq A x (isClosed_of_mem_fiber φ.left _ (isClosed_pt A c) x hx)
  exact ⟨b, pt_injective A (by rw [pt_comp]; exact hx)⟩

/-- **L35** (dominant case): `((φ^* D_1) ⋯ (φ^* D_g)) = deg φ · (D_1 ⋯ D_g)`. -/
theorem inum_comap_dom (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) (φ : A ⟶ A) [IsMonHom φ]
    [IsDominant φ.left] (hD' : ∀ i, ((D i).comap φ.left).support ≠ ⊤) :
    inum A g hdim (fun i => (D i).comap φ.left) hD' = degree φ.left * inum A g hdim D hD := by
  obtain ⟨U, hU, hne, hUs⟩ := inum_spec A g hdim D hD
  have := flat_left A φ
  have := isFinite_left A φ
  refine (inum_unique A g hdim _ hD' _ ((Pmap A φ g).left ⁻¹' U)
    (hU.preimage (Pmap A φ g).left.continuous) ?_ ?_).symm
  · have := isProper_Pw A g
    obtain ⟨c', hc'⟩ := exists_pt_mem (Pw A g) U hU.isLocallyClosed hne
    choose b hb using fun i => exists_lift A φ (c' ≫ proj A g i)
    refine ⟨pt (Pw A g) (ptOf A g b), ?_⟩
    show (Pmap A φ g).left (pt (Pw A g) (ptOf A g b)) ∈ U
    rw [← pt_comp, ptOf_Pmap, funext hb, ptOf_comp_proj]
    exact hc'
  · intro c hc
    have hc' : pt (Pw A g) (c ≫ Pmap A φ g) ∈ U := by rw [pt_comp]; exact hc
    obtain ⟨hfin, hlen⟩ := hUs _ hc'
    have hZ : Zid A (fun i => (D i).comap φ.left) (fun i => c ≫ proj A g i) =
        (Zid A D (fun i => (c ≫ Pmap A φ g) ≫ proj A g i)).comap φ.left := by
      rw [Zid_comap]
      congr 2
      funext i
      rw [Category.assoc, Category.assoc, Pmap_proj]
    obtain ⟨V, hV⟩ := exists_affine_mem A hfin.toFinset
    rw [hZ, len_comap_flat A _ V (fun x hx => hV x (hfin.mem_toFinset.2 hx)) hfin φ.left
      (Over.w φ) _ (finrank_eq_degree A φ), hlen]

end Variety

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_IsogDegB_Unram =====
section

/-!
# S4-IsogDegB, algebra part (lemma L27 of S4_COREB_ROUTE.md §3)

`S → R` a local homomorphism of local rings. If `𝔪_R = 𝔪_S R + 𝔪_R²` (the cotangent map is surjective)
and `R = im S + 𝔪_R`, then `Ω[R⁄S] = 0` (Nakayama), so `R` is formally unramified over `S`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.IsogDegB

open IsLocalRing

section Unram

variable {S R : Type*} [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R] [Algebra S R]
  [IsLocalHom (algebraMap S R)]

theorem algebraMap_mem_maximalIdeal {s : S} (hs : s ∈ maximalIdeal S) :
    algebraMap S R s ∈ maximalIdeal R :=
  (mem_maximalIdeal _).2 fun hu ↦ (mem_maximalIdeal _).1 hs (isUnit_of_map_unit _ _ hu)

/-- `d x ∈ 𝔪 • Ω` for `x ∈ 𝔪_S R ⊔ 𝔪_R ^ 2`. -/
theorem D_mem_smul_of_mem {x : R}
    (hx : x ∈ Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2) :
    KaehlerDifferential.D S R x ∈ (maximalIdeal R) • (⊤ : Submodule R Ω[R⁄S]) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  refine Submodule.add_mem _ ?_ ?_
  · have key : y ∈ maximalIdeal R ∧
        KaehlerDifferential.D S R y ∈ (maximalIdeal R) • (⊤ : Submodule R Ω[R⁄S]) := by
      refine Submodule.span_induction (p := fun y _ ↦ y ∈ maximalIdeal R ∧
        KaehlerDifferential.D S R y ∈ (maximalIdeal R) • (⊤ : Submodule R Ω[R⁄S]))
        ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨s, hs, rfl⟩
        refine ⟨algebraMap_mem_maximalIdeal hs, ?_⟩
        rw [(KaehlerDifferential.D S R).map_algebraMap]
        exact Submodule.zero_mem _
      · simp
      · intro a b _ _ ha hb
        rw [map_add]
        exact ⟨Submodule.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
      · intro a b _ hb
        refine ⟨Ideal.mul_mem_left _ a hb.1, ?_⟩
        rw [smul_eq_mul, Derivation.leibniz]
        exact Submodule.add_mem _ (Submodule.smul_mem _ a hb.2)
          (Submodule.smul_mem_smul hb.1 Submodule.mem_top)
    exact key.2
  · rw [pow_two] at hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro u hu v hv
      rw [Derivation.leibniz]
      exact Submodule.add_mem _ (Submodule.smul_mem_smul hu Submodule.mem_top)
        (Submodule.smul_mem_smul hv Submodule.mem_top)
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb

/-- Nakayama: surjective cotangent map + residue fields generated by `S` give `Ω[R⁄S] = 0`. -/
theorem subsingleton_kaehler [Module.Finite R Ω[R⁄S]]
    (hres : ∀ r : R, ∃ s : S, r - algebraMap S R s ∈ maximalIdeal R)
    (hle : maximalIdeal R ≤ Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2) :
    Subsingleton Ω[R⁄S] := by
  have hspan : Submodule.span R (Set.range (KaehlerDifferential.D S R)) ≤
      (maximalIdeal R) • (⊤ : Submodule R Ω[R⁄S]) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    obtain ⟨s, hs⟩ := hres r
    have h := D_mem_smul_of_mem (S := S) (hle hs)
    rwa [map_sub, (KaehlerDifferential.D S R).map_algebraMap, sub_zero] at h
  rw [KaehlerDifferential.span_range_derivation] at hspan
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
    (Module.Finite.fg_top) hspan (maximalIdeal_le_jacobson _)
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hx : x ∈ (⊤ : Submodule R Ω[R⁄S]) := Submodule.mem_top
  rwa [hbot, Submodule.mem_bot] at hx

theorem formallyUnramified_of_le [Module.Finite R Ω[R⁄S]]
    (hres : ∀ r : R, ∃ s : S, r - algebraMap S R s ∈ maximalIdeal R)
    (hle : maximalIdeal R ≤ Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2) :
    Algebra.FormallyUnramified S R :=
  ⟨subsingleton_kaehler hres hle⟩

end Unram

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_IsogDegB_Der =====
section

/-!
# S4-IsogDegB, tangent vectors from the cotangent space (lemma L27 of S4_COREB_ROUTE.md §3)

`R` a local `k`-algebra with a `k`-point `ev : R →ₐ[k] k` (kernel `𝔪_R`), `S → R` local. If
`𝔪_R ⊄ 𝔪_S R + 𝔪_R²` (the cotangent map is not surjective) there is a `k`-algebra map
`h : R → k[ε]` lifting `ev`, killing `𝔪_S` in the `ε`-part and nonzero in the `ε`-part
(a nonzero tangent vector killed by the differential).
-/

set_option autoImplicit false

namespace RamanujanPetersson.IsogDegB

open IsLocalRing

section Der

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- The pointed derivation `r ↦ l (r - ev r)`. -/
def dmap (ev : R →ₐ[k] k) (l : R →ₗ[k] k) : R →ₗ[k] k :=
  l ∘ₗ (LinearMap.id - Algebra.linearMap k R ∘ₗ ev.toLinearMap)

theorem dmap_apply (ev : R →ₐ[k] k) (l : R →ₗ[k] k) (r : R) :
    dmap ev l r = l (r - algebraMap k R (ev r)) := rfl

theorem dmap_algebraMap (ev : R →ₐ[k] k) (l : R →ₗ[k] k) (c : k) :
    dmap ev l (algebraMap k R c) = 0 := by
  simp [dmap_apply]

/-- Leibniz rule for `dmap`, given that `l` kills products of elements of `ker ev`. -/
theorem dmap_mul (ev : R →ₐ[k] k) (l : R →ₗ[k] k)
    (hl : ∀ a b : R, ev a = 0 → ev b = 0 → l (a * b) = 0) (a b : R) :
    dmap ev l (a * b) = ev a * dmap ev l b + ev b * dmap ev l a := by
  have key : a * b - algebraMap k R (ev (a * b)) =
      (a - algebraMap k R (ev a)) * (b - algebraMap k R (ev b)) +
      ev a • (b - algebraMap k R (ev b)) + ev b • (a - algebraMap k R (ev a)) := by
    rw [map_mul, map_mul, Algebra.smul_def, Algebra.smul_def]; ring
  rw [dmap_apply, key, map_add, map_add, map_smul, map_smul,
    hl _ _ (by simp) (by simp), zero_add, dmap_apply, dmap_apply, smul_eq_mul, smul_eq_mul]

/-- The `k`-linear map `r ↦ ev r + ε · dmap r` into the dual numbers. -/
def toDualLin (ev : R →ₐ[k] k) (l : R →ₗ[k] k) : R →ₗ[k] DualNumber k :=
  Algebra.linearMap k (DualNumber k) ∘ₗ ev.toLinearMap + TrivSqZeroExt.inrHom k k ∘ₗ dmap ev l

theorem toDualLin_fst (ev : R →ₐ[k] k) (l : R →ₗ[k] k) (r : R) :
    (toDualLin ev l r).fst = ev r := by
  simp [toDualLin, TrivSqZeroExt.algebraMap_eq_inl]

theorem toDualLin_snd (ev : R →ₐ[k] k) (l : R →ₗ[k] k) (r : R) :
    (toDualLin ev l r).snd = dmap ev l r := by
  simp [toDualLin, TrivSqZeroExt.algebraMap_eq_inl]

/-- The `k`-algebra map `R → k[ε]` attached to a functional killing `(ker ev)²`. -/
def toDual (ev : R →ₐ[k] k) (l : R →ₗ[k] k)
    (hl : ∀ a b : R, ev a = 0 → ev b = 0 → l (a * b) = 0) : R →ₐ[k] DualNumber k :=
  AlgHom.ofLinearMap (toDualLin ev l)
    (by
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [toDualLin_fst, map_one, TrivSqZeroExt.fst_one]
      · rw [toDualLin_snd, TrivSqZeroExt.snd_one, ← map_one (algebraMap k R), dmap_algebraMap])
    (fun a b ↦ by
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [toDualLin_fst, map_mul, TrivSqZeroExt.fst_mul, toDualLin_fst, toDualLin_fst]
      · rw [toDualLin_snd, TrivSqZeroExt.snd_mul, toDualLin_fst, toDualLin_fst, toDualLin_snd,
          toDualLin_snd, dmap_mul ev l hl, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
          smul_eq_mul, mul_comm (dmap ev l a)])

theorem toDual_fst (ev : R →ₐ[k] k) (l : R →ₗ[k] k)
    (hl : ∀ a b : R, ev a = 0 → ev b = 0 → l (a * b) = 0) (r : R) :
    (toDual ev l hl r).fst = ev r := toDualLin_fst ev l r

theorem toDual_snd (ev : R →ₐ[k] k) (l : R →ₗ[k] k)
    (hl : ∀ a b : R, ev a = 0 → ev b = 0 → l (a * b) = 0) (r : R) :
    (toDual ev l hl r).snd = dmap ev l r := toDualLin_snd ev l r

end Der

section Lambda

variable {k S R : Type*} [Field k] [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
  [Algebra S R] [IsLocalHom (algebraMap S R)] [Algebra k R]

theorem ev_eq_zero_iff (ev : R →ₐ[k] k) (hm : ∀ r, ev r = 0 → r ∈ maximalIdeal R) (r : R) :
    ev r = 0 ↔ r ∈ maximalIdeal R := by
  refine ⟨hm r, fun hr ↦ by_contra fun h0 ↦ ?_⟩
  have h1 : r - algebraMap k R (ev r) ∈ maximalIdeal R := hm _ (by simp)
  have h2 : algebraMap k R (ev r) ∈ maximalIdeal R := by
    simpa using Ideal.sub_mem _ hr h1
  exact (mem_maximalIdeal _).1 h2 ((Ne.isUnit h0).map (algebraMap k R))

/-- **Alg-1.** A non-surjective cotangent map gives a nonzero tangent vector killed by `S`. -/
theorem exists_tangent_of_not_le (ev : R →ₐ[k] k) (hm : ∀ r, ev r = 0 → r ∈ maximalIdeal R)
    (hJ : ¬ maximalIdeal R ≤ Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2) :
    ∃ h : R →ₐ[k] DualNumber k, (∀ r, (h r).fst = ev r) ∧
      (∀ s ∈ maximalIdeal S, (h (algebraMap S R s)).snd = 0) ∧ ∃ r, (h r).snd ≠ 0 := by
  set J := Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2
  obtain ⟨x, hxm, hxJ⟩ := Set.not_subset.1 hJ
  have hx : x ∉ J.restrictScalars k := hxJ
  obtain ⟨l, hlx, hlJ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hl0 : ∀ y ∈ J, l y = 0 := fun y hy ↦
    LinearMap.mem_ker.1 (LinearMap.le_ker_iff_map.2 hlJ (show y ∈ J.restrictScalars k from hy))
  have hl : ∀ a b : R, ev a = 0 → ev b = 0 → l (a * b) = 0 := fun a b ha hb ↦
    hl0 _ (Ideal.mem_sup_right (by
      rw [pow_two]; exact Ideal.mul_mem_mul ((ev_eq_zero_iff ev hm a).1 ha)
        ((ev_eq_zero_iff ev hm b).1 hb)))
  refine ⟨toDual ev l hl, toDual_fst ev l hl, fun s hs ↦ ?_, x, ?_⟩
  · have hsm := algebraMap_mem_maximalIdeal (R := R) hs
    rw [toDual_snd, dmap_apply, (ev_eq_zero_iff ev hm _).2 hsm, map_zero, sub_zero]
    exact hl0 _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hs))
  · rw [toDual_snd, dmap_apply, (ev_eq_zero_iff ev hm _).2 hxm, map_zero, sub_zero]
    exact hlx

end Lambda

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_IsogDegB_TanA =====
section

/-!
# S4-IsogDegB, the tangent space at the identity (lemma L27 of S4_COREB_ROUTE.md §3)

`T A := {t : Spec k[ε] ⟶ A // ι0 ≫ t = 1}` (a subgroup of the Hom-group), `dφ t := t ≫ φ`.
A tangent vector is determined by its stalk map `tvec t : 𝒪_{A,e} → k[ε]` (whose `ε`-free part is the
fixed `k`-point `ev0`), hence by the `ε`-parts `(tvec t r).snd`.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

section Stalk

variable {X : Scheme.{u}} {R : CommRingCat.{u}} [IsLocalRing R]

theorem exists_stalkLift (f : Spec R ⟶ X) {x : X} (hx : f (closedPoint R) = x) :
    ∃ g : X.presheaf.stalk x ⟶ R, IsLocalHom g.hom ∧ Spec.map g ≫ X.fromSpecStalk x = f := by
  subst hx
  exact ⟨_, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk f⟩

theorem stalkLift_injective {x : X} (g₁ g₂ : X.presheaf.stalk x ⟶ R) [IsLocalHom g₁.hom]
    [IsLocalHom g₂.hom] (h : Spec.map g₁ ≫ X.fromSpecStalk x = Spec.map g₂ ≫ X.fromSpecStalk x) :
    g₁ = g₂ := by
  have := (SpecToEquivOfLocalRing X R).symm.injective
    (a₁ := ⟨x, g₁, inferInstance⟩) (a₂ := ⟨x, g₂, inferInstance⟩) h
  obtain ⟨_, e⟩ := SpecToEquivOfLocalRing_eq_iff.1 this
  simpa using e

end Stalk

section Tangent

variable (k : Type u) [Field k]

/-- `Spec k[ε]` over `k`. -/
noncomputable abbrev DS : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- `ε ↦ 0`. -/
noncomputable abbrev fstC : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
  CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom

instance : IsLocalHom (fstC k).hom := ⟨fun _ hx ↦ TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hx⟩

/-- The `k`-point of `Spec k[ε]`. -/
noncomputable def ι0 : 𝟙_ (Over (Spec (.of k))) ⟶ DS k :=
  Over.homMk (Spec.map (fstC k)) (by
    have h : CommRingCat.ofHom (algebraMap k (DualNumber k)) ≫ fstC k = 𝟙 _ := by
      ext x; simp
    change Spec.map (fstC k) ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) = 𝟙 _
    rw [← Spec.map_comp, h, Spec.map_id])

theorem DS_eq_closedPoint (x : PrimeSpectrum (DualNumber k)) : x = closedPoint (DualNumber k) := by
  have hε : (DualNumber.eps : DualNumber k) ∈ x.asIdeal := by
    rcases x.isPrime.mem_or_mem (show DualNumber.eps * DualNumber.eps ∈ x.asIdeal by
      rw [DualNumber.eps_mul_eps]; exact x.asIdeal.zero_mem) with h | h <;> exact h
  have hle : maximalIdeal (DualNumber k) ≤ x.asIdeal := by
    rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_le, Set.singleton_subset_iff]
    exact hε
  exact PrimeSpectrum.ext ((maximalIdeal.isMaximal _).eq_of_le x.isPrime.ne_top hle).symm

variable {k} (A : Over (Spec (.of k))) [GrpObj A]

theorem left_closedPoint (t : DS k ⟶ A) (ht : ι0 k ≫ t = 1) :
    t.left (closedPoint (DualNumber k)) = pt A 1 := by
  rw [← ht, pt_comp]
  congr 1
  exact (DS_eq_closedPoint k _).symm

/-- Restriction along `ι0`. -/
noncomputable def resι : (DS k ⟶ A) →* (𝟙_ (Over (Spec (.of k))) ⟶ A) where
  toFun t := ι0 k ≫ t
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- The tangent space of `A` at the identity. -/
noncomputable def Tan : Subgroup (DS k ⟶ A) := (resι A).ker

variable {A}

theorem tan_spec (t : Tan A) : ι0 k ≫ t.1 = 1 := MonoidHom.mem_ker.1 t.2

/-- The differential of a homomorphism at the identity. -/
noncomputable def dφ (φ : A ⟶ A) [IsMonHom φ] : Tan A →* Tan A where
  toFun t := ⟨t.1 ≫ φ, MonoidHom.mem_ker.2 (by
    show ι0 k ≫ t.1 ≫ φ = 1
    rw [← Category.assoc, tan_spec, MonObj.one_comp])⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' t s := Subtype.ext (MonObj.mul_comp _ _ _)

theorem dφ_val (φ : A ⟶ A) [IsMonHom φ] (t : Tan A) : (dφ φ t).1 = t.1 ≫ φ := rfl

theorem exists_tvec (t : Tan A) :
    ∃ g : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (DualNumber k),
      IsLocalHom g.hom ∧ Spec.map g ≫ A.left.fromSpecStalk (pt A 1) = t.1.left :=
  exists_stalkLift (R := CommRingCat.of (DualNumber k)) t.1.left (left_closedPoint A t.1 (tan_spec t))

/-- The stalk map `𝒪_{A,e} → k[ε]` of a tangent vector. -/
noncomputable def tvec (t : Tan A) : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (DualNumber k) :=
  (exists_tvec t).choose

instance (t : Tan A) : IsLocalHom (tvec t).hom := (exists_tvec t).choose_spec.1

theorem tvec_spec (t : Tan A) : Spec.map (tvec t) ≫ A.left.fromSpecStalk (pt A 1) = t.1.left :=
  (exists_tvec t).choose_spec.2

variable (A) in
theorem exists_ev0 : ∃ g : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of k, IsLocalHom g.hom ∧
    Spec.map g ≫ A.left.fromSpecStalk (pt A 1) = (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A).left :=
  exists_stalkLift (R := CommRingCat.of k) (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A).left rfl

variable (A) in
/-- Evaluation at the identity point, `𝒪_{A,e} → k`. -/
noncomputable def ev0 : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of k := (exists_ev0 A).choose

instance : IsLocalHom (ev0 A).hom := (exists_ev0 A).choose_spec.1

theorem ev0_spec : Spec.map (ev0 A) ≫ A.left.fromSpecStalk (pt A 1) =
    (1 : 𝟙_ (Over (Spec (.of k))) ⟶ A).left := (exists_ev0 A).choose_spec.2

theorem tvec_fst (t : Tan A) : tvec t ≫ fstC k = ev0 A := by
  have : IsLocalHom (tvec t ≫ fstC k).hom := by rw [CommRingCat.hom_comp]; infer_instance
  apply stalkLift_injective
  rw [Spec.map_comp, Category.assoc, tvec_spec, ev0_spec]
  exact congrArg CommaMorphism.left (tan_spec t)

/-- The `ε`-part of a tangent vector. -/
noncomputable def coeff (t : Tan A) (r : A.left.presheaf.stalk (pt A 1)) : k := ((tvec t).hom r).snd

theorem fst_tvec (t : Tan A) (r : A.left.presheaf.stalk (pt A 1)) :
    ((tvec t).hom r).fst = (ev0 A).hom r :=
  congrArg (fun g ↦ g.hom r) (tvec_fst t)

theorem tan_ext {t s : Tan A} (h : ∀ r, coeff t r = coeff s r) : t = s := by
  have hv : tvec t = tvec s := by
    ext r
    · exact (fst_tvec t r).trans (fst_tvec s r).symm
    · exact h r
  apply Subtype.ext
  apply Over.OverMorphism.ext
  rw [← tvec_spec t, ← tvec_spec s, hv]

end Tangent

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_IsogDegB_TanB =====
section

/-!
# S4-IsogDegB, differentials on stalks and tangent vectors from stalk maps (L27 of S4_COREB_ROUTE.md §3)

`tvec (dφ t) = φ♯ ≫ tvec t` with `φ♯ : 𝒪_{A,e} → 𝒪_{A,e}` the stalk map of `φ` at the identity;
the structure map `kS A : k → 𝒪_{A,e}` (so `kS ≫ ev0 = 𝟙`); every local `h : 𝒪_{A,e} → k[ε]` with
`h ≫ fst = ev0` and `kS ≫ h = algebraMap` is `tvec` of a tangent vector.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

section Stalk

variable {X Y : Scheme.{u}} {R : CommRingCat.{u}}

theorem stalkLift_comp (f : X ⟶ Y) {x : X} {y : Y} (hxy : f x = y) (g : X.presheaf.stalk x ⟶ R) :
    Spec.map ((Y.presheaf.stalkSpecializes (specializes_of_eq hxy) ≫ f.stalkMap x) ≫ g) ≫
      Y.fromSpecStalk y = Spec.map g ≫ X.fromSpecStalk x ≫ f := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem stalkSpec_fromSpecStalk (f : X ⟶ Y) {x : X} {y : Y} (hxy : f x = y) :
    Spec.map (Y.presheaf.stalkSpecializes (specializes_of_eq hxy) ≫ f.stalkMap x) ≫
      Y.fromSpecStalk y = X.fromSpecStalk x ≫ f := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem isLocalHom_stalkLift (f : X ⟶ Y) {x : X} {y : Y} (hxy : f x = y)
    (g : X.presheaf.stalk x ⟶ R) [IsLocalHom g.hom] :
    IsLocalHom ((Y.presheaf.stalkSpecializes (specializes_of_eq hxy) ≫ f.stalkMap x) ≫ g).hom := by
  subst hxy
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, CommRingCat.hom_comp]
  infer_instance

end Stalk

section Tangent

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

theorem left_pt_one (φ : A ⟶ A) [IsMonHom φ] : φ.left (pt A 1) = pt A 1 := by
  rw [← pt_comp, MonObj.one_comp]

/-- The stalk map `φ♯ : 𝒪_{A,e} → 𝒪_{A,e}` of `φ` at the identity. -/
noncomputable abbrev sharp (φ : A ⟶ A) [IsMonHom φ] :
    A.left.presheaf.stalk (pt A 1) ⟶ A.left.presheaf.stalk (pt A 1) :=
  A.left.presheaf.stalkSpecializes (specializes_of_eq (left_pt_one φ)) ≫ φ.left.stalkMap (pt A 1)

theorem tvec_dφ (φ : A ⟶ A) [IsMonHom φ] (t : Tan A) : tvec (dφ φ t) = sharp φ ≫ tvec t := by
  have := isLocalHom_stalkLift φ.left (left_pt_one φ) (tvec t)
  apply stalkLift_injective
  rw [tvec_spec, dφ_val, Over.comp_left, stalkLift_comp φ.left (left_pt_one φ) (tvec t),
    ← Category.assoc, tvec_spec]

theorem coeff_dφ (φ : A ⟶ A) [IsMonHom φ] (t : Tan A) (r : A.left.presheaf.stalk (pt A 1)) :
    coeff (dφ φ t) r = coeff t ((sharp φ).hom r) := by
  rw [coeff, coeff, tvec_dφ]; rfl

variable (A) in
/-- The structure map `k → 𝒪_{A,e}`. -/
noncomputable def kS : CommRingCat.of k ⟶ A.left.presheaf.stalk (pt A 1) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (A.hom (pt A 1)) trivial) ≫
    A.hom.stalkMap (pt A 1)

theorem fromSpecStalk_comp_hom : A.left.fromSpecStalk (pt A 1) ≫ A.hom = Spec.map (kS A) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, kS]
  simp only [Spec.map_comp, Category.assoc]

theorem kS_ev0 : kS A ≫ ev0 A = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, ← fromSpecStalk_comp_hom, ← Category.assoc, ev0_spec, Over.w, Spec.map_id]
  rfl

/-- The tangent vector with stalk map `h`. -/
noncomputable def tOf (h : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (DualNumber k))
    (hh : h ≫ fstC k = ev0 A) (hk : kS A ≫ h = CommRingCat.ofHom (algebraMap k (DualNumber k))) :
    Tan A :=
  ⟨Over.homMk (Spec.map h ≫ A.left.fromSpecStalk (pt A 1)) (by
      rw [Category.assoc, fromSpecStalk_comp_hom, ← Spec.map_comp, hk]; rfl),
    MonoidHom.mem_ker.2 (by
      apply Over.OverMorphism.ext
      show Spec.map (fstC k) ≫ Spec.map h ≫ _ = _
      rw [← Category.assoc, ← Spec.map_comp, hh, ev0_spec])⟩

theorem tvec_tOf (h : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (DualNumber k))
    [IsLocalHom h.hom] (hh : h ≫ fstC k = ev0 A)
    (hk : kS A ≫ h = CommRingCat.ofHom (algebraMap k (DualNumber k))) :
    tvec (tOf h hh hk) = h :=
  stalkLift_injective _ _ (tvec_spec _)

theorem coeff_tOf (h : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (DualNumber k))
    [IsLocalHom h.hom] (hh : h ≫ fstC k = ev0 A)
    (hk : kS A ≫ h = CommRingCat.ofHom (algebraMap k (DualNumber k))) (r) :
    coeff (tOf h hh hk) r = (h.hom r).snd := by
  rw [coeff, tvec_tOf]

theorem kS_sharp (φ : A ⟶ A) [IsMonHom φ] : kS A ≫ sharp φ = kS A := by
  apply Spec.map_injective
  rw [Spec.map_comp, ← fromSpecStalk_comp_hom, ← Category.assoc,
    stalkSpec_fromSpecStalk φ.left (left_pt_one φ), Category.assoc, Over.w]

end Tangent

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_IsogDegB_TanC =====
section

/-!
# S4-IsogDegB, the group law on tangent vectors is addition (L27 of S4_COREB_ROUTE.md §3)

With `D2 = Spec k[ε₁, ε₂]` (`k[ε₁, ε₂] = TrivSqZeroExt k (k × k)`), `u := (p₁ ≫ t) * (p₂ ≫ s)` restricts to
`t * s`, `t`, `s` along `δ, ι₁, ι₂ : Spec k[ε] → D2`; on stalks this reads `coeff (t * s) = coeff t + coeff s`.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

section Maps

variable (k : Type u) [Field k]

/-- `k[ε₁, ε₂]`. -/
abbrev K2 := TrivSqZeroExt k (k × k)

instance : IsLocalRing (K2 k) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
  rcases eq_or_ne x.fst 0 with h | h
  · right; rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]; simp [h]
  · left; rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]; exact h.isUnit

theorem tsze_eq_closedPoint {M : Type u} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] [IsLocalRing (TrivSqZeroExt k M)] (x : PrimeSpectrum (TrivSqZeroExt k M)) :
    x = closedPoint _ := by
  have hle : maximalIdeal (TrivSqZeroExt k M) ≤ x.asIdeal := fun y hy ↦ by
    have h0 : y.fst = 0 := by
      by_contra h
      exact (mem_maximalIdeal _).1 hy (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h))
    have hy' : y * y = 0 := by ext <;> simp [h0]
    rcases x.isPrime.mem_or_mem (show y * y ∈ x.asIdeal by rw [hy']; exact x.asIdeal.zero_mem)
      with h | h <;> exact h
  exact PrimeSpectrum.ext ((maximalIdeal.isMaximal _).eq_of_le x.isPrime.ne_top hle).symm

variable {M N L : Type u} [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M]
  [AddCommGroup N] [Module k N] [Module kᵐᵒᵖ N] [IsCentralScalar k N]
  [AddCommGroup L] [Module k L] [Module kᵐᵒᵖ L] [IsCentralScalar k L]

/-- `TrivSqZeroExt.map f` in `CommRingCat`. -/
noncomputable abbrev mapC (f : M →ₗ[k] N) :
    CommRingCat.of (TrivSqZeroExt k M) ⟶ CommRingCat.of (TrivSqZeroExt k N) :=
  CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom

instance (f : M →ₗ[k] N) : IsLocalHom (mapC k f).hom :=
  ⟨fun x hx ↦ by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at hx ⊢
    simpa using hx⟩

/-- `Spec (TrivSqZeroExt k M)` over `k`. -/
noncomputable abbrev DM (M : Type u) [AddCommGroup M] [Module k M] [Module kᵐᵒᵖ M]
    [IsCentralScalar k M] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (TrivSqZeroExt k M))))

/-- The morphism `Spec (k ⊕ N) → Spec (k ⊕ M)` of `f : M → N`. -/
noncomputable def homOfMap (f : M →ₗ[k] N) : DM k N ⟶ DM k M :=
  Over.homMk (Spec.map (mapC k f)) (by
    change Spec.map (mapC k f) ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x <;> simp)

theorem homOfMap_comp (f : M →ₗ[k] N) (g : L →ₗ[k] M) :
    homOfMap k f ≫ homOfMap k g = homOfMap k (f ∘ₗ g) := by
  apply Over.OverMorphism.ext
  change Spec.map (mapC k f) ≫ Spec.map (mapC k g) = Spec.map (mapC k (f ∘ₗ g))
  rw [← Spec.map_comp]
  congr 1
  ext x <;> simp

theorem homOfMap_id : homOfMap k (LinearMap.id : M →ₗ[k] M) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (mapC k LinearMap.id) = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  ext x <;> simp

theorem toUnit_left_DS : (toUnit (DS k)).left = (DS k).hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (DS k)))

theorem homOfMap_zero : homOfMap k (0 : k →ₗ[k] k) = toUnit (DS k) ≫ ι0 k := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, toUnit_left_DS]
  change Spec.map (mapC k 0) = Spec.map _ ≫ Spec.map (fstC k)
  rw [← Spec.map_comp]
  congr 1
  ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

end Maps

section GroupLaw

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

theorem tvec_of_comp (v : Tan A) {u : DM k (k × k) ⟶ A}
    (U : A.left.presheaf.stalk (pt A 1) ⟶ CommRingCat.of (K2 k)) [IsLocalHom U.hom]
    (hU : Spec.map U ≫ A.left.fromSpecStalk (pt A 1) = u.left) (f : k × k →ₗ[k] k)
    (hv : homOfMap k f ≫ u = v.1) : tvec v = U ≫ mapC k f := by
  have : IsLocalHom (U ≫ mapC k f).hom := by rw [CommRingCat.hom_comp]; infer_instance
  apply stalkLift_injective
  rw [tvec_spec, ← hv, Over.comp_left, Spec.map_comp, Category.assoc, hU]
  rfl

/-- **Group law = addition** on tangent vectors. -/
theorem coeff_mul (t s : Tan A) (r : A.left.presheaf.stalk (pt A 1)) :
    coeff (t * s) r = coeff t r + coeff s r := by
  set u : DM k (k × k) ⟶ A :=
    (homOfMap k (LinearMap.inl k k k) ≫ t.1) * (homOfMap k (LinearMap.inr k k k) ≫ s.1)
  have hδ : homOfMap k (LinearMap.coprod LinearMap.id LinearMap.id) ≫ u = (t * s).1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homOfMap_comp, homOfMap_comp,
      LinearMap.coprod_inl, LinearMap.coprod_inr, homOfMap_id, Category.id_comp, Category.id_comp]
    rfl
  have h1 : homOfMap k (LinearMap.fst k k k) ≫ u = t.1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homOfMap_comp, homOfMap_comp,
      LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, homOfMap_id, homOfMap_zero, Category.id_comp,
      Category.assoc, tan_spec, MonObj.comp_one, _root_.mul_one]
  have h2 : homOfMap k (LinearMap.snd k k k) ≫ u = s.1 := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homOfMap_comp, homOfMap_comp,
      LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, homOfMap_id, homOfMap_zero, Category.id_comp,
      Category.assoc, tan_spec, MonObj.comp_one, _root_.one_mul]
  have hpt : u.left (closedPoint (K2 k)) = pt A 1 := by
    have e1 : (homOfMap k (LinearMap.coprod LinearMap.id LinearMap.id)).left
        (closedPoint (DualNumber k)) = closedPoint (K2 k) := tsze_eq_closedPoint k _
    have e2 : (t * s).1.left (closedPoint (DualNumber k)) = pt A 1 :=
      left_closedPoint A _ (tan_spec (t * s))
    rw [← hδ] at e2
    calc u.left (closedPoint (K2 k))
        = u.left ((homOfMap k (LinearMap.coprod LinearMap.id LinearMap.id)).left
          (closedPoint (DualNumber k))) := by rw [e1]
      _ = pt A 1 := e2
  obtain ⟨U, hUl, hU⟩ := exists_stalkLift (R := CommRingCat.of (K2 k)) u.left hpt
  rw [coeff, coeff, coeff, tvec_of_comp (t * s) U hU _ hδ, tvec_of_comp t U hU _ h1,
    tvec_of_comp s U hU _ h2]
  simp

theorem coeff_one (r : A.left.presheaf.stalk (pt A 1)) : coeff (1 : Tan A) r = 0 := by
  have h := coeff_mul (1 : Tan A) 1 r
  rw [_root_.mul_one] at h
  calc coeff (1 : Tan A) r = coeff (1 : Tan A) r + coeff (1 : Tan A) r - coeff (1 : Tan A) r := by ring
    _ = 0 := by rw [← h, sub_self]

/-- `coeff` as a homomorphism to the additive group of functions. -/
noncomputable def coeffHom : Tan A →* Multiplicative (A.left.presheaf.stalk (pt A 1) → k) where
  toFun t := Multiplicative.ofAdd (coeff t)
  map_one' := by
    ext r
    exact coeff_one r
  map_mul' t s := by
    ext r
    exact coeff_mul t s r

theorem coeff_zpow (t : Tan A) (n : ℤ) (r : A.left.presheaf.stalk (pt A 1)) :
    coeff (t ^ n) r = n * coeff t r := by
  have := congrArg (fun f : Multiplicative (A.left.presheaf.stalk (pt A 1) → k) ↦ Multiplicative.toAdd f r) (map_zpow (coeffHom (A := A)) t n)
  simpa [coeffHom, toAdd_zpow, zsmul_eq_mul] using this

theorem tan_eq_one_iff (t : Tan A) : t = 1 ↔ ∀ r, coeff t r = 0 :=
  ⟨fun h r ↦ h ▸ coeff_one r, fun h ↦ tan_ext fun r ↦ (h r).trans (coeff_one r).symm⟩

end GroupLaw

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_IsogDegB_DerT =====
section

/-!
# S4-IsogDegB, tangent vectors over a `k`-tower (L27 of S4_COREB_ROUTE.md §3)

With `k → S → R` and `k`-points on `S` and `R`: the tangent vector of `exists_tangent_of_not_le` kills all of `S`,
and the residue hypotheses of `Unram.formallyUnramified_of_le` hold.
-/

set_option autoImplicit false

namespace RamanujanPetersson.IsogDegB

open IsLocalRing

section Points

variable {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [Algebra k R]

theorem mem_of_ev_eq_zero (ev : R →ₐ[k] k) (r : R) (hr : ev r = 0) : r ∈ maximalIdeal R :=
  (mem_maximalIdeal _).2 fun hu ↦ (hu.map ev).ne_zero hr

theorem sub_algebraMap_mem (ev : R →ₐ[k] k) (r : R) : r - algebraMap k R (ev r) ∈ maximalIdeal R :=
  mem_of_ev_eq_zero ev _ (by simp)

end Points

section Tower

variable {k S R : Type*} [Field k] [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
  [Algebra S R] [IsLocalHom (algebraMap S R)] [Algebra k R] [Algebra k S] [IsScalarTower k S R]

/-- **Alg-1 over a tower.** A non-surjective cotangent map gives a nonzero tangent vector of `R`
killed by all of `S`. -/
theorem exists_tangent_of_not_le' (ev : R →ₐ[k] k) (evS : S →ₐ[k] k)
    (hJ : ¬ maximalIdeal R ≤ Ideal.map (algebraMap S R) (maximalIdeal S) ⊔ maximalIdeal R ^ 2) :
    ∃ h : R →ₐ[k] DualNumber k, (∀ r, (h r).fst = ev r) ∧
      (∀ s, (h (algebraMap S R s)).snd = 0) ∧ ∃ r, (h r).snd ≠ 0 := by
  obtain ⟨h, h1, h2, h3⟩ := exists_tangent_of_not_le (S := S) ev (mem_of_ev_eq_zero ev) hJ
  refine ⟨h, h1, fun s ↦ ?_, h3⟩
  have e : algebraMap S R s =
      algebraMap S R (s - algebraMap k S (evS s)) + algebraMap k R (evS s) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply, sub_add_cancel]
  rw [e, map_add, TrivSqZeroExt.snd_add, h2 _ (sub_algebraMap_mem evS s), h.commutes]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

end Tower

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_IsogDegB_Sep =====
section

/-!
# S4-IsogDegB, file Sep: an injective differential makes `φ` unramified at the identity

Sep-3: if `dφ` is injective on the tangent space at `e`, the cotangent map of the stalk map
`φ♯ : 𝒪_{A,φ e} → 𝒪_{A,e}` is surjective (`𝔪_e = φ♯ 𝔪 + 𝔪_e²`). Otherwise `DerT` gives a nonzero
tangent vector killed by `φ♯`, i.e. a nontrivial element of the kernel of `dφ`.
Sep-4 (first half): then `φ♯` is formally unramified (`Unram`), hence quasi-finite, so `φ` is
quasi-finite at `e` and locally quasi-finite (`IsogDegA.locallyQuasiFinite_of_quasiFiniteAt`).
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

section Sep

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

/-- `ρ : 𝒪_{A,e} → 𝒪_{A,φ e}` along `φ e = e`. -/
noncomputable abbrev rho (φ : A ⟶ A) [IsMonHom φ] :
    A.left.presheaf.stalk (pt A 1) ⟶ A.left.presheaf.stalk (φ.left (pt A 1)) :=
  A.left.presheaf.stalkSpecializes (specializes_of_eq (left_pt_one φ))

theorem kS_rho_stalkMap (φ : A ⟶ A) [IsMonHom φ] :
    kS A ≫ rho φ ≫ φ.left.stalkMap (pt A 1) = kS A := kS_sharp φ

/-- Residues of `φ♯` exhaust the residue field (constants lift). -/
theorem exists_res_stalk (φ : A ⟶ A) [IsMonHom φ] (r : A.left.presheaf.stalk (pt A 1)) :
    ∃ s, r - (φ.left.stalkMap (pt A 1)).hom s ∈ maximalIdeal (A.left.presheaf.stalk (pt A 1)) := by
  refine ⟨(kS A ≫ rho φ).hom ((ev0 A).hom r), ?_⟩
  have e : (φ.left.stalkMap (pt A 1)).hom ((kS A ≫ rho φ).hom ((ev0 A).hom r)) =
      (kS A).hom ((ev0 A).hom r) := by
    show (kS A ≫ rho φ ≫ φ.left.stalkMap (pt A 1)).hom ((ev0 A).hom r) = _
    rw [kS_rho_stalkMap]
  rw [e, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 : (ev0 A).hom ((kS A).hom ((ev0 A).hom r)) = (ev0 A).hom r := by
    show (kS A ≫ ev0 A).hom _ = _
    rw [kS_ev0]; rfl
  have h0 : (ev0 A).hom (r - (kS A).hom ((ev0 A).hom r)) = 0 := by
    rw [map_sub, h1, sub_self]
  exact not_isUnit_zero (h0 ▸ hu.map (ev0 A).hom)

/-- **Sep-3.** An injective differential makes the cotangent map at `e` surjective. -/
theorem cotangent_le_of_injective (φ : A ⟶ A) [IsMonHom φ] (hinj : Function.Injective (dφ φ)) :
    maximalIdeal (A.left.presheaf.stalk (pt A 1)) ≤
      Ideal.map (φ.left.stalkMap (pt A 1)).hom
          (maximalIdeal (A.left.presheaf.stalk (φ.left (pt A 1)))) ⊔
        maximalIdeal (A.left.presheaf.stalk (pt A 1)) ^ 2 := by
  let : Algebra k (A.left.presheaf.stalk (pt A 1)) := (kS A).hom.toAlgebra
  let : Algebra k (A.left.presheaf.stalk (φ.left (pt A 1))) := (kS A ≫ rho φ).hom.toAlgebra
  let : Algebra (A.left.presheaf.stalk (φ.left (pt A 1))) (A.left.presheaf.stalk (pt A 1)) :=
    (φ.left.stalkMap (pt A 1)).hom.toAlgebra
  have : IsLocalHom (algebraMap (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1))) :=
    inferInstanceAs (IsLocalHom (φ.left.stalkMap (pt A 1)).hom)
  have : IsScalarTower k (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1)) :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      show (kS A).hom c = (kS A ≫ rho φ ≫ φ.left.stalkMap (pt A 1)).hom c
      rw [kS_rho_stalkMap]
  let ev : A.left.presheaf.stalk (pt A 1) →ₐ[k] k :=
    { toRingHom := (ev0 A).hom
      commutes' := fun c ↦ by
        show (kS A ≫ ev0 A).hom c = c
        rw [kS_ev0]; rfl }
  let evS : A.left.presheaf.stalk (φ.left (pt A 1)) →ₐ[k] k :=
    { toRingHom := (φ.left.stalkMap (pt A 1) ≫ ev0 A).hom
      commutes' := fun c ↦ by
        show ((kS A ≫ rho φ ≫ φ.left.stalkMap (pt A 1)) ≫ ev0 A).hom c = c
        rw [kS_rho_stalkMap, kS_ev0]; rfl }
  by_contra hJ
  obtain ⟨h, h1, h2, r, hr⟩ := exists_tangent_of_not_le' ev evS hJ
  have hloc : IsLocalHom (CommRingCat.ofHom h.toRingHom).hom := ⟨fun x hx ↦ by
    have hx' : IsUnit ((ev0 A).hom x) := by
      have := TrivSqZeroExt.isUnit_iff_isUnit_fst.1 hx
      exact (h1 x) ▸ this
    exact isUnit_of_map_unit (ev0 A).hom x hx'⟩
  have hh : CommRingCat.ofHom h.toRingHom ≫ fstC k = ev0 A := by
    ext x; exact h1 x
  have hk : kS A ≫ CommRingCat.ofHom h.toRingHom =
      CommRingCat.ofHom (algebraMap k (DualNumber k)) := by
    exact CommRingCat.hom_ext (RingHom.ext fun c ↦ h.commutes c)
  have ht : tOf (CommRingCat.ofHom h.toRingHom) hh hk ≠ 1 := by
    intro h0
    have := coeff_tOf (CommRingCat.ofHom h.toRingHom) hh hk r
    rw [h0, coeff_one] at this
    exact hr this.symm
  refine ht (hinj ?_)
  rw [map_one, tan_eq_one_iff]
  intro r'
  rw [coeff_dφ]
  exact (coeff_tOf (CommRingCat.ofHom h.toRingHom) hh hk _).trans (h2 ((rho φ).hom r'))

/-- **Sep-4a.** An injective differential makes `φ` quasi-finite at the identity. -/
theorem quasiFiniteAt_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    (hinj : Function.Injective (dφ φ)) : φ.left.QuasiFiniteAt (pt A 1) := by
  let : Algebra (A.left.presheaf.stalk (φ.left (pt A 1))) (A.left.presheaf.stalk (pt A 1)) :=
    (φ.left.stalkMap (pt A 1)).hom.toAlgebra
  have : IsLocalHom (algebraMap (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1))) :=
    inferInstanceAs (IsLocalHom (φ.left.stalkMap (pt A 1)).hom)
  have : Algebra.EssFiniteType (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1)) := LocallyOfFiniteType.stalkMap φ.left (pt A 1)
  have : Algebra.FormallyUnramified (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1)) :=
    formallyUnramified_of_le (fun r ↦ exists_res_stalk φ r) (cotangent_le_of_injective φ hinj)
  exact (RingHom.quasiFinite_algebraMap (R := A.left.presheaf.stalk (φ.left (pt A 1)))
    (S := A.left.presheaf.stalk (pt A 1))).2 inferInstance

end Sep

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_IsogDegB_SepFF =====
section

/-!
# S4-IsogDegB, file SepFF: an injective differential makes the isogeny separable (Sep-4b)

`φ♯ : 𝒪_{A,φ e} → 𝒪_{A,e}` is formally unramified (file Sep). Composing with the localization
`𝒪_{A,e} → K(A)` and restricting scalars to `φ^* K(A)` makes `K(A) / φ^* K(A)` formally unramified,
hence separable. So `deg φ = [K(A) : φ^* K(A)]_s = #Ker φ(k)` (IsogDegA, L24 + L26).
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory IsLocalRing

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

/-- The stalk-to-function-field maps intertwine `f.stalkMap x` and the function-field map. -/
theorem stalkSpec_ffMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace X] [IrreducibleSpace Y]
    [IsDominant f] (x : X) :
    Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ (f x))) ≫
        ffMap f =
      f.stalkMap x ≫ X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x)) := by
  rw [ffMap, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp,
    ← Scheme.Hom.stalkSpecializes_stalkMap]

section Abstract

variable {S R K L : Type*} [CommRing S] [CommRing R] [Field K] [Field L]
  [Algebra S R] [Algebra R L] [IsFractionRing R L] [hKL : Algebra K L]

/-- A formally unramified local map, localized at the generic point, gives a separable extension. -/
theorem isSeparable_of_square [Algebra.FormallyUnramified S R] [hfin : Module.Finite K L]
    (a : S →+* K) (hsq : (algebraMap R L).comp (algebraMap S R) = (algebraMap K L).comp a) :
    Algebra.IsSeparable K L := by
  let _ : Algebra S L := ((algebraMap K L).comp a).toAlgebra
  let _ : Algebra S K := a.toAlgebra
  have : IsScalarTower S K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower S R L :=
    IsScalarTower.of_algebraMap_eq fun s ↦ (RingHom.congr_fun hsq s).symm
  have : Algebra.FormallyUnramified R L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors R)
  have : Algebra.FormallyUnramified S L := Algebra.FormallyUnramified.comp S R L
  have : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_restrictScalars S K L
  exact (Algebra.FormallyUnramified.iff_isSeparable K L).1 this

end Abstract

section Variety

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

/-- An injective differential makes `φ♯` formally unramified. -/
theorem formallyUnramified_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    (hinj : Function.Injective (dφ φ)) :
    @Algebra.FormallyUnramified (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1)) _ _ (φ.left.stalkMap (pt A 1)).hom.toAlgebra := by
  let _ : Algebra (A.left.presheaf.stalk (φ.left (pt A 1))) (A.left.presheaf.stalk (pt A 1)) :=
    (φ.left.stalkMap (pt A 1)).hom.toAlgebra
  have : IsLocalHom (algebraMap (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1))) :=
    inferInstanceAs (IsLocalHom (φ.left.stalkMap (pt A 1)).hom)
  have : Algebra.EssFiniteType (A.left.presheaf.stalk (φ.left (pt A 1)))
      (A.left.presheaf.stalk (pt A 1)) := LocallyOfFiniteType.stalkMap φ.left (pt A 1)
  exact formallyUnramified_of_le (fun r ↦ exists_res_stalk φ r) (cotangent_le_of_injective φ hinj)

/-- **Sep-4b.** An injective differential makes `K(A) / φ^* K(A)` separable. -/
theorem isSeparable_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] [IsDominant φ.left] (hinj : Function.Injective (dφ φ)) :
    @Algebra.IsSeparable A.left.functionField A.left.functionField _ _ (ffAlgebra φ.left) := by
  let _ : Algebra (A.left.presheaf.stalk (φ.left (pt A 1))) (A.left.presheaf.stalk (pt A 1)) :=
    (φ.left.stalkMap (pt A 1)).hom.toAlgebra
  have := formallyUnramified_of_injective φ hinj
  exact isSeparable_of_square (hKL := ffAlgebra φ.left) (hfin := ffMap_finite A φ)
    (A.left.presheaf.stalkSpecializes
      ((genericPoint_spec A.left).specializes (Set.mem_univ (φ.left (pt A 1))))).hom
    (congrArg CommRingCat.Hom.hom (stalkSpec_ffMap φ.left (pt A 1))).symm

/-- An injective differential gives `deg φ = #Ker φ(k)`. -/
theorem degree_eq_card_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] [IsDominant φ.left] (hinj : Function.Injective (dφ φ)) :
    degree φ.left = Nat.card (kerPts A φ) := by
  have hsep := isSeparable_of_injective φ hinj
  letI := ffAlgebra φ.left
  rw [(isogDeg_L24 A φ).1, (card_kerPts A φ).2.1]
  exact (Field.finSepDegree_eq_finrank_of_isSeparable (F := A.left.functionField)
    (E := A.left.functionField)).symm

end Variety

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_IsogDegB_DomA =====
section

/-!
# S4-IsogDegB, file DomA: locally quasi-finite endomorphisms are dominant (O4, part 1)

For an endomorphism `f` of an irreducible scheme with Noetherian underlying space, the closures of
`f^n η` form a descending chain, so `f^n η = f^(n+1) η` for some `n`. Then `η ⤳ f η` lie in one
fibre of `f^n`; if `f` is locally quasi-finite that fibre is discrete, so `f η = η`.
Consequences: an injective differential gives a dominant, separable isogeny with `deg = #Ker`.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

section Iterate

variable {X : Scheme.{u}} (f : X ⟶ X)

/-- `f^n` as a morphism (`f^(n+1) = f ≫ f^n`). -/
noncomputable def iter : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => f ≫ iter n

theorem iter_succ_apply (n : ℕ) (x : X) : iter f (n + 1) x = iter f n (f x) :=
  Scheme.Hom.comp_apply f (iter f n) x

theorem lqf_iter [LocallyQuasiFinite f] : ∀ n, LocallyQuasiFinite (iter f n)
  | 0 => by show LocallyQuasiFinite (𝟙 X); infer_instance
  | n + 1 => by
    have := lqf_iter n
    show LocallyQuasiFinite (f ≫ iter f n); infer_instance

/-- **Dom-1.** A locally quasi-finite endomorphism of an irreducible scheme with Noetherian
underlying space is dominant. -/
theorem isDominant_of_lqf [IrreducibleSpace X] [NoetherianSpace X] [LocallyQuasiFinite f] :
    IsDominant f := by
  have hη : genericPoint X ⤳ f (genericPoint X) :=
    (genericPoint_spec X).specializes (Set.mem_univ _)
  have hx : ∀ n, iter f n (genericPoint X) ⤳ iter f (n + 1) (genericPoint X) := fun n ↦ by
    rw [iter_succ_apply]; exact hη.map (iter f n).continuous
  let U : ℕ →o Opens X :=
    ⟨fun n ↦ ⟨(closure {iter f n (genericPoint X)})ᶜ, isClosed_closure.isOpen_compl⟩,
      monotone_nat_of_le_succ fun n ↦ by
        show (closure {iter f n (genericPoint X)})ᶜ ⊆ (closure {iter f (n + 1) (genericPoint X)})ᶜ
        exact Set.compl_subset_compl.2 (specializes_iff_closure_subset.1 (hx n))⟩
  obtain ⟨n, hn⟩ := wellFoundedGT_iff_monotone_chain_condition.1 inferInstance U
  have hc : closure {iter f n (genericPoint X)} = closure {iter f (n + 1) (genericPoint X)} :=
    compl_injective (congrArg (fun V : Opens X ↦ (V : Set X)) (hn (n + 1) (Nat.le_succ n)))
  have he : iter f (n + 1) (genericPoint X) = iter f n (genericPoint X) :=
    ((specializes_iff_closure_subset.2 hc.le).antisymm (hx n)).eq
  rw [iter_succ_apply] at he
  have := lqf_iter f n
  exact isDominant_of_map_genericPoint f
    (((iter f n).isDiscrete_preimage_singleton (iter f n (genericPoint X))).eq_of_specializes
      hη rfl he).symm

end Iterate

section Variety

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

omit [GrpObj A] in
theorem noetherianSpace_left [IsProper A.hom] : NoetherianSpace A.left := by
  have := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : IsNoetherian A.left := { }
  infer_instance

/-- An isogeny quasi-finite at one point is dominant. -/
theorem isDominant_of_quasiFiniteAt (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] (x₀ : A.left) (h₀ : φ.left.QuasiFiniteAt x₀) : IsDominant φ.left := by
  have := locallyQuasiFinite_of_quasiFiniteAt A φ x₀ h₀
  have := noetherianSpace_left (A := A)
  exact isDominant_of_lqf φ.left

/-- **L27 (separability criterion).** An injective differential makes `φ` a dominant isogeny
with `K(A) / φ^* K(A)` separable and `deg φ = #Ker φ(k)`. -/
theorem separable_of_injective (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] (hinj : Function.Injective (dφ φ)) :
    ∃ _ : IsDominant φ.left,
      @Algebra.IsSeparable A.left.functionField A.left.functionField _ _ (ffAlgebra φ.left) ∧
      degree φ.left = Nat.card (kerPts A φ) := by
  have := isDominant_of_quasiFiniteAt φ (pt A 1) (quasiFiniteAt_of_injective φ hinj)
  exact ⟨this, isSeparable_of_injective φ hinj, degree_eq_card_of_injective φ hinj⟩

end Variety

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_IsogDegB_DomB =====
section

/-!
# S4-IsogDegB, file DomB: finite kernel ⇔ dominant ⇔ deg ≠ 0 (O4, part 2)

`Ker φ(k)` finite ⇒ the fibre `φ⁻¹{e}` is finite (it is closed, and in the Jacobson space `A` its
closed points, which are the kernel points, are dense) ⇒ `φ` is quasi-finite at `e`
(the fibre scheme is finite, hence discrete) ⇒ `φ` is dominant (DomA).
Conversely a dominant `φ` has a finite kernel (IsogDegA, L26), and `deg φ = 0` iff `φ` is not dominant.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IsogDegB

open RamanujanPetersson.IsogDegA

universe u

set_option backward.isDefEq.respectTransparency.types false in
/-- A finite fibre makes a morphism locally of finite type quasi-finite there (cf. Stacks 02UP). -/
theorem quasiFiniteAt_of_finite_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : (f ⁻¹' {f x}).Finite) : f.QuasiFiniteAt x := by
  have : Finite (f ⁻¹' {f x}) := hx.to_subtype
  have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr ‹_›
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)

/-- A closed set of a Jacobson space with finitely many closed points is finite. -/
theorem finite_of_closedPoints {X : Type*} [TopologicalSpace X] [JacobsonSpace X] {Z : Set X}
    (hZ : IsClosed Z) (h : (Z ∩ closedPoints X).Finite) : Z.Finite := by
  have hcl : IsClosed (Z ∩ closedPoints X) := by
    rw [← Set.biUnion_of_singleton (Z ∩ closedPoints X)]
    exact h.isClosed_biUnion fun x hx ↦ hx.2
  rw [← closure_inter_closedPoints hZ, hcl.closure_eq]
  exact h

theorem finrank_ne_zero_of_finite {K L : Type*} [Field K] [Field L] [hKL : Algebra K L]
    [hfin : Module.Finite K L] : Module.finrank K L ≠ 0 :=
  Module.finrank_pos.ne'

section Variety

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [GrpObj A]

/-- Finitely many kernel points ⇒ finite fibre over `e`. -/
theorem finite_fiber_of_finite_ker (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    (h : Finite (kerPts A φ)) : (φ.left ⁻¹' {pt A 1}).Finite := by
  have := LocallyOfFiniteType.jacobsonSpace A.hom
  refine finite_of_closedPoints (IsClosed.preimage φ.left.continuous (isClosed_pt A 1)) ?_
  refine (Set.finite_range (fun c : kerPts A φ ↦ pt A c.1)).subset ?_
  rintro z ⟨hz, hzc⟩
  obtain ⟨c, rfl⟩ := exists_pt_eq A z hzc
  refine ⟨⟨c, pt_injective A ?_⟩, rfl⟩
  rw [pt_comp]
  exact hz

/-- Finitely many kernel points ⇒ `φ` dominant. -/
theorem isDominant_of_finite_ker (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] (h : Finite (kerPts A φ)) : IsDominant φ.left := by
  refine isDominant_of_quasiFiniteAt φ (pt A 1) (quasiFiniteAt_of_finite_fiber φ.left (pt A 1) ?_)
  rw [left_pt_one φ]
  exact finite_fiber_of_finite_ker φ h

/-- **Finite kernel ⇔ dominant.** -/
theorem isDominant_iff_finite_ker (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] : IsDominant φ.left ↔ Finite (kerPts A φ) :=
  ⟨fun _ ↦ (card_kerPts A φ).1, isDominant_of_finite_ker φ⟩

/-- **deg φ = 0 ⇔ Ker φ(k) infinite** (the `deg_eq_zero_iff` field of `DegreeData`). -/
theorem degree_eq_zero_iff (φ : A ⟶ A) [IsMonHom φ] [IsAlgClosed k] [IsProper A.hom]
    [IsIntegral A.left] : degree φ.left = 0 ↔ Infinite (kerPts A φ) := by
  rw [← not_finite_iff_infinite, ← isDominant_iff_finite_ker φ]
  constructor
  · intro h0 hd
    rw [(isogDeg_L24 A φ).1] at h0
    exact finrank_ne_zero_of_finite (hKL := ffAlgebra φ.left) (hfin := ffMap_finite A φ) h0
  · exact isogDeg_L24_zero A φ

end Variety

end RamanujanPetersson.IsogDegB


end

-- ===== S4.Def_RP_IntersectC_NonDom =====
section

/-!
# S4-IntersectC, file NonDom: the projection formula (L35, O6)

* `inum_comap_nondom`: for non-dominant `φ`, `((φ^* D_1) ⋯ (φ^* D_g)) = 0`: a generic translated
  intersection of the pullbacks is stable under the (infinite) kernel, hence empty.
* `inum_comap`: **L35**, `((φ^* D_1) ⋯ (φ^* D_g)) = deg φ · (D_1 ⋯ D_g)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA RamanujanPetersson.IntersectB

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- **L35** (non-dominant case): the pullbacks along a non-dominant `φ` have intersection `0`. -/
theorem inum_comap_nondom (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (φ : A ⟶ A) [IsMonHom φ] (h : ¬ IsDominant φ.left)
    (hD' : ∀ i, ((D i).comap φ.left).support ≠ ⊤) :
    inum A g hdim (fun i => (D i).comap φ.left) hD' = 0 := by
  have hinf : Infinite (kerPts A φ) :=
    (IsogDegB.degree_eq_zero_iff φ).mp (isogDeg_L24_zero A φ h)
  obtain ⟨U, hU, hne, hUs⟩ := inum_spec A g hdim _ hD'
  have := isProper_Pw A g
  obtain ⟨c, hc⟩ := exists_pt_mem (Pw A g) U hU.isLocallyClosed hne
  obtain ⟨hfin, hlen⟩ := hUs c hc
  rw [← hlen]
  set J := Zid A (fun i => (D i).comap φ.left) (fun i => c ≫ proj A g i) with hJ
  have hS : ∀ x, x ∈ (J.support : Set A.left) ↔
      φ.left x ∈ ((Zid A D (fun i => (c ≫ proj A g i) ≫ φ)).support : Set A.left) := by
    intro x
    rw [hJ, Zid_comap, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_preimage]
  have hempty : (J.support : Set A.left) = ∅ := by
    by_contra hne'
    obtain ⟨b, hb⟩ := exists_pt_mem A _ J.support.isClosed.isLocallyClosed
      (Set.nonempty_iff_ne_empty.2 hne')
    have hmaps : ∀ κ : kerPts A φ, pt A (b * κ.1) ∈ (J.support : Set A.left) := by
      intro κ
      rw [hS, ← pt_comp, mul_comp, κ.2, _root_.mul_one, pt_comp, ← hS]
      exact hb
    have hinj : Function.Injective
        (fun κ : kerPts A φ => (⟨pt A (b * κ.1), hmaps κ⟩ : (J.support : Set A.left))) := by
      intro κ κ' hk
      have h1 : pt A (b * κ.1) = pt A (b * κ'.1) := congrArg Subtype.val hk
      exact Subtype.ext (_root_.mul_left_cancel (pt_injective A h1))
    have : Infinite (J.support : Set A.left) := Infinite.of_injective _ hinj
    exact (Set.infinite_coe_iff.mp this) hfin
  have hJtop : J = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    ext1
    exact hempty
  rw [hJtop, len_top]

/-- **L35** (projection formula): `((φ^* D_1) ⋯ (φ^* D_g)) = deg φ · (D_1 ⋯ D_g)`, where
`deg φ = 0` for non-dominant `φ`. -/
theorem inum_comap (g : ℕ) (hdim : ∀ x : A.left, Order.height x ≤ g)
    (D : Fin g → A.left.IdealSheafData) (hD : ∀ i, (D i).support ≠ ⊤) (φ : A ⟶ A) [IsMonHom φ]
    (hD' : ∀ i, ((D i).comap φ.left).support ≠ ⊤) :
    inum A g hdim (fun i => (D i).comap φ.left) hD' = degree φ.left * inum A g hdim D hD := by
  by_cases h : IsDominant φ.left
  · exact inum_comap_dom A g hdim D hD φ hD'
  · rw [isogDeg_L24_zero A φ h, zero_mul]
    exact inum_comap_nondom A g hdim D φ h hD'

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_JacComplete_Ext =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `Ext`: rational maps to `J` (first half of L21)

Weil's extension theorem (S4-JacDivisors, Milne I.3.2) applied to the proper group `J` (L19, `isProper_Jac`):
* `domain_eq_top_Jac`: a rational map over `K` from a smooth `V` (with `V`, `V ×_K V` integral) to `J` is defined
  everywhere;
* `extJ f hf : V ⟶ J`, `ι_extJ` (it restricts to `f` on the domain of `f`), `eq_extJ` (unique);
* `UO V U`, `ιU V U` (a dense open `U ⊆ V` over `K`) and `eq_of_kpt_eq`: maps `V ⟶ J` from a reduced `V` locally of
  finite type are determined by their values at the `K`-points of a dense open.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open Polynomial

namespace RamanujanPetersson.JacComplete

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open RamanujanPetersson.JacLaw

universe u

section Ext

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable {V : Over (Spec (.of K))} [IsReduced V.left]

variable (V) in
/-- An open `U ⊆ V` as an object over `Spec K`. -/
noncomputable abbrev UO (U : V.left.Opens) : Over (Spec (.of K)) := Over.mk (U.ι ≫ V.hom)

variable (V) in
/-- The inclusion `U ⟶ V` over `Spec K`. -/
noncomputable abbrev ιU (U : V.left.Opens) : UO V U ⟶ V := Over.homMk U.ι rfl

end Ext

end RamanujanPetersson.JacComplete


end

-- ===== S4.Def_RP_ThetaSquare_Def =====
section

/-!
# Unit S4-ThetaSquare, file Def: the theta divisor `Θ` of the Jacobian (L38, Milne III.5)

* `irreducibleSpace_X1`, `isIntegral_X1`: the curve `X1 = Sym¹ X` is integral (its charts are domains and pairwise meet);
* `isIntegral_PP n`: `X1^n` is integral (`IntersectA.isIntegral_pullback`);
* `W P0 := Φ_{g-1}(X1^{g-1}) ⊆ J` (`isClosed_W`, `isIrreducible_W`), `zTheta P0` its generic point;
* `Theta P0 : AlgebraicCycle J ℤ`, the prime cycle `[W_{g-1}]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Def

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

instance isIntegral_cht (A : (ChartIdx K)ᵒᵖ) : IsIntegral (cht K F A) := by
  show IsIntegral (Spec (CommRingCat.of (SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1)))
  infer_instance

variable (K F) in
/-- **The curve `X1` is irreducible**: the charts are irreducible, open, cover `X1` and any two meet in a third. -/
theorem irreducibleSpace_X1 : IrreducibleSpace (X1 K F) := by
  let D := symDiagram K (algebraMap K[X] F X) 1
  let A0 : (ChartIdx K)ᵒᵖ := op ⟨{0}, Finset.singleton_nonempty 0⟩
  haveI : Nonempty (X1 K F) := by
    obtain ⟨z⟩ : Nonempty (D.obj A0) := (inferInstance : IsIntegral (cht K F A0)).nonempty
    exact ⟨colimit.ι D A0 z⟩
  refine IntersectA.irreducibleSpace_of_cover (fun A : (ChartIdx K)ᵒᵖ => Set.range (colimit.ι D A))
    (fun A => (colimit.ι D A).isOpenEmbedding.isOpen_range) (fun A => ?_) (fun y => ?_) (fun A A' => ?_)
  · haveI hA : IrreducibleSpace (D.obj A) := (inferInstance : IrreducibleSpace (cht K F A))
    have h := ((IrreducibleSpace.isIrreducible_univ (D.obj A)).image _
      (colimit.ι D A).continuous.continuousOn).isPreirreducible
    rw [Set.image_univ] at h
    exact h
  · obtain ⟨A, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective D y
    exact ⟨A, z, rfl⟩
  · let B : ChartIdx K := ⟨A.unop.1 ∪ A'.unop.1, A.unop.2.mono Finset.subset_union_left⟩
    obtain ⟨z⟩ : Nonempty (D.obj (op B)) := (inferInstance : IsIntegral (cht K F (op B))).nonempty
    have h1 := colimit.w D (homOfLE (show A.unop ≤ B from Finset.subset_union_left)).op
    have h2 := colimit.w D (homOfLE (show A'.unop ≤ B from Finset.subset_union_right)).op
    refine ⟨colimit.ι D (op B) z, ⟨D.map (homOfLE (show A.unop ≤ B from Finset.subset_union_left)).op z, ?_⟩,
      ⟨D.map (homOfLE (show A'.unop ≤ B from Finset.subset_union_right)).op z, ?_⟩⟩
    · rw [← h1]; rfl
    · rw [← h2]; rfl

instance isIntegral_X1 : IsIntegral (X1 K F) := by
  haveI := irreducibleSpace_X1 K F
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

/-- **`X1^n` is integral.** -/
instance isIntegral_PP (n : ℕ) : IsIntegral (PP K F n).left := by
  induction n with
  | zero =>
    show IsIntegral (Spec (.of K))
    infer_instance
  | succ n ih =>
    haveI := ih
    show IsIntegral (pullback (PP K F n).hom (toSpecK K (algebraMap K[X] F X) 1))
    exact IntersectA.isIntegral_pullback (PP K F n).hom (toSpecK K (algebraMap K[X] F X) 1)

instance irreducibleSpace_PP (n : ℕ) : IrreducibleSpace (PP K F n).left := inferInstance

variable (K F) in
/-- `g - 1`. -/
noncomputable abbrev n0 : ℕ := genusFK K F - 1

variable (P0 : Place K F)

end Def

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Ne =====
section

/-!
# Unit S4-ThetaSquare, file Ne: `W_{g-1} ≠ J`, so `Θ` has codimension `≥ 1`

* `not_clsK_eq_eff`: for a nonspecial `g`-set `C` and a point `R ∉ C`, the class of `Zdiv C - [R]` (degree `g - 1`)
  contains no effective divisor (an `f` with `div f + Zdiv C - [R] ≥ 0` lies in `L(Zdiv C)`, so is constant);
* `exists_not_mem_W`: for `g ≥ 1` the `K`-point with class `Σ_{φ ∈ C} ([φ] - [P0]) - ([R] - [P0])` is not on `W`
  (Riemann's theorem `mem_W_iff`);
* `one_le_coheight_zTheta`: `1 ≤ coheight (zTheta P0)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Ne

open Classical
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

variable (P0 : Place K F)

theorem clsK_sum {α : Type*} (s : Finset α) (D : α → Places.Divisor K F) :
    clsK K F (∑ i ∈ s, D i) = ∑ i ∈ s, clsK K F (D i) :=
  map_sum (QuotientAddGroup.mk' (PrincK K F)) D s

/-- **A non-effective class of degree `g - 1`**: `Zdiv C - [R]` for a nonspecial `C` and `R ∉ C`. -/
theorem not_clsK_eq_eff {C : Finset (Rfin K F →ₐ[K] K)} (hC : IsNS K F C) {R : Rfin K F →ₐ[K] K}
    (hR : R ∉ C) {E : Places.Divisor K F} (hE : 0 ≤ E)
    (h : clsK K F (Zdiv C - Finsupp.single (Sum.inl (ptP R)) 1) = clsK K F E) : False := by
  obtain ⟨f, hf, hfd⟩ := (mem_PrincK K F).1 ((clsK_eq_iff K F).1 h)
  have hE' : PlacesK.div f + (Zdiv C - Finsupp.single (Sum.inl (ptP R)) 1) = E := by rw [hfd]; abel
  have hDC : Zdiv C - Finsupp.single (Sum.inl (ptP R)) 1 ≤ Zdiv C :=
    sub_le_self _ (Finsupp.single_nonneg.2 zero_le_one)
  have hfL : f ∈ LFK K F (Zdiv C) := by
    rw [mem_LFK hf]
    calc (0 : Places.Divisor K F) ≤ E := hE
      _ = PlacesK.div f + (Zdiv C - Finsupp.single (Sum.inl (ptP R)) 1) := hE'.symm
      _ ≤ PlacesK.div f + Zdiv C := add_le_add (le_refl _) hDC
  obtain ⟨c, rfl⟩ := hC f hfL
  have h0 : (PlacesK.div (algebraMap K F c) : Places.Divisor K F) = 0 :=
    (PlacesK.div_eq_zero_iff (K := K) (F := F) hf).2 (IntermediateField.algebraMap_mem _ c)
  rw [h0, zero_add] at hE'
  have hv := congrArg (fun G : Places.Divisor K F => G (Sum.inl (ptP R))) hE'
  have hv0 : (0 : ℤ) ≤ E (Sum.inl (ptP R)) := Finsupp.le_def.1 hE _
  simp only [Finsupp.coe_sub, Pi.sub_apply, Zdiv_inl_ptP, if_neg hR, Finsupp.single_eq_same] at hv
  omega

end Ne

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_ThetaSquare_Stab =====
section

/-!
# Unit S4-ThetaSquare, file Stab: the stabiliser of `W_{g-1}` is trivial (divisor form, Riemann-Roch only)

* `ell_add_single_le`: `ℓ(D + P) ≤ ℓ(D) + 1`;
* `card_le_ell`, `exists_ell_zero`, `exists_ell_one`: for `deg B = 0` and `ℓ(B) = 0` there is a `g`-set `C` of
  distinct points with `ℓ(B + Zdiv C) = 1` (greedy choice, as in `JacLaw_GenNS`, twisted by `B`);
* `exists_eq_of_ell_one`: if `ℓ(D) = 1`, the class of `D` contains exactly one effective divisor;
* **`mem_PrincK_of_stab`**: if `deg B = 0` and `Zdiv S + B` is equivalent to an effective divisor for every
  `(g-1)`-set `S`, then `B` is principal (each point `P` of `C` lies on the unique effective `D'' ~ B + Zdiv C`,
  so `D'' = Zdiv C`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Stab

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- `ℓ(D + P) ≤ ℓ(D) + 1` (Riemann-Roch). -/
theorem ell_add_single_le (D : Places.Divisor K F) (v : Place K F) :
    ellFK K F (D + Finsupp.single v 1) ≤ ellFK K F D + 1 := by
  obtain ⟨W0, hW⟩ := exists_isCanonicalFK (K := K) (F := F)
  have hk := constField_eq_bot' (K := K) (F := F)
  have h1 := riemannRochFK' hk hW (D + Finsupp.single v 1)
  have h2 := riemannRochFK' hk hW D
  have h3 : ellFK K F (W0 - (D + Finsupp.single v 1)) ≤ ellFK K F (W0 - D) :=
    ellFK_mono (sub_le_sub_left (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one)) _)
  rw [PlacesK.Divisor.deg_add, deg_single_one] at h1
  omega

/-- If every `P ∈ S` raises `ℓ` above `ℓ(D) = 0`, then `ℓ(D + Zdiv S) ≥ #S`. -/
theorem card_le_ell (D : Places.Divisor K F) (hD : ellFK K F D = 0) (S : Finset (Rfin K F →ₐ[K] K))
    (hbad : ∀ φ ∈ S, 1 ≤ ellFK K F (D + Finsupp.single (Sum.inl (ptP φ)) 1)) :
    S.card ≤ ellFK K F (D + Zdiv S) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert φ S hφ ih =>
    have ih' := ih fun ψ hψ => hbad ψ (Finset.mem_insert_of_mem hψ)
    have hle : D ≤ D + Zdiv S := le_add_of_nonneg_right (Zdiv_nonneg S)
    have hval : (D + Zdiv S) (Sum.inl (ptP φ)) = D (Sum.inl (ptP φ)) := by
      rw [Finsupp.add_apply, Zdiv_inl_ptP, if_neg hφ, add_zero]
    have key := ellFK_step (Sum.inl (ptP φ)) hle hval
    have hb := hbad φ (Finset.mem_insert_self φ S)
    rw [Finset.card_insert_of_notMem hφ, Zdiv_insert hφ, ← add_assoc]
    omega

/-- Greedy step, twisted by `B` (`deg B = 0`, `ℓ(B) = 0`): `i`-sets `C` with `ℓ(B + Zdiv C) = 0` for `i < g`. -/
theorem exists_ell_zero (B : Places.Divisor K F) (hB : ellFK K F B = 0) (hd : B.deg = 0) :
    ∀ i, i + 1 ≤ genusFK K F →
      ∃ C : Finset (Rfin K F →ₐ[K] K), C.card = i ∧ ellFK K F (B + Zdiv C) = 0 := by
  obtain ⟨T, hT, -⟩ := JacComplete.exists_pool (K := K) (F := F) 1 one_ne_zero (2 * genusFK K F)
  intro i
  induction i with
  | zero => intro _; exact ⟨∅, Finset.card_empty, by rw [Zdiv_empty, add_zero, hB]⟩
  | succ i ih =>
    intro hi
    obtain ⟨C, hCc, hC0⟩ := ih (by omega)
    by_contra hne
    have hbad : ∀ φ ∈ T \ C, 1 ≤ ellFK K F (B + Zdiv C + Finsupp.single (Sum.inl (ptP φ)) 1) := by
      intro φ hφ
      have hφC : φ ∉ C := (Finset.mem_sdiff.1 hφ).2
      by_contra h0
      exact hne ⟨insert φ C, by rw [Finset.card_insert_of_notMem hφC, hCc], by
        rw [Zdiv_insert hφC, ← add_assoc]; omega⟩
    have hge := card_le_ell (B + Zdiv C) hC0 (T \ C) hbad
    have hcard := Finset.le_card_sdiff C T
    have hdeg : (B + Zdiv C + Zdiv (T \ C)).deg = ((i + (T \ C).card : ℕ) : ℤ) := by
      rw [PlacesK.Divisor.deg_add, PlacesK.Divisor.deg_add, hd, deg_Zdiv, deg_Zdiv, hCc]; push_cast; ring
    have hrr := ellFK_eq_of_deg (constField_eq_bot' (K := K) (F := F)) (D := B + Zdiv C + Zdiv (T \ C))
      (by rw [hdeg]; push_cast; omega)
    rw [hdeg] at hrr
    push_cast at hrr
    omega

/-- A `g`-set `C` with `ℓ(B + Zdiv C) = 1`, for `deg B = 0`, `ℓ(B) = 0`, `g ≥ 1`. -/
theorem exists_ell_one (hg : 0 < genusFK K F) (B : Places.Divisor K F) (hB : ellFK K F B = 0)
    (hd : B.deg = 0) :
    ∃ C : Finset (Rfin K F →ₐ[K] K), C.card = genusFK K F ∧ ellFK K F (B + Zdiv C) = 1 := by
  obtain ⟨C, hCc, hC0⟩ := exists_ell_zero B hB hd (genusFK K F - 1) (by omega)
  obtain ⟨T, hT, -⟩ := JacComplete.exists_pool (K := K) (F := F) 1 one_ne_zero (genusFK K F)
  obtain ⟨φ, -, hφC⟩ : ∃ φ ∈ T, φ ∉ C := by
    by_contra h
    push Not at h
    have := Finset.card_le_card (fun x hx => h x hx)
    omega
  refine ⟨insert φ C, by rw [Finset.card_insert_of_notMem hφC, hCc]; omega, le_antisymm ?_ ?_⟩
  · have := ell_add_single_le (B + Zdiv C) (Sum.inl (ptP φ))
    rw [Zdiv_insert hφC, ← add_assoc]
    omega
  · have := riemann_inequalityFK' (constField_eq_bot' (K := K) (F := F)) (B + Zdiv (insert φ C))
    rw [PlacesK.Divisor.deg_add, hd, deg_Zdiv, Finset.card_insert_of_notMem hφC, hCc] at this
    omega

/-- If `ℓ(D) = 1`, the class of `D` contains exactly one effective divisor, `div f0 + D`. -/
theorem exists_eq_of_ell_one {D : Places.Divisor K F} (h1 : ellFK K F D = 1) :
    ∃ f0 : F, f0 ≠ 0 ∧ 0 ≤ PlacesK.div f0 + D ∧ ∀ E : Places.Divisor K F, 0 ≤ E →
      clsK K F E = clsK K F D → E = PlacesK.div f0 + D := by
  rw [ellFK_def] at h1
  obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.1 h1
  have hv0 : (v : F) ≠ 0 := fun h => hv (Subtype.ext h)
  refine ⟨v, hv0, (mem_LFK hv0).1 v.2, fun E hE hc => ?_⟩
  obtain ⟨h, hh, hdiv⟩ := (mem_PrincK K F).1 ((clsK_eq_iff K F).1 hc.symm)
  have hL : h ∈ LFK K F D := by
    rw [mem_LFK hh, hdiv, show -D + E + D = E by abel]
    exact hE
  obtain ⟨a, ha⟩ := hall ⟨h, hL⟩
  have ha' : algebraMap K F a * v = h := by
    rw [← Algebra.smul_def]
    exact congrArg Subtype.val ha
  have ha0 : algebraMap K F a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at ha'
    exact hh ha'.symm
  have hdc : (PlacesK.div (algebraMap K F a) : Places.Divisor K F) = 0 :=
    (PlacesK.div_eq_zero_iff (K := K) (F := F) ha0).2 (IntermediateField.algebraMap_mem _ a)
  rw [← ha', PlacesK.div_mul ha0 hv0, hdc, zero_add] at hdiv
  rw [hdiv]
  abel

/-- **Trivial stabiliser, divisor form**: if `deg B = 0` and `Zdiv S + B` is equivalent to an effective divisor for
every `(g-1)`-set `S` of distinct points, then `B` is principal. -/
theorem mem_PrincK_of_stab (hg : 0 < genusFK K F) (B : Places.Divisor K F) (hd : B.deg = 0)
    (hstab : ∀ S : Finset (Rfin K F →ₐ[K] K), S.card = n0 K F →
      ∃ E : Places.Divisor K F, 0 ≤ E ∧ clsK K F E = clsK K F (Zdiv S + B)) :
    B ∈ PrincK K F := by
  by_cases hB : ellFK K F B = 0
  swap
  · have hne : LFK K F B ≠ ⊥ := by
      intro h
      apply hB
      rw [ellFK_def, h, finrank_bot]
    obtain ⟨f, hfL, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hz := eq_zero_of_nonneg_of_deg ((mem_LFK hf).1 hfL)
      (by rw [PlacesK.Divisor.deg_add, PlacesK.deg_div hf, hd, add_zero])
    exact ⟨f⁻¹, inv_ne_zero hf, by rw [divK_inv K hf]; exact (eq_neg_of_add_eq_zero_right hz).symm⟩
  obtain ⟨C, hCc, hC1⟩ := exists_ell_one hg B hB hd
  obtain ⟨f0, hf0, hpos, huniq⟩ := exists_eq_of_ell_one hC1
  have hpt : ∀ φ ∈ C, 1 ≤ (PlacesK.div f0 + (B + Zdiv C) : Places.Divisor K F) (Sum.inl (ptP φ)) := by
    intro φ hφ
    have hS : (C.erase φ).card = n0 K F := by
      rw [Finset.card_erase_of_mem hφ, hCc]
    obtain ⟨E, hE, hcl⟩ := hstab _ hS
    have hZ : Zdiv C = Zdiv (C.erase φ) + Finsupp.single (Sum.inl (ptP φ)) 1 := by
      conv_lhs => rw [← Finset.insert_erase hφ]
      exact Zdiv_insert (Finset.notMem_erase φ _)
    have hcls : clsK K F (E + Finsupp.single (Sum.inl (ptP φ)) 1) = clsK K F (B + Zdiv C) := by
      rw [hZ, show B + (Zdiv (C.erase φ) + Finsupp.single (Sum.inl (ptP φ)) 1) =
        (Zdiv (C.erase φ) + B) + Finsupp.single (Sum.inl (ptP φ)) 1 by abel,
        clsK_add (K := K) (F := F) E, clsK_add (K := K) (F := F) (Zdiv (C.erase φ) + B), hcl]
    have hE' := huniq _ (add_nonneg hE (Finsupp.single_nonneg.2 zero_le_one)) hcls
    rw [← hE', Finsupp.add_apply, Finsupp.single_eq_same]
    have := Finsupp.le_def.1 hE (Sum.inl (ptP φ))
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  have hge : Zdiv C ≤ PlacesK.div f0 + (B + Zdiv C) := by
    rw [Finsupp.le_def]
    intro v
    by_cases hv : ∃ φ ∈ C, v = Sum.inl (ptP φ)
    · obtain ⟨φ, hφ, rfl⟩ := hv
      rw [Zdiv_inl_ptP, if_pos hφ]
      exact hpt φ hφ
    · have h0 : Zdiv C v = 0 := by
        rw [Zdiv, Finsupp.finsetSum_apply]
        refine Finset.sum_eq_zero fun φ hφ => ?_
        rw [Finsupp.single_apply, if_neg]
        exact fun h => hv ⟨φ, hφ, h.symm⟩
      rw [h0]
      exact Finsupp.le_def.1 hpos v
  have h0 : 0 ≤ PlacesK.div f0 + B := by
    have := sub_nonneg.2 hge
    rwa [show PlacesK.div f0 + (B + Zdiv C) - Zdiv C = PlacesK.div f0 + B by abel] at this
  have hz := eq_zero_of_nonneg_of_deg h0 (by rw [PlacesK.Divisor.deg_add, PlacesK.deg_div hf0, hd, add_zero])
  exact ⟨f0⁻¹, inv_ne_zero hf0, by rw [divK_inv K hf0]; exact (eq_neg_of_add_eq_zero_right hz).symm⟩

end Stab

end RamanujanPetersson.ThetaSquare


end

-- ===== S4.Def_RP_IntersectC_Pit =====
section

/-!
# S4-IntersectC, file Pit: Krull's height theorem on a scheme (L36, O8)

* `exists_gen_of_span`: if `J` is generated on an affine chart by `i` sections and `y` lies in
  its support with `i < coheight y`, some other point of the support generalizes `y`.
* `exists_span_of_iSup`: a finite sup of locally principal ideal sheaves is generated, near any
  point, by one section per term.
* `locPrin_comap_iso`: pulling back along an isomorphism keeps an ideal sheaf locally principal.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.IntersectB

/-- A finite sup of locally principal ideal sheaves is locally generated by one section per term. -/
theorem exists_span_of_iSup {X : Scheme.{u}} {n : ℕ} (I : Fin n → X.IdealSheafData)
    (hI : ∀ j (x : X), ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧
      ∃ u, (I j).ideal W = Ideal.span {u}) (x : X) :
    ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧
      ∃ v : Fin n → Γ(X, W), (⨆ j, I j).ideal W = Ideal.span (Set.range v) := by
  choose W hxW u hu using fun j => hI j x
  let O : X.Opens := ⟨⋂ j, ((W j : X.Opens) : Set X), isOpen_iInter_of_finite fun j => (W j).1.2⟩
  have hxO : x ∈ O := Set.mem_iInter.mpr hxW
  obtain ⟨W0, hW0, hxW0, hle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxO
  have hle' : ∀ j, (⟨W0, hW0⟩ : X.affineOpens) ≤ W j := fun j z hz => Set.mem_iInter.mp (hle hz) j
  refine ⟨⟨W0, hW0⟩, hxW0, fun j => X.presheaf.map (homOfLE (hle' j)).op (u j), ?_⟩
  rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply, ← Set.iUnion_singleton_eq_range,
    Ideal.span_iUnion]
  exact iSup_congr fun j => ideal_res_span (I j) (hle' j) (hu j)

/-- Pulling back along an isomorphism keeps an ideal sheaf locally principal. -/
theorem locPrin_comap_iso {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) [IsIso f]
    (hI : ∀ y : Y, ∃ W : Y.affineOpens, y ∈ (W : Y.Opens) ∧ ∃ u, I.ideal W = Ideal.span {u})
    (x : X) : ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧ ∃ u, (I.comap f).ideal W = Ideal.span {u} := by
  obtain ⟨W, hxW, u, hu⟩ := hI (f x)
  let W' : X.affineOpens := ⟨f ⁻¹ᵁ W, W.2.preimage f⟩
  let W'' : Y.affineOpens := ⟨f ''ᵁ (W' : X.Opens), W'.2.image_of_isOpenImmersion f⟩
  have hle : W'' ≤ W := f.image_preimage_le W
  let σ : Γ(Y, (W'' : Y.Opens)) ≃+* Γ(X, (W' : X.Opens)) :=
    (f.appIso (W' : X.Opens)).commRingCatIsoToRingEquiv
  refine ⟨W', hxW, σ (Y.presheaf.map (homOfLE hle).op u), ?_⟩
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, ideal_res_span I hle hu]
  change Ideal.comap (σ.symm : Γ(X, (W' : X.Opens)) →+* Γ(Y, (W'' : Y.Opens))) _ = _
  rw [Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, Set.image_singleton]

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_IntersectC_Pit2 =====
section

/-!
# S4-IntersectC, file Pit2: Krull at translated intersections; many `k`-points (L36, O8)

* `infinite_pts`: a closed set containing a proper specialization `z ⤳ y` has infinitely many
  `k`-points (Jacobson).
* `locPrin_effI`: the ideal sheaf of an effective Weil divisor is locally principal.
* `pit_transl`: a point of codimension `> i` in the intersection of `i` translates of `effI D` has a
  proper generalization in that intersection.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA
  RamanujanPetersson.IntersectB

/-- The ideal sheaf of an effective Weil divisor is locally principal. -/
theorem locPrin_effI {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {D : AlgebraicCycle X ℤ} (hD : D ∈ weilDivisors X) (hfin : (Function.support D).Finite)
    (x : X) : ∃ W : X.affineOpens, x ∈ (W : X.Opens) ∧ ∃ u, (effI D).ideal W = Ideal.span {u} := by
  obtain ⟨W, hxW, u, -, hu, -⟩ := effGen hufd hD hfin x
  exact ⟨W, hxW, u, hu⟩

section Pts

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k)))
  [LocallyOfFiniteType A.hom]

/-- A closed set containing a proper specialization has infinitely many `k`-points. -/
theorem infinite_pts (S : Set A.left) (hS : IsClosed S) {y z : A.left} (hzS : z ∈ S)
    (hzy : z ⤳ y) (hne : z ≠ y) :
    {b : 𝟙_ (Over (Spec (.of k))) ⟶ A | pt A b ∈ S}.Infinite := by
  intro hfin
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hsub : closure {z} ∩ closedPoints A.left ⊆ pt A '' {b | pt A b ∈ S} := by
    rintro x ⟨hx, hxc⟩
    obtain ⟨b, rfl⟩ := exists_pt_eq A x hxc
    exact ⟨b, closure_minimal (Set.singleton_subset_iff.2 hzS) hS hx, rfl⟩
  have hT : (closure {z} ∩ closedPoints A.left).Finite := (hfin.image (pt A)).subset hsub
  have hTc : IsClosed (closure {z} ∩ closedPoints A.left) := by
    rw [← Set.biUnion_of_singleton (closure {z} ∩ closedPoints A.left)]
    exact hT.isClosed_biUnion fun x hx => hx.2
  have h1 := closure_inter_closedPoints (X := A.left) (isClosed_closure (s := {z}))
  rw [hTc.closure_eq] at h1
  have hz : z ∈ closure {z} ∩ closedPoints A.left := by
    rw [h1]; exact subset_closure (Set.mem_singleton z)
  have hzc : IsClosed ({z} : Set A.left) := hz.2
  have hy : y ∈ closure ({z} : Set A.left) := specializes_iff_mem_closure.mp hzy
  rw [hzc.closure_eq] at hy
  exact hne (Set.mem_singleton_iff.mp hy).symm

end Pts

section Transl

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **Krull at translates**: a point of codimension `> i` in the intersection of `i` translates of
`effI D` has a proper generalization in that intersection. -/
theorem pit_transl [IsIntegral A.left] [IsLocallyNoetherian A.left]
    (hufd : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x))
    {D : AlgebraicCycle A.left ℤ} (hD : D ∈ weilDivisors A.left)
    (hfin : (Function.support D).Finite) {i : ℕ}
    (a : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A)) {y : A.left}
    (hy : y ∈ ((Zid A (fun _ => effI D) a).support : Set A.left))
    (hi : (i : ℕ∞) < Order.coheight y) :
    ∃ z ∈ ((Zid A (fun _ => effI D) a).support : Set A.left), z ≠ y ∧ z ⤳ y := by
  have hI : ∀ (j : Fin i) (x : A.left), ∃ W : A.left.affineOpens, x ∈ (W : A.left.Opens) ∧
      ∃ u, ((effI D).comap (transl A (a j)).left).ideal W = Ideal.span {u} := fun j x => by
    have := isIso_translL A (a j)
    exact locPrin_comap_iso _ _ (locPrin_effI hufd hD hfin) x
  obtain ⟨W, hyW, v, hv⟩ := exists_span_of_iSup _ hI y
  exact exists_gen_of_span (Zid A (fun _ => effI D) a) W hyW v hv hy hi

end Transl

end RamanujanPetersson.IntersectC


end

-- ===== S4.Def_RP_IntersectC_Pos =====
section

/-!
# S4-IntersectC, file Pos: positivity of the self-intersection (L36, O9)

* `le_coheight_closed`: closed points have codimension `≥ g` (homogeneity).
* `len_pos`: a closed subscheme with finite nonempty support has positive length.
* `zid_nonempty`: `i ≤ g` translates of `supp D` always meet, when translates separate points.
* **L36** `inum_pos`: `0 < (D^g)` for an effective Weil divisor whose translates separate points.
-/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj CartesianMonoidalCategory
  TopologicalSpace

namespace RamanujanPetersson.IntersectC

open RamanujanPetersson.JacDivisors RamanujanPetersson.IsogDegA RamanujanPetersson.IntersectA
  RamanujanPetersson.IntersectB

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [IsProper A.hom] [IsIntegral A.left]

/-- The slice `b ↦ (a', b)` of `A^(i+1) = A^i × A` over the point with coordinates `a'`. -/
noncomputable def slice {i : ℕ} (a' : Fin i → (𝟙_ (Over (Spec (.of k))) ⟶ A)) :
    A ⟶ Pw A (i + 1) :=
  lift (toUnit A ≫ ptOf A i a') (𝟙 A)

end RamanujanPetersson.IntersectC


end


