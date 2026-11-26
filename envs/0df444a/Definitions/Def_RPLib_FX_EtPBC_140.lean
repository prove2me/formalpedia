-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_140
-- name    : RPLib_FX_EtPBC_140
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:22:10.487803+00:00
-- url     : https://prove2.me/theorems/686fe31e-129b-53a8-bcc7-52e8e3c3ea6b
-- title:
--   Proper base change for the projective line, library file 140
-- statement:
--   File 140 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Km4b`: S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains
--   * `S4.Def_RP_EtPBC_A_O2P3b`: S4-EtPBC-A, O2 M5 P3b: purity for `H¹(Spec B[1/t], Λ)`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_132

/-!
# Proper base change for the projective line, library file 140

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Km4b`: S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains
* `S4.Def_RP_EtPBC_A_O2P3b`: S4-EtPBC-A, O2 M5 P3b: purity for `H¹(Spec B[1/t], Λ)`
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Km4b =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains

**`h1_exists_kappa`**: if `Γ = Γ(X, ⊤)` is noetherian, its localizations at maximal ideals are domains and its
quotients by minimal primes are Dedekind, every `c ∈ H¹(X, Λ)` is `Σ_p kapS h Λ p (χ_p)` with `χ_p` a character of
`π₁(Γ ⧸ p)` (`kappaLH_surj` on each piece, `h1_split`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur

section Kappa

variable {X : Scheme.{0}} [IsAffine X] [IsNoetherianRing Γ(X, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ p : minimalPrimes Γ(X, ⊤), IsDedekindDomain (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))]
  [Fintype (minimalPrimes Γ(X, ⊤))] [DecidableEq (minimalPrimes Γ(X, ⊤))] (Λ : Type) [CommRing Λ]

theorem h1_exists_kappa_piece (c : H Λ (unitSh Λ X) 1) (p : minimalPrimes Γ(X, ⊤)) :
    ∃ χ : ChL (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ,
      kappaLH (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ χ =
        h1_eS h Λ p ((Ext.mk₀ (splitIn (piS (piEquiv h)) Λ p)).comp c (zero_add 1)) :=
  kappaLH_surj (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ _

end Kappa

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2P3b =====
section

/-!
# S4-EtPBC-A, O2 M5 P3b: purity for `H¹(Spec B[1/t], Λ)`

`B` Dedekind, `Bt = B[1/t]` with `(t)` prime, `K = Frac B`, `N` invertible in `B`, `N • Λ = 0`, `ζ₀ ∈ K` a primitive
`N`-th root of unity, `τ ∈ maxUnram Bt K` with `τ ^ N = t`.

* `etale_away`, `map_genPt_away`: `Spec Bt → Spec B` is etale and maps generic point to generic point;
* `cyc_mem`: the class of a cyclic character `σ ↦ (c σ).val • g` lies in `res H¹(Spec B) + κ(kumChi τ Λ)`;
* **`purity`**, **`purity_exists`**: every `κ ∈ H¹(Spec Bt, Λ)` is `res κ₀ + κ(kumChi τ c)` with `κ₀ ∈ H¹(Spec B, Λ)`,
  `c ∈ Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.Pur

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer RamanujanPetersson.EtPi1
  RamanujanPetersson.EtCompact.GalTrE

section Away

end Away

section Pur

variable {B Bt K : Type} [CommRing B] [IsDedekindDomain B] [CommRing Bt] [IsDedekindDomain Bt] [Algebra B Bt]
  {t : B} [IsLocalization.Away t Bt] (ht : t ≠ 0) (hP : (Ideal.span {t}).IsPrime)
  [Field K] [Algebra B K] [Algebra Bt K] [IsScalarTower B Bt K] [IsFractionRing B K] [IsFractionRing Bt K]
  [Etale (Spec.map (CommRingCat.ofHom (algebraMap B Bt)))]
  {Λ : Type} [CommRing Λ] {N : ℕ} [NeZero N] (hN : IsUnit (N : B)) (hΛ : ∀ x : Λ, N • x = 0)
  {ζ0 : K} (hζ0 : IsPrimitiveRoot ζ0 N) {τ : (maxUnram Bt K)ˣ}
  (hτ : (τ : maxUnram Bt K) ^ N = algebraMap K (maxUnram Bt K) (algebraMap B K t))

include ht hP hN in
/-- **Purity**: `H¹(Spec Bt, Λ) = res H¹(Spec B, Λ) + κ(kumChi τ Λ)`. -/
theorem purity (κ : H Λ (unitSh Λ (Spec (CommRingCat.of Bt))) 1) :
    κ ∈ (resLEHom (Λ := Λ) (Spec.map (CommRingCat.ofHom (algebraMap B Bt))) 1).range ⊔
      ((kappaLH Bt K Λ).comp (kumTau (zetaE_prim Bt hζ0) (zetaE_fix Bt ζ0) (mem_rad_of_pow_eq hτ) hΛ)).range := by
  classical
  obtain ⟨χ, rfl⟩ := kappaLH_surj Bt K Λ κ
  obtain ⟨hχ, hl⟩ := mem_ChL.1 χ.2
  obtain ⟨ι, hι, d, hd, g, c, hdN, hg, hcl, hhom, hsum⟩ := exists_cdec hΛ χ.1 hχ hl hl.range_finite
  have e : χ = ∑ i, (⟨fun σ => (c i σ).val • g i, chl_cyc (hd i) (hcl i) (hhom i) (hg i)⟩ : ChL Bt K Λ) := by
    apply Subtype.ext
    funext σ
    rw [hsum σ, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  rw [e, map_sum]
  exact AddSubgroup.sum_mem _ (fun i _ => by
    have := hd i
    exact cyc_mem ht hP hN hΛ hζ0 hτ (hdN i) (c i) (hcl i) (hhom i) (hg i))

end Pur

end RamanujanPetersson.EtCompact.Pur

end

end


