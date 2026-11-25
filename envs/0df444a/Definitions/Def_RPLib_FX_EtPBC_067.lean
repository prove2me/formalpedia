-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_067
-- name    : RPLib_FX_EtPBC_067
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T20:39:53.70469+00:00
-- url     : https://prove2.me/theorems/d7448551-d527-5978-9a27-b922a6a2d547
-- title:
--   Proper base change for the projective line, library file 067
-- statement:
--   File 067 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
--   * `S4.Def_RP_EtPBC_A_O2N3`: S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map
--   * `S4.Def_RP_EtPBC_A_O2Km4b`: S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_046
import Definitions.Def_RPLib_FX_EtPBC_058
import Definitions.Def_RPLib_FX_EtPBC_059

/-!
# Proper base change for the projective line, library file 067

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Fl2`: S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`
* `S4.Def_RP_EtPBC_A_O2N3`: S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map
* `S4.Def_RP_EtPBC_A_O2Km4b`: S4-EtPBC-A, O2 M6 (O2Km4b): `H¹` of an affine scheme whose ring is a product of Dedekind domains
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Fl2 =====
section

/-!
# S4-EtPBC-A, O2 (MV route), Fl2: restriction along `extFree`

* `extAdjMap_mk₀_comp`: the adjunction map on `Ext` is natural in the source;
* `lshFreeHom_natural`, `lshFreeInv_natural`: `Λ[e ∘ V] ≅ e_! Λ[V]` is natural in `V`;
* `toW W V : e ∘ V ⟶ W` (`e = W.hom`, `V : W.left.Etale`), `extFreeV : Ext_P(Λ[e ∘ V], F) ≃ Ext_W(Λ[V], F|_W)`;
* **`extFreeV_restrict`**: restricting `β ∈ Ext_P(Λ[W], F)` along `toW W V` is restricting `extFree β ∈ H(W, F|_W)`
  to `V`; **`restrict_eq_zero`**: if `extFree β` dies on `V`, then `β` dies on `e ∘ V`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC
  RamanujanPetersson.EtPBC.GenAlg RamanujanPetersson.EtPBC.FreeStk

universe w v v' u₁ u₂ u

section Adj

end Adj

variable {Λ : Type u} [CommRing Λ]

section Nat

end Nat

section Obj

variable {P : Scheme.{u}}

/-- **If `extFree β` dies on `V`, then `β` dies on `e ∘ V`.** -/
theorem restrict_eq_zero (W : P.Etale) (V : W.left.Etale) (F : EtSh Λ P) {n : ℕ} (β : Ext.{u} (freeSh Λ W) F n)
    (h : (Ext.mk₀ (freeMap Λ (toTop V) ≫ (unitIso Λ W.left).hom)).comp (extFree Λ W F n β) (zero_add n) = 0) :
    (Ext.mk₀ (freeMap Λ (toW W V))).comp β (zero_add n) = 0 :=
  (extFreeV Λ W V F n).injective ((extFreeV_restrict W V F β).trans (h.trans (map_zero _).symm))

end Obj

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2N3 =====
section

/-!
# S4-EtPBC-A, O2 M5 N2b: restriction of Kummer classes along an etale map

* `kchar_transport` (field theory): two Kummer characters agree when the two groups act compatibly through
  embeddings `e : L → Ω`, `e' : L' → Ω` and one `σ ∈ Aut Ω`, `e ζ = e' ζ'` is fixed by `σ` and `e (γ^N) = e' (γ'^N)`;
* `val_add_smul`, `kumChi hζ γ c : τ ↦ (kchar γ τ).val • c` (an additive locally constant character when
  `N • c = 0`): `kumChi_mul`, `kumChi_isLocallyConstant`;
* `sepX g h`, `resMapX g h` for `h : g y = x` (`sepE`, `residueFieldMap` transported), `galTrX_apply`,
  `sepX_algebraMap`;
* **`resLE_kappaL_kum`** (NAT for Kummer classes): `resLE g 1 (κ (kumChi ζ γ c)) = κ (kumChi ζ' γ' c)` when
  `sepX (ζ) = ζ'` and `sepX (γ^N) = γ'^N` in `κ(η')^sep`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtCompact.GalTrE

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtSheaves.GenBr
  RamanujanPetersson.EtSheaves.TorSec RamanujanPetersson.Kummer

section KumTr

end KumTr

section KumChi

end KumChi

section Sep

universe u

end Sep

section KumNat

variable {A K A' K' : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]
  [CommRing A'] [IsDomain A'] [Field K'] [Algebra A' K'] [IsFractionRing A' K'] [IsIntegrallyClosed A']
  [IsNoetherianRing A'] {Λ : Type} [CommRing Λ]
  (g : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A)) [Etale g] (hg : g (genPt A') = genPt A)
  {N : ℕ} [NeZero N] {ζ : maxUnram A K} {ζ' : maxUnram A' K'} (hζ : IsPrimitiveRoot ζ N)
  (hζ' : IsPrimitiveRoot ζ' N) (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 A K)), σ ζ = ζ)
  (hζΓ' : ∀ σ ∈ (⊤ : Subgroup (Pi1 A' K')), σ ζ' = ζ')

/-- **NAT for Kummer classes**: restriction along an etale `g` (with `g η' = η`) sends the class of `kchar γ`
to the class of `kchar γ'` when `ζ ↦ ζ'` and `γ^N ↦ γ'^N` in `κ(η')^sep` (through `sepX` and `genEmb`). -/
theorem resLE_kappaL_kum {γ : (maxUnram A K)ˣ} (hγ : γ ∈ rad (⊤ : Subgroup (Pi1 A K)) N)
    {γ' : (maxUnram A' K')ˣ} (hγ' : γ' ∈ rad (⊤ : Subgroup (Pi1 A' K')) N) {c : Λ} (hc : N • c = 0)
    (hζe : sepX g hg (genEmb A K ζ) = genEmb A' K' ζ')
    (hpow : sepX g hg (genEmb A K ((γ : maxUnram A K) ^ N)) = genEmb A' K' ((γ' : maxUnram A' K') ^ N)) :
    resLE g 1 (kappaL A K Λ (kumChi_mul hζ hζΓ hγ hc) (kumChi_isLocallyConstant hζ γ c)) =
      kappaL A' K' Λ (kumChi_mul hζ' hζΓ' hγ' hc) (kumChi_isLocallyConstant hζ' γ' c) := by
  refine resLE_kappaL g hg _ _ _ _ (fun σ => ?_)
  have hσζ : σ.toRingEquiv (genEmb A' K' ζ') = genEmb A' K' ζ' := by
    show σ (genEmb A' K' ζ') = genEmb A' K' ζ'
    rw [← genEmb_genToPi1 A' K' σ ζ', hζΓ' _ (Subgroup.mem_top _)]
  have hk := kchar_transport hζ hζ' ((sepX g hg).toRingHom.comp (genEmb A K)) (genEmb A' K') σ.toRingEquiv
    (⟨genToPi1 A K (galTrX g hg σ), Subgroup.mem_top _⟩ : (⊤ : Subgroup (Pi1 A K)))
    (⟨genToPi1 A' K' σ, Subgroup.mem_top _⟩ : (⊤ : Subgroup (Pi1 A' K')))
    (fun z => by
      show sepX g hg (genEmb A K (genToPi1 A K (galTrX g hg σ) z)) = σ (sepX g hg (genEmb A K z))
      rw [genEmb_genToPi1, galTrX_apply, RingEquiv.apply_symm_apply])
    (fun z => genEmb_genToPi1 A' K' σ z) hζe hσζ hγ hγ' hpow
  exact congrArg (fun k : ZMod N => k.val • c) hk.symm

end KumNat

end RamanujanPetersson.EtCompact.GalTrE

end

end

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

/-- `extFreeU` on the `p`-th piece, with its target written over `Spec (Γ ⧸ p)` (pays the identification once). -/
def h1_eS (p : minimalPrimes Γ(X, ⊤)) :
    Ext.{0} (freeSh Λ (piS (piEquiv h) p)) (unitSh Λ X) 1 ≃+
      H Λ (unitSh Λ (Spec (CommRingCat.of (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))) 1 :=
  extFreeU Λ (piS (piEquiv h) p) 1

end Kappa

end RamanujanPetersson.EtPBC.EtKum

end

end


