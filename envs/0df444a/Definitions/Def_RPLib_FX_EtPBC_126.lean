-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_126
-- name    : RPLib_FX_EtPBC_126
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:16:37.414984+00:00
-- url     : https://prove2.me/theorems/7dcef9c9-e805-555b-b326-1d4f97226501
-- title:
--   Proper base change for the projective line, library file 126
-- statement:
--   File 126 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2Th1c`: S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`
--   * `S4.Def_RP_EtPBC_A_O2PPTb`: S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map
--   * `S4.Def_RP_EtPBC_A_O2UKd3`: S4-EtPBC-A, O2 M6 (O2UKd3): a global Kummer class with local value 0
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_065
import Definitions.Def_RPLib_FX_EtPBC_112
import Definitions.Def_RPLib_FX_EtPBC_114
import Definitions.Def_RPLib_FX_EtPBC_121

/-!
# Proper base change for the projective line, library file 126

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2Th1c`: S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`
* `S4.Def_RP_EtPBC_A_O2PPTb`: S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map
* `S4.Def_RP_EtPBC_A_O2UKd3`: S4-EtPBC-A, O2 M6 (O2UKd3): a global Kummer class with local value 0
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2Th1c =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Th1c): naturality of Shapiro over a FIXED base `D₀`

For `τ : T ⟶ D₀` (`W₀ := D₀ ×_P R ⟶ D₀` quasi-compact, separated, of constant degree `n`):
* `theta_apply`: `θ_τ x = extFreeU (thX x)` (via `thXE`, `theta_eq_thXE`, `thXE_eq`);
* **`theta_natural`**: for `m : T₁ ⟶ T₂` with `m ≫ τ₂ = τ₁`,
  `θ_{τ₁}(Λ[m]^* x) = resLE (wm m) (θ_{τ₂} x)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtCompact.GalTrE

universe u

section Gen

end Gen

section GenNat

universe w₁ v₁ u₁

end GenNat

section Theta

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}} {D₀ : P.Etale} (R : P.Etale)

variable [QuasiCompact ((etPull D₀.hom).obj R).hom] [IsSeparated ((etPull D₀.hom).obj R).hom]
  (n : ℕ) (hn : ∀ y : D₀.left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull D₀.hom).obj R)) = n)

/-- Square 3 of `thX_natural` (Shapiro naturality and `thZ_natural`). -/
def thX_natural_h3 {T₁ T₂ : P.Etale} (m : T₁ ⟶ T₂) {τ₁ : T₁ ⟶ D₀} {τ₂ : T₂ ⟶ D₀} (h : m ≫ τ₂ = τ₁)
    (x : Ext.{u} (freeSh Λ T₂) (freeSh Λ R) 1) :
    (Ext.mk₀ ((pull ((etPull D₀.hom).obj R).hom Λ).map (freeMap Λ (ovrMap m h)))).comp
        ((shapExt Λ ((etPull D₀.hom).obj R) n hn (freeSh Λ (ovr τ₂)) 1).symm (thZ Λ R τ₂ x)) (zero_add 1) =
      (shapExt Λ ((etPull D₀.hom).obj R) n hn (freeSh Λ (ovr τ₁)) 1).symm
        (thZ Λ R τ₁ ((Ext.mk₀ (freeMap Λ m)).comp x (zero_add 1))) :=
  (shapExt_symm_natural Λ ((etPull D₀.hom).obj R) n hn (freeMap Λ (ovrMap m h)) (thZ Λ R τ₂ x)).symm.trans
    (congrArg (shapExt Λ ((etPull D₀.hom).obj R) n hn (freeSh Λ (ovr τ₁)) 1).symm (thZ_natural Λ R m h x))

end Theta

end RamanujanPetersson.EtPBC.EtShap

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PPTb =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTb): a piece Kummer class pulled back along an etale map

GLOB/REL PLAN v1 (5), piece part. For etale `f : X₁ ⟶ X` of affine schemes whose rings are finite products of
Dedekind domains:
* **`exists_rad_hom`**: moving a radical `α` (`α ^ d = u`) along `ψ : K →+* K'` (`φ : A →+* A'` compatible);
* **`exists_gam`**: one radical `γ p₁` on every piece `p₁` of `X₁` over `p`, with `γ p₁ ^ d = Ψ u` for every
  compatible `Ψ`;
* **`resLE_kapS_off`**: a piece class of `X` vanishes on the pieces of `X₁` not over its piece;
* **`resLE_kapS_kumD_sum`**: `resLE f (kapS p (kumD α)) = Σ_{p₁} kapS p₁ (χ₁ p₁)` with `χ₁ p₁ = kumD (γ p₁)` for the
  pieces `p₁` over `p` and `χ₁ p₁ = 0` for the others.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtCompact.Pur RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer
  RamanujanPetersson.EtCompact.GalTrE

section RadHom

end RadHom

section PPTb

variable {X X₁ : Scheme.{0}} [IsAffine X] [IsAffine X₁] [IsNoetherianRing Γ(X, ⊤)] [IsNoetherianRing Γ(X₁, ⊤)]
  (h : ∀ (m : Ideal Γ(X, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (h₁ : ∀ (m : Ideal Γ(X₁, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  [∀ p : minimalPrimes Γ(X, ⊤), IsDedekindDomain (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))]
  [∀ p : minimalPrimes Γ(X₁, ⊤), IsDedekindDomain (Γ(X₁, ⊤) ⧸ (p : Ideal Γ(X₁, ⊤)))]
  [Fintype (minimalPrimes Γ(X, ⊤))] [DecidableEq (minimalPrimes Γ(X, ⊤))]
  [Fintype (minimalPrimes Γ(X₁, ⊤))] [DecidableEq (minimalPrimes Γ(X₁, ⊤))] (Λ : Type) [CommRing Λ]
  (f : X₁ ⟶ X) [Etale f] (p : minimalPrimes Γ(X, ⊤)) {N : ℕ} [NeZero N]
  {ζ : maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))))}
  (hζ : IsPrimitiveRoot ζ N)
  (hζΓ : ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))),
    σ ζ = ζ)
  {ζ₁ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1))}
  (hζ₁ : ∀ p₁, IsPrimitiveRoot (ζ₁ p₁) N)
  (hζΓ₁ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤),
    ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))), σ (ζ₁ p₁) = ζ₁ p₁)
  {d : ℕ} [NeZero d] (hdN : d ∣ N)
  {α : (maxUnram (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))ˣ}
  (hα : α ∈ rad (⊤ : Subgroup (Pi1 (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))
    (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))))) d)
  {γ : ∀ p₁ : minimalPrimes Γ(X₁, ⊤), (maxUnram (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))ˣ}
  (hγ : ∀ p₁, γ p₁ ∈ rad (⊤ : Subgroup (Pi1 (Γ(X₁, ⊤) ⧸ p₁.1) (FractionRing (Γ(X₁, ⊤) ⧸ p₁.1)))) d)
  {gΛ : Λ} (hgΛ : d • gΛ = 0)

set_option maxHeartbeats 1000000 in
include h h₁ in
def resLE_kapS_kumD_sum_off (p₁ : minimalPrimes Γ(X₁, ⊤)) (hp : ¬ (p : Ideal Γ(X, ⊤)) ≤ RingHom.ker (kerMap f p₁))
    (χ : ChL (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤))) (FractionRing (Γ(X, ⊤) ⧸ (p : Ideal Γ(X, ⊤)))) Λ)
    (χ₁ : ChL (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) Λ)
    (h0 : χ₁ = 0) :
    resLE (piHom (piEquiv h₁) p₁) 1 (resLE f 1 (kapS h Λ p χ)) =
      kappaLH (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) Λ χ₁ := by
  subst h0
  exact (resLE_kapS_off h h₁ Λ f p p₁ hp χ).trans (kappaLH (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤))) (FractionRing (Γ(X₁, ⊤) ⧸ (p₁ : Ideal Γ(X₁, ⊤)))) Λ).map_zero'.symm

end PPTb

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UKd3 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UKd3): a global Kummer class with local value 0

Setting of `uk_kill` (O2UK2c). A global Kummer class `c_Y` of a unit `H` on `Y = (T' ×_P R)` (`τ' : T' ⟶ U_o`,
`m : D ×_P U_o ⟶ T'` over `U_o`), with `H = u (1 + t e_p)` on the piece `p` of `W` and `H = 1 + t e_q` on the other
pieces (`e_q` roots of one monic `g ∈ B[X]`, `t` zero at `z`):
* **`uk_kill_glob`**: `ε_loc(D) ∘ Λ[m]^*(θ'⁻¹ c_Y) = 0` when `H = 1 + t e_q` on every piece.
Proof: `exists_ukChart` (one etale nbhd where every `1 + t e_q` is a `d`-th power), `locCls_shrink`, `theta_natural`
(twice: along `M₁` and along `m`, never along `M₁ ≫ m`), O2UKd1 with `exists_pow_of_uk`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section GenUKK

universe w' v₀ u₀ v₁ u₁ v₂ u₂ v₃ u₃

end GenUKK

section UKd

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B) [Etale (Spec.map φ ≫ c)] {Uo Uz : P.Opens}
  (h : Uo ≤ Uz) {a : k} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k a)) (hG : Subsingleton (Gal (c (A1pt k a))))
  (hD : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
  (hDn : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj (chEt c φ)))
  (hDr : ∀ v : (chEt c φ).left, (chEt c φ).hom v ∈ Uo ∨ (chEt c φ).hom v = c (A1pt k a))
  (R : P.Etale) [IsAffine R.left] [IsAffine ((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤))]
  (hW : ∀ (m : Ideal Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  (Λ : Type) [CommRing Λ] {N : ℕ} [NeZero N]
  {ζ : ∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1))}
  (hζ : ∀ p, IsPrimitiveRoot (ζ p) N)
  (hζΓ : ∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)
    (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)))), σ (ζ p) = ζ p)
  (n : ℕ) (hn : ∀ y : (opEt Uo).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt Uo).hom).obj R)) = n)

  {T' : P.Etale} (τ' : T' ⟶ opEt Uo) (m : prd (chEt c φ) (opEt Uo) ⟶ T')
  (hm : m ≫ τ' = prT (chEt c φ) (opEt Uo))
  [IsAffine ((etPull T'.hom).obj R).left] [IsNoetherianRing Γ(((etPull T'.hom).obj R).left, ⊤)]
  [∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ (Q : Ideal Γ(((etPull T'.hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤))]
  (hY : ∀ (m : Ideal Γ(((etPull T'.hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))
  {ζY : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1))}
  (hζY : ∀ Q, IsPrimitiveRoot (ζY Q) N)
  (hζΓY : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤),
    ∀ σ ∈ (⊤ : Subgroup (Pi1 (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))), σ (ζY Q) = ζY Q)

set_option maxHeartbeats 1000000 in
include hW hz h in
def uk_kill_glob_h0a {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {β : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))ˣ}
    (hβ : ∀ Q, β Q ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0) {K : Type} [Field K] (χ : B →+* K)
    (hχ : (chEt c φ).hom (⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩ : Spec B) = c (A1pt k a))
    {g : B[X]} (hg : g.Monic) (hgn : 0 < g.natDegree) {t : B} (ht : χ t = 0) (hd : IsUnit (d : B))
    {e : ∀ q : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1)}
    (he : ∀ q, g.eval₂ (bK (Spec.map φ ≫ c) (opEt Uo) R q) (e q) = 0) (sY : Γ(((etPull T'.hom).obj R).left, ⊤))
    (hzY : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), ζY Q = algebraMap _ (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))
      (algebraMap (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 sY)))
    {Hg : Γ(((etPull T'.hom).obj R).left, ⊤)}
    (hβH : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), (β Q : maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1))) ^ d =
      algebraMap _ (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1))) (algebraMap (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 Hg)))
    (cY : H Λ (unitSh Λ ((etPull T'.hom).obj R).left) 1)
    (hcY : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), resLE (piHom (piEquiv hY) Q) 1 cY =
      kappaLH (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)) Λ (kumD (hζY Q) (hζΓY Q) hdN (hβ Q) hgΛ))
    (hHq : ∀ q, algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1))
      (Ideal.Quotient.mk q.1 ((wm (R := R) m).appTop Hg)) = 1 + bK (Spec.map φ ≫ c) (opEt Uo) R q t * e q) 
    {B' : CommRingCat.{0}} (ι : B ⟶ B') [Etale (Spec.map ι)] (y : Fin g.natDegree → B')
    (hy : ∀ (S : Type) [CommRing S] (σ : B' →+* S) (e : S), g.eval₂ (σ.comp ι.hom) e = 0 →
        (∑ i : Fin g.natDegree, σ (y i) * e ^ (i : ℕ)) ^ d = 1 + σ (ι t) * e)
    {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
    (d₁ : chEt c φ₁ ⟶ Scheme.Etale.mk (Spec.map ι ≫ (Spec.map φ ≫ c)))
    (hDr₁ : ∀ v : (chEt c φ₁).left, (chEt c φ₁).hom v ∈ Uo ∨ (chEt c φ₁).hom v = c (A1pt k a)) :
    resLE (wm (R := R) (prdMap (d₁ ≫ nD (Spec.map φ ≫ c) ι) (opEt Uo))) 1 (resLE (wm (R := R) m) 1 cY) = 0 := by
  have : IsAffine (prd (chEt c φ₁) (opEt Uo)).left := isAffine_prdUo c φ₁ (mem_Uo_iff c φ₁ h hz hDr₁)
  letI : Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) := Fintype.ofFinite _
  letI : DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) :=
    Classical.decEq _
  exact resLE_kumG_eq_zero_comp hW hY (fun m _ => isDomain_loc_W c φ₁ (Uo := Uo) R m) Λ (wm (R := R) (prdMap (d₁ ≫ nD (Spec.map φ ≫ c) ι) (opEt Uo)))
    (wm (R := R) m) hζY hζΓY hdN hβ hgΛ sY hzY hβH cY hcY
    (r := fun q => 1 + bK (Spec.map φ ≫ c) (opEt Uo) R q t * e q) hHq
    (fun p₁ q Ψ hΨ => exists_pow_of_uk (Spec.map φ ≫ c) (opEt Uo) R ι d₁ q p₁ Ψ hΨ hy (he q))

end UKd

end RamanujanPetersson.EtPBC.EtKum

end

end


