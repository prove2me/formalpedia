-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_144
-- name    : RPLib_FX_EtPBC_144
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:27:00.74835+00:00
-- url     : https://prove2.me/theorems/84ad1591-6c49-5e3c-bdc3-6d28d9856110
-- title:
--   Proper base change for the projective line, library file 144
-- statement:
--   File 144 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2UKd2`: S4-EtPBC-A, O2 M6 (O2UKd2): the local value of a global Kummer class
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_137

/-!
# Proper base change for the projective line, library file 144

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2UKd2`: S4-EtPBC-A, O2 M6 (O2UKd2): the local value of a global Kummer class
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2UKd2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UKd2): the local value of a global Kummer class

Setting of `uk_kill` (O2UK2c). A global Kummer class `c_Y` of a unit `H` on `Y = (T' ×_P R)` (`τ' : T' ⟶ U_o`,
`m : D ×_P U_o ⟶ T'` over `U_o`), with `H = u (1 + t e_p)` on the piece `p` of `W` and `H = 1 + t e_q` on the other
pieces (`e_q` roots of one monic `g ∈ B[X]`, `t` zero at `z`):
* **`uk_diff`**: `ε_loc(D) ∘ θ⁻¹(kapS p (kumD α)) = ε_loc(D) ∘ Λ[m]^*(θ'⁻¹ c_Y)` for `α ^ d = u`;
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

section GenUKD

universe w' v₀ u₀ v₁ u₁ v₂ u₂ v₃ u₃

end GenUKD

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
include h hz hD hDn hDr hW hY hm hn in
/-- Chart step of `uk_diff`. -/
def uk_diff_hk (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {α : (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)))ˣ}
    (hα : α ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)))) d)
    {β : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))ˣ}
    (hβ : ∀ Q, β Q ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0) {K : Type} [Field K] (χ : B →+* K)
    (hχ : (chEt c φ).hom (⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩ : Spec B) = c (A1pt k a))
    {g : B[X]} (hg : g.Monic) (hgn : 0 < g.natDegree) {t : B} (ht : χ t = 0) (hd : IsUnit (d : B))
    {e : ∀ q : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤), FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1)}
    (he : ∀ q, g.eval₂ (bK (Spec.map φ ≫ c) (opEt Uo) R q) (e q) = 0)
    (sX : Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) (sY : Γ(((etPull T'.hom).obj R).left, ⊤)) (hs : (wm (R := R) m).appTop sY = sX)
    (hzX : ζ p = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)))
      (algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)) (Ideal.Quotient.mk p.1 sX)))
    (hzY : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), ζY Q = algebraMap _ (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)))
      (algebraMap (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 sY)))
    {u : (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1))}
    (hu : (α : maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1))) ^ d = algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1))) u)
    {Hg : Γ(((etPull T'.hom).obj R).left, ⊤)} (hH : IsUnit Hg)
    (hβH : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), (β Q : maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1))) ^ d =
      algebraMap _ (maxUnram (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1))) (algebraMap (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 Hg)))
    (cY : H Λ (unitSh Λ ((etPull T'.hom).obj R).left) 1)
    (hcY : ∀ Q : minimalPrimes Γ(((etPull T'.hom).obj R).left, ⊤), resLE (piHom (piEquiv hY) Q) 1 cY =
      kappaLH (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull T'.hom).obj R).left, ⊤) ⧸ Q.1)) Λ (kumD (hζY Q) (hζΓY Q) hdN (hβ Q) hgΛ))
    (hHp : algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ p.1)) (Ideal.Quotient.mk p.1 ((wm (R := R) m).appTop Hg)) =
      u * (1 + bK (Spec.map φ ≫ c) (opEt Uo) R p t * e p))
    (hHq : ∀ q, q ≠ p → algebraMap (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1) (FractionRing (Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤) ⧸ q.1))
      (Ideal.Quotient.mk q.1 ((wm (R := R) m).appTop Hg)) = 1 + bK (Spec.map φ ≫ c) (opEt Uo) R q t * e q)
    {B' : CommRingCat.{0}} (ι : B ⟶ B') [Etale (Spec.map ι)] (y : Fin g.natDegree → B')
    (hy : ∀ (S : Type) [CommRing S] (σ : B' →+* S) (e : S), g.eval₂ (σ.comp ι.hom) e = 0 →
        (∑ i : Fin g.natDegree, σ (y i) * e ^ (i : ℕ)) ^ d = 1 + σ (ι t) * e)
    {B₁ : CommRingCat.{0}} (φ₁ : CommRingCat.of k[X] ⟶ B₁) [Etale (Spec.map φ₁ ≫ c)]
    (d₁ : chEt c φ₁ ⟶ Scheme.Etale.mk (Spec.map ι ≫ (Spec.map φ ≫ c)))
    (hDr₁ : ∀ v : (chEt c φ₁).left, (chEt c φ₁).hom v ∈ Uo ∨ (chEt c φ₁).hom v = c (A1pt k a)) :
    resLE (wm (R := R) (prdMap (d₁ ≫ nD (Spec.map φ ≫ c) ι) (opEt Uo))) 1 (kapS hW Λ p (kumD (hζ p) (hζΓ p) hdN hα hgΛ)) =
      resLE (wm (R := R) (prdMap (d₁ ≫ nD (Spec.map φ ≫ c) ι) (opEt Uo))) 1 (resLE (wm (R := R) m) 1 cY) := by
  have : IsAffine (prd (chEt c φ₁) (opEt Uo)).left := isAffine_prdUo c φ₁ (mem_Uo_iff c φ₁ h hz hDr₁)
  letI : Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) := Fintype.ofFinite _
  letI : DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) :=
    Classical.decEq _
  have hd₁ : IsUnit (d : Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) := by
    have e1 := hd.map (ι ≫ bW₁ (Spec.map φ ≫ c) (opEt Uo) R ι d₁).hom
    rwa [map_natCast] at e1
  exact resLE_kapS_kumD_eq_comp hW hY (fun m _ => isDomain_loc_W c φ₁ (Uo := Uo) R m) Λ (wm (R := R) (prdMap (d₁ ≫ nD (Spec.map φ ≫ c) ι) (opEt Uo)))
      (wm (R := R) m) p (hζ p) (hζΓ p) hζY hζΓY hdN hα hβ hgΛ sX sY hzX hzY hs hu hH hβH cY hcY hd₁
      (r := fun q => 1 + bK (Spec.map φ ≫ c) (opEt Uo) R q t * e q) hHp hHq
      (fun p₁ q Ψ hΨ => exists_pow_of_uk (Spec.map φ ≫ c) (opEt Uo) R ι d₁ q p₁ Ψ hΨ hy (he q))

end UKd

end RamanujanPetersson.EtPBC.EtKum

end

end


