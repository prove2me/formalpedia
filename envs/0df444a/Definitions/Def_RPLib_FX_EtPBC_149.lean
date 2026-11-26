-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_149
-- name    : RPLib_FX_EtPBC_149
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:38:47.538379+00:00
-- url     : https://prove2.me/theorems/9e51a8af-4529-5e33-845c-675a91e72564
-- title:
--   Proper base change for the projective line, library file 149
-- statement:
--   File 149 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2UKd3`: S4-EtPBC-A, O2 M6 (O2UKd3): a global Kummer class with local value 0
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_091
import Definitions.Def_RPLib_FX_EtPBC_143

/-!
# Proper base change for the projective line, library file 149

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2UKd3`: S4-EtPBC-A, O2 M6 (O2UKd3): a global Kummer class with local value 0
-/

set_option autoImplicit false

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
include hG hz hDr hm in
/-- **A global Kummer class with radicand `1 + t e_q` on every piece over `z` has local value `0` at `z`.** -/
def uk_kill_glob {d : ℕ} [NeZero d] (hdN : d ∣ N)
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
      (Ideal.Quotient.mk q.1 ((wm (R := R) m).appTop Hg)) = 1 + bK (Spec.map φ ≫ c) (opEt Uo) R q t * e q) :
    (locC_shortExact (Λ := Λ) (chEt c φ) h (c (A1pt k a)) hz hD hDn hDr).extClass.comp
      ((Ext.mk₀ (freeMap Λ m)).comp ((theta Λ R n hn τ').symm cY) (zero_add 1))
      (show 1 + 1 = 2 from rfl) = 0 := by
  have hC := exists_ukChart c φ hz hG hDr χ hχ hg hgn ht hd
  refine hC.elim fun B' hC => hC.elim fun ι hC => hC.elim fun hι hC => hC.elim fun y hC => ?_
  refine hC.2.elim fun B₁ hC' => hC'.elim fun φ₁ hC' => hC'.elim fun hφ₁ hC' => hC'.elim fun d₁ hC' => ?_
  have hy := hC.1
  have hD₁ := hC'.1
  have hDn₁ := hC'.2.1
  have hDr₁ := hC'.2.2
  have : IsAffine (prd (chEt c φ₁) (opEt Uo)).left := isAffine_prdUo c φ₁ (mem_Uo_iff c φ₁ h hz hDr₁)
  letI : Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) := Fintype.ofFinite _
  letI : DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ₁) (opEt Uo)).hom).obj R).left, ⊤)) :=
    Classical.decEq _
  exact uk_kill_gen
    (locC_shortExact (Λ := Λ) (chEt c φ) h (c (A1pt k a)) hz hD hDn hDr).extClass
    (locC_shortExact (Λ := Λ) (chEt c φ₁) h (c (A1pt k a)) hz hD₁ hDn₁ hDr₁).extClass
    (freeMap Λ (prdMap (d₁ ≫ nD (Spec.map φ ≫ c) ι) (opEt Uo))) (freeMap Λ m)
    (locCls_shrink h (d₁ ≫ nD (Spec.map φ ≫ c) ι)
      (locC_shortExact (Λ := Λ) (chEt c φ₁) h (c (A1pt k a)) hz hD₁ hDn₁ hDr₁)
      (locC_shortExact (Λ := Λ) (chEt c φ) h (c (A1pt k a)) hz hD hDn hDr))
    (theta Λ R n hn (prT (chEt c φ₁) (opEt Uo))) (theta Λ R n hn (prT (chEt c φ) (opEt Uo))) (theta Λ R n hn τ')
    (resLE (wm (R := R) (prdMap (d₁ ≫ nD (Spec.map φ ≫ c) ι) (opEt Uo))) 1) (resLE (wm (R := R) m) 1)
    (theta_natural Λ R n hn (prdMap (d₁ ≫ nD (Spec.map φ ≫ c) ι) (opEt Uo))
      (prdMap_prT (d₁ ≫ nD (Spec.map φ ≫ c) ι) (opEt Uo)))
    (theta_natural Λ R n hn m hm)
    cY
    (uk_kill_glob_h0a (c := c) (φ := φ) (h := h) (hz := hz) (hW := hW) (Λ := Λ) (hY := hY)
      (hζY := hζY) (hζΓY := hζΓY) (hdN := hdN) (hβ := hβ) (hgΛ := hgΛ) (χ := χ) (hχ := hχ) (hg := hg) (hgn := hgn)
      (ht := ht) (hd := hd) (he := he) (sY := sY) (hzY := hzY) (hβH := hβH) (cY := cY) (hcY := hcY) (hHq := hHq)
      (ι := ι) (y := y) (hy := hy) (φ₁ := φ₁) (d₁ := d₁) (hDr₁ := hDr₁) (m := m))

end UKd

end RamanujanPetersson.EtPBC.EtKum

end

end


