-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_158
-- name    : RPLib_FX_EtPBC_158
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-26T00:38:04.097109+00:00
-- url     : https://prove2.me/theorems/c7790fa6-d5dc-532c-9602-ae26f74cb25f
-- title:
--   Proper base change for the projective line, library file 158
-- statement:
--   File 158 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2UKd2`: S4-EtPBC-A, O2 M6 (O2UKd2): the local value of a global Kummer class
--   * `S4.Def_RP_EtPBC_A_O2Bd5`: S4-EtPBC-A, O2 REL (O2Bd5): a relation term at a bad point vanishes (no chart map to `D_{g₀}`)
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_056
import Definitions.Def_RPLib_FX_EtPBC_119
import Definitions.Def_RPLib_FX_EtPBC_149
import Definitions.Def_RPLib_FX_EtPBC_151

/-!
# Proper base change for the projective line, library file 158

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2UKd2`: S4-EtPBC-A, O2 M6 (O2UKd2): the local value of a global Kummer class
* `S4.Def_RP_EtPBC_A_O2Bd5`: S4-EtPBC-A, O2 REL (O2Bd5): a relation term at a bad point vanishes (no chart map to `D_{g₀}`)
-/

set_option autoImplicit false

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
include hG hz hDr hm in
/-- **The local value at `z` of a global Kummer class** (`H = u (1 + t e_p)` on `p`, `H = 1 + t e_q` elsewhere). -/
def uk_diff (p : minimalPrimes Γ(((etPull (prd (chEt c φ) (opEt Uo)).hom).obj R).left, ⊤)) {d : ℕ} [NeZero d] (hdN : d ∣ N)
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
      (Ideal.Quotient.mk q.1 ((wm (R := R) m).appTop Hg)) = 1 + bK (Spec.map φ ≫ c) (opEt Uo) R q t * e q) :
    (locC_shortExact (Λ := Λ) (chEt c φ) h (c (A1pt k a)) hz hD hDn hDr).extClass.comp
      ((theta Λ R n hn (prT (chEt c φ) (opEt Uo))).symm
        (kapS hW Λ p (kumD (hζ p) (hζΓ p) hdN hα hgΛ)))
      (show 1 + 1 = 2 from rfl) =
    (locC_shortExact (Λ := Λ) (chEt c φ) h (c (A1pt k a)) hz hD hDn hDr).extClass.comp
      ((Ext.mk₀ (freeMap Λ m)).comp ((theta Λ R n hn τ').symm cY) (zero_add 1))
      (show 1 + 1 = 2 from rfl) := by
  have hC := exists_ukChart c φ hz hG hDr χ hχ hg hgn ht hd
  refine hC.elim fun B' hC => hC.elim fun ι hC => hC.elim fun hι hC => hC.elim fun y hC => ?_
  refine hC.2.elim fun B₁ hC' => hC'.elim fun φ₁ hC' => hC'.elim fun hφ₁ hC' => hC'.elim fun d₁ hC' => ?_
  have hy := hC.1
  have hD₁ := hC'.1
  have hDn₁ := hC'.2.1
  have hDr₁ := hC'.2.2
  exact uk_diff_core (c := c) (φ := φ) (hζ := hζ) (hζΓ := hζΓ) (h := h) (hz := hz) (hD := hD) (hDn := hDn) (hDr := hDr) (R := R) (hW := hW) (Λ := Λ)
      (n := n) (hn := hn) (τ' := τ') (m := m) (hm := hm) (hY := hY) (hζY := hζY) (hζΓY := hζΓY)
      (p := p) (hdN := hdN) (hα := hα) (hβ := hβ) (hgΛ := hgΛ) (χ := χ) (hχ := hχ) (hg := hg) (hgn := hgn) (ht := ht) (hd := hd) (he := he) (sX := sX) (sY := sY) (hs := hs) (hzX := hzX) (hzY := hzY) (hu := hu) (hH := hH) (hβH := hβH) (cY := cY) (hcY := hcY) (hHp := hHp) (hHq := hHq)
      (ι := ι) (y := y) (hy := hy) (φ₁ := φ₁) (d₁ := d₁) (hD₁ := hD₁) (hDn₁ := hDn₁) (hDr₁ := hDr₁)

end UKd

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Bd5 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Bd5): a relation term at a bad point vanishes (no chart map to `D_{g₀}`)

REL PLAN v2 (s126). At a bad point `c(b)` (`b ≠ a`, outside `U₀`), with the relation nbhd `S` of `c(b)` and a chart
`D' = chEt c φ'` with `d' : D' ⟶ S`, `D' ×_P U₀ ⊆ U₁ = D(G)` (NO `dg : D' ⟶ D_{g₀}`: s128 fix, O2Bd4) and `φ'(X - C a)` a unit:
* **`bad_term_zero'`**: `ε(S, U₁) ∘ Λ[prT S U₁]^* κ_rel = 0` for `κ_rel = Λ[sigG]^* θ(prT D_G U₀)⁻¹ (Σ_Q kapS Q (kumD β_Q))`
  (`bad_term_eq` (O2Rel1), then `uk_kill_glob` (O2UKd3) with the `e`, `g`, `he`, `hHq` of `exists_bad_e'` (O2Bd4) and
  the residue character `χ` of `exists_chi` (O2Gl3b)). A `def` (big statement, see O2Gl2k).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.EtMV
  RamanujanPetersson.EtPBC.EtShap RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtCompact.Pur
  RamanujanPetersson.EtPi1 RamanujanPetersson.Kummer RamanujanPetersson.EtCompact.GalTrE

section BadZero

variable {k : Type} [Field k] {P : Scheme.{0}} [P.IsSeparated] (c : A1 k ⟶ P) [IsOpenImmersion c]
  {Uo Uz : P.Opens} (h : Uo ≤ Uz) {b : k} (hz : ∀ x : P, x ∈ Uz ↔ x ≠ c (A1pt k b))
  (hGal : Subsingleton (Gal (c (A1pt k b))))
  (R : P.Etale) [IsAffine R.left] {g₀ G : k[X]} (hG₀ : g₀ ∣ G) (hle : opnDg c G ≤ Uo) (h₁ : opnDg c G ≤ Uz)
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).left]
  [IsAffine (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).left]
  {S : P.Etale} (hSs : Subsingleton ((geomPtAt (c (A1pt k b))).point.fiber.obj S))
  (hSn : Nonempty ((geomPtAt (c (A1pt k b))).point.fiber.obj S))
  (hSr : ∀ v : S.left, S.hom v ∈ opnDg c G ∨ S.hom v = c (A1pt k b))
  {B' : CommRingCat.{0}} (φ' : CommRingCat.of k[X] ⟶ B') [Etale (Spec.map φ' ≫ c)]
  [IsAffine (prd (chEt c φ') (opEt Uo)).left]
  (d' : chEt c φ' ⟶ S)
  (hDs : Subsingleton ((geomPtAt (c (A1pt k b))).point.fiber.obj (chEt c φ')))
  (hDn : Nonempty ((geomPtAt (c (A1pt k b))).point.fiber.obj (chEt c φ')))
  (hDr₁ : ∀ v : (chEt c φ').left, (chEt c φ').hom v ∈ opnDg c G ∨ (chEt c φ').hom v = c (A1pt k b))
  (hDr : ∀ v : (chEt c φ').left, (chEt c φ').hom v ∈ Uo ∨ (chEt c φ').hom v = c (A1pt k b))
  (hD' : ∀ v : (prd (chEt c φ') (opEt Uo)).left, (prd (chEt c φ') (opEt Uo)).hom v ∈ opnDg c G)
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c φ') (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c φ') (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c φ') (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c φ') (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c φ') (opEt Uo)).hom).obj R).left, ⊤))]
  (Λ : Type) [CommRing Λ] (n : ℕ)
  (hn : ∀ y : (opEt Uo).left, Nat.card ((geomPtAt y).point.fiber.obj ((etPull (opEt Uo).hom).obj R)) = n)
  {N : ℕ} [NeZero N] {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N)
  [IsAffine ((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left] [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)]
  [∀ p : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), IsDedekindDomain (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ (p : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)))]
  [Fintype (minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤))] [DecidableEq (minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤))]
  (hY : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)) [m.IsMaximal], IsDomain (Localization.AtPrime m))

set_option maxHeartbeats 1000000 in
/-- **A relation term at a bad point vanishes.** -/
def bad_term_zero'
    [Algebra k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    (hAY : algebraMap k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤) =
      gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R))
    (hY₀ : ∀ (m : Ideal Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
      [m.IsMaximal], IsDomain (Localization.AtPrime m))
    [IsNoetherianRing Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)]
    {a : k} {M : ℕ} (hta : IsUnit (φ'.hom (X - C a)))
    (uS : integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
    (hu : uS - algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C a) ^ M ∈
      Ideal.span {algebraMap k[X] (integralClosure k[X] Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤)) (X - C b)})
    {Hg : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤)}
    (hH : Hg * (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
        (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a)) ^ M =
      (wm (R := R) (prdMap (toDG c hG₀) (opEt Uo))).appTop
        (liveMod hY₀ (uS : Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) g₀)) (opEt Uo)).hom).obj R).left, ⊤))
          (gamMap (shG c (locF (B := CommRingCat.of k[X]) g₀) (Uo := Uo) R) (X - C a) ^ M)))
    {d : ℕ} [NeZero d] (hdN : d ∣ N)
    {β : ∀ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), (maxUnram (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)))ˣ}
    (hβ : ∀ Q, β Q ∈ rad (⊤ : Subgroup (Pi1 (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)))) d)
    {gΛ : Λ} (hgΛ : d • gΛ = 0)
    (hβH : ∀ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), (β Q : (maxUnram (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)))) ^ d =
      algebraMap _ (maxUnram (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1))) (algebraMap (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1) (FractionRing (Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤) ⧸ Q.1)) (Ideal.Quotient.mk Q.1 Hg))) :
    (locC_shortExact (Λ := Λ) S h₁ (c (A1pt k b)) hz hSs hSn hSr).extClass.comp
      ((Ext.mk₀ (freeMap Λ (prT S (opEt (opnDg c G))))).comp
        ((Ext.mk₀ (freeMap Λ (sigG c hle))).comp
          ((theta Λ R n hn (prT (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo))).symm
            (∑ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), kapS hY Λ Q (kumD (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0 Q) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0) Q) hdN (hβ Q) hgΛ))) (zero_add 1))
        (zero_add 1))
      (show 1 + 1 = 2 from rfl) = 0 :=
  hDn.elim fun n' =>
  (exists_chi c φ' n').elim fun _K hK => hK.elim fun _ hK => hK.elim fun χ hχ =>
  haveI : Nontrivial B' := RingHom.domain_nontrivial χ
  (exists_bad_e' c R hG₀ hle φ' hD' hAY hY₀ hta uS hu hH).elim fun _e he' => he'.elim fun _g hg =>
  (bad_term_eq hle h h₁ hz d' hSs hSn hSr hDs hDn hDr₁ hDr hD' (sigG c hle)
    ((theta Λ R n hn (prT (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo))).symm
      (∑ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), kapS hY Λ Q (kumD (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0 Q) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0) Q) hdN (hβ Q) hgΛ)))).trans
  (uk_kill_glob c φ' h hz hGal hDs hDn hDr R (fun m _ => isDomain_loc_W c φ' (Uo := Uo) R m) Λ n hn
    (prT (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)) (mG c hle (chEt c φ') hD') (mG_prT c hle (chEt c φ') hD')
    hY (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0))
    hdN hβ hgΛ χ hχ.1 hg.1 hg.2.1 hχ.2 (isUnit_natCast_of_prim φ' hζ0 hdN) hg.2.2.1
    (sXW c (locF (B := CommRingCat.of k[X]) G) R ζ0) (ζW_eq c (locF (B := CommRingCat.of k[X]) G) R hζ0) hβH
    (∑ Q : minimalPrimes Γ(((etPull (prd (chEt c (locF (B := CommRingCat.of k[X]) G)) (opEt Uo)).hom).obj R).left, ⊤), kapS hY Λ Q (kumD (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0 Q) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0) Q) hdN (hβ Q) hgΛ))
    (resLE_kapS_sum hY Λ (fun Q => kumD (hζW c (locF (B := CommRingCat.of k[X]) G) R hζ0 Q) (hζWΓ c (locF (B := CommRingCat.of k[X]) G) R (ζ0 := ζ0) Q) hdN (hβ Q) hgΛ))
    hg.2.2.2)

end BadZero

end RamanujanPetersson.EtPBC.EtKum

end

end


