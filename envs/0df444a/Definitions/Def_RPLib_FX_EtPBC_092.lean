-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_092
-- name    : RPLib_FX_EtPBC_092
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:25:45.713447+00:00
-- url     : https://prove2.me/theorems/2d24593c-c7d5-56a2-80d9-293250d4f47d
-- title:
--   Proper base change for the projective line, library file 092
-- statement:
--   File 092 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
--   * `S4.Def_RP_EtPBC_A_O2L8a`: S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_072
import Definitions.Def_RPLib_FX_EtPBC_077

/-!
# Proper base change for the projective line, library file 092

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat2`: S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts
* `S4.Def_RP_EtPBC_A_O2L8a`: S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_CovHat2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3b): the completed overlap ring and the maps from the base charts

* **`hE`** `⊆ L₀ × L₁` (fractions `x / T₁ᵃ T₀ᵇ`, `x ∈ Gam (a + b)`); **`hψ₀ : hE₀ →+* hE`**, **`hψ₁ : hE₁ →+* hE`**;
* `ρ₀_fB`, `ρ₁_fB`, **`famB_mem`**: `(fB₀ b₀, fB₁ b₁) ∈ Gam d` when `φ₀ b₀ = φ₀ t₀ ^ d * φ₁ b₁`;
* **`liftN₀ : N →+* L₀`**, **`liftN₁ : N →+* L₁`** (from `N = B₀[1/t₀] = B₁[1/t₁]`), `liftN₀_φ₀`, `liftN₁_φ₁`,
  `liftN₀_inv`, `liftN₁_inv`.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Hat2

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k))

/-- **`Ê₀ → Ê`** (`x / T₀ᵈ ↦ x / T₁⁰ T₀ᵈ`). -/
def hψ₀ (hts : φ₀ t₀ * φ₁ t₁ = 1) : hE₀ C H hts →+* hE C H hts :=
  ((RingHom.prodMap (jL₀ C) (RingHom.id (L₁ C))).comp (hE₀ C H hts).subtype).codRestrict (hE C H hts)
    fun z => by
      obtain ⟨d, x, hx, h1, h2⟩ := (mem_hE₀ C H hts z.1).1 z.2
      refine ⟨0, d, x, gam_cast C H (Nat.zero_add d).symm hx, ?_, h2⟩
      show jL₀ C (tFm C ^ 0) * jL₀ C z.1.1 = jL₀ C x.1
      rw [pow_zero, map_one, one_mul, h1]

theorem hψ₀_val (hts : φ₀ t₀ * φ₁ t₁ = 1) (z : hE₀ C H hts) :
    (hψ₀ C H hts z : L₀ C × L₁ C) = (jL₀ C (z : (∀ k, (C k).E₀) × L₁ C).1, (z : (∀ k, (C k).E₀) × L₁ C).2) :=
  rfl

end Hat2

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L8a =====
section

/-!
# S4-EtPBC-A, O2 L8a: finite coproducts, and the transport `TrG` for every sheaf on `P¹_S`
* **`Delta.surjAt_coprod`**: surjectivity on germs passes to finite coproducts (`ι : Type`, finite);
* `wGIso`, `wG`, `wG_natural`: `e^* ιP^* G ≅ ι^* G` (`e = fibToP1`, `e ≫ ιP = ι`), natural in `G`;
* **`TrG`** `G x = u ∘ e^*x ∘ wG`: `Ext²(Λ[P¹_K], ιP^*G) → Ext²(Λ_{P_s}, ι^*G)`; `TrGh` (additive, `rfl`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.PushBC

universe u

section TrG

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

/-- `TrG` as an additive map: `TrGh x = TrG x` by `rfl`. -/
def TrGh (G : EtSh Λ (PV K gS)) :
    Ext.{0} (freeSh Λ (etId (P1 K))) ((pull (ιP gS s) Λ).obj G) 2 →+
      Ext.{0} (unitSh Λ (fib (qV K gS) s)) ((pull (fibι (qV K gS) s) Λ).obj G) 2 :=
  (Ext.bilinearComp _ _ _ 0 2 2 (zero_add 2) (Ext.mk₀ (uE gS s Λ))).comp
    (((Ext.bilinearComp _ _ _ 2 0 2 (add_zero 2)).flip (Ext.mk₀ (wG gS s Λ G))).comp
      ((pull (fibToP1 K gS s) Λ).mapExtAddHom _ _ 2))

end TrG

end RamanujanPetersson.EtPBC.EtMV

end

end


