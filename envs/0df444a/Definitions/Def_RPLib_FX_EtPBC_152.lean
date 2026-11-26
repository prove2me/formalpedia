-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_152
-- name    : RPLib_FX_EtPBC_152
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T23:30:26.201065+00:00
-- url     : https://prove2.me/theorems/5467e65c-a749-5d17-9d68-2ce7f7a5c3a8
-- title:
--   Proper base change for the projective line, library file 152
-- statement:
--   File 152 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovHat5`: S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations
--   * `S4.Def_RP_EtPBC_A_O2Rel7`: S4-EtPBC-A, O2 REL (O2Rel7): the relation at `c(a)` lies in the localized subgroup
--   * `S4.Def_RP_EtPBC_A_O2L8b`: S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_145

/-!
# Proper base change for the projective line, library file 152

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovHat5`: S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations
* `S4.Def_RP_EtPBC_A_O2Rel7`: S4-EtPBC-A, O2 REL (O2Rel7): the relation at `c(a)` lies in the localized subgroup
* `S4.Def_RP_EtPBC_A_O2L8b`: S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_CovHat5 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2c-3e): fractions of `R`-combinations

* `ιP : R →+* ∏E₀ × ∏E₁`, `ιh₀ = β₀ ∘ ιB₀`, `ιh₁ = β₁ ∘ ιB₁`, **`levF_eq`** (`levF σ a = ∑ ιP (aᵢ) σᵢ`),
  **`frac₀_lin`**, **`frac₁_lin`**: fractions of `R`-combinations are combinations of fractions.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lin

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] {φ₀ : B₀ →+* N}
  {φ₁ : B₁ →+* N} {J₀ : Ideal B₀} {J₁ : Ideal B₁} {JN : Ideal N} {h₀ : J₀.map φ₀ = JN} {h₁ : J₁.map φ₁ = JN}
  {t₀ : B₀} {t₁ : B₁} (C : ∀ k, LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k)
  (H : ∀ k, TwoCovHom (down J₀ k) (down J₁ k) (down JN k) (C (k + 1)) (C k)) (ιB₀ : R →+* B₀)
  (ιB₁ : R →+* B₁) (hts : φ₀ t₀ * φ₁ t₁ = 1) (hφ₀ : IsAwayMap φ₀ t₀) (hu₀ : IsUnit (φ₀ t₀))
  (hφ₁ : IsAwayMap φ₁ t₁) (hu₁ : IsUnit (φ₁ t₁))

/-- **Fractions of combinations** (chart 0). -/
theorem frac₀_lin (hιB : φ₀.comp ιB₀ = φ₁.comp ιB₁) {r d : ℕ} {w : Fin r → (∀ k, (C k).E₀) × (∀ k, (C k).E₁)}
    (hw : ∀ i, w i ∈ Gam C H d) (c : Fin r → R) {x : (∀ k, (C k).E₀) × (∀ k, (C k).E₁)} (hx : x ∈ Gam C H d)
    (hsum : x = ∑ i, ιP C ιB₀ ιB₁ (c i) * w i) :
    frac₀ C H hts d x hx = ∑ i, ιh₀ C H ιB₀ hts hφ₁ hu₁ (c i) * frac₀ C H hts d (w i) (hw i) := by
  refine hE₀_ext hts d ?_ ?_
  · show x.1 = _
    rw [AddSubmonoidClass.coe_finsetSum, Prod.fst_sum, hsum, Prod.fst_sum]
    exact Finset.sum_congr rfl fun i _ => rfl
  · rw [frac₀_spec, AddSubmonoidClass.coe_finsetSum, Prod.snd_sum, Finset.mul_sum, hsum, Prod.snd_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hιc : φ₁ (ιB₁ (c i)) = φ₀ (ιB₀ (c i)) := (RingHom.congr_fun hιB (c i)).symm
    show jL₁ C (fB₁ C (ιB₁ (c i)) * (w i).2) = jL₁ C (sFm C ^ d) * (liftN₁ C hφ₁ hu₁ (φ₀ (ιB₀ (c i))) *
      (frac₀ C H hts d (w i) (hw i) : (∀ k, (C k).E₀) × L₁ C).2)
    rw [map_mul, ← liftN₁_φ₁ C hφ₁ hu₁ (ιB₁ (c i)), hιc, ← frac₀_spec hts (hw i)]
    ring

end Lin

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel7 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel7): the relation at `c(a)` lies in the localized subgroup

REL PLAN v2 (s126) + s128 fix, last REL file. `term_mem_cofinite` (O2Rel5) with `U₀ := U₁ = c(D(G))` and the bad-point
input `bad_term_at` (O2Rel6):
* **`bad_pt_root`**: a point of `c(A¹)` outside `c(D(G))` is `c(b)` for a root `b` of `G` (given `hpt`);
* **`rel_glob`** (DEF): `ε(S₀, U₁) ∘ Λ[prT S₀ U₁]^* κ_rel ∈ Gr` when points of `U₀` and outside `c(A¹)` are good.
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

section BadPt

variable {k : Type} [Field k] {P : Scheme.{0}} (c : A1 k ⟶ P) [IsOpenImmersion c] {G : k[X]}

/-- **`rel_glob`, generic in `κ`**: the term at `c(a)` lies in `Gr` when points of `Uo` and outside `c(A¹)` are good and
every bad point `c(b) ∉ Uo`, `b ≠ a`, has zero term. -/
theorem rel_glob_gen {Λ : Type} [CommRing Λ] {F : EtSh Λ P} (Gr : AddSubgroup (Ext.{0} (freeSh Λ (etId P)) F 2))
    (good : P → Prop) (hGd : ∀ x, good x → ∀ γ, IsLoc Λ F x γ → γ ∈ Gr)
    (κ : Ext.{0} (freeSh Λ (opEt (opnDg c G))) F 1) {Uo : P.Opens} {a : k} (hG0 : G ≠ 0)
    (hgood : ∀ x ∈ Uo, good x) (hgoodc : ∀ x ∉ Set.range c, good x)
    (hfin : (Set.range c)ᶜ.Finite) (hclc : ∀ x ∉ Set.range c, IsClosed ({x} : Set P))
    (hclA : ∀ b : k, IsClosed ({c (A1pt k b)} : Set P))
    (hpt : ∀ y : A1 k, G ∈ y.asIdeal → ∃ b, y = A1pt k b)
    (hbad : ∀ b : k, a ≠ b → c (A1pt k b) ∉ Uo →
      ∀ (V : P.Opens) (_hV : ∀ y : P, y ∈ V ↔ y ∈ opnDg c G ∨ y = c (A1pt k b))
      (Uz : P.Opens) (h : opnDg c G ≤ Uz) (hz : ∀ y : P, y ∈ Uz ↔ y ≠ c (A1pt k b))
      (hS : Subsingleton ((geomPtAt (c (A1pt k b))).point.fiber.obj (opEt V)))
      (hN : Nonempty ((geomPtAt (c (A1pt k b))).point.fiber.obj (opEt V)))
      (hR : ∀ v : (opEt V).left, (opEt V).hom v ∈ opnDg c G ∨ (opEt V).hom v = c (A1pt k b)),
      (locC_shortExact (Λ := Λ) (opEt V) h (c (A1pt k b)) hz hS hN hR).extClass.comp
        ((Ext.mk₀ (freeMap Λ (prT (opEt V) (opEt (opnDg c G))))).comp κ (zero_add 1))
        (show 1 + 1 = 2 from rfl) = 0)
    {S₀ : P.Etale} {Uz₀ : P.Opens} (h₀ : opnDg c G ≤ Uz₀) (hz₀ : ∀ x : P, x ∈ Uz₀ ↔ x ≠ c (A1pt k a))
    (hS₀ : Subsingleton ((geomPtAt (c (A1pt k a))).point.fiber.obj S₀))
    (hN₀ : Nonempty ((geomPtAt (c (A1pt k a))).point.fiber.obj S₀))
    (hR₀ : ∀ v : S₀.left, S₀.hom v ∈ opnDg c G ∨ S₀.hom v = c (A1pt k a)) :
    (locC_shortExact (Λ := Λ) S₀ h₀ (c (A1pt k a)) hz₀ hS₀ hN₀ hR₀).extClass.comp
      ((Ext.mk₀ (freeMap Λ (prT S₀ (opEt (opnDg c G))))).comp κ (zero_add 1))
      (show 1 + 1 = 2 from rfl) ∈ Gr := by
  refine term_mem_cofinite (opnDg c G) Gr good hGd κ h₀ hz₀ hS₀ hN₀ hR₀ ?_ ?_
    (fun hz => (hz₀ _).1 (h₀ hz) rfl) ?_
  · refine (hfin.union ((Polynomial.finite_setOfPred_isRoot hG0).image fun b => c (A1pt k b))).subset
      fun x hx => ?_
    by_cases hxc : x ∈ Set.range c
    · obtain ⟨b, rfl, hb⟩ := bad_pt_root c hx hxc hpt
      exact Or.inr ⟨b, hb, rfl⟩
    · exact Or.inl hxc
  · intro x hx
    by_cases hxc : x ∈ Set.range c
    · obtain ⟨b, rfl, -⟩ := bad_pt_root c hx hxc hpt
      exact hclA b
    · exact hclc x hxc
  · intro x hxU hxz
    by_cases hxo : x ∈ Uo
    · exact Or.inl (hgood x hxo)
    by_cases hxc : x ∈ Set.range c
    · obtain ⟨b, rfl, -⟩ := bad_pt_root c hxU hxc hpt
      refine Or.inr (hbad b ?_ hxo)
      rintro rfl
      exact hxz rfl
    · exact Or.inl (hgoodc x hxc)

end BadPt

section RelGlob

end RelGlob

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L8b =====
section

/-!
# S4-EtPBC-A, O2 L8b: `TrG` is onto and natural; `BCSurj 2` for `FGT` sheaves; killing degree-1 classes
* `TrG_surjective`, **`TrG_natural`** (`TrG G (x ∘ ιP^*m) = TrG H x ∘ ι^*m`);
* **`bcSurj_two_fgt`**: `BCSurj 2` for every `FGT` sheaf on `P¹_S` (`surjAt_coprod`, `bcSurj_two_free`, `bcSurj_two_of_epi`);
* `NT`, **`kill_lift`**: for `T` affine over `P¹_K`, every `κ ∈ Ext¹(Λ[T], ιP^*G)` is `κH ∘ ιP^*m` with `m : H ⟶ G`,
  `H` an `FGT` sheaf (`exists_kill` on `T`, `extFree_comp_mk₀`, the covariant exact sequence).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtCompact.Cech RamanujanPetersson.EtPBC.GenGeo RamanujanPetersson.EtPBC.Z3
  RamanujanPetersson.EtPBC.EtDeg RamanujanPetersson.EtPBC.EtKum RamanujanPetersson.EtCompact.GalTrE
  RamanujanPetersson.EtCompact.PushBC

universe u

section GenSurjG

universe w v₁ u₁ v₂ u₂

end GenSurjG

section TrG

variable {K : Type} [Field K] [IsAlgClosed K] {S : Scheme.{0}} (gS : S ⟶ Spec (CommRingCat.of K))
  (s : GeomPt S) [IsIso (s.pt ≫ gS)] (Λ : Type) [CommRing Λ]

theorem TrG_surjective (G : EtSh Λ (PV K gS)) : Function.Surjective (TrG gS s Λ G) :=
  surj_conj_genG (pull (fibToP1 K gS s) Λ) 2
    (pull_ext_bijective (Λ := Λ) (fibToP1 K gS s) (freeSh Λ (etId (P1 K))) ((pull (ιP gS s) Λ).obj G) 2).2
    (uE gS s Λ) (wG gS s Λ G)

end TrG

end RamanujanPetersson.EtPBC.EtMV

end

end


